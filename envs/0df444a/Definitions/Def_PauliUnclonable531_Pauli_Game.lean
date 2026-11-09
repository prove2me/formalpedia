-- Prove2me | Definitions.Def_PauliUnclonable531_Pauli_Game
-- name    : PauliUnclonable531_Pauli_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:36.74148+00:00
-- url     : https://prove2.me/theorems/f968cd18-3efd-4f90-9610-0d5f41b48250
-- title:
--   Pre-key splitting attacks and the full one-bit game
-- statement:
--   An attack has one key-independent complex-linear CPTP channel Φ from the ciphertext to arbitrary finite registers B⊗C, and key-dependent local binary POVMs. Each zero effect and its identity complement must be positive semidefinite. The published binary-POVM constructor supplies the two effects; the published all-ancilla channel predicate supplies admissibility.
--
--   For adversarial challenge messages u,v∈{0,1}, the game samples k and a bit b independently and uniformly, encrypts u when b=0 and v otherwise, and accepts exactly when both local outcomes equal b:
--
--   $$p_{u,v}=\sum_k\Pr[k]\,\frac12\sum_{b=0}^1\operatorname{Tr}[(\Lambda^k_{B,b}\otimes\Lambda^k_{C,b})\Phi(\rho_{k,m_b})].$$
--
--   The real part is used for Born probabilities. win is the pair (0,1). GeneralAttack conditions on all four message pairs, with nonnegative masses summing to one and unrestricted conditional attacks. This includes randomized message selection and correlated auxiliary preparation; these physical conditions do not assert security.
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Definitions 2.10–2.11 and Remark 2.12, pp.14–15; §4.1, p.18

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Scheme
import Definitions.Def_MayersBC_binaryPOVM

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Paper-specific attack wrapper (§2.3, pp.14–15). Effects are arbitrary PSD binary
POVMs; the splitter is independent of the unrevealed key. -/
structure Attack (n : ℕ) (B C : Type) [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] where
  split : Op (Bits n) →ₗ[ℂ] Op (B × C)
  channel : WildeQIT.EntBreaking.IsQuantumChannel split
  bobZero : Key n → Op B
  charlieZero : Key n → Op C
  bob_pos : ∀ k, (bobZero k).PosSemidef
  bob_complement_pos : ∀ k, (1 - bobZero k).PosSemidef
  charlie_pos : ∀ k, (charlieZero k).PosSemidef
  charlie_complement_pos : ∀ k, (1 - charlieZero k).PosSemidef

variable {n : ℕ} {B C : Type} [Fintype B] [Fintype C] [DecidableEq B] [DecidableEq C]

def bobEffect (a : Attack n B C) (k : Key n) (b : Fin 2) : Op B :=
  MayersBC.binaryPOVM (a.bobZero k) b

def charlieEffect (a : Attack n B C) (k : Key n) (b : Fin 2) : Op C :=
  MayersBC.binaryPOVM (a.charlieZero k) b

/-- Uniform independent key and challenge bit. m₀,m₁ are adversarial one-bit messages. -/
noncomputable def pairWin (scheme : Scheme n) (a : Attack n B C) (m₀ m₁ : Fin 2) : ℝ :=
  ∑ k : Key n, scheme.gen k * ((1/2 : ℝ) * ∑ b : Fin 2,
    born (Matrix.kronecker (bobEffect a k b) (charlieEffect a k b))
      (a.split (scheme.enc k (if b = 0 then m₀ else m₁))))

noncomputable def win (a : Attack n B C) : ℝ := pairWin (explicitScheme n) a 0 1

/-- Conditioning on the four possible message pairs includes correlated auxiliary
preparation, as in Remark 2.12. Each conditional splitter is unrestricted CPTP. -/
structure GeneralAttack (n : ℕ) (B C : Type) [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] where
  mass : Fin 2 → Fin 2 → ℝ
  nonneg : ∀ u v, 0 ≤ mass u v
  normalized : (∑ u, ∑ v, mass u v) = 1
  conditional : Fin 2 → Fin 2 → Attack n B C

noncomputable def generalWin (scheme : Scheme n) (a : GeneralAttack n B C) : ℝ :=
  ∑ u, ∑ v, a.mass u v * pairWin scheme (a.conditional u v) u v

end PauliUnclonable531.Pauli


