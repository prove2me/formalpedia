-- Prove2me | Definitions.Def_TorchFire_Model_traceDist
-- name    : TorchFire_Model_traceDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:30:03.954905+00:00
-- url     : https://prove2.me/theorems/676bfc29-9b6f-48c0-a9cb-009f827ced3b
-- title:
--   Trace distance $D(\rho,\sigma)=\tfrac12\Vert\rho-\sigma\Vert_1$, partial traces, effects and averages
-- statement:
--   The quantum-information vocabulary of §3.
--
--   1. **Trace distance** $D(\rho,\sigma)=\tfrac12\Vert\rho-\sigma\Vert_1$, with the published trace norm $\Vert A\Vert_1=\mathrm{Tr}\sqrt{A^\dagger A}$ (`WildeQIT.traceNorm`).
--   2. The $\ell_2$ norm of a vector, the operator $|\psi\rangle\langle\psi|$, basis vectors $|s\rangle$, and conjugation $\rho\mapsto U\rho U^\dagger$.
--   3. **Discarding registers** $\mathrm{Tr}_J$ (through `WildeQIT.partialTraceRight` after a regrouping of the registers).
--   4. **The conditional state after a computational-basis measurement** of a classical register $K$: for outcome $k$, the unnormalized block $(\langle k|\otimes I)\rho(|k\rangle\otimes I)$, whose trace is $\Pr[k]$.
--   5. A linear map applied to one factor, $(I\otimes\Phi)(\rho)$, and the **acceptance effect** $E$ of a procedure $\Phi$ followed by a test $F$, characterized by $\mathrm{Tr}(E\rho)=\mathrm{Tr}(F\Phi(\rho))$ for all $\rho$.
--   6. Acceptance probabilities $\mathrm{Tr}(E\rho)$, effects $0\preceq E\preceq I$, subnormalized states ($\rho\succeq0$, $\mathrm{Tr}\rho\le1$), and the average over a finite uniform distribution.
--   7. The **cloning loop**: iterating a channel that returns a flame and a new current register, as in the cloning-correctness experiments (17) and (33).
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §3 pp.16–17 (states, effects, trace distance); (17) p.25, (33) p.45 (cloning loop)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_TorchFire_Model_basisMat

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix
open scoped ComplexOrder

namespace TorchFire.Model

/-- **Trace distance** `D(ρ, σ) = ½‖ρ − σ‖₁` (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with
Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593, §3 "Operator Norms and
Trace Distance", p.17), with the published trace norm `WildeQIT.traceNorm` (`Tr √(A†A)`). -/
noncomputable def traceDist {n : Type} [Fintype n] [DecidableEq n] (ρ σ : Matrix n n ℂ) : ℝ :=
  WildeQIT.traceNorm (ρ - σ) / 2

/-- The Euclidean (`ℓ₂`) norm `‖|ψ⟩‖` of a vector (p.16: "The norm `‖|ψ⟩‖` is the standard `ℓ₂`
norm"). -/
noncomputable def l2norm {n : Type} [Fintype n] (v : n → ℂ) : ℝ :=
  Real.sqrt (∑ i, Complex.normSq (v i))

/-- The density operator `|ψ⟩⟨ψ|` of a vector. -/
def ketbra {n : Type} (v : n → ℂ) : Matrix n n ℂ :=
  Matrix.of fun i j => v i * star (v j)

/-- The basis vector `|s⟩`. -/
def ket {n : Type} [DecidableEq n] (s : n) : n → ℂ := fun i => if i = s then 1 else 0

/-- Conjugation `ρ ↦ U ρ U†` by an operator (a unitary, an isometry, or a Kraus operator). -/
def conjMat {S T : Type} [Fintype S] (U : Matrix T S ℂ) (ρ : Matrix S S ℂ) : Matrix T T ℂ :=
  U * ρ * Uᴴ

/-- **Discarding registers.** If `uv : O × J → S` is a bijection exhibiting `S` as kept registers
`O` and discarded registers `J`, then `traceOutVia uv ρ = Tr_J ρ` ("tracing out workspace", p.56;
`WildeQIT.partialTraceRight` after the regrouping). -/
def traceOutVia {S O J : Type} [Fintype J] (uv : O × J → S) (ρ : Matrix S S ℂ) : Matrix O O ℂ :=
  WildeQIT.partialTraceRight (Matrix.of fun (x y : O × J) => ρ (uv x) (uv y))

/-- **The conditional (unnormalized) state after measuring a classical register.** For a state on
`K × A` and a computational-basis outcome `k` of the register `K`, `block ρ k` is
`(⟨k| ⊗ I) ρ (|k⟩ ⊗ I)`; its trace is the probability of `k` (§3 "Projectors and Measurements",
p.17: "The unnormalized state after outcome `i` is `Π_i ρ Π_i`"). -/
def block {K A : Type} (ρ : Matrix (K × A) (K × A) ℂ) (k : K) : Matrix A A ℂ :=
  Matrix.of fun a b => ρ (k, a) (k, b)

/-- **A linear map applied to one factor**: `(I_C ⊗ Φ)(ρ)` for a linear map `Φ` on matrices,
computed from `Φ`'s values on matrix units. -/
def idTensor {C A B : Type} [Fintype A] [DecidableEq A] (Φ : Matrix A A ℂ → Matrix B B ℂ)
    (ρ : Matrix (C × A) (C × A) ℂ) : Matrix (C × B) (C × B) ℂ :=
  Matrix.of fun x y => ∑ a, ∑ a', ρ (x.1, a) (y.1, a') * Φ (Matrix.single a a' 1) x.2 y.2

/-- **The acceptance effect of a procedure** (Heisenberg picture). For a linear map `Φ` (a channel)
and an effect `F` on its output, `heis Φ F` is the operator `E` with `Tr(E ρ) = Tr(F Φ(ρ))` for every
`ρ` (§3 "Quantum Effects", p.17: "Applying `V` and then testing `Π` has acceptance effect
`E = V†ΠV`"). Its entries are `E_{ab} = Tr(F Φ(|b⟩⟨a|))`. -/
def heis {A B : Type} [DecidableEq A] [Fintype B] (Φ : Matrix A A ℂ → Matrix B B ℂ) (F : Matrix B B ℂ) :
    Matrix A A ℂ :=
  Matrix.of fun a b => Matrix.trace (F * Φ (Matrix.single b a 1))

/-- The probability `Tr(E ρ)` (real part) that the test with effect `E` accepts `ρ`. -/
noncomputable def accProb {S : Type} [Fintype S] (E ρ : Matrix S S ℂ) : ℝ :=
  (Matrix.trace (E * ρ)).re

/-- **Expectation over a finite uniform distribution**: `E_{ω ← Ω}[f(ω)] = |Ω|⁻¹ Σ_ω f(ω)`
(§3, p.16: "`x ← S` to denote uniform sampling from `S`"). -/
noncomputable def avg (Ω : Type) [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω

/-- An **effect** `0 ⪯ E ⪯ I` (§3 "Quantum Effects", p.17). -/
def IsEffect {S : Type} [Fintype S] [DecidableEq S] (E : Matrix S S ℂ) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

/-- A possibly **subnormalized state**: `ρ ⪰ 0`, `Tr ρ ≤ 1` (§3 "Pure and Mixed States", p.17). -/
def IsSubState {S : Type} [Fintype S] (ρ : Matrix S S ℂ) : Prop :=
  ρ.PosSemidef ∧ (Matrix.trace ρ).re ≤ 1

/-- **Iterated application of a cloning-type channel** (the loop of (17) and (33), pp.25, 45).
`Φ` maps the current register `X` to a returned flame `F` (the first returned flame, which "replaces
the input register") and a new current register `X`. After `i` steps the state lives on
`(Fin i → F) × X`: the flames returned so far, in order, and the current register. -/
def chain {F X : Type} [Fintype X] [DecidableEq X] (Φ : Matrix X X ℂ → Matrix (F × X) (F × X) ℂ)
    (ρ₀ : Matrix X X ℂ) : (i : ℕ) → Matrix ((Fin i → F) × X) ((Fin i → F) × X) ℂ
  | 0 => Matrix.of fun x y => ρ₀ x.2 y.2
  | i + 1 =>
    let σ := idTensor Φ (chain Φ ρ₀ i)
    Matrix.of fun x y =>
      σ (Fin.init x.1, (x.1 (Fin.last i), x.2)) (Fin.init y.1, (y.1 (Fin.last i), y.2))

end TorchFire.Model


