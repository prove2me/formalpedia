-- Prove2me | Definitions.Def_TDHamSim_QueryOptimal_Model
-- name    : TDHamSim_QueryOptimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:16:26.96049+00:00
-- url     : https://prove2.me/theorems/7a28c8bb-33a1-4629-9d3e-c7a1a7095ebe
-- title:
--   Registers, spectral norms, propagator and HAM-T access
-- statement:
--   An $n$-qubit register has basis the binary strings of length $n$ and state space $\mathbb C^{2^n}$ with its Euclidean norm. Matrices use the induced spectral norm. A Hamiltonian is Hermitian, bounded by $\alpha$, and $\beta$-Lipschitz on $[0,T]$. Its propagator is selected by the initial-value equation
--
--   $$iU_H'(t)=H(t)U_H(t),\qquad U_H(0)=I.$$
--
--   HAM-T is the direct sum of Hermitian unitary oracle blocks whose zero-ancilla compression is $H(jT/J)/\alpha$. Compression, insertion of zero auxiliary registers, and the reflection convention in (80) are also defined. The separate propagator specification target establishes existence and unitarity; the simulator never assumes an arbitrary propagator. Block encodings use the referenced published definition.
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Definition 2, Definition 3 and (7)–(9), pp.11–12; (80), p.31. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Mathlib
import Definitions.Def_ConstDepthUnitary_OGate
import Definitions.Def_QAlgorithms_Defs_BlockEncoding

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Mat (ι : Type) := Matrix ι ι ℂ
abbrev Ket (ι : Type) := EuclideanSpace ℂ ι

/-- All matrix norms in this development are the Euclidean operator norm. -/
noncomputable def opNorm {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : Matrix ι κ ℂ) : ℝ := ‖M‖
noncomputable def act {ι κ : Type} [Fintype κ] (M : Matrix ι κ ℂ) (v : Ket κ) : Ket ι :=
  WithLp.toLp 2 (M.mulVec v)
def IsUnitary {ι : Type} [Fintype ι] [DecidableEq ι] (M : Mat ι) : Prop :=
  M.conjTranspose * M = 1 ∧ M * M.conjTranspose = 1

def IsHamiltonian {n : ℕ} (H : ℝ → Mat (Bits n)) (α β T : ℝ) : Prop :=
  (∀ t ∈ Set.Icc 0 T, (H t).IsHermitian ∧ opNorm (H t) ≤ α) ∧
  ∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, opNorm (H t - H s) ≤ β * |t - s|

/-- The ODE on the closed time interval, with one-sided derivatives at its endpoints. -/
def IsPropagator {n : ℕ} (H U : ℝ → Mat (Bits n)) (T : ℝ) : Prop :=
  U 0 = 1 ∧ ContinuousOn U (Set.Icc 0 T) ∧
  ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt U ((-Complex.I) • (H t * U t)) (Set.Icc 0 T) t

/-- Select the uniquely characterized propagator. Existence is a separate target, never a
hypothesis supplied by a simulation certificate. At T=0 its terminal value is the identity. -/
noncomputable def propagator {n : ℕ} (H : ℝ → Mat (Bits n)) (T : ℝ) : ℝ → Mat (Bits n) :=
  if T = 0 then fun _ => 1 else Classical.epsilon (fun U => IsPropagator H U T)

noncomputable def grid (J : ℕ) (T : ℝ) (j : ℕ) : ℝ := j * T / J
noncomputable def stepWeight (α T : ℝ) (J : ℕ) : ℝ := α * T / J

/-- Definition 3: exact compression, Hermitian blocks and unitary blocks. -/
def IsHAMT {n a J : ℕ} (H : ℝ → Mat (Bits n)) (α T : ℝ)
    (O : Fin J → Mat (Bits a × Bits n)) : Prop :=
  ∀ j, (O j).IsHermitian ∧ IsUnitary (O j) ∧
    ∀ x y, O j ((fun _ => false), x) ((fun _ => false), y) =
      (α : ℂ)⁻¹ * H (grid J T j) x y

noncomputable def hamT {n a J : ℕ} (O : Fin J → Mat (Bits a × Bits n)) :
    Mat (Fin J × (Bits a × Bits n)) :=
  fun x y => if x.1 = y.1 then O x.1 x.2 y.2 else 0

/-- The source's block compression, shared with the published block-encoding definition. -/
noncomputable def block {κ ι : Type} (z : κ) (V : Mat (κ × ι)) : Mat ι :=
  fun x y => V (z, x) (z, y)
noncomputable def zeroIn {κ ι : Type} [DecidableEq κ] (z : κ) (v : Ket ι) : Ket (κ × ι) :=
  WithLp.toLp 2 (fun x => if x.1 = z then v x.2 else 0)
noncomputable def zeroProj {κ ι : Type} [DecidableEq κ] [DecidableEq ι] (z : κ) : Mat (κ × ι) :=
  fun x y => if x = y ∧ x.1 = z then 1 else 0

/-- (80), including the sign and the reflection convention of the paper. -/
noncomputable def amplify {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ]
    [DecidableEq ι] (z : κ) (V : Mat (κ × ι)) : Mat (κ × ι) :=
  let R := (2 : ℂ) • zeroProj (ι := ι) z - 1;
  -(V * R * V.conjTranspose * R * V)

noncomputable def qStar (α T ε : ℝ) : ℝ :=
  α * T + Real.log (1 / ε) / Real.log (Real.exp 1 + Real.log (1 / ε) / (α * T))
noncomputable def nStar (a : ℕ) (α β T ε : ℝ) : ℝ :=
  a + Real.log (1 + T * (α + β * T) / ε)

end TDHamSim.QueryOptimal


