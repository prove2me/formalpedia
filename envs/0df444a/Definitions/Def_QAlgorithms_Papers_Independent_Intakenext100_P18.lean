-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P18
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P18
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T04:21:49.090115+00:00
-- url     : https://prove2.me/theorems/44b8c02e-84eb-4f48-9185-c9c274b35504
-- title:
--   Definitions for General teleportation channel, singlet fraction and quasi-distillation
-- statement:
--   The objects the formalized statements of *General teleportation channel, singlet fraction and quasi-distillation* (arXiv:quant-ph/9807091) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `choiInverse`: PDF pp.3--4, (8)--(9): computed inverse on matrix units. Equivalently `d Tr_reference ((X^T tensor I) rho)`; the transpose belongs to the input X.
--   - `noisySinglet`: PDF p.5, (13): the original convex-mixture noisy-singlet family. Statements about this family impose 0 <= p <= 1.
--   - `retentionChannel`: PDF p.6, (18): source retention p. The frozen map uses noise weight, so it is called with 1-p. It includes Tr(X) on arbitrary operators.
--   - `stateTwirl`: PDF p.5, (17): U tensor conjugate U, averaged with probability Haar law. The second factor is entrywise conjugation, not adjoint.
--   - `standardTeleport`: PDF pp.4--6, (11)--(12),(20): actual complete Bell measurement followed by the outcome-conditioned correction. All d^2 branches are retained.
--   - `basisClassical`: PDF p.8: explicit classical achiever, measuring in the computational basis and preparing the basis state reported by Alice.
--   - `IsLocalFilter`: PDF pp.9--10: a local successful filter is a contraction. Its failure can be completed by sqrt(I-A†A), so it is a physical two-outcome operation.
--   - `ExactlyDistillable`: PDF p.9, (33): exact noncollective m-by-m distillation. Rectangular local maps include output-frame changes. Rescaling unrestricted A,B to contractions preserves the conditional state and positive success.
--   - `IsRankProjection`: PDF p.10: orthogonal rank-m projection on a local space.
--   - `coordinateProjection`: PDF p.10: Bob's projection onto his first N coordinates.
--   - `rectangularPlus`: PDF p.10: N-dimensional plus vector embedded in N tensor M.
--   - `rectangularResource`: PDF p.10: convex resource family for exact rectangular extraction.
-- source:
--   General teleportation channel, singlet fraction and quasi-distillation, arXiv:quant-ph/9807091v2, https://arxiv.org/abs/quant-ph/9807091v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P40

/-!
Statements from Horodecki, Horodecki and Horodecki, quant-ph/9807091v2.
All page citations below are PDF pages. Compilation is pending the batch handoff.
The general adaptive-LQCC nodes are explicitly deferred in the unit's HARD.md;
no separable-operation or fixed Bell-protocol surrogate is used for them.
-/

noncomputable section

open QAlgorithms MeasureTheory
open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P18

-- Pinned accepted imports, allowed by the independent-paper override.
open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)
open QAlgorithms.Papers.Independent.Support50.P11 (choiState teleportWeyl bellKet)
open QAlgorithms.Papers.Independent.Renew46.P40 (initialJoint)

/-- PDF pp.3--4, (8)--(9): computed inverse on matrix units. Equivalently
`d Tr_reference ((X^T tensor I) rho)`; the transpose belongs to the input X. -/
def choiInverse (d : ℕ)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Superop (Fin d) (Fin d) :=
  fun X a b => (d : ℂ) * ∑ i, ∑ j, X i j * rho (i, a) (j, b)

/-- PDF p.5, (13): the original convex-mixture noisy-singlet family.
Statements about this family impose 0 <= p <= 1. -/
def noisySinglet (d : ℕ) (hd : 0 < d) (p : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (p : ℂ) • maximallyEntangledDensity d + (((1 - p) / (d : ℝ)^2 : ℝ) : ℂ) • 1

/-- PDF p.6, (18): source retention p. The frozen map uses noise weight,
so it is called with 1-p. It includes Tr(X) on arbitrary operators. -/
def retentionChannel (d : ℕ) (hd : 0 < d) (p : ℝ) : Superop (Fin d) (Fin d) :=
  QuditFidelity.depolarizingMap d hd (1 - p)

/-- PDF p.5, (17): U tensor conjugate U, averaged with probability Haar law.
The second factor is entrywise conjugation, not adjoint. -/
def stateTwirl (d : ℕ)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    let W := Matrix.kronecker (U : Matrix (Fin d) (Fin d) ℂ)
      (fun i j => conj ((U : Matrix (Fin d) (Fin d) ℂ) i j))
    W * rho * Wᴴ ∂Schur.unitaryHaar d

/-- PDF pp.4--6, (11)--(12),(20): actual complete Bell measurement followed
by the outcome-conditioned correction. All d^2 branches are retained. -/
def standardTeleport (d : ℕ)
    (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : Superop (Fin d) (Fin d) :=
  fun X => ∑ c : Fin (d * d), conjSuperop (teleportWeyl d c)
    (traceLeft (conjSuperop
      (Matrix.kronecker (pureDensity (bellKet d c)) (1 : Matrix (Fin d) (Fin d) ℂ))
      (initialJoint X rho)))

/-- PDF p.8: explicit classical achiever, measuring in the computational
basis and preparing the basis state reported by Alice. -/
def basisClassical (d : ℕ) : Superop (Fin d) (Fin d) :=
  fun X i j => if i = j then X i i else 0

/-- PDF pp.9--10: a local successful filter is a contraction. Its failure
can be completed by sqrt(I-A†A), so it is a physical two-outcome operation. -/
def IsLocalFilter {N m : ℕ} (A : Matrix (Fin m) (Fin N) ℂ) : Prop :=
  (1 - Aᴴ * A).PosSemidef

/-- PDF p.9, (33): exact noncollective m-by-m distillation. Rectangular
local maps include output-frame changes. Rescaling unrestricted A,B to
contractions preserves the conditional state and positive success. -/
def ExactlyDistillable {N M : ℕ}
    (rho : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ) (m : ℕ) (hm : 0 < m) : Prop :=
  ∃ A : Matrix (Fin m) (Fin N) ℂ, ∃ B : Matrix (Fin m) (Fin M) ℂ,
    IsLocalFilter A ∧ IsLocalFilter B ∧
    (let omega := conjSuperop (Matrix.kronecker A B) rho;
     0 < omega.trace.re ∧ ((omega.trace.re)⁻¹ : ℂ) • omega = maximallyEntangledDensity m)

/-- PDF p.10: orthogonal rank-m projection on a local space. -/
def IsRankProjection {N : ℕ} (m : ℕ) (P : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  Pᴴ = P ∧ P * P = P ∧ P.rank = m

/-- PDF p.10: Bob's projection onto his first N coordinates. -/
def coordinateProjection (N M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal (fun i : Fin M => if i.val < N then 1 else 0)

/-- PDF p.10: N-dimensional plus vector embedded in N tensor M. -/
def rectangularPlus (N M : ℕ) : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ :=
  pureDensity (WithLp.toLp 2 fun z : Fin N × Fin M =>
    if z.1.val = z.2.val then ((Real.sqrt N)⁻¹ : ℂ) else 0)

/-- PDF p.10: convex resource family for exact rectangular extraction. -/
def rectangularResource (N M : ℕ) (p : ℝ)
    (tau : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ) :
    Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ :=
  (p : ℂ) • rectangularPlus N M + ((1 - p : ℝ) : ℂ) • tau

/-- Sanity: the computed matrix-unit inverse is homogeneous at zero. -/
example (d : ℕ) : choiInverse d 0 = fun _ => 0 := by
  funext X a b
  simp [choiInverse]

/-- Sanity: retention one means the identity channel. -/
example (d : ℕ) (hd : 0 < d) (X : Matrix (Fin d) (Fin d) ℂ) :
    retentionChannel d hd 1 X = X := by
  simp [retentionChannel, QuditFidelity.depolarizingMap]

/-- Sanity: mixture weight one selects the imported normalized plus projector. -/
example (d : ℕ) (hd : 0 < d) :
    noisySinglet d hd 1 = maximallyEntangledDensity d := by
  simp [noisySinglet]

/-- Sanity: a zero twirl has no affine constant. -/
example (d : ℕ) : stateTwirl d 0 = 0 := by
  simp [stateTwirl]

/-- Sanity: every retained Bell branch vanishes on the zero input operator. -/
example (d : ℕ) (rho : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    standardTeleport d rho 0 = 0 := by
  have hzero : initialJoint (0 : Matrix (Fin d) (Fin d) ℂ) rho = 0 := by
    ext a b
    simp [initialJoint]
  have hmat : Matrix.of (fun (_ _ : Fin d) => (0 : ℂ)) =
      (0 : Matrix (Fin d) (Fin d) ℂ) := rfl
  simp [standardTeleport, hzero, conjSuperop, traceLeft, hmat]

/-- Sanity: the classical achiever preserves each diagonal coefficient. -/
example (d : ℕ) (X : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) :
    basisClassical d X i i = X i i := by simp [basisClassical]

/-- Sanity: identity is a physical local filter. -/
example (N : ℕ) : IsLocalFilter (1 : Matrix (Fin N) (Fin N) ℂ) := by
  simp [IsLocalFilter, Matrix.PosSemidef.zero]

/-- Sanity: identity is a full-rank orthogonal projection. -/
example (N : ℕ) : IsRankProjection N (1 : Matrix (Fin N) (Fin N) ℂ) := by
  simp [IsRankProjection]

/-- Sanity: Bob retains the first coordinate in the rectangular example. -/
example : coordinateProjection 1 2 0 0 = 1 := by
  norm_num [coordinateProjection]

/-- Sanity: the embedded one-dimensional target is |00><00|. -/
example : rectangularPlus 1 2 (0, 0) (0, 0) = 1 := by
  norm_num [rectangularPlus, pureDensity]

/-- Sanity: weight one selects the rectangular target. -/
example (N M : ℕ) (tau : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ) :
    rectangularResource N M 1 tau = rectangularPlus N M := by
  simp [rectangularResource]

/-- Sanity: a zero resource has zero success and cannot satisfy exact distillation. -/
example {N M : ℕ} (m : ℕ) (hm : 0 < m) :
    ¬ ExactlyDistillable (0 : Matrix (Fin N × Fin M) (Fin N × Fin M) ℂ) m hm := by
  rintro ⟨A, B, _, _, hp, _⟩
  simpa [conjSuperop] using hp

end QAlgorithms.Papers.Independent.Intakenext100.P18


