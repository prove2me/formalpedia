-- Prove2me | Definitions.Def_OAIQ098D002
-- name    : OAIQ098D002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:21:41.498017+00:00
-- url     : https://prove2.me/theorems/6e604338-aa17-440e-aa17-5c04f6142599
-- title:
--   Definitions bundle OAIQ098D002 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 137 declarations of OpenAI's Lean: 33 definitions, 8 instances and 96 theorems. The definitions and types are `OAI.SharpPlanar.IntegerBasis.densityNum`, `OAI.SharpPlanar.Numerical.lDeriv`, `OAI.SharpPlanar.atomBase`, `OAI.SharpPlanar.atomFactorRat`, `OAI.SharpPlanar.atomMass`, `OAI.SharpPlanar.bernsteinWeight`, `OAI.SharpPlanar.complexDirectFactor`, `OAI.SharpPlanar.deletedPolynomial`, `OAI.SharpPlanar.dilateSchwartz`, `OAI.SharpPlanar.directKernel`, `OAI.SharpPlanar.expCut`, `OAI.SharpPlanar.expCutSchwartz`, `OAI.SharpPlanar.gaussianSchwartz`, `OAI.SharpPlanar.halfBase`, `OAI.SharpPlanar.hexForm`, `OAI.SharpPlanar.hexNat`, `OAI.SharpPlanar.jetPartial`, `OAI.SharpPlanar.jetTaylor`, `OAI.SharpPlanar.leftHalf`, `OAI.SharpPlanar.liftedInverse`, `OAI.SharpPlanar.momentPower`, `OAI.SharpPlanar.piUpper`, `OAI.SharpPlanar.pieceBase`, `OAI.SharpPlanar.powerToBernstein`, `OAI.SharpPlanar.rightHalf`, `OAI.SharpPlanar.rowDUpper`, `OAI.SharpPlanar.rowQLower`, `OAI.SharpPlanar.scaleEquiv`, `OAI.SharpPlanar.spectralForm`, `OAI.SharpPlanar.tableConstant`, `OAI.SharpPlanar.thetaKernel`, `OAI.SharpPlanar.zCap`, `OAI.starSubalgebraCommCStarAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_AtomTail`, `PlanarPacking_BarrierProduct`, `PlanarPacking_BernsteinSign`, `PlanarPacking_CanonicalRows`, `PlanarPacking_Cardinal`, `PlanarPacking_Certificate_TableData`, `PlanarPacking_Dilation`, `PlanarPacking_Entire`, `PlanarPacking_FiniteLift`, `PlanarPacking_HexLattice`, `PlanarPacking_HighFactorBase`, `PlanarPacking_Indices`, `PlanarPacking_RationalBounds`, `PlanarPacking_Schur`, `PlanarPacking_TaylorControl`, `PlanarPacking_Theta`.
--
--   **Imports.** It imports the published bundle `Def_PlanarPacking`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ098D005`; the statements `OAI.SharpPlanar.atomBase_contains`, `OAI.SharpPlanar.atomBase_pos`, `OAI.SharpPlanar.basis_piece_integrable`, `OAI.SharpPlanar.complexDirectFactor_disk_bound`, `OAI.SharpPlanar.continuous_directKernel`, `OAI.SharpPlanar.decay_atomBase`, `OAI.SharpPlanar.directDensity_split`, `OAI.SharpPlanar.directDensity_tsum`, `OAI.SharpPlanar.directIntegrand_analytic`, `OAI.SharpPlanar.directIntegrand_disk_bound`, `OAI.SharpPlanar.directKernel_norm`, `OAI.SharpPlanar.directMoment_piece_average_error`, `OAI.SharpPlanar.directMoment_piece_error`, `OAI.SharpPlanar.directMoment_rule_error`, `OAI.SharpPlanar.direct_basis_integral_bound`, `OAI.SharpPlanar.direct_basis_integral_summable`, `OAI.SharpPlanar.direct_basis_pair`, `OAI.SharpPlanar.direct_piece_integrable` and `OAI.SharpPlanar.normalized_direct`; the proofs of `OAI.SharpPlanar.atomBase_pos`, `OAI.SharpPlanar.basis_piece_integrable`, `OAI.SharpPlanar.complexDirectFactor_disk_bound`, `OAI.SharpPlanar.continuous_directKernel`, `OAI.SharpPlanar.directDensity_split`, `OAI.SharpPlanar.directDensity_tsum`, `OAI.SharpPlanar.directIntegrand_analytic`, `OAI.SharpPlanar.directIntegrand_disk_bound`, `OAI.SharpPlanar.directKernel_norm`, `OAI.SharpPlanar.directMoment_piece_average_error`, `OAI.SharpPlanar.directMoment_piece_error`, `OAI.SharpPlanar.directMoment_rule_error`, `OAI.SharpPlanar.direct_basis_integral_bound`, `OAI.SharpPlanar.direct_basis_integral_summable`, `OAI.SharpPlanar.direct_basis_pair`, `OAI.SharpPlanar.direct_piece_integrable` and `OAI.SharpPlanar.normalized_direct`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Definitions.Def_PlanarPacking

section
-- module Solutions.OAIQ098_PP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open Complex

noncomputable def complexDirectFactor (m y : ℝ) (ell : ℕ) (t : ℂ) : ℂ :=
  Complex.exp (Complex.I*Real.pi*t*m) * (Complex.I*Real.pi*t*y)^ell / (ell.factorial:ℂ)

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


noncomputable def zCap : Fin 7 → ℝ := ![2934/1000,2713/1000,2269/1000,1859/1000,1548/1000,1320/1000,1151/1000]

end SharpPlanar

namespace SharpPlanar.IntegerBasis

-- Zero-based piece indexing: this is exactly the source M_1,...,M_6.
def densityNum : Fin 6 → ℤ := ![56,48,35,25,19,1571]

lemma unit_phase_norm (n : ℕ) (t : ℝ) : ‖Complex.exp (-Complex.I*Real.pi*t*n)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

end SharpPlanar.IntegerBasis

namespace SharpPlanar
open IntegerBasis

lemma zCap_nonneg (j : Fin 7) : 0 ≤ zCap j := by fin_cases j <;> norm_num [zCap]
noncomputable def atomMass : Fin 7 → ℝ := ![5,4,4,4,2,4,2]

lemma exp_segment_bound {a l u : ℝ} (ha : 0 ≤ a) (hlu : l ≤ u) :
    (∫ t in l..u, Real.exp (-a*(u-t))) ≤ if a=0 then u-l else min (u-l) (1/a) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-a*(u-t))) := by fun_prop
  have hcl : (∫ t in l..u, Real.exp (-a*(u-t))) ≤ u-l := by
    calc
      _ ≤ ∫ t in l..u, (1:ℝ) := by
        apply intervalIntegral.integral_mono_on hlu (hc.intervalIntegrable l u) (continuous_const.intervalIntegrable l u)
        intro t ht
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (sub_nonneg.mpr ht.2)
      _ = u-l := by simp
  split_ifs with h0
  · exact hcl
  · apply le_min hcl
    have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
    have hp : ∀ t ∈ Set.uIcc l u, HasDerivAt (fun t : ℝ => Real.exp (-a*(u-t))/a)
        (Real.exp (-a*(u-t))) t := by
      intro t _
      exact ((((hasDerivAt_id t).const_sub u).const_mul (-a)).exp.div_const a).congr_deriv (by simp [h0])
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hp (hc.intervalIntegrable l u)]
    simp only [sub_self,mul_zero,Real.exp_zero]
    exact sub_le_self _ (div_nonneg (Real.exp_pos _).le ha)

end SharpPlanar

namespace SharpPlanar
open IntegerBasis


lemma periodic_geometric_sum {f : ℕ → ℝ} {q : ℝ} (hf : ∀ n, 0 ≤ f n)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hb : ∀ (a : Fin 12) (k : ℕ), f (k*12+a.val) ≤ q^k*f a.val) :
    Summable f ∧ (∑' n, f n) ≤ (∑ a : Fin 12, f a.val)/(1-q) := by
  let g : ℕ × Fin 12 → ℝ := fun p => q^p.1*f p.2.val
  have hgeom := (hasSum_geometric_of_lt_one hq0 hq1).summable
  have hg : Summable g := by
    apply (summable_prod_of_nonneg (fun p => mul_nonneg (pow_nonneg hq0 _) (hf _))).mpr
    constructor
    · intro k; exact summable_of_hasFiniteSupport (Set.toFinite _)
    · simpa only [g,← Finset.mul_sum,tsum_fintype] using hgeom.mul_right (∑ a : Fin 12, f a.val)
  have hh : Summable (fun p : ℕ × Fin 12 => f (p.1*12+p.2.val)) :=
    Summable.of_nonneg_of_le (fun _ => hf _) (fun p => hb p.2 p.1) hg
  have heq : (fun p : ℕ × Fin 12 => f (p.1*12+p.2.val)) = f ∘ (Nat.divModEquiv 12).symm := rfl
  have hs : Summable f := ((Nat.divModEquiv 12).symm.summable_iff).mp (heq ▸ hh)
  refine ⟨hs,?_⟩
  calc
    (∑' n, f n) = ∑' p : ℕ × Fin 12, f (p.1*12+p.2.val) := by
      exact ((Nat.divModEquiv 12).symm.tsum_eq f).symm
    _ ≤ ∑' p : ℕ × Fin 12, g p := hh.tsum_le_tsum (fun p => hb p.2 p.1) hg
    _ = (∑ a : Fin 12, f a.val)/(1-q) := by
      rw [hg.tsum_prod]
      simp only [g,tsum_fintype,← Finset.mul_sum,tsum_mul_right]
      rw [tsum_geometric_of_lt_one hq0 hq1]
      rw [div_eq_mul_inv]
      ring

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

lemma paired_jet_bound {q : ℝ} (hq : 0 < q) (d a b : ℝ) :
    |-a/q|+|(d*a-b)/q| ≤ ((1+|d|)*|a|+|b|)/q := by
  rw [abs_div,abs_div,abs_neg,abs_of_pos hq,← add_div]
  apply div_le_div_of_nonneg_right _ hq.le
  have hh := abs_sub (d*a) b
  rw [abs_mul] at hh
  nlinarith

end SharpPlanar

namespace SharpPlanar
open IntegerBasis

noncomputable def rowQLower (n : ℕ) : ℝ :=
  if n%12=0 ∨ n%12=4 then 32898/10000 else
  if n%12=1 ∨ n%12=3 then 17629/10000 else 24555/1000
noncomputable def rowDUpper (n : ℕ) : ℝ :=
  if n%12=0 ∨ n%12=4 then 21162/10000 else
  if n%12=1 ∨ n%12=3 then 8260/10000 else 2214/10000

lemma pi_fine : (314159/100000:ℝ) < Real.pi ∧ Real.pi < 31416/10000 := by
  constructor <;> linarith [Real.pi_gt_d6,Real.pi_lt_d6]

end SharpPlanar

namespace SharpPlanar
open IntegerBasis
noncomputable def pieceBase : Fin 6 → ℝ := ![469/1000000,7279/1000000,59165/1000000,219974/1000000,494744/1000000,828986/1000000]
lemma pieceBase_pos (j : Fin 6) : 0 < pieceBase j := by fin_cases j <;> norm_num [pieceBase]
lemma pieceBase_lt_one (j : Fin 6) : pieceBase j < 1 := by fin_cases j <;> norm_num [pieceBase]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_AtomTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerBasis
noncomputable def atomBase : Fin 7 → ℝ := ![1/10000,469/1000000,7279/1000000,59165/1000000,219974/1000000,494744/1000000,828986/1000000]
noncomputable def atomFactorRat (j : Fin 7) (n : ℕ) : ℝ := (1+rowDUpper n+(31416/10000:ℝ)*zCap j)/rowQLower n
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BarrierProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpPlanar
open Set Filter
open scoped Topology

noncomputable def leftHalf : ℕ → ℝ
  | 0 => 3/2 | 1 => 1/2 | 3 => 1 | 4 => 1/2 | 7 => 3/2 | 9 => 1 | _ => 0
noncomputable def rightHalf : ℕ → ℝ
  | 0 => 1/2 | 1 => 1 | 3 => 1/2 | 4 => 3/2 | 7 => 1 | 9 => 3/2 | _ => 0

end SharpPlanar


end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BernsteinSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Finset

noncomputable def bernsteinWeight (d k : ℕ) (v : ℝ) : ℝ :=
  (d.choose k : ℝ) * v^k * (1-v)^(d-k)
noncomputable def powerToBernstein (d : ℕ) (T : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ r ∈ range (k+1), (k.choose r : ℝ) / (d.choose r : ℝ) * T r

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

open scoped BigOperators
namespace SharpPlanar


noncomputable def tableConstant (i : Bool) : ℚ := if i then 17/1000 else -13/1000

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Dilation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped FourierTransform
noncomputable def scaleEquiv (a : ℝ) (ha : a≠0) : Plane ≃L[ℝ] Plane where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℝ Plane a ha
  continuous_toFun := continuous_const_smul a
  continuous_invFun := continuous_const_smul a⁻¹
noncomputable def dilateSchwartz (f : SchwartzMap Plane ℝ) (a : ℝ) (ha : a≠0) : SchwartzMap Plane ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (scaleEquiv a ha) f
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar

noncomputable def spectralForm : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (-1/2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ

end SharpPlanar

namespace SharpPlanar
open MeasureTheory Set

noncomputable def directKernel (ell : ℕ) (s t : ℝ) : ℂ :=
  (Complex.I*Real.pi*(t:ℂ))^ell * Complex.exp (Complex.I*Real.pi*(t:ℂ)*s)

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

namespace SharpPlanar

noncomputable def expCut (c x : ℝ) : ℝ :=
  Real.smoothTransition (x+1) * Real.exp (-c*x)

lemma expCut_smooth (c : ℝ) : ContDiff ℝ ∞ (expCut c) := by
  unfold expCut
  fun_prop

lemma expCut_eq (c x : ℝ) (hx : 0 ≤ x) : expCut c x = Real.exp (-c*x) := by
  simp [expCut, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x+1)]

lemma expCut_zero (c x : ℝ) (hx : x ≤ -1) : expCut c x = 0 := by
  simp [expCut, Real.smoothTransition.zero_of_nonpos (by linarith : x+1 ≤ 0)]

lemma iteratedDeriv_expCut_pos (c : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (expCut c) x = (-c)^n * Real.exp (-c*x) := by
  have he : expCut c =ᶠ[𝓝 x] (fun y => Real.exp (-c*y)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact expCut_eq c y hy.le
  rw [he.iteratedDeriv_eq n, iteratedDeriv_exp_const_mul]

lemma iteratedDeriv_expCut_neg (c : ℝ) (n : ℕ) {x : ℝ} (hx : x < -1) :
    iteratedDeriv n (expCut c) x = 0 := by
  have he : expCut c =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [eventually_lt_nhds hx] with y hy
    exact expCut_zero c y hy.le
  rw [he.iteratedDeriv_eq n]
  simp

lemma expCut_decay (c : ℝ) (hc : 0 < c) (k n : ℕ) :
    ∃ C : ℝ, ∀ x, ‖x‖^k * ‖iteratedFDeriv ℝ n (expCut c) x‖ ≤ C := by
  let g : ℝ → ℝ := fun x => ‖x‖^k * ‖iteratedDeriv n (expCut c) x‖
  have hg : Continuous g := by
    exact (continuous_norm.pow k).mul
      (((expCut_smooth c).continuous_iteratedDeriv n (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).norm)
  have ht : Tendsto g atTop (𝓝 0) := by
    have he : g =ᶠ[atTop] (fun x : ℝ => (x^(k : ℝ) * Real.exp (-c*x)) * ‖(-c)^n‖) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      change ‖x‖^k * ‖iteratedDeriv n (expCut c) x‖ = _
      rw [iteratedDeriv_expCut_pos c n hx, norm_mul]
      simp only [Real.norm_eq_abs, abs_of_pos hx, Real.rpow_natCast, Real.abs_exp]
      ring
    apply Tendsto.congr' he.symm
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).mul_const ‖(-c)^n‖
  have hb : Tendsto g atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_lt_atBot (-1 : ℝ)] with x hx
    simp [g, iteratedDeriv_expCut_neg c n hx]
  have hbd := hg.isBounded_range_iff_isBigO_atTop_atBot.mpr
    ⟨ht.isBigO_one ℝ, hb.isBigO_one ℝ⟩
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  refine ⟨C, fun x => ?_⟩
  have hx := hC (g x) (mem_range_self x)
  simpa only [g, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_abs, norm_norm] using hx

noncomputable def expCutSchwartz (c : ℝ) (hc : 0 < c) : SchwartzMap ℝ ℝ where
  toFun := expCut c
  smooth' := expCut_smooth c
  decay' := expCut_decay c hc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


noncomputable def gaussianSchwartz (c : ℝ) (hc : 0 < c) : SchwartzMap E ℝ :=
  SchwartzMap.compCLM ℝ (g := fun x : E => ‖x‖^2) (Function.hasTemperateGrowth_norm_sq E)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
      nlinarith [sq_nonneg (‖x‖-1)]⟩ (expCutSchwartz c hc)

end SharpPlanar


open scoped SchwartzMap

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

section Neumann
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


theorem neumann_exists_unique (T : E →L[ℝ] E) (hT : ‖T‖ < 1) (r : E) :
    ∃! x : E, x - T x = r := by
  have hb : Function.Bijective (1 - T : E →L[ℝ] E) :=
    ContinuousLinearMap.isUnit_iff_bijective.mp (isUnit_one_sub_of_norm_lt_one hT)
  obtain ⟨x, hx⟩ := hb.surjective r
  refine ⟨x, hx, ?_⟩
  intro y hy
  apply hb.injective
  exact hy.trans hx.symm


end Neumann

section Schur
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


omit [CompleteSpace F] in
theorem finite_schur_bound
    (V : E →L[ℝ] E) (U : F →L[ℝ] E) (L : E →L[ℝ] F) (D : F →L[ℝ] F)
    (hV : ‖V‖ ≤ 32) (hD : ‖D‖ ≤ 28/100) (hL : ‖L‖ ≤ 11/100)
    (hVU : ‖V.comp U‖ ≤ 37/10)
    {x rE : E} {y rF : F} (hx : x = V (rE + U y))
    (hy : y - L x - D y = rF) :
    ‖x‖ + ‖y‖ ≤ 90 * (‖rE‖ + ‖rF‖) := by
  have hxnorm : ‖x‖ ≤ 32 * ‖rE‖ + (37/10) * ‖y‖ := calc
    ‖x‖ = ‖V rE + (V.comp U) y‖ := by rw [hx]; simp
    _ ≤ ‖V rE‖ + ‖(V.comp U) y‖ := norm_add_le _ _
    _ ≤ ‖V‖ * ‖rE‖ + ‖V.comp U‖ * ‖y‖ := add_le_add (V.le_opNorm _) ((V.comp U).le_opNorm _)
    _ ≤ 32 * ‖rE‖ + (37/10) * ‖y‖ := by gcongr
  have hyrepr : y = rF + L x + D y := by rw [← hy]; abel
  have hynorm : ‖y‖ ≤ ‖rF‖ + (11/100) * ‖x‖ + (28/100) * ‖y‖ := calc
    ‖y‖ = ‖rF + L x + D y‖ := congrArg norm hyrepr
    _ ≤ ‖rF‖ + ‖L x‖ + ‖D y‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖rF‖ + ‖L‖ * ‖x‖ + ‖D‖ * ‖y‖ := by
      gcongr
      exacts [L.le_opNorm _, D.le_opNorm _]
    _ ≤ ‖rF‖ + (11/100) * ‖x‖ + (28/100) * ‖y‖ := by gcongr
  nlinarith [norm_nonneg rE, norm_nonneg rF]


end Schur
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
section Lift
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


noncomputable def liftedInverse (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F) : E →L[ℝ] E :=
  1 + I.comp (V.comp (R.comp S))

lemma liftedInverse_apply (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F) (x : E) :
    liftedInverse I R S V x = x + I (V (R (S x))) := rfl

lemma liftedInverse_left (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hVA : ∀ y, V (y - R (S (I y))) = y) (x : E) :
    liftedInverse I R S V (x-I (R (S x))) = x := by
  rw [liftedInverse_apply,map_sub,map_sub,hVA]
  abel

lemma liftedInverse_right (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hAV : ∀ y, V y - R (S (I (V y))) = y) (x : E) :
    liftedInverse I R S V x - I (R (S (liftedInverse I R S V x))) = x := by
  rw [liftedInverse_apply,map_add,map_add,map_add]
  have h := congrArg I (hAV (R (S x)))
  rw [map_sub] at h
  calc
    _ = x + (I (V (R (S x))) - I (R (S (I (V (R (S x)))))) - I (R (S x))) := by abel
    _ = x := by rw [h]; simp

lemma liftedInverse_norm (I : F →L[ℝ] E) (R : E →L[ℝ] F)
    (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hI : ‖I‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hS : ‖S‖ ≤ 28) (hV : ‖V‖ ≤ 90) :
    ‖liftedInverse I R S V‖ ≤ 2521 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [liftedInverse_apply]
  calc
    ‖x + I (V (R (S x)))‖ ≤ ‖x‖ + ‖I (V (R (S x)))‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ‖I‖*(‖V‖*(‖R‖*(‖S‖*‖x‖))) := by
      gcongr
      exact (I.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((V.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          ((R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg _)))
          (norm_nonneg _))) (norm_nonneg _))
    _ ≤ ‖x‖ + 1*(90*(1*(28*‖x‖))) := by gcongr
    _ = 2521*‖x‖ := by ring


theorem finiteLift_exists_unique [CompleteSpace E]
    (I : F →L[ℝ] E) (R : E →L[ℝ] F) (S : E →L[ℝ] E) (V : F →L[ℝ] F)
    (hVA : ∀ y, V (y - R (S (I y))) = y)
    (hAV : ∀ y, V y - R (S (I (V y))) = y)
    (hI : ‖I‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hS : ‖S‖ ≤ 28) (hV : ‖V‖ ≤ 90)
    (htail : ‖S-I.comp (R.comp S)‖ ≤ 1/2000000000) (r : E) :
    ∃! x : E, x-S x = r := by
  let B := liftedInverse I R S V
  let T := B.comp (S-I.comp (R.comp S))
  have hB : ‖B‖ ≤ 2521 := liftedInverse_norm I R S V hI hR hS hV
  have hT : ‖T‖ ≤ 2521/2000000000 := calc
    ‖T‖ ≤ ‖B‖*‖S-I.comp (R.comp S)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 2521*(1/2000000000) := by gcongr
    _ = _ := by ring
  have hBinj : Function.Injective B := by
    intro x y he
    have hx := liftedInverse_right I R S V hAV x
    have hy := liftedInverse_right I R S V hAV y
    rw [show liftedInverse I R S V x = liftedInverse I R S V y from he] at hx
    exact hx.symm.trans hy
  have heq (x : E) : B (x-S x) = x-T x := by
    have hx := liftedInverse_left I R S V hVA x
    change B (x-I (R (S x))) = x at hx
    simp only [map_sub] at hx
    change B (x - S x) = x - B (S x - I (R (S x)))
    simp only [map_sub]
    calc
      _ = (B x - B (I (R (S x)))) - (B (S x) - B (I (R (S x)))) := by abel
      _ = _ := by rw [hx]
  obtain ⟨x,hx,hu⟩ := neumann_exists_unique T (hT.trans_lt (by norm_num)) (B r)
  refine ⟨x, hBinj (by rw [heq]; exact hx), ?_⟩
  intro y hy
  apply hu
  rw [← heq,hy]


end Lift
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HexLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
def hexForm (v : ℤ×ℤ) : ℤ := v.1^2+v.1*v.2+v.2^2
def hexNat (v : ℤ×ℤ) : ℕ := (hexForm v).toNat
lemma hexForm_nonneg (v : ℤ×ℤ) : 0 ≤ hexForm v := by
  unfold hexForm
  nlinarith [sq_nonneg (2*v.1+v.2),sq_nonneg v.2]
lemma hexForm_zero_iff (v : ℤ×ℤ) : hexForm v=0 ↔ v=0 := by
  constructor
  · intro hv
    have h1 : v.1=0 := by
      have h := sq_nonneg (v.1+2*v.2)
      unfold hexForm at hv
      nlinarith [sq_nonneg v.1,sq_nonneg v.2]
    have h2 : v.2=0 := by simpa [hexForm,h1] using hv
    exact Prod.ext h1 h2
  · rintro rfl; norm_num [hexForm]
lemma hexNat_coe (v : ℤ×ℤ) : (hexNat v:ℤ)=hexForm v := Int.toNat_of_nonneg (hexForm_nonneg v)
lemma hexNat_zero_iff (v : ℤ×ℤ) : hexNat v=0 ↔ v=0 := by
  rw [← hexForm_zero_iff]
  have hh := hexNat_coe v
  omega
lemma hexNat_pos {v : ℤ×ℤ} (hv : v≠0) : 0<hexNat v := Nat.pos_of_ne_zero ((hexNat_zero_iff v).not.mpr hv)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighFactorBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval bounds for the normalized Gaussian moment powers -/

namespace SharpPlanar
open IntegerBasis
noncomputable def momentPower (ell : ℕ) (t : ℂ) : ℂ :=
  (Complex.I*Real.pi*t)^ell/(ell.factorial:ℂ)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Indices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite node coordinates

These coordinates enumerate the value and derivative data on the first
triangular shell nodes in the planar Fourier interpolation problem.
-/

namespace SharpPlanar.Numerical

def lDeriv : Fin 12 → Bool := ![false,false,false,false,false,false,true,true,true,true,true,true]
open scoped BigOperators
end SharpPlanar.Numerical

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_RationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational Fourier envelopes

Explicit rational majorants control the direct and transformed spectral envelopes
at integral and half-integral radii.
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
noncomputable def piUpper : ℝ := 31416/10000
noncomputable def halfBase : Fin 6 → ℝ := ![21657/1000000,85318/1000000,243240/1000000,469014/1000000,703381/1000000,910487/1000000]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TaylorControl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
open Set
noncomputable def jetTaylor (J : ℕ → ℝ → ℝ) (n : ℕ) (m u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), J k m/(k.factorial:ℝ)*u^k
noncomputable def jetPartial (J : ℕ → ℝ → ℝ) (q : ℕ) (m u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range q, J k m/(k.factorial:ℝ)*u^k
noncomputable def deletedPolynomial (T : ℕ → ℝ → ℝ) (ν d : ℕ) (m u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (d+1), T (r+ν) m/((r+ν).factorial:ℝ)*u^r
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Theta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open Complex
noncomputable def thetaKernel (a : ℂ) (r : ℝ) (k j : ℤ) : ℂ :=
  Complex.exp (-(Real.pi:ℂ)*a*(((j:ℂ)+(k:ℂ)/2)^2/(r:ℂ)+(r:ℂ)*(k:ℂ)^2))

end SharpPlanar

end OAI
end


