-- Prove2me | Definitions.Def_OAIQ098G1643
-- name    : OAIQ098G1643
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-07T16:16:33.554198+00:00
-- url     : https://prove2.me/theorems/a806eff9-dc11-41fb-b5bd-b738e5df09d5
-- title:
--   Definitions bundle OAIQ098G1643 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 100 declarations of OpenAI's Lean: 22 definitions, 8 instances and 70 theorems. The definitions and types are `OAI.SharpPlanar.HeadNodeIndex`, `OAI.SharpPlanar.atomBase`, `OAI.SharpPlanar.bernsteinWeight`, `OAI.SharpPlanar.complexDirectFactor`, `OAI.SharpPlanar.deletedPolynomial`, `OAI.SharpPlanar.dilateSchwartz`, `OAI.SharpPlanar.directKernel`, `OAI.SharpPlanar.halfBase`, `OAI.SharpPlanar.jetPartial`, `OAI.SharpPlanar.jetTaylor`, `OAI.SharpPlanar.leftHalf`, `OAI.SharpPlanar.momentPower`, `OAI.SharpPlanar.piUpper`, `OAI.SharpPlanar.powerToBernstein`, `OAI.SharpPlanar.rightHalf`, `OAI.SharpPlanar.scaleEquiv`, `OAI.SharpPlanar.spectral`, `OAI.SharpPlanar.spectralForm`, `OAI.SharpPlanar.tableConstant`, `OAI.SharpPlanar.thetaKernel`, `OAI.circleMeasurableSpace`, `OAI.starSubalgebraCommCStarAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`PlanarPacking_AtomTail`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/AtomTail.lean), [`PlanarPacking_BarrierProduct`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BarrierProduct.lean), [`PlanarPacking_BernsteinSign`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/BernsteinSign.lean), [`PlanarPacking_Cardinal`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Cardinal.lean), [`PlanarPacking_Certificate_TableData`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Certificate/TableData.lean), [`PlanarPacking_Dilation`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Dilation.lean), [`PlanarPacking_Entire`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Entire.lean), [`PlanarPacking_HighFactorBase`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/HighFactorBase.lean), [`PlanarPacking_RationalBounds`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/RationalBounds.lean), [`PlanarPacking_TailHead`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TailHead.lean), [`PlanarPacking_TaylorControl`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/TaylorControl.lean), [`PlanarPacking_Theta`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/PlanarPacking/Theta.lean).
--
--   **Imports.** It imports the published bundle `Def_PlanarPacking`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098G1644`, `OAIQ098G1671`, `OAIQ098G1672`, `OAIQ098G1676`, `OAIQ098G1680`, `OAIQ098G1684`, `OAIQ098G1689` and `OAIQ098G1691`; the statements `OAI.SharpPlanar.CachedData.mpower0_19_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_6_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_7_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_8_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_9_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_10_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_14_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_15_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_20_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_25_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_30_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_4_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_5_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_9_contains_g`, `OAI.SharpPlanar.atomBase_contains_g`, `OAI.SharpPlanar.atomBase_pos_g`, `OAI.SharpPlanar.basis_piece_integrable_g`, `OAI.SharpPlanar.bernsteinBox_contains_g`, `OAI.SharpPlanar.complexDirectFactor_disk_bound_g`, `OAI.SharpPlanar.continuous_directKernel_g`, `OAI.SharpPlanar.decay_atomBase_g`, `OAI.SharpPlanar.directDensity_series_g`, `OAI.SharpPlanar.directDensity_split_g`, `OAI.SharpPlanar.directDensity_tsum_g`, `OAI.SharpPlanar.directIntegrand_analytic_g`, `OAI.SharpPlanar.directIntegrand_disk_bound_g`, `OAI.SharpPlanar.directMoment_piece_average_error_g`, `OAI.SharpPlanar.directMoment_piece_error_g`, `OAI.SharpPlanar.directMoment_rule_error_g`, `OAI.SharpPlanar.direct_basis_integral_bound_g`, `OAI.SharpPlanar.direct_basis_integral_summable_g`, `OAI.SharpPlanar.direct_basis_pair_g`, `OAI.SharpPlanar.direct_piece_integrable_g` and `OAI.SharpPlanar.direct_positive_series_g`; the proofs of `OAI.SharpPlanar.CachedData.mpower0_19_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_6_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_7_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_8_contains_g`, `OAI.SharpPlanar.CachedData.mpower0_9_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_10_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_14_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_15_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_20_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_25_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_30_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_4_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_5_contains_g`, `OAI.SharpPlanar.CachedData.mpower1_9_contains_g`, `OAI.SharpPlanar.Pmoment_norm_bound_g`, `OAI.SharpPlanar.atomBase_contains_g`, `OAI.SharpPlanar.atomBase_pos_g`, `OAI.SharpPlanar.basis_piece_integrable_g`, `OAI.SharpPlanar.bernsteinBox_contains_g`, `OAI.SharpPlanar.complexDirectFactor_disk_bound_g`, `OAI.SharpPlanar.continuous_directKernel_g`, `OAI.SharpPlanar.decay_atomBase_g`, `OAI.SharpPlanar.directDensity_series_g`, `OAI.SharpPlanar.directDensity_split_g`, `OAI.SharpPlanar.directDensity_tsum_g`, `OAI.SharpPlanar.directIntegrand_analytic_g`, `OAI.SharpPlanar.directIntegrand_disk_bound_g`, `OAI.SharpPlanar.directMoment_piece_average_error_g`, `OAI.SharpPlanar.directMoment_piece_error_g`, `OAI.SharpPlanar.directMoment_rule_error_g`, `OAI.SharpPlanar.direct_basis_integral_bound_g`, `OAI.SharpPlanar.direct_basis_integral_summable_g`, `OAI.SharpPlanar.direct_basis_pair_g`, `OAI.SharpPlanar.direct_piece_integrable_g`, `OAI.SharpPlanar.direct_positive_series_g` and `OAI.SharpPlanar.direct_spectral_bound_g`.
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
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- d13f23b's `BorelSpace Circle`, for `circleMeasurableSpace`. -/
theorem circleBorelSpace : @BorelSpace Circle _ circleMeasurableSpace :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
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
-- module Solutions.OAIQ098_PP.PlanarPacking_AtomTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
noncomputable def atomBase : Fin 7 → ℝ := ![1/10000,469/1000000,7279/1000000,59165/1000000,219974/1000000,494744/1000000,828986/1000000]
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
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

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

noncomputable def spectral (μ : Measure ℝ) (f : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ t, Complex.exp (((Real.pi*t*s : ℝ) : ℂ)*Complex.I) * f t ∂μ

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


open scoped SchwartzMap

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
noncomputable def momentPower (ell : ℕ) (t : ℂ) : ℂ :=
  (Complex.I*Real.pi*t)^ell/(ell.factorial:ℂ)
end SharpPlanar

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
-- module Solutions.OAIQ098_PP.PlanarPacking_TailHead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators
abbrev HeadNodeIndex := Option (Fin 21)
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


