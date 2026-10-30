-- Prove2me | Definitions.Def_OAIQ124K003
-- name    : OAIQ124K003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:41:54.845796+00:00
-- url     : https://prove2.me/theorems/93963e26-c0f4-4f6c-824d-c0f7f7a8746e
-- title:
--   Definitions bundle OAIQ124K003 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 124 declarations of OpenAI's Lean: 37 definitions, 10 instances and 77 theorems. The definitions and types are `OAI.KLInvariance.Hilbert.degreeMap`, `OAI.KLInvariance.Hilbert.imageMap`, `OAI.KLInvariance.LocalCover.splitEquiv`, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeQuotient`, `OAI.KLInvariance.MomentGraph.Sheaf.baseChangeScalar`, `OAI.KLInvariance.MomentGraph.Sheaf.propPiEquiv`, `OAI.KLInvariance.MomentGraph.Sheaf.quotientPullback`, `OAI.KLInvariance.ReverseFiltration.imageMapKernelEquiv`, `OAI.KLInvariance.ReverseFiltration.scalarKernelEquiv`, `OAI.KLInvariance.ScalarQuotient.coordinateReduction`, `OAI.KLInvariance.ScalarQuotient.submodule`, `OAI.KLInvariance.SchedulePaths.instDecidable_solutions_5`, `OAI.KLInvariance.SignedDihedral.Before`, `OAI.KLInvariance.SignedDihedral.instDecidable_solutions_1`, `OAI.KLInvariance.SignedDihedral.positiveCount`, `OAI.KLInvariance.SymmetricPlaneIdeal.backward`, `OAI.KLInvariance.SymmetricPlaneIdeal.forward`, `OAI.KLInvariance.SymmetricPlaneIdeal.ideal`, `OAI.KLInvariance.SymmetricPlaneIdeal.linearQuotient`, `OAI.KLInvariance.SymmetricPlaneIdeal.quotientEquiv`, `OAI.KLInvariance.SymmetricPlaneIdeal.quotientMap`, `OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable`, `OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_1`, `OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_2`, `OAI.KLInvariance.TitsSpace.PlaneBasis.instDecidable_3`, `OAI.KLInvariance.TitsSpace.charDecEqA`, `OAI.KLInvariance.TitsSpace.instDecidable_solutions_10`, `OAI.KLInvariance.TitsSpace.instDecidable_solutions_11`, `OAI.KLInvariance.TitsSpace.instDecidable_solutions_7`, `OAI.KLInvariance.TitsSpace.instDecidable_solutions_8`, `OAI.KLInvariance.TitsSpace.pencil`, `OAI.KLInvariance.WallDyer.instDecidable_solutions`, `OAI.KLInvariance.instDecidableEq_solutions`, `OAI.KLInvariance.kernelMixedEquiv`, `OAI.KLInvariance.kernelSourceEquiv`, `OAI.KLInvariance.rPolynomial`, `OAI.KLInvariance.scaledKL`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `KazhdanLusztig_BalancedPairings`, `KazhdanLusztig_BottSamelson`, `KazhdanLusztig_Bruhat`, `KazhdanLusztig_CharacterReciprocity`, `KazhdanLusztig_Dihedral`, `KazhdanLusztig_DihedralIntervals`, `KazhdanLusztig_DyerPaths`, `KazhdanLusztig_EdgeLocalization`, `KazhdanLusztig_Hecke`, `KazhdanLusztig_HilbertSeries`, `KazhdanLusztig_IntegralPairings`, `KazhdanLusztig_MinimalExtensions`, `KazhdanLusztig_ModuleAlgebra`, `KazhdanLusztig_PlaneLocalization`, `KazhdanLusztig_PositiveTransfer`, `KazhdanLusztig_ReflectionOrders`, `KazhdanLusztig_Support`, `KazhdanLusztig_TerminalKernels`.
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K006` and `OAIQ124K007`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance

section
-- module Solutions.OAIQ124_KL.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
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
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ModuleAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Height-one membership into free targets, minimal covers, graded Nakayama, reverse projectivity, saturated edge kernels and strict Hilbert detection.
-/

section


/-! The local algebra step in `loc:decomposition`, source §4.4. The maps
are actual linear maps; neither a decomposition nor a lift is assumed. -/
namespace KLInvariance.LocalCover

variable {R B P N : Type*} [CommRing R] [IsLocalRing R]
  [AddCommGroup B] [Module R B] [AddCommGroup P] [Module R P]
  [AddCommGroup N] [Module R N]

/-- An explicit linear equivalence for a split surjection, with the kernel
as the second summand. It is used below to produce the local sheaf summand. -/
noncomputable def splitEquiv (g : B →ₗ[R] P) (s : P →ₗ[R] B)
    (hs : g.comp s = LinearMap.id) : B ≃ₗ[R] P × LinearMap.ker g := by
  have hs' (p : P) : g (s p) = p := LinearMap.congr_fun hs p
  let k : B →ₗ[R] LinearMap.ker g :=
    { toFun := fun b => ⟨b - s (g b), by simp [LinearMap.mem_ker, hs']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_sub]) }
  exact
    { toFun := fun b => (g b, k b)
      invFun := fun p => s p.1 + p.2
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp
      left_inv := fun b => by simp [k]
      right_inv := fun ⟨p, b⟩ => by
        apply Prod.ext
        · simp [hs']
        · apply Subtype.ext
          simp [k, hs'] }

end KLInvariance.LocalCover


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Bruhat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Strong Bruhat order, subwords, length, finite lower ideals and arbitrary finite intervals; the selected R family.
-/

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}


noncomputable def rPolynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  (klFamilies cs).1 x y

end KLInvariance

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Hecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hecke and Laurent actions, braid independence, bar involution, triangular support and inverse coefficients.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


noncomputable local instance instDecidableEq_solutions : DecidableEq W := Classical.decEq W


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Dihedral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Interval restrictions, dihedral Coxeter and Hecke calculations, and the genuine square-parameter R normalization.
-/

section

namespace KLInvariance
open Polynomial
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

/-- The manuscript's q^{-d/2} P(q), written with t^2=q so no square-root
branch is hidden. This is an evaluation of the already constructed genuine
KL polynomial, not a new combinatorial invariant. -/
noncomputable def scaledKL {C : Type*} [Field C]
    (cs : CoxeterSystem M W) (t : C) (x b : W) : C :=
  t ^ ((cs.length x : ℤ)-cs.length b) *
    eval₂ (Int.castRingHom C) (t^2) (klPolynomial cs x b)

end KLInvariance


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_HilbertSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert series of graded modules and boundary sheaves, positivity and strict detection.
-/


section

namespace KLInvariance.Hilbert
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]


section FiniteModule
variable {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

def degreeMap (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) (n : ℤ) :
    𝓜 n →ₗ[k] 𝓝 n :=
  LinearMap.codRestrict (𝓝 n) ((f.restrictScalars k).comp (𝓜 n).subtype)
    (fun m => hf n m m.property)

end FiniteModule


end KLInvariance.Hilbert


end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/


section


namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um un
variable {R : Type ur}
  [CommRing R]
  {V : Type uv}
  [PartialOrder V]
  {E : Type ue}
noncomputable section

variable (S : Type us) [CommRing S] [Algebra R S]

def baseChangeScalar : S ⊗[R] R ≃ₗ[S] S := AlgebraTensorModule.rid R S S

 theorem span_map (a : R) :
    (Ideal.span {a}).map (algebraMap R S) = Ideal.span {algebraMap R S a} := by
  rw [Ideal.map_span,Set.image_singleton]

 def baseChangeQuotient (a : R) :
    S ⊗[R] (R ⧸ Ideal.span {a}) ≃ₗ[S] S ⧸ Ideal.span {algebraMap R S a} :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (Ideal.span {a})).symm.toLinearEquiv.trans
    (Ideal.quotientEquivAlgOfEq S (span_map S a)).toLinearEquiv

 def quotientPullback (a : R) (p q : Prop) (h : q → p) :
    (PLift p → R) →ₗ[R] (PLift q → R ⧸ Ideal.span {a}) :=
  LinearMap.pi fun t => (Ideal.Quotient.mkₐ R (Ideal.span {a})).toLinearMap.comp
    (LinearMap.proj ⟨h t.down⟩)

end
end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/


section

/-! Transport of actual linear-map kernels along a source isomorphism. -/
namespace KLInvariance
universe ur um un up
variable {R : Type ur} [Ring R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]

def kernelSourceEquiv (f : M →ₗ[R] P) (e : M ≃ₗ[R] N) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker (f.comp e.symm.toLinearMap) where
  toFun x := ⟨e x.val,by simpa only [LinearMap.mem_ker,LinearMap.comp_apply,
    LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using x.property⟩
  invFun y := ⟨e.symm y.val,y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' r x := Subtype.ext (map_smul e r x.val)

end KLInvariance

end


section

namespace KLInvariance
universe uk ua um un up uq
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  {P : Type up} [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]
  {Q : Type uq} [AddCommGroup Q] [Module k Q]

def kernelMixedEquiv (f : M →ₗ[A] P) (e : M ≃ₗ[A] N) (g : P ≃ₗ[k] Q) :
    LinearMap.ker f ≃ₗ[k] LinearMap.ker
      (g.toLinearMap.comp ((f.comp e.symm.toLinearMap).restrictScalars k)) where
  toFun x := ⟨e x.val, by
    change g (f (e.symm (e x.val)))=0
    rw [e.symm_apply_apply,LinearMap.mem_ker.mp x.property,map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    apply g.injective
    have hy : g (f (e.symm y.val))=0 := y.property
    simpa only [map_zero] using hy⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add e x.val y.val)
  map_smul' c x := Subtype.ext (map_smul (e.restrictScalars k) c x.val)

end KLInvariance

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/


section

/-! Genuine word stalk normalization and identification with the honest
Hecke word. This does not identify the indecomposable BMP character with KL. -/
namespace KLInvariance.TitsSpace
open Module
universe u
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type u}
  [Group W]
  (cs : CoxeterSystem M W)
  {σ : Type u}
  [Fintype σ]
noncomputable section
local instance instDecidable_solutions_7 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section

namespace TransportPerfectPairing
open Module
variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

theorem symmetric (e : M ≃ₗ[A] N) (D : M ≃ₗ[A] Dual A M)
    (h : ∀ x y, D x y = D y x) (s z : N) :
    (e.symm.trans (D.trans e.symm.dualMap)) s z =
    (e.symm.trans (D.trans e.symm.dualMap)) z s :=
  h (e.symm s) (e.symm z)

end TransportPerfectPairing

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section

namespace KLInvariance.Hilbert
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 def imageMap (S : Submodule A M) (f : M →ₗ[A] N) : S →ₗ[A] S.map f where
  toFun v := ⟨f v.val,Submodule.mem_map.mpr ⟨_,v.property,rfl⟩⟩
  map_add' _ _ := by ext; exact map_add f _ _
  map_smul' _ _ := by ext; exact map_smul f _ _

end KLInvariance.Hilbert

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section

/-! Genuine word costalk character from the integral word pairing, transported
along the fixed symmetric-algebra coordinate isomorphism. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph
universe u
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type u}
  [Group W]
  (cs : CoxeterSystem M W)
  {σ : Type u}
  [Fintype σ]
noncomputable section

local instance charDecEqA (a : Type*) : DecidableEq a := Classical.decEq a

end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DyerPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/


section

/-! Geometric orders adapted to a fixed upper vertex. These are honest
ratios of linear functionals, with a strictly positive denominator. They
will be used only as a permissible choice of the source's schedule. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance instDecidable_solutions_8 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.TitsSpace

end


section

/-! Rank-two path reversal in the actual induced root plane, for every finite
full interval. This is a required Dyer wall-crossing relation, not the Dyer
identification itself. -/

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)}
local instance instDecidable (p : Prop) : Decidable p := Classical.propDecidable p

end PlaneBasis
end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)}
local instance instDecidable_1 (p : Prop) : Decidable p := Classical.propDecidable p

end PlaneBasis
end
end KLInvariance.TitsSpace

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite sweep algebra, wall orders and the full reflection-order path formula.
-/


section

/-! Localization of genuine directed paths in a maximal root-plane coset.
The full relative interval is proved to contain every such path. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module
universe u v
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type v}
  [Group W]
  {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)}
noncomputable section
local instance instDecidable_2 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! The actual rank-two edge product is independent of every linear
functional restricted to that root plane, including a wall tie refinement. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance instDecidable_solutions_10 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.TitsSpace

end


section

/-! Generic pencils of genuine linear root-label functionals. At a wall all
roots of a tied block belong to one full actual root plane. -/

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance instDecidable_solutions_11 (p : Prop) : Decidable p := Classical.propDecidable p

def pencil (f g : Module.Dual ℝ (I → ℝ)) (t : ℝ) : Module.Dual ℝ (I → ℝ) :=
  (1-t) • f + t • g

end
end KLInvariance.TitsSpace

end


section

/-! Finite wall crossing for actual reflection-edge path matrices. -/
namespace KLInvariance.WallDyer
open Module TitsSpace
open scoped Topology
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.WallDyer

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DihedralIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed dihedral coordinates, actual dihedral intervals, exact later-edge counts and root-plane calculations.
-/


section


namespace KLInvariance.SignedDihedral
noncomputable section

 local instance instDecidable_solutions_r2d3b82_1 (p : Prop) : Decidable p := Classical.propDecidable p
def Before (a b : ℤ) : Prop :=
  (0 < a ∧ 0 < b ∧ a < b) ∨ (a < 0 ∧ b < 0 ∧ a < b) ∨ (0 < a ∧ b < 0)

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.SignedDihedral
noncomputable section
local instance instDecidable_solutions_1 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.SignedDihedral
noncomputable section

 local instance instDecidable_solutions_2_r2d3b82_1 (p : Prop) : Decidable p := Classical.propDecidable p
def positiveCount (L M C : ℕ) : ℕ :=
  (∑ r ∈ Finset.range C, if L < r ∧ Odd (L+r) then (if M < r then 2 else 1) else 0) +
    (if M < C ∧ Odd (L+C) then 1 else 0)

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.TitsSpace.PlaneBasis
universe u v
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type v}
  [Group W]
  {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)}
noncomputable section
local instance instDecidable_3 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.TitsSpace.PlaneBasis

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PlaneLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Symmetric plane ideals, sheaf localization and scaled local products along genuine edges.
-/

section

namespace KLInvariance.SymmetricPlaneIdeal
universe uk uv
variable {k : Type uk} [Field k] {V : Type uv} [AddCommGroup V] [Module k V]
noncomputable section

 def ideal (P : Submodule k V) : Ideal (SymmetricAlgebra k V) :=
  Ideal.span ((SymmetricAlgebra.ι k V) '' (P : Set V))

 def quotientMap (P : Submodule k V) :
    SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k (V ⧸ P) :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k (V ⧸ P)).comp P.mkQ)

@[simp] theorem quotientMap_ι (P : Submodule k V) (v : V) :
    quotientMap P (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v) :=
  SymmetricAlgebra.lift_ι_apply _ _

 theorem ideal_le_ker (P : Submodule k V) : ideal P ≤ RingHom.ker (quotientMap P) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨v,hv,rfl⟩
  change quotientMap P (SymmetricAlgebra.ι k V v) = 0
  rw [quotientMap_ι,show P.mkQ v = 0 from (Submodule.Quotient.mk_eq_zero P).mpr hv,map_zero]

 def forward (P : Submodule k V) : (SymmetricAlgebra k V ⧸ ideal P) →ₐ[k]
    SymmetricAlgebra k (V ⧸ P) :=
  Ideal.Quotient.liftₐ _ (quotientMap P) (fun _ hz => ideal_le_ker P hz)

 def linearQuotient (P : Submodule k V) : V ⧸ P →ₗ[k]
    (SymmetricAlgebra k V ⧸ ideal P) :=
  P.liftQ ((Ideal.Quotient.mkₐ k (ideal P)).toLinearMap.comp (SymmetricAlgebra.ι k V)) (by
    intro v hv
    apply LinearMap.mem_ker.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨v,hv,rfl⟩))

 def backward (P : Submodule k V) : SymmetricAlgebra k (V ⧸ P) →ₐ[k]
    (SymmetricAlgebra k V ⧸ ideal P) := SymmetricAlgebra.lift (linearQuotient P)

@[simp] theorem forward_mk (P : Submodule k V) (z : SymmetricAlgebra k V) :
    forward P (Ideal.Quotient.mk (ideal P) z) = quotientMap P z := rfl

@[simp] theorem backward_ι_mk (P : Submodule k V) (v : V) :
    backward P (SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v)) =
      Ideal.Quotient.mk (ideal P) (SymmetricAlgebra.ι k V v) := by
  rw [backward,SymmetricAlgebra.lift_ι_apply]
  rfl

 def quotientEquiv (P : Submodule k V) : (SymmetricAlgebra k V ⧸ ideal P) ≃ₐ[k]
    SymmetricAlgebra k (V ⧸ P) :=
  AlgEquiv.ofAlgHom (forward P) (backward P)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      obtain ⟨v,rfl⟩ := P.mkQ_surjective v
      change forward P (backward P (SymmetricAlgebra.ι k _ (P.mkQ v))) = _
      rw [backward_ι_mk,forward_mk,quotientMap_ι]
      rfl)
    (by
      apply Ideal.Quotient.algHom_ext
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      change backward P (forward P (Ideal.Quotient.mk (ideal P) (SymmetricAlgebra.ι k V v))) = _
      rw [forward_mk,quotientMap_ι,backward_ι_mk]
      rfl)

@[simp] theorem quotientEquiv_mk_ι (P : Submodule k V) (v : V) :
    quotientEquiv P (Ideal.Quotient.mk (ideal P) (SymmetricAlgebra.ι k V v)) =
      SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v) := quotientMap_ι P v

 theorem ι_mem_iff (P : Submodule k V) (v : V) :
    SymmetricAlgebra.ι k V v ∈ ideal P ↔ v ∈ P := by
  constructor
  · intro hv
    have hh := ideal_le_ker P hv
    change quotientMap P (SymmetricAlgebra.ι k V v) = 0 at hh
    rw [quotientMap_ι] at hh
    apply (Submodule.Quotient.mk_eq_zero P).mp
    have he : SymmetricAlgebra.ι k (V ⧸ P) (P.mkQ v) =
        SymmetricAlgebra.ι k (V ⧸ P) 0 := by simpa only [map_zero] using hh
    by_contra hn
    obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero k hn
    have h := congrArg (SymmetricAlgebra.lift f) he
    rw [SymmetricAlgebra.lift_ι_apply,SymmetricAlgebra.lift_ι_apply,map_zero] at h
    exact hf h
  · intro hv
    exact Ideal.subset_span ⟨v,hv,rfl⟩

 theorem ideal_eq_ker (P : Submodule k V) : ideal P = RingHom.ker (quotientMap P) := by
  apply le_antisymm (ideal_le_ker P)
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (quotientEquiv P).injective
  change quotientMap P z = quotientEquiv P 0
  rw [map_zero]
  exact hz

 instance ideal_isPrime (P : Submodule k V) : (ideal P).IsPrime := by
  rw [ideal_eq_ker]
  exact RingHom.ker_isPrime (quotientMap P)

end
end KLInvariance.SymmetricPlaneIdeal

end


section

/-! The relative rank-one structure models are natural under full strictly
order-compatible graph embeddings, with exactly the pulled-back labels. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue uw uf
variable {R : Type ur}
  [CommRing R]
  {V : Type uv}
  [PartialOrder V]
  {E : Type ue}
  {W : Type uw}
  [PartialOrder W]
  {F : Type uf}
noncomputable section

 def propPiEquiv (N : Type*) [AddCommGroup N] [Module R N]
    {p q : Prop} (h : p ↔ q) : (PLift p → N) ≃ₗ[R] (PLift q → N) where
  toFun v t := v ⟨h.mpr t.down⟩
  invFun v t := v ⟨h.mp t.down⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end
end KLInvariance.MomentGraph.Sheaf

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_EdgeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bruhat sheaf localization, graded transport, local edge-image bounds and support.
-/


section

/-! Actual transported numerical R-tilde matrix and its genuine KL reciprocal
vector. No sheaf or desired invariance conclusion is assumed. -/
namespace KLInvariance.SchedulePaths
universe u v w w'
variable {V : Type u} {E : Type v} {R : Type w} {S : Type w'}
  [Semiring R] [Semiring S] (source target : E → V)
noncomputable section
local instance instDecidable_solutions_5 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.SchedulePaths

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_PositiveTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Positive transfer inequalities, strict Hilbert-series detection including higher-codimension support, and reverse-filtration projective-to-free arguments.
-/


section

namespace KLInvariance.ReverseFiltration
universe ua um un up
variable {A : Type ua} [CommRing A]
  {M : Type um} [AddCommGroup M] [Module A M]
  {N : Type un} [AddCommGroup N] [Module A N]
  {P : Type up} [AddCommGroup P] [Module A P]

/-- A kernel which is exactly a regular scalar multiple of its domain is
integrally isomorphic to that domain, not just to its fraction-field span. -/
noncomputable def scalarKernelEquiv (g : M →ₗ[A] N) (a : A)
    (hk : ∀ v, g v = 0 ↔ ∃ w, v = a • w)
    (ha : Function.Injective (fun v : M => a • v)) :
    M ≃ₗ[A] LinearMap.ker g := by
  let f : M →ₗ[A] LinearMap.ker g :=
    (LinearMap.lsmul A M a).codRestrict (LinearMap.ker g) (fun v =>
      (hk (a • v)).mpr ⟨v,rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact ha (congrArg Subtype.val h)
  · intro v
    obtain ⟨w,hw⟩ := (hk v.val).mp v.property
    exact ⟨w,Subtype.ext hw.symm⟩


 def imageMapKernelEquiv (S : Submodule A M) (f : M →ₗ[A] N) :
    ↥(S ⊓ LinearMap.ker f) ≃ₗ[A] LinearMap.ker (Hilbert.imageMap S f) where
  toFun v := ⟨⟨v.val,v.property.1⟩,Subtype.ext v.property.2⟩
  invFun v := ⟨v.val.val,v.val.property,congrArg Subtype.val v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end KLInvariance.ReverseFiltration

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_TerminalKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All-section transport, terminal kernels, scalar quotients, height-one membership in free targets and scaled edge-image inclusion.
-/


section

/-! The scalar quotient of an actual finite free presentation is free over
its quotient coefficient ring. There is no quotient-freeness hypothesis. -/
namespace KLInvariance.ScalarQuotient
open Module
universe ur um un ui
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {ι : Type ui} [Fintype ι]
noncomputable section

 def coordinateReduction (b : Basis ι R M) (a : R) :
    M →ₗ[R] (ι → R ⧸ Ideal.span {a}) :=
  (LinearMap.pi fun i => (Ideal.span ({a} : Set R)).mkQ.comp
    ((LinearMap.proj i).comp b.equivFun.toLinearMap))

 def submodule (a : R) [Module (R ⧸ Ideal.span {a}) N]
    [IsScalarTower R (R ⧸ Ideal.span {a}) N] (S : Submodule R N) :
    Submodule (R ⧸ Ideal.span {a}) N where
  carrier := S
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' c v hv := by
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective c
    change (algebraMap R (R ⧸ Ideal.span {a}) r) • v ∈ S
    simpa only [algebraMap_smul] using S.smul_mem r hv

end
end KLInvariance.ScalarQuotient

end


end OAI
end


