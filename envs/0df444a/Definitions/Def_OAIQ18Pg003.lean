-- Prove2me | Definitions.Def_OAIQ18Pg003
-- name    : OAIQ18Pg003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:53:24.242307+00:00
-- url     : https://prove2.me/theorems/4dbe363f-b7cf-4044-816d-1a42d31dd430
-- title:
--   Definitions bundle OAIQ18Pg003 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 130 declarations of OpenAI's Lean: 56 definitions, 6 instances and 68 theorems. The definitions and types are `OAI.SourceBurnside.Stability.FiniteAverage.average`, `OAI.SourceBurnside.Stability.FiniteNormal.averageChain`, `OAI.SourceBurnside.Stability.FiniteNormal.averageEnd`, `OAI.SourceBurnside.Stability.FiniteNormal.averageHomotopy`, `OAI.SourceBurnside.Stability.HomologyEdge.Z`, `OAI.SourceBurnside.Stability.HomologyEdge.cycleSequence`, `OAI.SourceBurnside.Stability.HomologyEdge.ontoCycles`, `OAI.SourceBurnside.Stability.MonomialInduction.basisSeed`, `OAI.SourceBurnside.Stability.MonomialInduction.charRep`, `OAI.SourceBurnside.Stability.MonomialInduction.character`, `OAI.SourceBurnside.Stability.MonomialInduction.coefficient`, `OAI.SourceBurnside.Stability.MonomialInduction.induced`, `OAI.SourceBurnside.Stability.MonomialInduction.inverseLinear`, `OAI.SourceBurnside.Stability.MonomialInduction.orbitBasis`, `OAI.SourceBurnside.Stability.MonomialInduction.residual`, `OAI.SourceBurnside.Stability.MonomialInduction.scalar`, `OAI.SourceBurnside.Stability.MonomialInduction.transporter`, `OAI.SourceBurnside.Stability.MonomialTrivial.induced`, `OAI.SourceBurnside.Stability.MonomialTrivial.scalarIso`, `OAI.SourceBurnside.Stability.MonomialTrivial.seed`, `OAI.SourceBurnside.Stability.RationalBar.B2`, `OAI.SourceBurnside.Stability.RationalBar.C2`, `OAI.SourceBurnside.Stability.RationalBar.C3`, `OAI.SourceBurnside.Stability.RationalBar.Cocycles`, `OAI.SourceBurnside.Stability.RationalBar.Extension`, `OAI.SourceBurnside.Stability.RationalBar.H2`, `OAI.SourceBurnside.Stability.RationalBar.T`, `OAI.SourceBurnside.Stability.RationalBar.Z2`, `OAI.SourceBurnside.Stability.RationalBar.d3`, `OAI.SourceBurnside.Stability.RationalBar.evaluation`, `OAI.SourceBurnside.Stability.RationalBar.evaluationMap`, `OAI.SourceBurnside.Stability.RationalBar.map2`, `OAI.SourceBurnside.Stability.RationalBar.map3`, `OAI.SourceBurnside.Stability.RationalBar.projection`, `OAI.SourceBurnside.Stability.RationalBar.pull`, `OAI.SourceBurnside.Stability.RationalBar.value`, `OAI.SourceBurnside.Stability.RationalBar.π`, `OAI.SourceBurnside.Stability.RelativeCoinvariants.adjunction`, `OAI.SourceBurnside.Stability.RelativeCoinvariants.counit`, `OAI.SourceBurnside.Stability.RelativeCoinvariants.functor` and 16 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: [`PeriodicGroups_Algebra_HierarchyGrowth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Algebra/HierarchyGrowth.lean), [`PeriodicGroups_Frames_AcyclicFrameEdge`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Frames/AcyclicFrameEdge.lean), [`PeriodicGroups_Homology_FiniteExtensions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/FiniteExtensions.lean), [`PeriodicGroups_Homology_FiniteNormalHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/FiniteNormalHomology.lean), [`PeriodicGroups_Homology_KernelStability`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/KernelStability.lean), [`PeriodicGroups_Homology_LocallyFiniteActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/LocallyFiniteActions.lean), [`PeriodicGroups_Homology_RelativeHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/RelativeHomology.lean), [`PeriodicGroups_Steinberg_RankActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Steinberg/RankActions.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ18Pg008`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ18_PG.Compat
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
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_FiniteExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open Classical Representation

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

namespace FiniteAverage
variable [Fintype G] (ρ : Representation ℚ G V)

def average : V →ₗ[ℚ] V := (Fintype.card G : ℚ)⁻¹ • ∑ g : G, ρ g

lemma average_apply (v : V) : average ρ v =
    (Fintype.card G : ℚ)⁻¹ • ∑ g : G, ρ g v := by
  simp [average]

lemma average_action (g : G) (v : V) : average ρ (ρ g v) = average ρ v := by
  simp only [average_apply]
  congr 1
  simp only [← Module.End.mul_apply, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) (fun h => ρ (h * g) v)
    (fun h => ρ h v) (fun _ => rfl)

lemma average_ker (v : V) (hv : v ∈ Coinvariants.ker ρ) : average ρ v = 0 := by
  apply (show Coinvariants.ker ρ ≤ (average ρ).ker from ?_) hv
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g, x⟩, rfl⟩
  change average ρ (ρ g x - x) = 0
  rw [map_sub, average_action, sub_self]

lemma mk_average (v : V) : Coinvariants.mk ρ (average ρ v) = Coinvariants.mk ρ v := by
  rw [average_apply, map_smul, map_sum]
  simp only [Coinvariants.mk_self_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

lemma intertwining (τ : Representation ℚ G W) (f : ρ.IntertwiningMap τ) (v : V) :
    f (average ρ v) = average τ (f v) := by
  simp only [average_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact DFunLike.congr_fun (f.isIntertwining' g) v

lemma map_injective (τ : Representation ℚ G W) (f : ρ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (Coinvariants.map ρ τ f) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ x
  have hz : average τ (f v) = 0 := average_ker τ _ ((Coinvariants.mk_eq_zero τ).mp hx)
  have hv : average ρ v = 0 := hf (by rw [intertwining ρ τ f, hz, map_zero])
  rw [← mk_average ρ v, hv, map_zero]
end FiniteAverage

end

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation
universe u
variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

namespace RelativeCoinvariants

abbrev functor : Rep.{u} ℚ G ⥤ Rep ℚ (G ⧸ N) :=
  Rep.quotientToCoinvariantsFunctor ℚ N

@[simp] lemma map_mk {A B : Rep.{u} ℚ G} (f : A ⟶ B) (x : A) :
    ((functor N).map f).hom (Coinvariants.mk _ x) = Coinvariants.mk _ (f.hom x) := rfl

instance instAdditiveRepRatQuotientSubgroupFunctor : (functor N).Additive where
  map_add {A B} f g := by
    ext x
    induction x using Coinvariants.induction_on with | h x =>
    change Coinvariants.mk (B.ρ.comp N.subtype) (f.hom x + g.hom x) = _
    exact map_add _ _ _

def unit (A : Rep.{u} ℚ G) :
    A ⟶ Rep.res (QuotientGroup.mk' N) ((functor N).obj A) :=
  Rep.toCoinvariantsMkQ A N

def counit (B : Rep.{u} ℚ (G ⧸ N)) :
    (functor N).obj (Rep.res (QuotientGroup.mk' N) B) ⟶ B :=
  Rep.ofHom
    { toLinearMap := Coinvariants.lift _ LinearMap.id (by
        intro g
        ext x
        change B.ρ (QuotientGroup.mk' N g.val) x = x
        have hg : QuotientGroup.mk' N g.val = 1 := (QuotientGroup.eq_one_iff _).mpr g.property
        rw [hg, map_one]
        rfl)
      isIntertwining' := by
        intro g
        induction g using QuotientGroup.induction_on with | H g =>
        ext x
        rfl }

@[simp] lemma unit_apply (A : Rep.{u} ℚ G) (x : A) :
    (unit N A).hom x = Coinvariants.mk _ x := rfl
@[simp] lemma counit_mk (B : Rep.{u} ℚ (G ⧸ N)) (x : B) :
    (counit N B).hom (Coinvariants.mk _ x) = x := rfl

def adjunction : functor N ⊣ Rep.resFunctor (QuotientGroup.mk' N) where
  unit :=
    { app := unit N
      naturality := by intros; ext x; rfl }
  counit :=
    { app := counit N
      naturality := by
        intro A B f
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        induction x using Coinvariants.induction_on with | h x => rfl }
  left_triangle_components A := by
    ext x
    induction x using Coinvariants.induction_on with | h x => rfl
  right_triangle_components B := by ext x; rfl

instance instIsLeftAdjointRepRatQuotientSubgroupFunctor : (functor N).IsLeftAdjoint := (adjunction N).isLeftAdjoint
instance instPreservesProjectiveObjectsRepRatQuotientSubgroupFunctor : (functor N).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms (adjunction N)

end RelativeCoinvariants
end

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep
open MonoidalCategory BraidedCategory

namespace RelativeCoinvariants
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def inductionIso : Rep.indFunctor ℚ (QuotientGroup.mk' N) ≅ functor N :=
  (Rep.indResAdjunction ℚ (QuotientGroup.mk' N)).leftAdjointUniq (adjunction N)

variable {H : Type} [Group H] (q : G →* H) (A : Rep ℚ H)

def projectionRight :
    Rep.indFunctor ℚ q ⋙ (Rep.coinvariantsTensor ℚ H).flip.obj A ≅
      (Rep.coinvariantsTensor ℚ G).flip.obj (Rep.res q A) :=
  NatIso.ofComponents (fun B => Rep.coinvariantsTensorIndIso q B A) (by
    intro B C f
    apply Rep.coinvariantsTensor_hom_ext
    apply Representation.IndV.hom_ext
    intro h
    ext b a
    simp [Rep.coinvariantsTensorIndHom, Rep.coinvariantsTensorMk,
      Rep.indMap])

def tensorSymmetry {K : Type} [Group K] (B : Rep ℚ K) :
    (Rep.coinvariantsTensor ℚ K).obj B ≅
      (Rep.coinvariantsTensor ℚ K).flip.obj B :=
  Functor.isoWhiskerRight (tensorLeftIsoTensorRight B) (Rep.coinvariantsFunctor ℚ K)

def projection :
    (Rep.coinvariantsTensor ℚ G).obj (Rep.res q A) ≅
      Rep.indFunctor ℚ q ⋙ (Rep.coinvariantsTensor ℚ H).obj A :=
  tensorSymmetry (Rep.res q A) ≪≫ (projectionRight q A).symm ≪≫
    Functor.isoWhiskerLeft (Rep.indFunctor ℚ q) (tensorSymmetry A).symm

def quotientProjection (B : Rep ℚ (G ⧸ N)) :
    (Rep.coinvariantsTensor ℚ G).obj (Rep.res (QuotientGroup.mk' N) B) ≅
      functor N ⋙ (Rep.coinvariantsTensor ℚ (G ⧸ N)).obj B :=
  projection (QuotientGroup.mk' N) B ≪≫
    Functor.isoWhiskerRight (inductionIso N) ((Rep.coinvariantsTensor ℚ (G ⧸ N)).obj B)

def trivialIso : (functor N).obj (Rep.trivial ℚ G ℚ) ≅ Rep.trivial ℚ (G ⧸ N) ℚ where
  hom := counit N (Rep.trivial ℚ (G ⧸ N) ℚ)
  inv := Rep.ofHom
    { toLinearMap := Coinvariants.mk _
      isIntertwining' := by
        intro g
        induction g using QuotientGroup.induction_on with | H g => rfl }
  hom_inv_id := by
    ext x
    induction x using Coinvariants.induction_on with | h x => rfl
  inv_hom_id := by ext; rfl

end RelativeCoinvariants
end
end SourceBurnside.Stability

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_RelativeHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open scoped TensorProduct
open MonoidalCategory

namespace RelativeCoinvariants
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

lemma inductionIso_one (B : Rep ℚ G) (b : B) :
    ((inductionIso N).hom.app B).hom (IndV.mk (QuotientGroup.mk' N) B.ρ 1 b) =
      Coinvariants.mk _ b := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (Rep.indResAdjunction ℚ (QuotientGroup.mk' N)) (adjunction N) B
  exact congrArg (fun f => f.hom b) h

lemma tensorSymmetry_mk {H : Type} [Group H] (A B : Rep ℚ H) (a : A) (b : B) :
    ((tensorSymmetry A).hom.app B) (coinvariantsTensorMk A B a b) =
      coinvariantsTensorMk B A b a := rfl

lemma tensorSymmetry_inv_mk {H : Type} [Group H] (A B : Rep ℚ H) (a : A) (b : B) :
    ((tensorSymmetry A).inv.app B) (coinvariantsTensorMk B A b a) =
      coinvariantsTensorMk A B a b := rfl

lemma tensor_map_mk {H : Type} [Group H] (A : Rep ℚ H) {B C : Rep ℚ H}
    (f : B ⟶ C) (a : A) (b : B) :
    (((coinvariantsTensor ℚ H).obj A).map f) (coinvariantsTensorMk A B a b) =
      coinvariantsTensorMk A C a (f.hom b) := rfl

lemma quotientProjection_mk (A : Rep ℚ (G ⧸ N)) (B : Rep ℚ G) (a : A) (b : B) :
    ((quotientProjection N A).hom.app B)
      (coinvariantsTensorMk (Rep.res (QuotientGroup.mk' N) A) B a b) =
      coinvariantsTensorMk A ((functor N).obj B) a (Coinvariants.mk _ b) := by
  change (((coinvariantsTensor ℚ (G ⧸ N)).obj A).map ((inductionIso N).hom.app B))
    (((tensorSymmetry A).inv.app (Rep.ind (QuotientGroup.mk' N) B))
      ((coinvariantsTensorIndInv (QuotientGroup.mk' N) B A)
        (((tensorSymmetry (Rep.res (QuotientGroup.mk' N) A)).hom.app B)
          (coinvariantsTensorMk (Rep.res (QuotientGroup.mk' N) A) B a b)))) = _
  rw [tensorSymmetry_mk]
  have h : coinvariantsTensorIndInv (QuotientGroup.mk' N) B A
      (coinvariantsTensorMk B (Rep.res (QuotientGroup.mk' N) A) b a) =
      coinvariantsTensorMk (Rep.ind (QuotientGroup.mk' N) B) A
        (IndV.mk (QuotientGroup.mk' N) B.ρ 1 b) a :=
    coinvariantsTensorIndInv_mk_tmul_indMk (QuotientGroup.mk' N) b a
  rw [h,tensorSymmetry_inv_mk]
  exact (tensor_map_mk A ((inductionIso N).hom.app B) a
    (IndV.mk (QuotientGroup.mk' N) B.ρ 1 b)).trans
    (congrArg (coinvariantsTensorMk A ((functor N).obj B) a) (inductionIso_one N B b))

lemma chainsIso_single {H : Type} [Group H] [DecidableEq H] (A : Rep ℚ H) (n : ℕ)
    (x : Fin n → H) (a : A) :
    ((groupHomology.inhomogeneousChainsIso A).hom.f n) (single x a) =
      coinvariantsTensorMk A ((Rep.barComplex ℚ H).X n) a (single x (.single 1 1)) :=
  Rep.finsuppToCoinvariantsTensorFree_single x a

end RelativeCoinvariants
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory
namespace VectorFactor
variable {U V W : Type} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

lemma exists_factor (f : U →ₗ[ℚ] V) (g : U →ₗ[ℚ] W) (h : f.ker ≤ g.ker) :
    ∃t : V →ₗ[ℚ] W, t.comp f = g := by
  let a : f.range →ₗ[ℚ] W := (f.ker.liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨t,ht⟩ := a.exists_extend
  refine ⟨t,?_⟩
  ext u
  have he := LinearMap.congr_fun ht (f.rangeRestrict u)
  change t (f u) = _ at he
  change t (f u) = g u
  rw [he]
  change (f.ker.liftQ g h) (f.quotKerEquivRange.symm (f.rangeRestrict u)) = g u
  have hq : f.rangeRestrict u = f.quotKerEquivRange (Submodule.Quotient.mk u) := rfl
  rw [hq,LinearEquiv.symm_apply_apply]
  rfl
end VectorFactor
namespace RationalBar
variable (G : Type) [Group G]
abbrev T := Rep.trivial ℚ G ℚ
abbrev C2 := G × G →₀ ℚ
abbrev C3 := G × G × G →₀ ℚ
abbrev d3 : C3 G →ₗ[ℚ] C2 G := (groupHomology.d₃₂ (T G)).hom
abbrev Z2 := groupHomology.cycles₂ (T G)
abbrev B2 := groupHomology.boundaries₂ (T G)
abbrev H2 := groupHomology (T G) 2
abbrev π : Z2 G →ₗ[ℚ] H2 G := (groupHomology.H2π (T G)).hom

def Cocycles : Submodule ℚ (C2 G →ₗ[ℚ] ℚ) :=
  LinearMap.ker (LinearMap.lcomp ℚ ℚ (d3 G))

variable {G}
lemma cocycle_iff (c : C2 G →ₗ[ℚ] ℚ) : c ∈ Cocycles G ↔ c.comp (d3 G)=0 := Iff.rfl
lemma cocycle_vanish (c : Cocycles G) (z : B2 G) : c.val z.val=0 := by
  obtain ⟨w,hw⟩ := z.property
  have h := LinearMap.congr_fun c.property w
  change c.val (d3 G w)=0 at h
  simpa only [hw] using h

lemma exists_evaluation (c : Cocycles G) :
    ∃e : H2 G →ₗ[ℚ] ℚ, e.comp (π G) = c.val.comp (Z2 G).subtype := by
  apply VectorFactor.exists_factor
  intro z hz
  have hb := (groupHomology.H2π_eq_zero_iff z).mp hz
  exact cocycle_vanish c ⟨z.val,hb⟩

def evaluation (c : Cocycles G) : H2 G →ₗ[ℚ] ℚ := (exists_evaluation c).choose
lemma evaluation_cycle (c : Cocycles G) (z : Z2 G) : evaluation c (π G z) = c.val z.val :=
  LinearMap.congr_fun (exists_evaluation c).choose_spec z

lemma cocycle_of_cycle_restriction (e : H2 G →ₗ[ℚ] ℚ) (c : C2 G →ₗ[ℚ] ℚ)
    (hc : c.comp (Z2 G).subtype = e.comp (π G)) : c ∈ Cocycles G := by
  rw [cocycle_iff]
  apply LinearMap.ext
  intro w
  let z : Z2 G := ⟨d3 G w,groupHomology.d₃₂_apply_mem_cycles₂ (A := T G) w⟩
  have hz : π G z=0 := (groupHomology.H2π_eq_zero_iff z).mpr ⟨w,rfl⟩
  have h := LinearMap.congr_fun hc z
  change c (d3 G w)=e (π G z) at h
  change c (d3 G w)=0
  simpa only [hz,map_zero] using h

lemma evaluation_surjective : Function.Surjective (evaluation (G := G)) := by
  intro e
  obtain ⟨c,hc⟩ := (e.comp (π G)).exists_extend
  refine ⟨⟨c,cocycle_of_cycle_restriction e c hc⟩,?_⟩
  apply LinearMap.ext
  intro h
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance h
  exact (evaluation_cycle _ z).trans (LinearMap.congr_fun hc z)

end RationalBar
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability.RationalBar
noncomputable section
open Classical CategoryTheory
variable {G H K : Type} [Group G] [Group H] [Group K]

def evaluationMap : Cocycles G →ₗ[ℚ] (H2 G →ₗ[ℚ] ℚ) where
  toFun := evaluation
  map_add' c d := by
    ext x
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance x
    change evaluation (c+d) (π G z)=evaluation c (π G z)+evaluation d (π G z)
    rw [evaluation_cycle,evaluation_cycle,evaluation_cycle]
    rfl
  map_smul' a c := by
    ext x
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance x
    change evaluation (a • c) (π G z)=a • evaluation c (π G z)
    rw [evaluation_cycle,evaluation_cycle]
    rfl

abbrev map2 (f : G →* H) : C2 G →ₗ[ℚ] C2 H :=
  (groupHomology.chainsMap₂ (A := T G) (B := T H) f (𝟙 (T G))).hom
abbrev map3 (f : G →* H) : C3 G →ₗ[ℚ] C3 H :=
  (groupHomology.chainsMap₃ (A := T G) (B := T H) f (𝟙 (T G))).hom

lemma map2_d3 (f : G →* H) : (map2 f).comp (d3 G) = (d3 H).comp (map3 f) := by
  exact (congrArg ModuleCat.Hom.hom (groupHomology.mapShortComplexH2 (A := T G) (B := T H) f (𝟙 (T G))).comm₁₂).symm

def pull (f : G →* H) : Cocycles H →ₗ[ℚ] Cocycles G where
  toFun c := ⟨c.val.comp (map2 f),by
    have hc : c.val.comp (d3 H)=0 := c.property
    rw [cocycle_iff,LinearMap.comp_assoc,map2_d3,←LinearMap.comp_assoc,hc]
    rfl⟩
  map_add' c d := by ext z; rfl
  map_smul' a c := by ext z; rfl

end

noncomputable section
open Classical CategoryTheory
variable {G H : Type} [Group G] [Group H]

def value (c : Cocycles G) (g h : G) : ℚ := c.val (Finsupp.single (g,h) 1)

lemma identity (c : Cocycles G) (g h k : G) :
    value c g h + value c (g*h) k = value c h k + value c g (h*k) := by
  have hc : c.val (d3 G (Finsupp.single (g,h,k) 1))=0 := LinearMap.congr_fun c.property _
  change c.val (groupHomology.d₃₂ (T G) (Finsupp.single (g,h,k) 1))=0 at hc
  rw [groupHomology.d₃₂_single] at hc
  change c.val (Finsupp.single (h,k) 1-Finsupp.single (g*h,k) 1+
    Finsupp.single (g,h*k) 1-Finsupp.single (g,h) 1)=0 at hc
  simp only [map_sub,map_add] at hc
  dsimp only [value]
  linarith

lemma value_one_left (c : Cocycles G) (g : G) : value c 1 g=value c 1 1 := by
  have h := identity c 1 1 g
  simp only [one_mul] at h
  linarith
lemma value_one_right (c : Cocycles G) (g : G) : value c g 1=value c 1 1 := by
  have h := identity c g 1 1
  simp only [mul_one] at h
  linarith
lemma value_inv (c : Cocycles G) (g : G) : value c g⁻¹ g=value c g g⁻¹ := by
  have h := identity c g g⁻¹ g
  simp only [mul_inv_cancel,inv_mul_cancel,value_one_left,value_one_right] at h
  linarith

def Extension (_c : Cocycles G) := ℚ × G

instance extensionGroup (c : Cocycles G) : Group (Extension c) where
  mul x y := (x.1+y.1+value c x.2 y.2,x.2*y.2)
  one := (-value c 1 1,1)
  inv x := (-value c 1 1-x.1-value c x.2 x.2⁻¹,x.2⁻¹)
  mul_assoc x y z := Prod.ext (by
    change x.1+y.1+value c x.2 y.2+z.1+value c (x.2*y.2) z.2 =
      x.1+(y.1+z.1+value c y.2 z.2)+value c x.2 (y.2*z.2)
    linarith [identity c x.2 y.2 z.2]) (mul_assoc _ _ _)
  one_mul x := Prod.ext (by
    change -value c 1 1+x.1+value c 1 x.2=x.1
    rw [value_one_left c x.2]; ring) (one_mul _)
  mul_one x := Prod.ext (by
    change x.1+-value c 1 1+value c x.2 1=x.1
    rw [value_one_right c x.2]; ring) (mul_one _)
  inv_mul_cancel x := Prod.ext (by
    change -value c 1 1-x.1-value c x.2 x.2⁻¹+x.1+value c x.2⁻¹ x.2=-value c 1 1
    rw [value_inv]; ring) (inv_mul_cancel _)

def projection (c : Cocycles G) : Extension c →* G where
  toFun := Prod.snd
  map_one' := rfl
  map_mul' _ _ := rfl

lemma pull_value (f : G →* H) (c : Cocycles H) (g h : G) :
    value (pull f c) g h = value c (f g) (f h) := by
  change c.val (map2 f (Finsupp.single (g,h) 1)) = _
  simp [map2,groupHomology.chainsMap₂,value]
  rfl

end
end SourceBurnside.Stability.RationalBar

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_HierarchyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.WeightedTests

open scoped BigOperators
noncomputable section
open Classical

variable {Γ : Type u} [Fintype Γ] {R : Type v} [Semiring R]

def product {r : ℕ} (f : Γ → R) (v : Fin r → Γ) : R :=
  (List.ofFn (f ∘ v)).prod

def length {r : ℕ} (l : Γ → ℕ) (v : Fin r → Γ) : ℕ := ∑ i, l (v i)

def lengthPolynomial (l : Γ → ℕ) (f : Γ → R) (n : ℕ) : Polynomial R :=
  ∑ r ∈ Finset.range (n+1), ∑ v : Fin r → Γ,
    if length l v = n then Polynomial.monomial r (product f v) else 0

end
end SourceBurnside.WeightedTests

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Frames_AcyclicFrameEdge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HomologyEdge
variable {G : Type} [Group G] (C : ChainComplex (Rep ℚ G) ℕ)

abbrev Z (i : ℕ) := kernel (C.d (i+1) i)

def ontoCycles (i : ℕ) : C.X (i+2) ⟶ Z C i :=
  kernel.lift _ (C.d (i+2) (i+1)) (C.d_comp_d _ _ _)

lemma ontoCycles_epi (i : ℕ) (h : (C.sc' (i+2) (i+1) i).Exact) :
    Epi (ontoCycles C i) := h.epi_kernelLift

def cycleSequence (i : ℕ) : ShortComplex (Rep ℚ G) :=
  ShortComplex.mk (kernel.ι (C.d (i+2) (i+1))) (ontoCycles C i) (by
    apply (cancel_mono (kernel.ι (C.d (i+1) i))).mp
    simp [ontoCycles])

lemma cycleSequence_exact (i : ℕ) : (cycleSequence C i).Exact := by
  let φ : cycleSequence C i ⟶ ShortComplex.kernelSequence (C.d (i+2) (i+1)) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι (C.d (i+1) i)
      comm₁₂ := by
        change 𝟙 _ ≫ kernel.ι _ = kernel.ι _ ≫ 𝟙 _
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      comm₂₃ := by
        change 𝟙 _ ≫ C.d (i+2) (i+1) =
          kernel.lift _ (C.d (i+2) (i+1)) _ ≫ kernel.ι _
        exact (Category.id_comp _).trans (kernel.lift_ι _ _ _).symm }
  have : Epi φ.τ₁ := by
    change Epi (𝟙 (kernel (C.d (i+2) (i+1))))
    infer_instance
  have : IsIso φ.τ₂ := by
    change IsIso (𝟙 (C.X (i+2)))
    infer_instance
  have : Mono φ.τ₃ := by
    change Mono (kernel.ι (C.d (i+1) i))
    exact inferInstanceAs (Mono (kernel.ι (C.d (i+1) i)))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr
    (ShortComplex.kernelSequence_exact _)

lemma cycleSequence_shortExact (i : ℕ) (h : (C.sc' (i+2) (i+1) i).Exact) :
    (cycleSequence C i).ShortExact := by
  have := ontoCycles_epi C i h
  exact { exact := cycleSequence_exact C i
          mono_f := by dsimp [cycleSequence]; infer_instance
          epi_g := by dsimp [cycleSequence]; infer_instance }

lemma zero_H0_of_epi {A B : Rep ℚ G} (f : A ⟶ B) [Epi f]
    (hA : IsZero (groupHomology A 0)) : IsZero (groupHomology B 0) := by
  have : Epi (groupHomology.map (MonoidHom.id G) f 0) := inferInstance
  exact IsZero.of_epi (groupHomology.map (MonoidHom.id G) f 0) hA

lemma isIso_H2_augmentation
    (hepi : Epi (C.d 1 0))
    (hex : ∀ i : Fin 3, (C.sc' (i.val+2) (i.val+1) i.val).Exact)
    (hacyc : ∀ i : Fin 3, ∀ q : ℕ, IsZero (groupHomology (C.X (i.val+2)) q)) :
    IsIso (groupHomology.map (MonoidHom.id G) (C.d 1 0) 2) := by
  have := hepi
  have := ontoCycles_epi C 2 (hex 2)
  have hz2 : IsZero (groupHomology (Z C 2) 0) :=
    zero_H0_of_epi (ontoCycles C 2) (hacyc 2 0)
  have hs1 := cycleSequence_shortExact C 1 (hex 1)
  have hz1 : IsZero (groupHomology (Z C 1) 1) :=
    (groupHomology.mapShortComplex₃_exact hs1 (i := 1) (j := 0) rfl).isZero_of_both_isZero
      (hacyc 1 1) hz2
  have := ontoCycles_epi C 1 (hex 1)
  have hz10 : IsZero (groupHomology (Z C 1) 0) :=
    zero_H0_of_epi (ontoCycles C 1) (hacyc 1 0)
  have hs0 := cycleSequence_shortExact C 0 (hex 0)
  have hz02 : IsZero (groupHomology (Z C 0) 2) :=
    (groupHomology.mapShortComplex₃_exact hs0 (i := 2) (j := 1) rfl).isZero_of_both_isZero
      (hacyc 0 2) hz1
  have hz01 : IsZero (groupHomology (Z C 0) 1) :=
    (groupHomology.mapShortComplex₃_exact hs0 (i := 1) (j := 0) rfl).isZero_of_both_isZero
      (hacyc 0 1) hz10
  have hs : (ShortComplex.kernelSequence (C.d 1 0)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _
      mono_f := inferInstance
      epi_g := by change Epi (C.d 1 0); infer_instance }
  have : Mono (groupHomology.map (MonoidHom.id G) (C.d 1 0) 2) :=
    ((groupHomology.mapShortComplex₂ _ 2).exact_iff_mono
      (hz02.eq_zero_of_src _)).mp (groupHomology.mapShortComplex₂_exact hs 2)
  have : Epi (groupHomology.map (MonoidHom.id G) (C.d 1 0) 2) :=
    ((groupHomology.mapShortComplex₃ hs (i := 2) (j := 1) rfl).exact_iff_epi
      (hz01.eq_zero_of_tgt _)).mp (groupHomology.mapShortComplex₃_exact hs rfl)
  exact isIso_of_mono_of_epi _

end HomologyEdge
end
end SourceBurnside.Stability

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_LocallyFiniteActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.UnorderedStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical
open scoped Pointwise

end SourceBurnside.Stability.UnorderedStabilizer

namespace SourceBurnside.Stability
open Classical CategoryTheory Representation Rep Module
namespace MonomialInduction
variable {G X : Type} [Group G] [MulAction G X] (x₀ : X)

abbrev charRep (χ : (MulAction.stabilizer G x₀) →* ℚˣ) : Rep ℚ (MulAction.stabilizer G x₀) := Rep.of (k := ℚ) (X := ℚ)
  { toFun s := (χ s).val • LinearMap.id
    map_one' := by ext; simp
    map_mul' s t := by ext; simp [mul_smul,mul_comm] }

@[simp] lemma charRep_apply (χ : (MulAction.stabilizer G x₀) →* ℚˣ) (s : (MulAction.stabilizer G x₀)) (a : ℚ) :
    (charRep x₀ χ).ρ s a = (χ s).val * a := rfl

lemma ind_relation (A : Rep ℚ (MulAction.stabilizer G x₀)) (s : (MulAction.stabilizer G x₀)) (g : G) (a : A) :
    IndV.mk (MulAction.stabilizer G x₀).subtype A.ρ (s.val*g) (A.ρ s a) = IndV.mk (MulAction.stabilizer G x₀).subtype A.ρ g a := by
  change Coinvariants.mk _ (MonoidAlgebra.single (s.val*g) (1 : ℚ) ⊗ₜ[ℚ] A.ρ s a) =
    Coinvariants.mk _ (MonoidAlgebra.single g (1 : ℚ) ⊗ₜ[ℚ] a)
  simpa using Coinvariants.mk_self_apply
    (Representation.tprod ((Representation.leftRegular ℚ G).comp (MulAction.stabilizer G x₀).subtype) A.ρ) s
    (MonoidAlgebra.single g (1 : ℚ) ⊗ₜ[ℚ] a)

variable (A : Rep.{0} ℚ G) (b : Basis X ℚ A) (χ : (MulAction.stabilizer G x₀) →* ℚˣ)
variable (hχ : ∀s : (MulAction.stabilizer G x₀), A.ρ s.val (b x₀) = ((χ s).val : ℚ) • b x₀)

def basisSeed (χ : (MulAction.stabilizer G x₀) →* ℚˣ)
    (hχ : ∀s : (MulAction.stabilizer G x₀), A.ρ s.val (b x₀) = ((χ s).val : ℚ) • b x₀) :
    charRep x₀ χ ⟶ Rep.res (MulAction.stabilizer G x₀).subtype A := by
  refine Rep.ofHom { toLinearMap := LinearMap.toSpanSingleton ℚ A (b x₀), isIntertwining' := ?_ }
  intro s
  apply LinearMap.ext
  intro a
  change ((χ s).val*a) • b x₀ = A.ρ s.val (a • b x₀)
  rw [map_smul,hχ,mul_smul,smul_comm]

def induced : Rep.ind (MulAction.stabilizer G x₀).subtype (charRep x₀ χ) ⟶ A :=
  (Rep.indResHomEquiv (MulAction.stabilizer G x₀).subtype _ A).symm (basisSeed x₀ A b χ hχ)

lemma induced_mk (g : G) (a : ℚ) :
    (induced x₀ A b χ hχ).hom (IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ g a) =
      a • A.ρ g⁻¹ (b x₀) := by
  simp [induced,Rep.indResHomEquiv,basisSeed]

variable (ht : ∀x : X, ∃g : G, g • x₀ = x)
variable (hm : ∀(g : G) (x : X), ∃c : ℚˣ, A.ρ g (b x) = c.val • b (g • x))

def transporter (x : X) : G := (ht x).choose
lemma transporter_spec (x : X) : transporter x₀ ht x • x₀ = x := (ht x).choose_spec

def coefficient (x : X) : ℚˣ := (hm (transporter x₀ ht x) x₀).choose

def orbitBasis : Basis X ℚ A := b.unitsSMul (coefficient x₀ A b ht hm)

lemma orbitBasis_eq (x : X) : orbitBasis x₀ A b ht hm x = A.ρ (transporter x₀ ht x) (b x₀) := by
  rw [orbitBasis,Basis.unitsSMul_apply]
  have h := (hm (transporter x₀ ht x) x₀).choose_spec
  change A.ρ (transporter x₀ ht x) (b x₀) = (coefficient x₀ A b ht hm x).val • b (transporter x₀ ht x • x₀) at h
  rw [transporter_spec] at h
  exact h.symm

def inverseLinear : A →ₗ[ℚ] Rep.ind (MulAction.stabilizer G x₀).subtype (charRep x₀ χ) :=
  (orbitBasis x₀ A b ht hm).constr ℚ
    (fun x => IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ (transporter x₀ ht x)⁻¹ 1)

lemma inverseLinear_basis (x : X) :
    inverseLinear x₀ A b χ ht hm (orbitBasis x₀ A b ht hm x) =
      IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ (transporter x₀ ht x)⁻¹ 1 := by
  exact Basis.constr_basis _ _ _ _

lemma induced_inverse :
    (induced x₀ A b χ hχ).hom.toLinearMap.comp (inverseLinear x₀ A b χ ht hm) = LinearMap.id := by
  apply (orbitBasis x₀ A b ht hm).ext
  intro x
  change (induced x₀ A b χ hχ).hom (inverseLinear x₀ A b χ ht hm (orbitBasis x₀ A b ht hm x)) = orbitBasis x₀ A b ht hm x
  rw [inverseLinear_basis,induced_mk,inv_inv,one_smul]
  exact (orbitBasis_eq x₀ A b ht hm x).symm

def residual (g : G) : MulAction.stabilizer G x₀ :=
  ⟨(transporter x₀ ht (g⁻¹ • x₀))⁻¹*g⁻¹,by
    rw [MulAction.mem_stabilizer_iff,mul_smul]
    exact (congrArg ((transporter x₀ ht (g⁻¹ • x₀))⁻¹ • ·) (transporter_spec x₀ ht (g⁻¹ • x₀))).symm.trans (inv_smul_smul _ _)⟩

include hχ in
lemma action_residual (g : G) :
    A.ρ g⁻¹ (b x₀) = ((χ (residual x₀ ht g)).val : ℚ) • orbitBasis x₀ A b ht hm (g⁻¹ • x₀) := by
  rw [orbitBasis_eq]
  have he : g⁻¹ = transporter x₀ ht (g⁻¹ • x₀) * (residual x₀ ht g).val := by
    simp [residual]
  conv_lhs => rw [he]
  rw [map_mul]
  change A.ρ (transporter x₀ ht (g⁻¹ • x₀)) (A.ρ (residual x₀ ht g).val (b x₀)) = _
  rw [hχ,map_smul]

lemma inverse_induced :
    (inverseLinear x₀ A b χ ht hm).comp (induced x₀ A b χ hχ).hom.toLinearMap = LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change inverseLinear x₀ A b χ ht hm ((induced x₀ A b χ hχ).hom (IndV.mk _ _ g a)) = IndV.mk _ _ g a
  rw [induced_mk,action_residual x₀ A b χ hχ ht hm,map_smul,map_smul,inverseLinear_basis]
  have he := ind_relation x₀ (charRep x₀ χ) (residual x₀ ht g) g 1
  change IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ
    ((residual x₀ ht g).val*g) ((χ (residual x₀ ht g)).val*1) = _ at he
  simp only [mul_one,residual,mul_assoc,inv_mul_cancel,mul_one] at he
  have hs : ((χ (residual x₀ ht g)).val : ℚ) • IndV.mk (MulAction.stabilizer G x₀).subtype
      (charRep x₀ χ).ρ (transporter x₀ ht (g⁻¹ • x₀))⁻¹ 1 =
        IndV.mk (MulAction.stabilizer G x₀).subtype (charRep x₀ χ).ρ g 1 := by
    rw [←map_smul]
    simpa only [residual,smul_eq_mul,mul_one] using he
  rw [hs,←map_smul]
  simp

include ht hm in
lemma induced_isIso : IsIso (induced x₀ A b χ hχ) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hl : Function.LeftInverse (inverseLinear x₀ A b χ ht hm) (induced x₀ A b χ hχ).hom :=
    fun a => congrArg (fun f : Rep.ind (MulAction.stabilizer G x₀).subtype (charRep x₀ χ) →ₗ[ℚ] _ => f a)
      (inverse_induced x₀ A b χ hχ ht hm)
  have hr : Function.RightInverse (inverseLinear x₀ A b χ ht hm) (induced x₀ A b χ hχ).hom :=
    fun a => congrArg (fun f : A →ₗ[ℚ] A => f a) (induced_inverse x₀ A b χ hχ ht hm)
  exact ⟨hl.injective,hr.surjective⟩

end MonomialInduction
end SourceBurnside.Stability

namespace SourceBurnside.Stability.MonomialInduction
open Classical CategoryTheory Module
variable {G X : Type} [Group G] [MulAction G X]
variable (x₀ : X) (A : Rep.{0} ℚ G) (b : Basis X ℚ A)
variable (hm : ∀(g : G) (x : X), ∃c : ℚˣ, A.ρ g (b x) = c.val • b (g • x))

def scalar (s : MulAction.stabilizer G x₀) : ℚˣ := (hm s.val x₀).choose

lemma scalar_spec (s : MulAction.stabilizer G x₀) :
    A.ρ s.val (b x₀) = (scalar x₀ A b hm s).val • b x₀ := by
  have h := (hm s.val x₀).choose_spec
  change A.ρ s.val (b x₀) = (scalar x₀ A b hm s).val • b (s.val • x₀) at h
  rwa [s.property] at h

omit [MulAction G X] in
lemma smul_basis_injective : Function.Injective (fun c : ℚ => c • b x₀) := by
  intro c d h
  have he := congrArg (fun v : A => b.repr v x₀) h
  simpa using he

def character : MulAction.stabilizer G x₀ →* ℚˣ where
  toFun := scalar x₀ A b hm
  map_one' := by
    apply Units.ext
    apply smul_basis_injective x₀ A b
    dsimp only
    rw [←scalar_spec]
    change A.ρ 1 (b x₀) = (1 : ℚ) • b x₀
    simp
  map_mul' s t := by
    apply Units.ext
    apply smul_basis_injective x₀ A b
    dsimp only
    rw [←scalar_spec]
    change A.ρ (s.val*t.val) (b x₀) = ((scalar x₀ A b hm s).val*(scalar x₀ A b hm t).val) • b x₀
    rw [map_mul]
    change A.ρ s.val (A.ρ t.val (b x₀)) = _
    rw [scalar_spec,map_smul,scalar_spec,mul_smul,smul_comm]

lemma character_spec (s : MulAction.stabilizer G x₀) :
    A.ρ s.val (b x₀) = ((character x₀ A b hm s).val : ℚ) • b x₀ := scalar_spec x₀ A b hm s

end SourceBurnside.Stability.MonomialInduction

namespace SourceBurnside.Stability
open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace ShapiroMap
variable {G : Type} [Group G] (S : Subgroup G)

def resolution : ProjectiveResolution (Rep.trivial ℚ S ℚ) :=
  (Rep.resFunctor S.subtype).mapProjectiveResolution (Rep.barResolution ℚ G)

def tensorIso (A : Rep ℚ S) :
    (resolution S).complex.coinvariantsTensorObj A ≅
      (Rep.barComplex ℚ G).coinvariantsTensorObj (Rep.ind S.subtype A) :=
  groupHomology.coinvariantsTensorResProjectiveResolutionIso S A (Rep.barResolution ℚ G)

def unit (A : Rep ℚ S) : A ⟶ Rep.res S.subtype (Rep.ind S.subtype A) :=
  (Rep.indResAdjunction ℚ S.subtype).unit.app A

@[simp] lemma unit_apply (A : Rep ℚ S) (a : A) :
    (unit S A).hom a = IndV.mk S.subtype A.ρ 1 a := rfl

lemma tensorIso_mk (A : Rep ℚ S) (n : ℕ) (a : A) (b : (Rep.barComplex ℚ G).X n) :
    ((tensorIso S A).hom.f n)
      (coinvariantsTensorMk A (Rep.res S.subtype ((Rep.barComplex ℚ G).X n)) a b) =
    coinvariantsTensorMk (Rep.ind S.subtype A) ((Rep.barComplex ℚ G).X n)
      (IndV.mk S.subtype A.ρ 1 a) b :=
  coinvariantsTensorIndInv_mk_tmul_indMk S.subtype a b

end ShapiroMap
end SourceBurnside.Stability

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_FiniteNormalHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability
section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep

namespace FiniteNormal
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [Fintype N]

def averageEnd (A : Rep ℚ G) : A ⟶ A := Rep.ofHom
  { toLinearMap := FiniteAverage.average (A.ρ.comp N.subtype)
    isIntertwining' := by
      intro g
      ext x
      simp only [LinearMap.comp_apply, FiniteAverage.average_apply, map_smul, map_sum,
        MonoidHom.comp_apply]
      congr 1
      apply Fintype.sum_equiv (MulAut.conjNormal (H := N) g⁻¹).toEquiv
      intro n
      change A.ρ n.val (A.ρ g x) = A.ρ g (A.ρ ((MulAut.conjNormal g⁻¹) n).val x)
      simp only [← Module.End.mul_apply, ← map_mul, MulAut.conjNormal_apply]
      congr 2
      group }

lemma averageEnd_natural {A B : Rep ℚ G} (f : A ⟶ B) :
    averageEnd N A ≫ f = f ≫ averageEnd N B := by
  ext x
  exact FiniteAverage.intertwining _ _ (Rep.resMap N.subtype f).hom x

lemma averageEnd_trivial : averageEnd N (Rep.trivial ℚ G ℚ) = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change FiniteAverage.average _ x = x
  rw [FiniteAverage.average_apply]
  simp only [MonoidHom.comp_apply, Representation.trivial_apply,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

def averageChain (C : ChainComplex (Rep ℚ G) ℕ) : C ⟶ C where
  f n := averageEnd N (C.X n)
  comm' i j _ := averageEnd_natural N (C.d i j)

lemma averageChain_π (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) :
    averageChain N P.complex ≫ P.π = P.π := by
  apply HomologicalComplex.Hom.ext
  funext n
  change averageEnd N (P.complex.X n) ≫ P.π.f n = P.π.f n
  rw [averageEnd_natural]
  cases n with
  | zero => rw [show averageEnd N (((ChainComplex.single₀ (Rep ℚ G)).obj
      (Rep.trivial ℚ G ℚ)).X 0) = 𝟙 _ from averageEnd_trivial N, Category.comp_id]
  | succ n => exact (Limits.isZero_zero _).eq_of_tgt _ _

def averageHomotopy (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) :
    Homotopy (averageChain N P.complex) (𝟙 P.complex) :=
  ProjectiveResolution.liftHomotopy (𝟙 _) _ _
    (by simpa using averageChain_π N P) (by simp)

lemma averageBalanced (A B : Rep ℚ G) :
    ((Rep.coinvariantsTensor ℚ G).obj A).map (averageEnd N B) =
      ((Rep.coinvariantsTensor ℚ G).map (averageEnd N A)).app B := by
  apply Rep.coinvariantsTensor_hom_ext
  ext a b
  change Coinvariants.mk (A.ρ.tprod B.ρ)
      (a ⊗ₜ[ℚ] FiniteAverage.average (B.ρ.comp N.subtype) b) =
    Coinvariants.mk (A.ρ.tprod B.ρ)
      (FiniteAverage.average (A.ρ.comp N.subtype) a ⊗ₜ[ℚ] b)
  simp only [FiniteAverage.average_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul,
    TensorProduct.tmul_sum, TensorProduct.sum_tmul, map_smul, map_sum, MonoidHom.comp_apply]
  congr 1
  calc
    _ = ∑ n : N, Coinvariants.mk (A.ρ.tprod B.ρ) (A.ρ n.val⁻¹ a ⊗ₜ[ℚ] b) := by
      apply Finset.sum_congr rfl
      intro n _
      exact (Coinvariants.mk_inv_tmul A.ρ B.ρ a b n.val).symm
    _ = _ := Fintype.sum_equiv (Equiv.inv N) _ _ (fun n => rfl)

lemma averageTensor_zero (A B : Rep ℚ G) (hA : averageEnd N A = 0) :
    ((Rep.coinvariantsTensor ℚ G).obj A).map (averageEnd N B) = 0 := by
  rw [averageBalanced, hA]
  apply Rep.coinvariantsTensor_hom_ext
  ext a b
  simp [Rep.coinvariantsTensorMk]

theorem homology_isZero (A : Rep ℚ G) (hA : averageEnd N A = 0) (n : ℕ) :
    IsZero (groupHomology A n) := by
  let P := Rep.barResolution ℚ G
  let F := (Rep.coinvariantsTensor ℚ G).obj A
  have hz : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (averageChain N P.complex) = 0 := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact averageTensor_zero N A _ hA
  have ht := (F.mapHomotopy (averageHomotopy N P)).homologyMap_eq n
  rw [hz, HomologicalComplex.homologyMap_zero, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id] at ht
  exact ((Limits.IsZero.iff_id_eq_zero _).mpr ht.symm).of_iso (groupHomologyIso A n P)

lemma averageEnd_zero_of_neg (A : Rep ℚ G) (t : N)
    (ht : ∀ a : A, A.ρ t.val a = -a) : averageEnd N A = 0 := by
  ext a
  change FiniteAverage.average (A.ρ.comp N.subtype) a = 0
  have h := FiniteAverage.average_action (A.ρ.comp N.subtype) t a
  change FiniteAverage.average (A.ρ.comp N.subtype) (A.ρ t.val a) = _ at h
  rw [ht, map_neg] at h
  have htwo : (2 : ℚ) • FiniteAverage.average (A.ρ.comp N.subtype) a = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h.symm
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end FiniteNormal
end

section
open Classical CategoryTheory CategoryTheory.Limits Rep

abbrev scalarRep {G : Type} [Group G] (χ : G →* ℚˣ) : Rep ℚ G :=
  Rep.of (k := ℚ) (X := ℚ)
    { toFun g := (χ g).val • LinearMap.id
      map_one' := by ext; simp
      map_mul' g h := by ext; simp [mul_smul,mul_comm] }

namespace SignHomology
variable {G H : Type} [Group G] [Group H]

lemma isZero_of_finite_normal (χ : G →* ℚˣ)
    (N : Subgroup G) [N.Normal] [Fintype N] (t : N) (ht : χ t.val = -1) (n : ℕ) :
    IsZero (groupHomology (scalarRep χ) n) := by
  apply FiniteNormal.homology_isZero N
  apply FiniteNormal.averageEnd_zero_of_neg N _ t
  intro a
  change (χ t.val).val • a = -a
  rw [ht]
  simp

lemma product_isZero {P : Type} [Group P] [Fintype P] (χ : G × P →* ℚˣ)
    (p : P) (hp : χ (1,p) = -1) (n : ℕ) :
    IsZero (groupHomology (scalarRep χ) n) := by
  let N : Subgroup (G × P) := (MonoidHom.fst G P).ker
  let e : N ≃ P :=
    { toFun x := x.val.2
      invFun p := ⟨(1,p),rfl⟩
      left_inv x := Subtype.ext (Prod.ext x.property.symm rfl)
      right_inv p := rfl }
  let : Fintype N := Fintype.ofEquiv P e.symm
  exact isZero_of_finite_normal χ N ⟨(1,p),rfl⟩ hp n

end SignHomology
end

attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module
open scoped Pointwise
end SourceBurnside.Stability

namespace SourceBurnside.Stability.FrameStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module
open scoped Pointwise

end SourceBurnside.Stability.FrameStabilizer

namespace SourceBurnside.Stability.MonomialTrivial
open Classical CategoryTheory Representation Rep Module
variable {G X : Type} [Group G] [MulAction G X] (x₀ : X)
variable (A : Rep.{0} ℚ G) (b : Basis X ℚ A)
variable (h0 : ∀s : MulAction.stabilizer G x₀, A.ρ s.val (b x₀) = b x₀)

def scalarIso : MonomialInduction.charRep x₀ 1 ≅ Rep.trivial ℚ (MulAction.stabilizer G x₀) ℚ :=
  Rep.mkIso
    { __ := LinearEquiv.refl ℚ ℚ
      isIntertwining' := by intro s; ext; simp }

def seed : Rep.trivial ℚ (MulAction.stabilizer G x₀) ℚ ⟶
    Rep.res (MulAction.stabilizer G x₀).subtype A :=
  Rep.ofHom
    { toLinearMap := LinearMap.toSpanSingleton ℚ A (b x₀)
      isIntertwining' := by
        intro s
        apply LinearMap.ext
        intro a
        change a • b x₀ = A.ρ s.val (a • b x₀)
        rw [map_smul,h0] }

def induced : Rep.ind (MulAction.stabilizer G x₀).subtype (Rep.trivial ℚ (MulAction.stabilizer G x₀) ℚ) ⟶ A :=
  (Rep.indResHomEquiv (MulAction.stabilizer G x₀).subtype _ A).symm (seed x₀ A b h0)

lemma induced_mk (g : G) (a : ℚ) :
    (induced x₀ A b h0).hom (IndV.mk (MulAction.stabilizer G x₀).subtype
      (Rep.trivial ℚ (MulAction.stabilizer G x₀) ℚ).ρ g a) = a • A.ρ g⁻¹ (b x₀) := by
  simp [induced,Rep.indResHomEquiv,seed]

include h0 in
lemma scalar_property (s : MulAction.stabilizer G x₀) :
    A.ρ s.val (b x₀) = ((1 : MulAction.stabilizer G x₀ →* ℚˣ) s).val • b x₀ := by
  simpa using h0 s

lemma indMap_mk {H : Type} [Group H] (S : Subgroup H) {B C : Rep ℚ S} (f : B ⟶ C) (g : H) (a : B) :
    (Rep.indMap S.subtype f).hom (IndV.mk S.subtype B.ρ g a) = IndV.mk S.subtype C.ρ g (f.hom a) := by
  simp [Rep.indMap,IndV.mk]

lemma scalar_comp : (Rep.indFunctor ℚ (MulAction.stabilizer G x₀).subtype).map (scalarIso x₀).hom ≫
      induced x₀ A b h0 =
    MonomialInduction.induced x₀ A b 1 (scalar_property x₀ A b h0) := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change (induced x₀ A b h0).hom ((Rep.indMap (MulAction.stabilizer G x₀).subtype (scalarIso x₀).hom).hom
     (IndV.mk _ _ g a)) = _
  rw [indMap_mk,induced_mk]
  change a • A.ρ g⁻¹ (b x₀) =
    (MonomialInduction.induced x₀ A b 1 (scalar_property x₀ A b h0)).hom
      (IndV.mk (MulAction.stabilizer G x₀).subtype (MonomialInduction.charRep x₀ 1).ρ g a)
  exact (MonomialInduction.induced_mk x₀ A b 1 (scalar_property x₀ A b h0) g a).symm

variable (ht : ∀x : X, ∃g : G, g • x₀=x)
variable (hm : ∀(g : G) (x : X), ∃c : ℚˣ, A.ρ g (b x) = c.val • b (g • x))

include ht hm in
lemma induced_isIso : IsIso (induced x₀ A b h0) := by
  let i := (Rep.indFunctor ℚ (MulAction.stabilizer G x₀).subtype).mapIso (scalarIso x₀)
  have := MonomialInduction.induced_isIso x₀ A b 1 (scalar_property x₀ A b h0) ht hm
  have he : induced x₀ A b h0 = i.inv ≫ MonomialInduction.induced x₀ A b 1 (scalar_property x₀ A b h0) := by
    rw [←scalar_comp]
    change _ = i.inv ≫ i.hom ≫ induced x₀ A b h0
    rw [Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

end SourceBurnside.Stability.MonomialTrivial

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_RankActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability
section
open Classical
namespace FiniteRootPairs
variable {G : Type*} [Group G]

lemma finite_pair (a b : G) (ha : a^2=1) (hb : b^2=1) (hab : IsOfFinOrder (a*b)) :
    Finite (Subgroup.closure ({a,b} : Set G)) := by
  let C := Subgroup.zpowers (a*b)
  let D : Set G := (C : Set G) ∪ ((a * ·) '' (C : Set G))
  have ha' : a*a=1 := by simpa only [pow_two] using ha
  have hb' : b*b=1 := by simpa only [pow_two] using hb
  have hai : a⁻¹=a := inv_eq_of_mul_eq_one_left ha'
  have hbi : b⁻¹=b := inv_eq_of_mul_eq_one_left hb'
  have hba : b*a=(a*b)⁻¹ := by simp only [mul_inv_rev,hai,hbi]
  have finiteC : (C : Set G).Finite := Set.finite_coe_iff.mp hab.finite_zpowers
  have hD : D.Finite := finiteC.union (finiteC.image (a * ·))
  have hg (x : G) (hx : x∈({a,b}:Set G)) (y : G) (hy : y∈D) : x*y∈D := by
    rcases hx with hx | hx
    · have hxa : x=a := hx
      subst x
      rcases hy with hy | ⟨k,hk,rfl⟩
      · exact Or.inr ⟨y,hy,rfl⟩
      · exact Or.inl (by simpa only [←mul_assoc,ha',one_mul] using hk)
    · have hxb : x=b := hx
      subst x
      rcases hy with hy | ⟨k,hk,rfl⟩
      · refine Or.inr ⟨(a*b)*y,C.mul_mem (Subgroup.mem_zpowers (a*b)) hy,?_⟩
        simp only [←mul_assoc,ha',one_mul]
      · exact Or.inl (by
          rw [←mul_assoc,hba]
          exact C.mul_mem (C.inv_mem (Subgroup.mem_zpowers (a*b))) hk)
  have hcl : (Subgroup.closure ({a,b}:Set G) : Set G) ⊆ D := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one => exact Or.inl C.one_mem
    | mul_left z hz y hy ih => exact hg z hz y ih
    | inv_mul_cancel z hz y hy ih =>
      have hz' : z⁻¹=z := by rcases hz with rfl | ⟨rfl⟩; exact hai; exact hbi
      rw [hz']
      exact hg z hz y ih
  exact (hD.subset hcl).to_subtype

lemma finite_pair_commute (a b : G) (ha : a^2=1) (hb : b^2=1) (hc : Commute a b) :
    Finite (Subgroup.closure ({a,b}:Set G)) :=
  finite_pair a b ha hb (isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,by rw [hc.mul_pow,ha,hb,one_mul]⟩)

end FiniteRootPairs
end

open Classical
namespace ExtensionRootLift
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
variable {n : ℕ}

lemma add_self_zero (a : R) : a+a=0 := by
  have ht : (2 : ZMod 2)=0 := by decide
  calc
    a+a=(2 : ZMod 2) • a := (two_smul (ZMod 2) a).symm
    _=0 := by rw [ht,zero_smul]

end ExtensionRootLift
end SourceBurnside.Stability

namespace SourceBurnside.Stability.SteinbergAction
section
open Classical

def preservers {G : Type*} [Group G] (S : Subgroup G) : Subgroup (MulAut G) where
  carrier := {f | ∀g, f g∈S ↔ g∈S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' {f h} hf hh g := (hf (h g)).trans (hh g)
  inv_mem' {f} hf g := by
    have hh := hf (f⁻¹ g)
    simpa using hh.symm

end

open Classical

end SourceBurnside.Stability.SteinbergAction

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_KernelStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability

open Classical
namespace SurjectiveDescent
variable {P G X : Type} [Group P] [Group G] [Group X]

def descend (p : P →* G) (hp : Function.Surjective p) (F : P →* X) (hk : p.ker≤F.ker) : G →* X :=
  (QuotientGroup.lift p.ker F hk).comp (QuotientGroup.quotientKerEquivOfSurjective p hp).symm.toMonoidHom

lemma descend_apply (p : P →* G) (hp : Function.Surjective p) (F : P →* X) (hk : p.ker≤F.ker) (u : P) :
    descend p hp F hk (p u)=F u := by
  let e := QuotientGroup.quotientKerEquivOfSurjective p hp
  have he : e (QuotientGroup.mk' p.ker u)=p u := rfl
  change QuotientGroup.lift p.ker F hk (e.symm (p u))=F u
  rw [←he,MulEquiv.symm_apply_apply]
  rfl
end SurjectiveDescent
namespace RationalBar
variable {G H : Type} [Group G] [Group H]

lemma pull_id (c : Cocycles G) : pull (MonoidHom.id G) c=c := by
  apply Subtype.ext
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext
  intro a
  obtain ⟨g,h⟩ := p
  change c.val (map2 (MonoidHom.id G) (Finsupp.single (g,h) a))=c.val (Finsupp.single (g,h) a)
  simp [map2,groupHomology.chainsMap₂]

end RationalBar
end SourceBurnside.Stability

end

end OAI
end


