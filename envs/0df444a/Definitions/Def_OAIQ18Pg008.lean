-- Prove2me | Definitions.Def_OAIQ18Pg008
-- name    : OAIQ18Pg008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:57:28.326206+00:00
-- url     : https://prove2.me/theorems/76af28d1-2b53-451a-a8fe-cc27ca105f36
-- title:
--   Definitions bundle OAIQ18Pg008 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 11 definitions and 45 theorems. The definitions and types are `OAI.SourceBurnside.Stability.RationalBar.d2`, `OAI.SourceBurnside.Stability.RationalBar.extension`, `OAI.SourceBurnside.Stability.RationalBar.inclusion`, `OAI.SourceBurnside.Stability.RationalBar.liftOfCoboundary`, `OAI.SourceBurnside.Stability.RationalBar.morphism`, `OAI.SourceBurnside.Stability.RelativeCoinvariants.barComparison`, `OAI.SourceBurnside.Stability.RelativeCoinvariants.barComparisonComponent`, `OAI.SourceBurnside.Stability.RelativeCoinvariants.comparisonTensor`, `OAI.SourceBurnside.Stability.RelativeCoinvariants.projectionChain`, `OAI.SourceBurnside.Stability.RelativeCoinvariants.quotientResolution`, `OAI.SourceBurnside.Stability.ShapiroMap.comparisonTensor`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: [`PeriodicGroups_Frames_ElementaryFrames`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Frames/ElementaryFrames.lean), [`PeriodicGroups_Homology_FiniteExtensions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/FiniteExtensions.lean), [`PeriodicGroups_Homology_FiniteNormalHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/FiniteNormalHomology.lean), [`PeriodicGroups_Homology_KernelStability`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/KernelStability.lean), [`PeriodicGroups_Homology_LocallyFiniteActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/LocallyFiniteActions.lean), [`PeriodicGroups_Homology_RelativeHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/RelativeHomology.lean), [`PeriodicGroups_Presentation_FinitePresentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Presentation/FinitePresentation.lean).
--
--   **Imports.** It imports the bundles `OAIQ18Pg000`, `OAIQ18Pg001`, `OAIQ18Pg002` and `OAIQ18Pg003` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ18Pg010`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ18Pg000
import Definitions.Def_OAIQ18Pg001
import Definitions.Def_OAIQ18Pg002
import Definitions.Def_OAIQ18Pg003

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_FiniteExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open Classical

namespace RationalExtension
variable {E G : Type*} [Group E] [Group G] (S : RationalExtension E G)

lemma inl_eq_one_of_finite_order (q : QGroup) (hq : IsOfFinOrder (S.inl q)) : q = 1 := by
  obtain ⟨m, hm, he⟩ := hq.exists_pow_eq_one
  have hq : q ^ m = 1 := S.inl_injective (by simpa only [map_pow, map_one] using he)
  have ha : (m : ℚ) * q.toAdd = 0 := congrArg Multiplicative.toAdd hq
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have : q.toAdd = 0 := (mul_eq_zero.mp ha).resolve_left hm'
  exact this

theorem torsion_lift_unique {x y : E} (hx : IsOfFinOrder x) (hy : IsOfFinOrder y)
    (hxy : S.rightHom x = S.rightHom y) : x = y := by
  have hr : x * y⁻¹ ∈ S.inl.range := by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, hxy,
      mul_inv_cancel]
  obtain ⟨q, hq⟩ := hr
  have hc : Commute x y := by
    have ht := (S.inl_central q).comm y
    rw [hq] at ht
    have : x * y = y * x := by
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using
        congrArg (fun z : E => z * y) ht.eq
    exact this
  have hf : IsOfFinOrder (S.inl q) := hq.symm ▸ hc.inv_right.isOfFinOrder_mul hx hy.inv
  have he := S.inl_eq_one_of_finite_order q hf
  rw [he, map_one] at hq
  exact mul_inv_eq_one.mp hq.symm

lemma liftFinite_finite_order (H : Subgroup G) [Finite H] (g : H) :
    IsOfFinOrder (S.liftFinite H g) := by
  obtain ⟨m, hm, he⟩ := (isOfFinOrder_of_finite g).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, by rw [← map_pow, he, map_one]⟩

end RationalExtension
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability
noncomputable section
open Classical Representation

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

lemma coinvariant_finite_witness (hG : LocallyFinite G) (ρ : Representation ℚ G V)
    {v : V} (hv : v ∈ Coinvariants.ker ρ) :
    ∃ H : Subgroup G, Finite H ∧ v ∈ Coinvariants.ker (ρ.comp H.subtype) := by
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_span_finite_of_mem_span hv
  let pick (x : s) : G × V := (hs x.property).choose
  have hp (x : s) : ρ (pick x).1 (pick x).2 - (pick x).2 = x.val :=
    (hs x.property).choose_spec
  obtain ⟨H, hH, hfin⟩ := hG (Finset.univ.image fun x : s => (pick x).1)
  refine ⟨H, hfin, (show Submodule.span ℚ (s : Set V) ≤
    Coinvariants.ker (ρ.comp H.subtype) from ?_) hvs⟩
  apply Submodule.span_le.mpr
  intro x hx
  let y : s := ⟨x, hx⟩
  have hg : (pick y).1 ∈ H := hH _ (Finset.mem_image.mpr ⟨y, Finset.mem_univ _, rfl⟩)
  change y.val ∈ Coinvariants.ker (ρ.comp H.subtype)
  rw [← hp y]
  exact Coinvariants.sub_mem_ker (ρ := ρ.comp H.subtype) ⟨(pick y).1, hg⟩ (pick y).2

lemma locallyFinite_coinvariants_injective (hG : LocallyFinite G)
    (ρ : Representation ℚ G V) (τ : Representation ℚ G W)
    (f : ρ.IntertwiningMap τ) (hf : Function.Injective f) :
    Function.Injective (Coinvariants.map ρ τ f) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective ρ x
  obtain ⟨H, hfin, hv⟩ := coinvariant_finite_witness hG τ
    ((Coinvariants.mk_eq_zero τ).mp hx)
  let : Finite H := hfin
  let : Fintype H := Fintype.ofFinite H
  let fH : Representation.IntertwiningMap (ρ.comp H.subtype) (τ.comp H.subtype) :=
    { f with isIntertwining' := fun h => f.isIntertwining' h.val }
  have hzero : Coinvariants.map _ _ fH (Coinvariants.mk _ v) = 0 :=
    (Coinvariants.mk_eq_zero _).mpr hv
  have hk : v ∈ Coinvariants.ker (ρ.comp H.subtype) :=
    (Coinvariants.mk_eq_zero _).mp
      ((injective_iff_map_eq_zero _).mp (FiniteAverage.map_injective _ _ fH hf) _ hzero)
  apply (Coinvariants.mk_eq_zero ρ).mpr
  apply (show Coinvariants.ker (ρ.comp H.subtype) ≤ Coinvariants.ker ρ from ?_) hk
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨h, w⟩, rfl⟩
  exact Coinvariants.sub_mem_ker (ρ := ρ) h.val w

end

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation
universe u
variable {G : Type u} [Group G] (N : Subgroup G) [N.Normal]

namespace RelativeCoinvariants

lemma preservesMonomorphisms (hN : LocallyFinite N) :
    (functor N).PreservesMonomorphisms where
  preserves {A B} f hf := by
    apply (Rep.mono_iff_injective _).mpr
    exact locallyFinite_coinvariants_injective hN (A.ρ.comp N.subtype)
      (B.ρ.comp N.subtype) (Rep.resMap N.subtype f).hom
      ((Rep.mono_iff_injective f).mp hf)

lemma preservesHomology (hN : LocallyFinite N) :
    (functor N).PreservesHomology := by
  let := preservesMonomorphisms N hN
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels _

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
open Classical CategoryTheory CategoryTheory.Limits Representation Rep

namespace RelativeCoinvariants
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def quotientResolution (hN : LocallyFinite N) :
    ProjectiveResolution (Rep.trivial ℚ (G ⧸ N) ℚ) := by
  letI := preservesHomology N hN
  let P := (functor N).mapProjectiveResolution (Rep.barResolution ℚ G)
  exact
    { complex := P.complex
      projective := P.projective
      π := P.π ≫ (ChainComplex.single₀ _).map (trivialIso N).hom
      quasiIso := inferInstance }

end RelativeCoinvariants
end

end SourceBurnside.Stability

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
open scoped TensorProduct
open MonoidalCategory

namespace RelativeCoinvariants
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

def barComparisonComponent (n : ℕ) :
    (functor N).obj ((Rep.barComplex ℚ G).X n) ⟶ (Rep.barComplex ℚ (G ⧸ N)).X n :=
  (functor N).map ((BarMap.chain (QuotientGroup.mk' N)).f n) ≫
    counit N ((Rep.barComplex ℚ (G ⧸ N)).X n)

@[simp] lemma barComparisonComponent_mk (n : ℕ) (x : (Rep.barComplex ℚ G).X n) :
    (barComparisonComponent N n).hom (Coinvariants.mk _ x) =
      (BarMap.component (QuotientGroup.mk' N) n).hom x := rfl
def barComparison :
    ((functor N).mapHomologicalComplex _).obj (Rep.barComplex ℚ G) ⟶
      Rep.barComplex ℚ (G ⧸ N) where
  f n := barComparisonComponent N n
  comm' i j h := by
    apply Rep.hom_ext
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    induction x using Coinvariants.induction_on with | h x =>
    exact congrArg (fun f => f.hom x) ((BarMap.chain (QuotientGroup.mk' N)).comm i j)

lemma barComparison_π (hN : LocallyFinite N) :
    (barComparison N).f 0 ≫ (Rep.barResolution ℚ (G ⧸ N)).π.f 0 =
      (quotientResolution N hN).π.f 0 ≫ 𝟙 _ := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  induction x using Coinvariants.induction_on with | h x =>
  change ((Rep.barResolution ℚ (G ⧸ N)).π.f 0).hom
      ((BarMap.component (QuotientGroup.mk' N) 0).hom x) =
    ((Rep.barResolution ℚ G).π.f 0).hom x
  have h : BarMap.component (QuotientGroup.mk' N) 0 ≫
      Rep.resMap (QuotientGroup.mk' N) ((Rep.barResolution ℚ (G ⧸ N)).π.f 0) =
      (Rep.barResolution ℚ G).π.f 0 := by
    apply Rep.free_ext
    intro y
    change ((Rep.barResolution ℚ (G ⧸ N)).π.f 0).hom
      ((BarMap.component (QuotientGroup.mk' N) 0).hom (single y (.single 1 1))) = _
    rw [BarMap.component_single, BarMap.augmentation_single]
    exact (BarMap.augmentation_single y 1 1).symm
  exact congrArg (fun f => f.hom x) h

lemma barComparison_homology_isIso (hN : LocallyFinite N)
    (A : Rep ℚ (G ⧸ N)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((Rep.coinvariantsTensor ℚ (G ⧸ N)).obj A).mapHomologicalComplex _ |>.map
        (barComparison N)) n) := by
  let P := quotientResolution N hN
  let Q := Rep.barResolution ℚ (G ⧸ N)
  let F := (Rep.coinvariantsTensor ℚ (G ⧸ N)).obj A
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 _) P Q
    (barComparison N) (barComparison_π N hN) F n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have he : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex _).map (barComparison N)) n =
      (P.isoLeftDerivedObj F n).inv ≫ (Q.isoLeftDerivedObj F n).hom := by
    rw [h]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  rw [he]
  exact inferInstanceAs (IsIso ((P.isoLeftDerivedObj F n).symm ≪≫
    Q.isoLeftDerivedObj F n).hom)

def projectionChain (A : Rep ℚ (G ⧸ N)) :
    (Rep.barComplex ℚ G).coinvariantsTensorObj (Rep.res (QuotientGroup.mk' N) A) ≅
      (((functor N).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.barComplex ℚ G)).coinvariantsTensorObj A :=
  (NatIso.mapHomologicalComplex (quotientProjection N A) (ComplexShape.down ℕ)).app (Rep.barComplex ℚ G)

def comparisonTensor (A : Rep ℚ (G ⧸ N)) :
    (((functor N).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.barComplex ℚ G)).coinvariantsTensorObj A ⟶
      (Rep.barComplex ℚ (G ⧸ N)).coinvariantsTensorObj A :=
  (((coinvariantsTensor ℚ (G ⧸ N)).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map (barComparison N)

lemma barComparison_free (n : ℕ) (x : Fin n → G) :
    (barComparisonComponent N n).hom (Coinvariants.mk _ (single x (.single 1 1))) =
      single (QuotientGroup.mk' N ∘ x) (.single 1 1) := by
  rw [barComparisonComponent_mk]
  exact (BarMap.component_single (QuotientGroup.mk' N) n x 1 1).trans (by rw [map_one])

lemma tensor_comparison_free (A : Rep ℚ (G ⧸ N)) (n : ℕ) (x : Fin n → G) (a : A) :
    ((comparisonTensor N A).f n)
      (coinvariantsTensorMk A ((functor N).obj ((Rep.barComplex ℚ G).X n)) a
        (Coinvariants.mk _ (single x (.single 1 1)))) =
      coinvariantsTensorMk A ((Rep.barComplex ℚ (G ⧸ N)).X n) a
        (single (QuotientGroup.mk' N ∘ x) (.single 1 1)) := by
  change (((coinvariantsTensor ℚ (G ⧸ N)).obj A).map (barComparisonComponent N n)) _ = _
  erw [tensor_map_mk,barComparison_free]

lemma projection_single (A : Rep ℚ (G ⧸ N)) (n : ℕ) (x : Fin n → G) (a : A) :
    ((projectionChain N A).hom.f n)
      (((groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom.f n) (single x a)) =
      coinvariantsTensorMk A ((functor N).obj ((Rep.barComplex ℚ G).X n)) a
        (Coinvariants.mk _ (single x (.single 1 1))) := by
  change ((quotientProjection N A).hom.app ((Rep.barComplex ℚ G).X n)) _ = _
  rw [chainsIso_single,quotientProjection_mk]

lemma tensor_comparison_chains (A : Rep ℚ (G ⧸ N)) (n : ℕ) (x : Fin n → G) (a : A) :
    ((comparisonTensor N A).f n)
      (coinvariantsTensorMk A ((functor N).obj ((Rep.barComplex ℚ G).X n)) a
        (Coinvariants.mk _ (single x (.single 1 1)))) =
    ((groupHomology.inhomogeneousChainsIso A).hom.f n) (single (QuotientGroup.mk' N ∘ x) a) := by
  exact (tensor_comparison_free N A n x a).trans
    (chainsIso_single A n (QuotientGroup.mk' N ∘ x) a).symm

lemma comparison_single (A : Rep ℚ (G ⧸ N)) (n : ℕ) (x : Fin n → G) (a : A) :
    ((comparisonTensor N A).f n) (((projectionChain N A).hom.f n)
      (((groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom.f n)
        (single x a))) =
      ((groupHomology.inhomogeneousChainsIso A).hom.f n) (single (QuotientGroup.mk' N ∘ x) a) := by
  exact (congrArg (fun z => ((comparisonTensor N A).f n) z)
    (projection_single N A n x a)).trans (tensor_comparison_chains N A n x a)

lemma quotient_chain_compare (A : Rep ℚ (G ⧸ N)) :
    groupHomology.chainsMap (QuotientGroup.mk' N) (𝟙 (Rep.res (QuotientGroup.mk' N) A)) ≫
      (groupHomology.inhomogeneousChainsIso A).hom =
    (groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom ≫
      (projectionChain N A).hom ≫
      comparisonTensor N A := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change ((groupHomology.inhomogeneousChainsIso A).hom.f n)
      ((groupHomology.chainsMap (QuotientGroup.mk' N) (𝟙 _)).f n (single x a)) =
    ((comparisonTensor N A).f n) (((projectionChain N A).hom.f n)
      (((groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom.f n)
        (single x a)))
  exact (congrArg (fun z => ((groupHomology.inhomogeneousChainsIso A).hom.f n) z)
    (groupHomology.chainsMap_f_single (QuotientGroup.mk' N) (𝟙 _) n x a)).trans
      (comparison_single N A n x a).symm

lemma quotient_map_isIso (hN : LocallyFinite N) (A : Rep ℚ (G ⧸ N)) (n : ℕ) :
    IsIso (groupHomology.map (QuotientGroup.mk' N) (𝟙 (Rep.res (QuotientGroup.mk' N) A)) n) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  have h := congrArg F.map (quotient_chain_compare N A)
  simp only [CategoryTheory.Functor.map_comp] at h
  have : IsIso (F.map (comparisonTensor N A)) := barComparison_homology_isIso N hN A n
  have he : groupHomology.map (QuotientGroup.mk' N) (𝟙 (Rep.res (QuotientGroup.mk' N) A)) n =
      F.map (groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A)).hom ≫
        F.map (projectionChain N A).hom ≫
        F.map (comparisonTensor N A) ≫
        F.map (groupHomology.inhomogeneousChainsIso A).inv := by
    change F.map (groupHomology.chainsMap (QuotientGroup.mk' N) (𝟙 _)) = _
    calc
      _ = (F.map (groupHomology.chainsMap (QuotientGroup.mk' N) (𝟙 _)) ≫
          F.map (groupHomology.inhomogeneousChainsIso A).hom) ≫
          F.map (groupHomology.inhomogeneousChainsIso A).inv := by simp [←Functor.map_comp]
      _ = _ := by rw [h]; simp only [Category.assoc]

  rw [he]
  exact IsIso.comp_isIso'
    (F.mapIso (groupHomology.inhomogeneousChainsIso (Rep.res (QuotientGroup.mk' N) A))).isIso_hom
    (IsIso.comp_isIso' (F.mapIso (projectionChain N A)).isIso_hom
      (IsIso.comp_isIso' (barComparison_homology_isIso N hN A n)
        (F.mapIso (groupHomology.inhomogeneousChainsIso A)).isIso_inv))

end RelativeCoinvariants
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory Representation Rep
namespace RelativeCoinvariants
variable {G H : Type} [Group G] [Group H]

lemma surjective_map_isIso (f : G →* H) (hf : Function.Surjective f)
    (hK : LocallyFinite f.ker) (A : Rep ℚ H) (n : ℕ) :
    IsIso (groupHomology.map f (𝟙 (Rep.res f A)) n) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let q := QuotientGroup.mk' f.ker
  have he : e.toMonoidHom.comp q = f := rfl
  have := quotient_map_isIso f.ker hK (Rep.res e.toMonoidHom A) n
  have := equiv_map_isIso e A n
  have h : groupHomology.map f (𝟙 (Rep.res f A)) n =
      groupHomology.map q (𝟙 (Rep.res q (Rep.res e.toMonoidHom A))) n ≫
        groupHomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n := by
    rw [←groupHomology.map_comp]
    apply groupHomology.map_congr he.symm
    rfl
  rw [h]
  exact IsIso.comp_isIso' (quotient_map_isIso f.ker hK (Rep.res e.toMonoidHom A) n)
    (equiv_map_isIso e A n)

end RelativeCoinvariants
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability.RationalHomology
noncomputable section
open CategoryTheory
variable {G H K : Type} [Group G] [Group H] [Group K]

lemma surjective_isIso (f : G →* H) (hf : Function.Surjective f)
    (hK : LocallyFinite f.ker) (n : ℕ) : IsIso (map f n) :=
  RelativeCoinvariants.surjective_map_isIso f hf hK (Rep.trivial ℚ H ℚ) n

end
end SourceBurnside.Stability.RationalHomology

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory
namespace RationalBar
variable (G : Type) [Group G]
abbrev d2 : C2 G →ₗ[ℚ] C1 G := (groupHomology.d₂₁ (T G)).hom

variable {G}

lemma evaluation_zero_iff (c : Cocycles G) : evaluation c=0 ↔
    ∃b : C1 G →ₗ[ℚ] ℚ, c.val=b.comp (d2 G) := by
  constructor
  · intro he
    obtain ⟨b,hb⟩ := VectorFactor.exists_factor (d2 G) c.val (by
      intro z hz
      have h := evaluation_cycle c ⟨z,hz⟩
      rw [he] at h
      exact h.symm)
    exact ⟨b,hb.symm⟩
  · rintro ⟨b,hb⟩
    apply LinearMap.ext
    intro h
    obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance h
    rw [evaluation_cycle,hb]
    change b (d2 G z.val)=0
    rw [z.property,map_zero]

end RationalBar
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability.RationalBar
noncomputable section
open Classical CategoryTheory
variable {G H K : Type} [Group G] [Group H] [Group K]

lemma evaluation_natural (f : G →* H) (c : Cocycles H) :
    evaluation (pull f c) = (evaluation c).comp (RationalHomology.map f 2).hom := by
  ext x
  obtain ⟨z,rfl⟩ := (ModuleCat.epi_iff_surjective (groupHomology.H2π (T G))).mp inferInstance x
  rw [evaluation_cycle]
  have he := congrArg (fun u : ModuleCat.of ℚ (Z2 G) ⟶ H2 H => u z)
    (groupHomology.H2π_comp_map (A := T G) (B := T H) f (𝟙 (T G)))
  change RationalHomology.map f 2 (π G z) = π H (groupHomology.mapCycles₂ (B := T H) f (𝟙 (T G)) z) at he
  change c.val (map2 f z.val) = evaluation c (RationalHomology.map f 2 (π G z))
  rw [he,evaluation_cycle]
  rfl

lemma extend (f : G →* H) [IsIso (RationalHomology.map f 2)] (c : Cocycles G) :
    ∃d : Cocycles H, ∃b : C1 G →ₗ[ℚ] ℚ,
      c.val - (pull f d).val = b.comp (d2 G) := by
  let e : H2 H →ₗ[ℚ] ℚ := (evaluation c).comp (inv (RationalHomology.map f 2)).hom
  obtain ⟨d,hd⟩ := evaluation_surjective (G := H) e
  have hd' : evaluation (pull f d)=evaluation c := by
    rw [evaluation_natural,hd]
    ext x
    change evaluation c ((inv (RationalHomology.map f 2)) ((RationalHomology.map f 2) x)) = evaluation c x
    have he := congrArg (fun t : H2 G ⟶ H2 G => t x) (IsIso.hom_inv_id (RationalHomology.map f 2))
    change (inv (RationalHomology.map f 2)) ((RationalHomology.map f 2) x)=x at he
    rw [he]
  have hz : evaluation (c-pull f d)=0 := by
    change evaluationMap (c-pull f d)=0
    rw [map_sub]
    change evaluation c-evaluation (pull f d)=0
    rw [hd',sub_self]
  obtain ⟨b,hb⟩ := (evaluation_zero_iff _).mp hz
  exact ⟨d,b,hb⟩

lemma pull_coboundary_iff (f : G →* H) [IsIso (RationalHomology.map f 2)] (c : Cocycles H) :
    (∃b : C1 G →ₗ[ℚ] ℚ, (pull f c).val=b.comp (d2 G)) ↔
    (∃b : C1 H →ₗ[ℚ] ℚ, c.val=b.comp (d2 H)) := by
  rw [←evaluation_zero_iff,←evaluation_zero_iff,evaluation_natural]
  constructor
  · intro h
    ext x
    obtain ⟨y,rfl⟩ := (ModuleCat.epi_iff_surjective (RationalHomology.map f 2)).mp inferInstance x
    exact LinearMap.congr_fun h y
  · intro h
    rw [h,LinearMap.zero_comp]

end

noncomputable section
open Classical CategoryTheory
variable {G H : Type} [Group G] [Group H]

def inclusion (c : Cocycles G) : QGroup →* Extension c where
  toFun q := (q.toAdd-value c 1 1,1)
  map_one' := Prod.ext (by change 0-value c 1 1 = -value c 1 1; ring) rfl
  map_mul' q r := Prod.ext (by
    change q.toAdd+r.toAdd-value c 1 1 =
      (q.toAdd-value c 1 1)+(r.toAdd-value c 1 1)+value c 1 1
    ring) (one_mul 1).symm

def extension (c : Cocycles G) : RationalExtension (Extension c) G where
  inl := inclusion c
  rightHom := projection c
  inl_injective := by
    intro q r h
    have he := congrArg Prod.fst h
    change q.toAdd-value c 1 1=r.toAdd-value c 1 1 at he
    change q.toAdd=r.toAdd
    linarith
  rightHom_surjective := fun g => ⟨(0,g),rfl⟩
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨q,rfl⟩; rfl
    · intro hx
      change x.2=1 at hx
      exact ⟨Multiplicative.ofAdd (x.1+value c 1 1),Prod.ext (by change x.1+value c 1 1-value c 1 1=x.1; ring) hx.symm⟩
  central := by
    rintro x ⟨q,rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Prod.ext
    · change y.1+(q.toAdd-value c 1 1)+value c y.2 1 =
        q.toAdd-value c 1 1+y.1+value c 1 y.2
      rw [value_one_left c y.2,value_one_right c y.2]; ring
    · exact (mul_one _).trans (one_mul _).symm

lemma coboundary_value (b : C1 G →ₗ[ℚ] ℚ) (g h : G) :
    b (d2 G (Finsupp.single (g,h) 1)) = b (Finsupp.single g 1)+b (Finsupp.single h 1)-b (Finsupp.single (g*h) 1) := by
  change b (groupHomology.d₂₁ (T G) (Finsupp.single (g,h) 1)) = _
  rw [groupHomology.d₂₁_single]
  change b (Finsupp.single h 1-Finsupp.single (g*h) 1+Finsupp.single g 1)=_
  simp only [map_add,map_sub]
  ring

lemma relation_value (f : G →* H) (c : Cocycles G) (d : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : c.val-(pull f d).val=b.comp (d2 G)) (g h : G) :
    value c g h = value d (f g) (f h) + b (Finsupp.single g 1)+b (Finsupp.single h 1)-b (Finsupp.single (g*h) 1) := by
  have he := LinearMap.congr_fun hb (Finsupp.single (g,h) 1)
  change value c g h-value (pull f d) g h=b (d2 G (Finsupp.single (g,h) 1)) at he
  rw [pull_value,coboundary_value] at he
  linarith

def morphism (f : G →* H) (c : Cocycles G) (d : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : c.val-(pull f d).val=b.comp (d2 G)) : Extension c →* Extension d where
  toFun x := (x.1+b (Finsupp.single x.2 1),f x.2)
  map_one' := Prod.ext (by
    have he := relation_value f c d b hb 1 1
    simp only [map_one,one_mul] at he
    change -value c 1 1+b (Finsupp.single 1 1) = -value d 1 1
    linarith) (map_one f)
  map_mul' x y := Prod.ext (by
    have he := relation_value f c d b hb x.2 y.2
    change x.1+y.1+value c x.2 y.2+b (Finsupp.single (x.2*y.2) 1) =
      (x.1+b (Finsupp.single x.2 1))+(y.1+b (Finsupp.single y.2 1))+value d (f x.2) (f y.2)
    linarith) (map_mul f x.2 y.2)

lemma morphism_inclusion (f : G →* H) (c : Cocycles G) (d : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : c.val-(pull f d).val=b.comp (d2 G)) (q : QGroup) :
    morphism f c d b hb (inclusion c q)=inclusion d q := by
  apply Prod.ext
  · have he := relation_value f c d b hb 1 1
    simp only [map_one,one_mul] at he
    change q.toAdd-value c 1 1+b (Finsupp.single 1 1)=q.toAdd-value d 1 1
    linarith
  · exact map_one f

lemma morphism_projection (f : G →* H) (c : Cocycles G) (d : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : c.val-(pull f d).val=b.comp (d2 G)) (x : Extension c) :
    projection d (morphism f c d b hb x)=f (projection c x) := rfl

end
end SourceBurnside.Stability.RationalBar

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_FinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R ι κ : Type*} [Ring R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma embed_off_column (e : ι ↪ κ) (U : (Matrix ι ι R)ˣ) (j : κ) (hj : j ∉ Set.range e)
    (i : κ) : (embed e U).val i j = (1 : Matrix κ κ R) i j := by
  let j' : {k // k ∉ Set.range e} := ⟨j,hj⟩
  obtain ⟨i',rfl⟩ := (embeddingEquiv e).surjective i
  change (Matrix.fromBlocks U.val 0 0 (1 : Matrix {k // k ∉ Set.range e} _ R))
    ((embeddingEquiv e).symm (embeddingEquiv e i'))
    ((embeddingEquiv e).symm (embeddingEquiv e (Sum.inr j'))) =
      if embeddingEquiv e i' = embeddingEquiv e (Sum.inr j') then 1 else 0
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rcases i' with i' | i'
  · change 0 = if _ then (1 : R) else 0
    exact (ite_eq_right ((embeddingEquiv e).injective.ne (Sum.inl_ne_inr))).symm
  · change (if i' = j' then (1 : R) else 0) = if _ then 1 else 0
    congr 1
    exact propext (((embeddingEquiv e).injective.eq_iff.trans Sum.inr_injective.eq_iff).symm)

lemma embed_off_row (e : ι ↪ κ) (U : (Matrix ι ι R)ˣ) (i : κ) (hi : i ∉ Set.range e)
    (j : κ) : (embed e U).val i j = (1 : Matrix κ κ R) i j := by
  let i' : {k // k ∉ Set.range e} := ⟨i,hi⟩
  obtain ⟨j',rfl⟩ := (embeddingEquiv e).surjective j
  change (Matrix.fromBlocks U.val 0 0 (1 : Matrix {k // k ∉ Set.range e} _ R))
    ((embeddingEquiv e).symm (embeddingEquiv e (Sum.inr i')))
    ((embeddingEquiv e).symm (embeddingEquiv e j')) =
      if embeddingEquiv e (Sum.inr i') = embeddingEquiv e j' then 1 else 0
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rcases j' with j' | j'
  · change 0 = if _ then (1 : R) else 0
    exact (ite_eq_right ((embeddingEquiv e).injective.ne (Sum.inr_ne_inl))).symm
  · change (if i' = j' then (1 : R) else 0) = if _ then 1 else 0
    congr 1
    exact propext (((embeddingEquiv e).injective.eq_iff.trans Sum.inr_injective.eq_iff).symm)

end
end SourceBurnside.Stability.MatrixGenerators

end
section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Frames_ElementaryFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.MatrixK1
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

variable [Algebra (ZMod 2) R]

variable [Fintype κ] [DecidableEq κ]

omit [Algebra (ZMod 2) R] in
lemma embed_sumInl (U : (Matrix ι ι R)ˣ) :
    embed (Function.Embedding.inl (β := κ)) U = blockInclusion U := by
  apply Units.ext
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => exact embed_entry _ _ _ _
    | inr j =>
      simpa [blockInclusion_val,Matrix.fromBlocks,Matrix.one_apply] using
        embed_off_column (Function.Embedding.inl (α := ι)) U (.inr j) (by simp) (.inl i)
  | inr i =>
    cases j with
    | inl j =>
      simpa [blockInclusion_val,Matrix.fromBlocks,Matrix.one_apply] using
        embed_off_row (Function.Embedding.inl (α := ι)) U (.inr i) (by simp) (.inl j)
    | inr j =>
     simpa [blockInclusion_val,Matrix.fromBlocks,Matrix.one_apply] using
      embed_off_row (Function.Embedding.inl (α := ι)) U (.inr i) (by simp) (.inr j)

end SourceBurnside.Stability.MatrixK1

end

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

namespace SourceBurnside.Stability
open Classical
namespace LocallyFinite

lemma of_injective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (hH : LocallyFinite H) : LocallyFinite G := by
  intro s
  obtain ⟨K,hK,hfin⟩ := hH (s.image f)
  have := hfin
  refine ⟨K.comap f,fun g hg => hK _ (Finset.mem_image_of_mem f hg),?_⟩
  exact Finite.of_injective (fun g : K.comap f => (⟨f g.val,g.property⟩ : K))
    (fun a b h => Subtype.ext (hf (congrArg Subtype.val h)))

lemma commTorsion (G : Type*) [CommGroup G] (hG : IsMulTorsion G) : LocallyFinite G := by
  intro s
  let K := Subgroup.closure (s : Set G)
  have hfg : K.FG := ⟨s,rfl⟩
  have : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hfg
  refine ⟨K,fun g hg => Subgroup.subset_closure hg,?_⟩
  apply CommGroup.finite_of_fg_isMulTorsion K
  intro g
  obtain ⟨n,hn,he⟩ := (hG g.val).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,Subtype.ext he⟩

lemma vector2 (A : Type*) [AddCommGroup A] [Module (ZMod 2) A] :
    LocallyFinite (Multiplicative A) := by
  apply commTorsion
  intro a
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,?_⟩
  change (2 : ℕ) • a.toAdd = 0
  have h : ((2 : ℕ) : ZMod 2) • a.toAdd = 0 := by
    rw [show ((2 : ℕ) : ZMod 2) = 0 from rfl,zero_smul]
  exact (Nat.cast_smul_eq_nsmul (ZMod 2) (2 : ℕ) a.toAdd).symm.trans h

end LocallyFinite
end SourceBurnside.Stability

namespace SourceBurnside.Stability.UnorderedStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators MatrixK1
open scoped Pointwise

end SourceBurnside.Stability.UnorderedStabilizer

namespace SourceBurnside.Stability.Frames
open Classical Module
variable {V : Type} [LinearOrder V]

lemma labelMap_basis_congr (f g : V → V) (s : Finset V) (h : ∀v∈s,f v=g v) :
    labelMap f (basis s) = labelMap g (basis s) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    obtain ⟨c,hc,he⟩ := basis_insert_inverse v s hv
    rw [he,map_smul,map_smul,map_mul,map_mul,labelMap_vertex,labelMap_vertex,
      h v (Finset.mem_insert_self _ _),ih (fun w hw => h w (Finset.mem_insert_of_mem hw))]

lemma labelMap_basis_fixed (f : V → V) (s : Finset V) (h : ∀v∈s,f v=v) :
    labelMap f (basis s) = basis s := by
  rw [labelMap_basis_congr f id s h,labelMap_id]
  rfl

lemma labelMap_basis_swap (f : V → V) (s : Finset V) (v w : V)
    (hv : v∉s) (hw : w∉s) (hvw : v≠w) (hfv : f v=w) (hfw : f w=v)
    (hs : ∀x∈s,f x=x) :
    labelMap f (basis (insert v (insert w s))) = -basis (insert v (insert w s)) := by
  obtain ⟨c,hc,he⟩ := basis_insert_inverse v (insert w s) (by simp [hv,hvw])
  obtain ⟨d,hd,hde⟩ := basis_insert_inverse w s hw
  rw [he,hde,map_smul,map_mul,labelMap_vertex,hfv,map_smul,map_mul,labelMap_vertex,hfw,
    labelMap_basis_fixed f s hs]
  have hanti := eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap
    (R := ℚ) (Finsupp.single w (1 : ℚ)) (Finsupp.single v (1 : ℚ)))
  change vertex V w * vertex V v = -(vertex V v * vertex V w) at hanti
  simp only [mul_smul_comm,←mul_assoc,hanti,neg_mul,smul_neg]

lemma labelMap_basis_transposition (f : V → V) (s : Finset V) (v w : V)
    (hv : v ∈ s) (hw : w ∈ s) (hvw : v≠w) (hfv : f v=w) (hfw : f w=v)
    (hs : ∀x∈s, x≠v → x≠w → f x=x) : labelMap f (basis s) = -basis s := by
  let t := (s.erase v).erase w
  have he : insert v (insert w t) = s := by
    ext x
    simp only [t,Finset.mem_insert,Finset.mem_erase]
    by_cases hxv : x=v <;> by_cases hxw : x=w <;> simp_all
  rw [←he]
  apply labelMap_basis_swap f t v w
  · simp [t]
  · simp [t]
  · exact hvw
  · exact hfv
  · exact hfw
  · intro x hx
    simp only [t,Finset.mem_erase] at hx
    exact hs x hx.2.2 hx.2.1 hx.1

end SourceBurnside.Stability.Frames

namespace SourceBurnside.Stability
open Classical CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace ShapiroMap
variable {G : Type} [Group G] (S : Subgroup G)

lemma comparison_π : (BarMap.chain S.subtype).f 0 ≫ (resolution S).π.f 0 =
    (Rep.barResolution ℚ S).π.f 0 ≫ 𝟙 _ := by
  apply Rep.free_ext
  intro x
  change ((Rep.barResolution ℚ G).π.f 0).hom
    ((BarMap.component S.subtype 0).hom (single x (.single 1 1))) =
    ((Rep.barResolution ℚ S).π.f 0).hom (single x (.single 1 1))
  rw [BarMap.component_single,BarMap.augmentation_single,BarMap.augmentation_single]

def comparisonTensor (A : Rep ℚ S) :
    (Rep.barComplex ℚ S).coinvariantsTensorObj A ⟶ (resolution S).complex.coinvariantsTensorObj A :=
  (((coinvariantsTensor ℚ S).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (BarMap.chain S.subtype)

lemma comparison_homology_isIso (A : Rep ℚ S) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (comparisonTensor S A) n) := by
  let P := Rep.barResolution ℚ S
  let Q := resolution S
  let F := (Rep.coinvariantsTensor ℚ S).obj A
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 _) P Q
    (BarMap.chain S.subtype) (comparison_π S) F n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have he : HomologicalComplex.homologyMap (comparisonTensor S A) n =
      (P.isoLeftDerivedObj F n).inv ≫ (Q.isoLeftDerivedObj F n).hom := by
    rw [h]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  rw [he]
  exact inferInstanceAs (IsIso ((P.isoLeftDerivedObj F n).symm ≪≫
    Q.isoLeftDerivedObj F n).hom)

lemma chain_compare (A : Rep ℚ S) :
    groupHomology.chainsMap S.subtype (unit S A) ≫
      (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom =
    (groupHomology.inhomogeneousChainsIso A).hom ≫ comparisonTensor S A ≫
      (tensorIso S A).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro x a
  change ((groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom.f n)
      ((groupHomology.chainsMap S.subtype (unit S A)).f n (single x a)) =
    ((tensorIso S A).hom.f n)
      ((((coinvariantsTensor ℚ S).obj A).map (BarMap.component S.subtype n))
        (((groupHomology.inhomogeneousChainsIso A).hom.f n) (single x a)))
  rw [groupHomology.chainsMap_f_single,RelativeCoinvariants.chainsIso_single,
    RelativeCoinvariants.chainsIso_single,RelativeCoinvariants.tensor_map_mk,
    BarMap.component_single,tensorIso_mk,unit_apply]
  simp only [map_one]
  all_goals rfl

lemma map_isIso (A : Rep ℚ S) (n : ℕ) :
    IsIso (groupHomology.map S.subtype (unit S A) n) := by
  let F := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  have h := congrArg F.map (chain_compare S A)
  simp only [CategoryTheory.Functor.map_comp] at h
  have hComparison : IsIso (F.map (comparisonTensor S A)) := comparison_homology_isIso S A n
  have he : groupHomology.map S.subtype (unit S A) n =
      F.map (groupHomology.inhomogeneousChainsIso A).hom ≫
        F.map (comparisonTensor S A) ≫ F.map (tensorIso S A).hom ≫
        F.map (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).inv := by
    change F.map (groupHomology.chainsMap S.subtype (unit S A)) = _
    calc
      _ = (F.map (groupHomology.chainsMap S.subtype (unit S A)) ≫
          F.map (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).hom) ≫
          F.map (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A)).inv := by
            simp [←Functor.map_comp]
      _ = _ := by rw [h]; simp only [Category.assoc]

  rw [he]
  exact IsIso.comp_isIso' (F.mapIso (groupHomology.inhomogeneousChainsIso A)).isIso_hom
    (IsIso.comp_isIso' hComparison
      (IsIso.comp_isIso' (F.mapIso (tensorIso S A)).isIso_hom
        (F.mapIso (groupHomology.inhomogeneousChainsIso (Rep.ind S.subtype A))).isIso_inv))
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

attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise
end SourceBurnside.Stability

namespace SourceBurnside.Stability.FrameStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise

end SourceBurnside.Stability.FrameStabilizer

namespace SourceBurnside.Stability.MonomialTrivial
open Classical CategoryTheory Representation Rep Module
variable {G X : Type} [Group G] [MulAction G X] (x₀ : X)
variable (A : Rep.{0} ℚ G) (b : Basis X ℚ A)
variable (h0 : ∀s : MulAction.stabilizer G x₀, A.ρ s.val (b x₀) = b x₀)

variable (ht : ∀x : X, ∃g : G, g • x₀=x)
variable (hm : ∀(g : G) (x : X), ∃c : ℚˣ, A.ρ g (b x) = c.val • b (g • x))

include ht hm in
lemma seed_homology_isIso (n : ℕ) :
    IsIso (groupHomology.map (B := A) (MulAction.stabilizer G x₀).subtype (seed x₀ A b h0) n) := by
  let S := MulAction.stabilizer G x₀
  let T := Rep.trivial ℚ S ℚ
  let f := induced x₀ A b h0
  have : IsIso f := induced_isIso x₀ A b h0 ht hm
  have := ShapiroMap.map_isIso S T n
  have he : groupHomology.map S.subtype (seed x₀ A b h0) n =
      groupHomology.map S.subtype (ShapiroMap.unit S T) n ≫
        groupHomology.map (B := A) (MonoidHom.id G) f n := by
    rw [←groupHomology.map_comp]
    apply groupHomology.map_congr rfl
    apply LinearMap.ext
    intro a
    change a • b x₀ = f.hom (IndV.mk S.subtype T.ρ 1 a)
    rw [induced_mk]
    simp
  have : IsIso (groupHomology.map (B := A) (MonoidHom.id G) f n) := by
    change IsIso ((groupHomology.functor (k := ℚ) (G := G) n).map f)
    infer_instance
  rw [he]
  infer_instance

end SourceBurnside.Stability.MonomialTrivial

namespace SourceBurnside.Stability
open Classical CategoryTheory MatrixGenerators MatrixK1 Representation
lemma trivial_map_factorization {G₁ G₂ G₃ : Type} [Group G₁] [Group G₂] [Group G₃]
    (f : G₁ →* G₂) (g : G₂ →* G₃) (B : Rep ℚ G₃)
    (φ : Rep.trivial ℚ G₂ ℚ ⟶ Rep.res g B) (ψ : B ⟶ Rep.trivial ℚ G₃ ℚ)
    (h : ∀ a : ℚ, ψ.hom (φ.hom a) = a) (n : ℕ) :
    RationalHomology.map (g.comp f) n = RationalHomology.map f n ≫
      groupHomology.map g φ n ≫ groupHomology.map (MonoidHom.id G₃) ψ n := by
  have hRight := groupHomology.map_comp (A := Rep.trivial ℚ G₂ ℚ) (B := B)
    (C := Rep.trivial ℚ G₃ ℚ) g (MonoidHom.id G₃) φ ψ n
  have hBoth := groupHomology.map_comp (A := Rep.trivial ℚ G₁ ℚ)
    (B := Rep.trivial ℚ G₂ ℚ) (C := Rep.trivial ℚ G₃ ℚ) f ((MonoidHom.id G₃).comp g)
    (𝟙 (Rep.trivial ℚ G₁ ℚ)) (φ ≫ (Rep.resFunctor g).map ψ) n
  calc
    _ = groupHomology.map (A := Rep.trivial ℚ G₁ ℚ) (B := Rep.trivial ℚ G₃ ℚ)
        (((MonoidHom.id G₃).comp g).comp f)
        ((𝟙 (Rep.trivial ℚ G₁ ℚ)) ≫ (Rep.resFunctor f).map
          (φ ≫ (Rep.resFunctor g).map ψ)) n := by
      apply groupHomology.map_congr rfl
      apply LinearMap.ext
      intro a
      exact (h a).symm
    _ = _ := hBoth
    _ = _ := congrArg (fun m => RationalHomology.map f n ≫ m) hRight

end SourceBurnside.Stability

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
namespace RationalBar
variable {G H : Type} [Group G] [Group H]

lemma coboundary_of_lift (f : G →* H) (c : Cocycles H) (s : G →* Extension c)
    (hs : (projection c).comp s=f) : ∃b : C1 G →ₗ[ℚ] ℚ, (pull f c).val=b.comp (d2 G) := by
  let b : C1 G →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun g : G => -(s g).1)
  have bs (g : G) (a : ℚ) : b (Finsupp.single g a) = -a*(s g).1 := by simp [b]
  have hproj (g : G) : (s g).2=f g := DFunLike.congr_fun hs g
  refine ⟨b,?_⟩
  apply Finsupp.lhom_ext'
  intro v
  apply LinearMap.ext
  intro a
  obtain ⟨g,h⟩ := v
  have he := congrArg Prod.fst (map_mul s g h)
  change (s (g*h)).1=(s g).1+(s h).1+value c (s g).2 (s h).2 at he
  rw [hproj,hproj] at he
  have hc : (pull f c).val (Finsupp.single (g,h) a)=a*value c (f g) (f h) := by
    rw [show Finsupp.single (g,h) a = a • Finsupp.single (g,h) 1 by simp,map_smul]
    change a*value (pull f c) g h=_
    rw [pull_value]
  change (pull f c).val (Finsupp.single (g,h) a)=b (groupHomology.d₂₁ (T G) (Finsupp.single (g,h) a))
  rw [hc,groupHomology.d₂₁_single]
  change a*value c (f g) (f h)=b (Finsupp.single h a-Finsupp.single (g*h) a+Finsupp.single g a)
  simp only [map_add,map_sub,bs]
  linear_combination -a*he

lemma coboundary_value_eq (f : G →* H) (c : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : (pull f c).val=b.comp (d2 G)) (g h : G) :
    value c (f g) (f h)=b (Finsupp.single g 1)+b (Finsupp.single h 1)-b (Finsupp.single (g*h) 1) := by
  have he := LinearMap.congr_fun hb (Finsupp.single (g,h) 1)
  change value (pull f c) g h=b (d2 G (Finsupp.single (g,h) 1)) at he
  rwa [pull_value,coboundary_value] at he

def liftOfCoboundary (f : G →* H) (c : Cocycles H) (b : C1 G →ₗ[ℚ] ℚ)
    (hb : (pull f c).val=b.comp (d2 G)) : G →* Extension c where
  toFun g := (-b (Finsupp.single g 1),f g)
  map_one' := Prod.ext (by
    change -b (Finsupp.single 1 1) = -value c 1 1
    have he := coboundary_value_eq f c b hb 1 1
    simp only [map_one,one_mul] at he
    linarith) (map_one f)
  map_mul' g h := Prod.ext (by
    change -b (Finsupp.single (g*h) 1) =
      -b (Finsupp.single g 1)+-b (Finsupp.single h 1)+value c (f g) (f h)
    linarith [coboundary_value_eq f c b hb g h]) (map_mul f g h)

end RationalBar
end SourceBurnside.Stability

end

end OAI
end


