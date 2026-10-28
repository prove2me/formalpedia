-- Prove2me | Definitions.Def_OAIQ18Pg002
-- name    : OAIQ18Pg002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T15:53:40.168988+00:00
-- url     : https://prove2.me/theorems/3a4563ad-86c2-4567-a5ad-34b74eb3e054
-- title:
--   Definitions bundle OAIQ18Pg002 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 382 declarations of OpenAI's Lean: 141 definitions, 7 inductive types or structures, 4 instances and 230 theorems. The definitions and types are `OAI.SourceBurnside.FiniteTable.Cell.GeometrySignature`, `OAI.SourceBurnside.FiniteTable.Cell.GeometrySignature.geometry`, `OAI.SourceBurnside.FiniteTable.Connected`, `OAI.SourceBurnside.HeadTour.Control`, `OAI.SourceBurnside.HeadTour.FullControl`, `OAI.SourceBurnside.HeadTour.Payload.passed`, `OAI.SourceBurnside.HeadTour.Payload.rank`, `OAI.SourceBurnside.HierarchyGrowth.dimension`, `OAI.SourceBurnside.HierarchyGrowth.exponent`, `OAI.SourceBurnside.HierarchyGrowth.height`, `OAI.SourceBurnside.Kernel.above`, `OAI.SourceBurnside.Kernel.awayCoordinates`, `OAI.SourceBurnside.Kernel.bigBasisUnits`, `OAI.SourceBurnside.Kernel.blockUnits`, `OAI.SourceBurnside.Kernel.blockUnitsHom`, `OAI.SourceBurnside.Kernel.coefficientConj`, `OAI.SourceBurnside.Kernel.coordinateEquiv`, `OAI.SourceBurnside.Kernel.coordinateIndex`, `OAI.SourceBurnside.Kernel.copyMatrixHom`, `OAI.SourceBurnside.Kernel.copyUnitsHom`, `OAI.SourceBurnside.Kernel.cyclicShift`, `OAI.SourceBurnside.Kernel.flattenRing`, `OAI.SourceBurnside.Kernel.innerHeight`, `OAI.SourceBurnside.Kernel.layer`, `OAI.SourceBurnside.Kernel.numericUnits`, `OAI.SourceBurnside.Kernel.padUnitsHom`, `OAI.SourceBurnside.Kernel.pascalMatrix`, `OAI.SourceBurnside.Kernel.permutationUnits`, `OAI.SourceBurnside.Kernel.rowFixed`, `OAI.SourceBurnside.Kernel.scalarEval`, `OAI.SourceBurnside.Kernel.scalarRingHom`, `OAI.SourceBurnside.Kernel.spareCoordinate`, `OAI.SourceBurnside.Kernel.swapUnits`, `OAI.SourceBurnside.Kernel.truncatedShift`, `OAI.SourceBurnside.MatrixNilKernel`, `OAI.SourceBurnside.MatrixTests.instAlgebraPolynomial_solutions`, `OAI.SourceBurnside.MatrixTests.polynomialMatrix`, `OAI.SourceBurnside.MatrixTests.tensor`, `OAI.SourceBurnside.Stability.BarMap.chain`, `OAI.SourceBurnside.Stability.BarMap.component` and 108 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: `PeriodicGroups_Algebra_HierarchyGrowth`, `PeriodicGroups_Algebra_MatrixTests`, `PeriodicGroups_Frames_AcyclicFrameEdge`, `PeriodicGroups_Frames_ElementaryFrames`, `PeriodicGroups_Frames_ExteriorComplex`, `PeriodicGroups_Homology_FiniteExtensions`, `PeriodicGroups_Homology_RelativeHomology`, `PeriodicGroups_Matrices_ElementaryGenerators`, `PeriodicGroups_Presentation_FinitePresentation`, `PeriodicGroups_Presentation_MatrixStabilizers`, `PeriodicGroups_Presentation_SmallFaithful`, `PeriodicGroups_Presentation_SmallSwapActions`, `PeriodicGroups_Rules_ConnectedWords`, `PeriodicGroups_Rules_GeometricRelations`, `PeriodicGroups_Rules_HeadTour`, `PeriodicGroups_Rules_LocalSyntax`, `PeriodicGroups_Rules_PrefixRewriting`, `PeriodicGroups_Rules_WordRewriting`, `PeriodicGroups_Steinberg_BandFactorization`, `PeriodicGroups_Steinberg_BlockEmbeddings`, `PeriodicGroups_Steinberg_CoefficientQuotients`, `PeriodicGroups_Steinberg_KernelRelations`, `PeriodicGroups_Steinberg_MatrixUnits`, `PeriodicGroups_Steinberg_MonomialPresentation`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ18Pg007` and `OAIQ18Pg008`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_LocalSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.LocalSyntax

section Chains
variable {α : Type*} {R : α → α → Prop}

lemma chain_change_head (s : List α) (a b : α) (h : ∀ c, R a c ↔ R b c) :
    List.IsChain R (a :: s) ↔ List.IsChain R (b :: s) := by
  cases s with
  | nil => simp
  | cons c s => simp only [List.isChain_cons_cons, h c]

lemma chain_change_last (p : List α) (a b : α) (h : ∀ c, R c a ↔ R c b) :
    List.IsChain R (p ++ [a]) ↔ List.IsChain R (p ++ [b]) := by
  induction p with
  | nil => simp
  | cons c p ih =>
    cases p with
    | nil => simpa only [List.cons_append, List.nil_append, List.isChain_pair] using h c
    | cons d p =>
      simp only [List.cons_append, List.isChain_cons_cons] at ih ⊢
      exact and_congr Iff.rfl ih

lemma chain_replace_one (p s : List α) (a b : α)
    (hl : ∀ c, R c a ↔ R c b) (hr : ∀ c, R a c ↔ R b c) :
    List.IsChain R (p ++ a :: s) ↔ List.IsChain R (p ++ b :: s) := by
  exact List.isChain_split.trans ((and_congr (chain_change_last p a b hl)
    (chain_change_head s a b hr)).trans List.isChain_split.symm)

lemma chain_replace_two (p s : List α) (a b a' b' : α)
    (hl : ∀ c, R c a ↔ R c a') (hr : ∀ c, R b c ↔ R b' c)
    (hm : R a b ↔ R a' b') :
    List.IsChain R (p ++ a :: b :: s) ↔ List.IsChain R (p ++ a' :: b' :: s) := by
  rw [List.isChain_append_cons_cons, List.isChain_append_cons_cons,
    chain_change_last p a a' hl, chain_change_head s b b' hr, hm]

end Chains

end SourceBurnside.LocalSyntax

end

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
open Classical

abbrev QGroup := Multiplicative ℚ

structure RationalExtension (E G : Type*) [Group E] [Group G]
    extends GroupExtension QGroup E G where
  central : inl.range ≤ Subgroup.center E

namespace RationalExtension
variable {E G : Type*} [Group E] [Group G] (S : RationalExtension E G)

lemma inl_central (q : QGroup) : S.inl q ∈ Subgroup.center E :=
  S.central ⟨q, rfl⟩

def kernelHom : QGroup →* S.rightHom.ker where
  toFun q := ⟨S.inl q, S.toGroupExtension.rightHom_inl q⟩
  map_one' := Subtype.ext (map_one S.inl)
  map_mul' q r := Subtype.ext (map_mul S.inl q r)

def kernelEquiv : QGroup ≃* S.rightHom.ker :=
  MulEquiv.ofBijective S.kernelHom
    ⟨fun q r h => S.inl_injective (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      have : x ∈ S.inl.range := S.range_inl_eq_ker_rightHom ▸ hx
      obtain ⟨q, hq⟩ := this
      exact ⟨q, Subtype.ext hq⟩⟩

@[simp] lemma kernelEquiv_val (q : QGroup) : (S.kernelEquiv q).val = S.inl q := rfl

section Finite
variable [Finite G]

def finiteRetraction : E →* QGroup :=
  haveI : S.rightHom.ker.FiniteIndex := Subgroup.finiteIndex_ker S.rightHom
  let divide : QGroup →* QGroup :=
    { toFun := fun q => Multiplicative.ofAdd (q.toAdd / (S.rightHom.ker.index : ℚ))
      map_one' := by change (0 : ℚ) / _ = 0; simp
      map_mul' := fun q r => by
        change (q.toAdd + r.toAdd) / _ = q.toAdd / _ + r.toAdd / _
        exact add_div _ _ _ }
  divide.comp (MonoidHom.transfer S.kernelEquiv.symm.toMonoidHom)

@[simp] theorem finiteRetraction_inl (q : QGroup) :
    S.finiteRetraction (S.inl q) = q := by
  let : S.rightHom.ker.FiniteIndex := Subgroup.finiteIndex_ker S.rightHom
  have hi : (S.rightHom.ker.index : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hp (k : ℕ) (x : E) (_ : x⁻¹ * S.inl q ^ k * x ∈ S.rightHom.ker) :
      x⁻¹ * S.inl q ^ k * x = S.inl q ^ k := by
    have h := (Subgroup.center E).pow_mem (S.inl_central q) k
    rw [← h.comm]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  unfold finiteRetraction
  dsimp only [MonoidHom.comp_apply]
  rw [MonoidHom.transfer_eq_pow _ _ hp]
  have he : (⟨S.inl q ^ S.rightHom.ker.index,
      MonoidHom.transfer_eq_pow_aux (S.inl q) hp⟩ : S.rightHom.ker) =
      S.kernelEquiv (q ^ S.rightHom.ker.index) := by
    apply Subtype.ext
    exact (map_pow S.inl q _).symm
  rw [he]
  simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  change ((S.rightHom.ker.index : ℚ) * q.toAdd) / (S.rightHom.ker.index : ℚ) = q.toAdd
  exact mul_div_cancel_left₀ _ hi

def finiteComplementMap : S.finiteRetraction.ker →* G :=
  S.rightHom.comp S.finiteRetraction.ker.subtype

lemma finiteComplementMap_bijective : Function.Bijective S.finiteComplementMap := by
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    rintro ⟨x, hx⟩ h
    have hg : S.rightHom x = 1 := h
    have hr : x ∈ S.inl.range := S.range_inl_eq_ker_rightHom ▸ hg
    obtain ⟨q, rfl⟩ := hr
    have hq : q = 1 := (S.finiteRetraction_inl q).symm.trans hx
    apply Subtype.ext
    simp [hq]
  · intro g
    obtain ⟨x, hx⟩ := S.rightHom_surjective g
    refine ⟨⟨x * (S.inl (S.finiteRetraction x))⁻¹, ?_⟩, ?_⟩
    · change S.finiteRetraction (x * (S.inl (S.finiteRetraction x))⁻¹) = 1
      simp only [map_mul, map_inv, finiteRetraction_inl, mul_inv_cancel]
    · change S.rightHom (x * (S.inl (S.finiteRetraction x))⁻¹) = g
      simp only [map_mul, map_inv, S.toGroupExtension.rightHom_inl, inv_one, mul_one, hx]

def finiteSplitting : S.toGroupExtension.Splitting where
  toMonoidHom := S.finiteRetraction.ker.subtype.comp
    (MulEquiv.ofBijective S.finiteComplementMap S.finiteComplementMap_bijective).symm.toMonoidHom
  rightInverse_rightHom g :=
    (MulEquiv.ofBijective S.finiteComplementMap S.finiteComplementMap_bijective).apply_symm_apply g

end Finite

def restrict (H : Subgroup G) : RationalExtension (H.comap S.rightHom) H where
  inl :=
    { toFun := fun q => ⟨S.inl q, by
        change S.rightHom (S.inl q) ∈ H
        rw [S.toGroupExtension.rightHom_inl]
        exact H.one_mem⟩
      map_one' := Subtype.ext (map_one S.inl)
      map_mul' := fun q r => Subtype.ext (map_mul S.inl q r) }
  rightHom :=
    { toFun := fun x => ⟨S.rightHom x, x.property⟩
      map_one' := Subtype.ext (map_one S.rightHom)
      map_mul' := fun q r => Subtype.ext (map_mul S.rightHom (q : E) (r : E)) }
  inl_injective := fun q r h => S.inl_injective (congrArg Subtype.val h)
  rightHom_surjective := by
    rintro ⟨g, hg⟩
    obtain ⟨x, hx⟩ := S.rightHom_surjective g
    exact ⟨⟨x, by change S.rightHom x ∈ H; rwa [hx]⟩, Subtype.ext hx⟩
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact Subtype.ext (S.toGroupExtension.rightHom_inl q)
    · intro hx
      have h : x.val ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom]
        exact congrArg Subtype.val hx
      obtain ⟨q, hq⟩ := h
      exact ⟨q, Subtype.ext hq⟩
  central := by
    rintro x ⟨q, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext ((S.inl_central q).comm y.val).eq.symm

def liftFinite (H : Subgroup G) [Finite H] : H →* E :=
  (H.comap S.rightHom).subtype.comp (S.restrict H).finiteSplitting.toMonoidHom

@[simp] lemma rightHom_liftFinite (H : Subgroup G) [Finite H] (g : H) :
    S.rightHom (S.liftFinite H g) = g.val :=
  congrArg Subtype.val ((S.restrict H).finiteSplitting.rightInverse_rightHom g)

def LocallyFinite (G : Type*) [Group G] : Prop :=
  ∀ s : Finset G, ∃ H : Subgroup G, (∀ g ∈ s, g ∈ H) ∧ Finite H

end RationalExtension
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability.CentralPushout
noncomputable section
open Classical
variable {P G : Type} [Group P] [Group G]

def graphHom (p : P →* G) (φ : p.ker →* QGroup) : p.ker →* P×QGroup where
  toFun j := (j.val,(φ j)⁻¹)
  map_one' := Prod.ext rfl (by simp)
  map_mul' j k := Prod.ext rfl (by simp [mul_comm])

def relation (p : P →* G) (_hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) : Subgroup (P×QGroup) :=
  (graphHom p φ).range

lemma relation_central (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) :
    relation p hc φ ≤ Subgroup.center (P×QGroup) := by
  rintro x ⟨j,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  apply Prod.ext
  · exact ((hc j.property).comm y.1).eq.symm
  · exact mul_comm _ _

instance relation_normal (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) :
    (relation p hc φ).Normal where
  conj_mem x hx y := by
    have he := ((relation_central p hc φ hx).comm y).eq
    rw [←he,mul_assoc,mul_inv_cancel,mul_one]
    exact hx

def Extension (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) :=
  (P×QGroup) ⧸ relation p hc φ
instance extensionGroup (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup) :
    Group (Extension p hc φ) := inferInstanceAs (Group ((P×QGroup) ⧸ relation p hc φ))

variable (p : P →* G) (hc : p.ker ≤ Subgroup.center P) (φ : p.ker →* QGroup)

def canonical : P →* Extension p hc φ := (QuotientGroup.mk' (relation p hc φ)).comp ((MonoidHom.id P).prod 1)
def inclusion : QGroup →* Extension p hc φ := (QuotientGroup.mk' (relation p hc φ)).comp ((1 : QGroup →* P).prod (MonoidHom.id QGroup))

def projection : Extension p hc φ →* G := QuotientGroup.lift (relation p hc φ)
  (p.comp (MonoidHom.fst P QGroup)) (by
    rintro x ⟨j,rfl⟩
    exact j.property)

lemma projection_inclusion (q : QGroup) : projection p hc φ (inclusion p hc φ q)=1 := map_one p

lemma canonical_kernel (j : p.ker) : canonical p hc φ j.val=inclusion p hc φ (φ j) := by
  apply (QuotientGroup.mk'_eq_mk' (relation p hc φ)).mpr
  refine ⟨graphHom p φ j⁻¹,⟨j⁻¹,rfl⟩,?_⟩
  apply Prod.ext
  · exact mul_inv_cancel _
  · change 1*(φ j⁻¹)⁻¹=φ j
    rw [map_inv,inv_inv,one_mul]

lemma mk_pair (s : P) (q : QGroup) : QuotientGroup.mk' (relation p hc φ) (s,q)=canonical p hc φ s*inclusion p hc φ q := by
  change _=QuotientGroup.mk' _ (s,1)*QuotientGroup.mk' _ (1,q)
  erw [←map_mul]
  congr 1
  exact Prod.ext (mul_one _).symm (one_mul _).symm

lemma inclusion_injective : Function.Injective (inclusion p hc φ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro q hq
  change inclusion p hc φ q=1 at hq
  have h : (1,q)∈relation p hc φ := (QuotientGroup.eq_one_iff (1,q)).mp hq
  obtain ⟨j,hj⟩ := h
  have hj1 : j=1 := Subtype.ext (congrArg Prod.fst hj)
  have he := congrArg Prod.snd hj
  change (φ j)⁻¹=q at he
  change q=1
  simpa only [hj1,map_one,inv_one] using he.symm

lemma exactness : (inclusion p hc φ).range=(projection p hc φ).ker := by
  ext x
  constructor
  · rintro ⟨q,rfl⟩
    exact projection_inclusion p hc φ q
  · intro hx
    obtain ⟨⟨s,q⟩,rfl⟩ := QuotientGroup.mk'_surjective (relation p hc φ) x
    have hs : s∈p.ker := hx
    refine ⟨φ ⟨s,hs⟩*q,?_⟩
    rw [map_mul,←canonical_kernel p hc φ ⟨s,hs⟩,mk_pair]

lemma inclusion_central : (inclusion p hc φ).range ≤ Subgroup.center (Extension p hc φ) := by
  rintro x ⟨q,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  obtain ⟨⟨s,r⟩,rfl⟩ := QuotientGroup.mk'_surjective (relation p hc φ) y
  change QuotientGroup.mk' _ (s,r)*QuotientGroup.mk' _ (1,q)=QuotientGroup.mk' _ (1,q)*QuotientGroup.mk' _ (s,r)
  erw [←map_mul,←map_mul]
  congr 1
  exact Prod.ext ((mul_one _).trans (one_mul _).symm) (mul_comm _ _)

def extension (hp : Function.Surjective p) : RationalExtension (Extension p hc φ) G where
  inl := inclusion p hc φ
  rightHom := projection p hc φ
  inl_injective := inclusion_injective p hc φ
  rightHom_surjective := by
    intro g
    obtain ⟨s,rfl⟩ := hp g
    exact ⟨canonical p hc φ s,rfl⟩
  range_inl_eq_ker_rightHom := exactness p hc φ
  central := inclusion_central p hc φ

end
end SourceBurnside.Stability.CentralPushout

namespace SourceBurnside.Stability
noncomputable section
open Classical Representation

variable {G V W : Type*} [Group G] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W]

abbrev LocallyFinite := RationalExtension.LocallyFinite

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

namespace BarMap
variable {G H : Type} [Group G] [Group H] (q : G →* H)

def component (n : ℕ) : Rep.free ℚ G (Fin n → G) ⟶
    Rep.res q (Rep.free ℚ H (Fin n → H)) :=
  Rep.freeLift ℚ G _ fun x => single (q ∘ x) (.single 1 1)

lemma component_single (n : ℕ) (x : Fin n → G) (g : G) (r : ℚ) :
    (component q n).hom (single x (.single g r)) = single (q ∘ x) (.single (q g) r) := by
  change Representation.freeLift ((Representation.free ℚ H (Fin n → H)).comp q)
    (fun x : Fin n → G => single (q ∘ x) (.single 1 (1 : ℚ)))
    (single x (.single g r)) = _
  rw [Representation.freeLift_single_single]
  change r • Representation.free ℚ H (Fin n → H) (q g) (single (q ∘ x) (.single 1 1)) = _
  simp only [Representation.free_single_single, mul_one, smul_single, MonoidAlgebra.smul_single, smul_eq_mul]
def chain : Rep.barComplex ℚ G ⟶
    ((Rep.resFunctor q).mapHomologicalComplex _).obj (Rep.barComplex ℚ H) where
  f n := component q n
  comm' i j h := by
    change j + 1 = i at h
    subst i
    rw [CategoryTheory.Functor.mapHomologicalComplex_obj_d, Rep.barComplex.d_def, Rep.barComplex.d_def]
    change component q (j+1) ≫ Rep.resMap q (Rep.barComplex.d ℚ H j) =
      Rep.barComplex.d ℚ G j ≫ component q j
    apply Rep.free_ext
    intro x
    change (Rep.barComplex.d ℚ H j).hom ((component q (j+1)).hom (single x (.single 1 1))) =
      (component q j).hom ((Rep.barComplex.d ℚ G j).hom (single x (.single 1 1)))
    simp only [← Representation.IntertwiningMap.toLinearMap_apply]
    have c (n : ℕ) (y : Fin n → G) (g : G) (r : ℚ) :
        (component q n).hom.toLinearMap (single y (.single g r)) =
          single (q ∘ y) (.single (q g) r) := component_single q n y g r
    have dG := Rep.barComplex.d_single (k := ℚ) j x
    have dH := Rep.barComplex.d_single (k := ℚ) j (q ∘ x)
    change (Rep.barComplex.d ℚ G j).hom.toLinearMap _ = _ at dG
    change (Rep.barComplex.d ℚ H j).hom.toLinearMap _ = _ at dH
    rw [c, map_one, dH, dG]
    simp only [map_add, map_sum, c, map_one]

    congr 1
    apply Finset.sum_congr rfl
    intro t _
    congr 2
    exact (Fin.comp_contractNth (· * ·) (· * ·) (fun a b => map_mul q a b) t x).symm
lemma diagonal_inv_single (m : ℕ) (f : Fin m → G) (g : G) (r : ℚ) :
    (Rep.diagonalSuccIsoFree ℚ G m).inv.hom (single f (.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  open MonoidalCategory in
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Rep.Hom.hom (leftRegularTensorTrivialIsoFree ℚ G (Fin m → G)).inv)
      (single f (.single g r)) = .single g 1 ⊗ₜ[ℚ] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [Action.tensorObj_V, tensor_V, tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := ℚ)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : ℚ) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := ℚ)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by
      simp only [one_mul]
      congr 1
      exact Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g f)
lemma augmentation_single (x : Fin 0 → G) (g : G) (r : ℚ) :
    ((Rep.barResolution ℚ G).π.f 0).hom (single x (.single g r)) = r := by
  change (Rep.standardComplex.ε ℚ G).hom
    ((Rep.diagonalSuccIsoFree ℚ G 0).inv.hom (single x (.single g r))) = r
  rw [diagonal_inv_single]
  simp [Rep.standardComplex.ε]

end BarMap
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability
noncomputable section
open Classical CategoryTheory Representation Rep
namespace RelativeCoinvariants
variable {G H : Type} [Group G] [Group H]

lemma equiv_map_isIso (e : G ≃* H) (A : Rep ℚ H) (n : ℕ) :
    IsIso (groupHomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n) := by
  let i := groupHomology.mapIso (A := Rep.res e.toMonoidHom A) (B := A) e
    (LinearEquiv.refl ℚ A) (fun g => by simp) n
  have he : groupHomology.map e.toMonoidHom (𝟙 (Rep.res e.toMonoidHom A)) n = i.hom := by
    apply groupHomology.map_congr rfl
    rfl
  rw [he]
  infer_instance

end RelativeCoinvariants
end
end SourceBurnside.Stability

namespace SourceBurnside.Stability.RationalHomology
noncomputable section
open CategoryTheory
variable {G H K : Type} [Group G] [Group H] [Group K]

abbrev map (f : G →* H) (n : ℕ) :
    groupHomology (Rep.trivial ℚ G ℚ) n ⟶ groupHomology (Rep.trivial ℚ H ℚ) n :=
  groupHomology.map (A := Rep.trivial ℚ G ℚ) (B := Rep.trivial ℚ H ℚ) f (𝟙 _) n

@[simp] lemma map_id (n : ℕ) : map (MonoidHom.id G) n = 𝟙 _ := groupHomology.map_id (A := Rep.trivial ℚ G ℚ) n

lemma map_comp (f : G →* H) (g : H →* K) (n : ℕ) :
    map (g.comp f) n = map f n ≫ map g n :=
  groupHomology.map_comp (A := Rep.trivial ℚ G ℚ) (B := Rep.trivial ℚ H ℚ) (C := Rep.trivial ℚ K ℚ)
    f g (𝟙 _) (𝟙 _) n

lemma equiv_isIso (e : G ≃* H) (n : ℕ) : IsIso (map e.toMonoidHom n) :=
  RelativeCoinvariants.equiv_map_isIso e (Rep.trivial ℚ H ℚ) n

end
end SourceBurnside.Stability.RationalHomology

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_HeadTour
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.HeadTour
open scoped BigOperators

inductive Control (N : ℕ)
  | acquisition | readLeft (p : Fin N) | readRight (p : Fin N)
  | beforeGate | afterGate | undoLeft (p : Fin N) | undoRight (p : Fin N) | finish
  deriving DecidableEq, Fintype

variable {N : ℕ}

namespace Payload

def passed : Control N → Prop
  | .afterGate | .undoLeft _ | .undoRight _ | .finish => True
  | _ => False

def rank : Control N → ℕ
  | .acquisition => 0
  | .readLeft p => 1 + (N-1-p.val)
  | .readRight p => 1 + N + p.val
  | .beforeGate => 1 + 2*N
  | .afterGate => 2 + 2*N
  | .undoLeft p => 3 + 2*N + (N-1-p.val)
  | .undoRight p => 3 + 3*N + p.val
  | .finish => 3 + 4*N

end Payload

inductive FullControl (m N : ℕ)
  | clause (j : Fin m) (c : Control N)
  | success
  deriving DecidableEq, Fintype

end SourceBurnside.HeadTour

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_ConnectedWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax

def Connected {N : ℕ} (cut : Fin N → Prop) (i j : Fin N) : Prop :=
  ∀ k, min i.val j.val ≤ k.val → k.val < max i.val j.val → ¬cut k

instance instDecidableConnectedOfDecidablePredFin {N : ℕ} (cut : Fin N → Prop) [DecidablePred cut] (i j : Fin N) :
    Decidable (Connected cut i j) := by unfold Connected; infer_instance

namespace Connected
variable {N : ℕ} {cut cut' : Fin N → Prop} {i j k a b : Fin N}
lemma refl (cut : Fin N → Prop) (i : Fin N) : Connected cut i i := by
  intro k hk hk'; omega
lemma symm (h : Connected cut i j) : Connected cut j i := by
  simpa only [Connected,min_comm,max_comm] using h
lemma trans (h : Connected cut i j) (h' : Connected cut j k) : Connected cut i k := by
  intro t ht ht'
  by_cases hh : min i.val j.val ≤ t.val ∧ t.val < max i.val j.val
  · exact h t hh.1 hh.2
  · exact h' t (by omega) (by omega)
lemma subinterval (h : Connected cut i j)
    (ha : min i.val j.val ≤ a.val) (ha' : a.val ≤ max i.val j.val)
    (hb : min i.val j.val ≤ b.val) (hb' : b.val ≤ max i.val j.val) :
    Connected cut a b := by
  intro t ht ht'
  exact h t (by omega) (by omega)
lemma adjacent_iff (hab : a.val+1=b.val) : Connected cut a b ↔ ¬cut a := by
  constructor
  · intro h; exact h a (by omega) (by omega)
  · intro h t ht ht'
    have he : t=a := Fin.ext (by omega)
    simpa only [he] using h
lemma right_barrier (h : Connected cut i j) (hj : i.val < j.val) : ¬cut i :=
  h i (by omega) (by omega)

end Connected

end SourceBurnside.FiniteTable
end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_WordRewriting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax
variable {q : ℕ}
  [NeZero q]
  {d : ℕ}

namespace Cell
abbrev GeometrySignature (q : ℕ) := Fin 11 × ((Fin q) ⊕ ((Fin 6 × Fin q) ⊕ Unit))

def GeometrySignature.geometry (x : GeometrySignature q) : ℕ :=
  (q+2)*x.1.val + x.2.elim Fin.val (Sum.elim (fun _ => q) (fun _ => q+1))

end Cell

lemma finRange_head : (List.finRange q).head? = some (0 : Fin q) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simpa using NeZero.pos q)]
  simp only [List.getElem_finRange]
  rfl

lemma finRange_last : (List.finRange q).getLast? = some ⟨q-1, Nat.sub_lt (NeZero.pos q) (by decide)⟩ := by
  rw [List.getLast?_eq_getElem?]
  simp only [List.length_finRange]
  rw [List.getElem?_eq_getElem (by simpa using Nat.sub_lt (NeZero.pos q) (show 0<1 by omega))]
  simp only [List.getElem_finRange]
  rfl

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_PrefixRewriting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable

open LocalSyntax
variable {q d : ℕ}
  [NeZero q]

omit [NeZero q] in
lemma coreRange_cons (p : Fin q) : (List.finRange q).drop p.val=
    p::(List.finRange q).drop (p.val+1) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp

end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_GeometricRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable

section
open LocalSyntax
variable {q d : ℕ}
  [NeZero q]

lemma rank_list_bound {l : List ℕ} (h : l.Pairwise (· < ·))
    (hb : ∀n∈l.tail,n<10) : l.length≤10 := by
  cases l with
  | nil => simp
  | cons a l =>
    cases l with
    | nil => simp
    | cons b l =>
      have ha : a<10 := lt_trans ((List.pairwise_cons.mp h).1 b (by simp)) (hb b (by simp))
      have hall : ∀n∈a::b::l,n<10 := by
        intro n hn
        rcases List.mem_cons.mp hn with rfl|hn
        · exact ha
        · exact hb n hn
      have hc : (a::b::l).toFinset ⊆ Finset.range 10 := by
        intro n hn
        exact Finset.mem_range.mpr (hall n (List.mem_toFinset.mp hn))
      have he := Finset.card_le_card hc
      rw [List.toFinset_card_of_nodup h.nodup,Finset.card_range] at he
      exact he

end

open LocalSyntax
end SourceBurnside.FiniteTable

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
namespace SourceBurnside.HierarchyGrowth
open scoped BigOperators

def height (H D n : ℕ) : ℕ := H * D ^ n

def dimension (d k : ℕ) (s : ℕ → ℕ) : ℕ → ℕ
  | 0 => d
  | n+1 => k * s n ^ k * dimension d k s n

def exponent (H D d k c n : ℕ) : ℕ :=
  d + k*n + k*c * ∑ i ∈ Finset.range n, height H D i

end SourceBurnside.HierarchyGrowth

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_MatrixTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {K A : Type*} [CommRing K] [Ring A] [Algebra K A]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def tensor (X : Matrix ι ι K) (a : A) : Matrix ι ι A := fun i j => X i j • a
omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma tensor_zero (X : Matrix ι ι K) : tensor X (0:A)=0 := by ext;simp [tensor]
omit [Fintype ι] in
@[simp] lemma tensor_one : tensor (1:Matrix ι ι K) (1:A)=1 := by
  ext i j
  by_cases h : i=j <;> simp [tensor,Matrix.one_apply,h]
end
end SourceBurnside.MatrixTests

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Frames_ExteriorComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.Frames
noncomputable section
open Classical Module

variable (V : Type*)
abbrev Labels := V →₀ ℚ
abbrev Ambient := ExteriorAlgebra ℚ (Labels V)

def vertex (v : V) : Ambient V := ExteriorAlgebra.ι ℚ (Finsupp.single v 1)

def augmentation : Labels V →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun _ : V => (1 : ℚ))

def boundary : Ambient V →ₗ[ℚ] Ambient V :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℚ (Labels V))) (augmentation V)

variable {V}
@[simp] lemma augmentation_single (v : V) : augmentation V (Finsupp.single v 1) = 1 := by
  simp [augmentation]

@[simp] lemma boundary_vertex (v : V) : boundary V (vertex V v) = 1 := by
  simp [boundary, vertex]

@[simp] lemma boundary_one : boundary V (1 : Ambient V) = 0 := by
  simp [boundary]

@[simp] lemma boundary_boundary (x : Ambient V) : boundary V (boundary V x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft (augmentation V) x

lemma boundary_cone (v : V) (x : Ambient V) :
    boundary V (vertex V v * x) = x - vertex V v * boundary V x := by
  simpa [boundary, vertex, augmentation] using
    (CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm ℚ (Labels V)))
      (augmentation V) (Finsupp.single v 1) x)

variable [LinearOrder V]

def basis : Basis (Finset V) ℚ (Ambient V) := (Finsupp.basisSingleOne : Basis V ℚ (Labels V)).ExteriorAlgebra

@[simp] lemma basis_empty : basis (V := V) ∅ = 1 := by
  rw [basis, ExteriorAlgebra.basis_apply_ofCard (s_card := Finset.card_empty)]
  simp [ExteriorAlgebra.ιMulti_family]

@[simp] lemma basis_singleton (v : V) : basis (V := V) {v} = vertex V v := by
  rw [basis, ExteriorAlgebra.basis_apply_ofCard (s_card := Finset.card_singleton v)]
  have he : (Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofCard (Finset.card_singleton v))) 0 = v := by
    apply Finset.mem_singleton.mp
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (Set.powersetCard.ofCard (Finset.card_singleton v)) _).mp ⟨0, rfl⟩
  simp [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply, vertex, he]

lemma vertex_mul_basis (v : V) (s : Finset V) (hv : v ∉ s) :
    ∃ c : ℚ, c ≠ 0 ∧ vertex V v * basis s = c • basis (insert v s) := by
  let t := Set.powersetCard.ofCard (Finset.card_singleton v)
  let u := Set.powersetCard.ofCard (rfl : s.card = s.card)
  have hd : Disjoint t.val u.val := by simpa [t, u] using Finset.disjoint_singleton_left.mpr hv
  have he := ExteriorAlgebra.basis_mul_of_disjoint
    (Finsupp.basisSingleOne : Basis V ℚ (Labels V)) t u hd
  have hu : (Set.powersetCard.disjUnion hd : Finset V) = insert v s := by
    ext x
    simp [Set.powersetCard.coe_disjUnion, t, u]
  change basis {v} * basis s = _ at he
  rw [basis_singleton, hu] at he
  refine ⟨((Set.powersetCard.permOfDisjoint hd).sign : ℤ), ?_, ?_⟩
  · exact_mod_cast (Set.powersetCard.permOfDisjoint hd).sign.ne_zero
  · simpa only [basis, Units.smul_def, Int.cast_smul_eq_zsmul] using he

variable {F W : Type*} [DivisionRing F] [AddCommGroup W] [Module F W]

def chains (ρ : V → W) (s : Set V) (k : ℕ) : Submodule ℚ (Ambient V) :=
  Submodule.span ℚ {x | ∃ t : Finset V, (t : Set V) ⊆ s ∧ t.card = k ∧
    LinearIndepOn F ρ (t : Set V) ∧ x = basis t}

lemma basis_mem_chains (ρ : V → W) {s : Set V} (t : Finset V) (ht : (t : Set V) ⊆ s)
    (hi : LinearIndepOn F ρ (t : Set V)) : basis t ∈ chains (F := F) ρ s t.card :=
  Submodule.subset_span ⟨t, ht, rfl, hi, rfl⟩

lemma chains_mono (ρ : V → W) {s t : Set V} (hst : s ⊆ t) (k : ℕ) :
    chains (F := F) ρ s k ≤ chains (F := F) ρ t k := by
  apply Submodule.span_mono
  rintro x ⟨u, hu, hc, hi, rfl⟩
  exact ⟨u, hu.trans hst, hc, hi, rfl⟩

lemma cone_mem_chains (ρ : V → W) {s : Set V} (v : V)
    (hv : ρ v ∉ Submodule.span F (ρ '' s)) {k : ℕ} {x : Ambient V}
    (hx : x ∈ chains (F := F) ρ s k) :
    vertex V v * x ∈ chains (F := F) ρ (insert v s) (k+1) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl, hi, rfl⟩ := hx
    have hn : v ∉ t := fun h => hv (Submodule.subset_span ⟨v, ht h, rfl⟩)
    obtain ⟨c, _, he⟩ := vertex_mul_basis v t hn
    rw [he]
    apply Submodule.smul_mem
    have hi' : LinearIndepOn F ρ (insert v (t : Set V)) :=
      hi.insert (fun h => hv (Submodule.span_mono (Set.image_mono ht) h))
    have hc : (insert v t).card = t.card+1 := Finset.card_insert_of_notMem hn
    rw [← hc]
    exact basis_mem_chains ρ _ (by simp only [Finset.coe_insert]; exact Set.insert_subset_insert ht)
      (by simpa only [Finset.coe_insert] using hi')
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [mul_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [mul_smul_comm] using Submodule.smul_mem _ c ih

lemma boundary_basis_mem (ρ : V → W) (k : ℕ) (t : Finset V) (hc : t.card = k+1)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    boundary V (basis t) ∈ chains (F := F) ρ (t : Set V) k := by
  induction k generalizing t with
  | zero =>
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    simp only [basis_singleton, boundary_vertex]
    rw [← basis_empty]
    exact basis_mem_chains ρ ∅ (by simp) (by simp [LinearIndepOn])
  | succ k ih =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < t.card)
    let u := t.erase v
    have hn : v ∉ u := Finset.notMem_erase _ _
    have hu : insert v u = t := Finset.insert_erase hv
    have hcu : u.card = k+1 := by
      have h := Finset.card_erase_of_mem hv
      change (t.erase v).card = k+1
      omega
    have hiu : LinearIndepOn F ρ (u : Set V) := hi.mono (Finset.erase_subset v t)
    have hout : ρ v ∉ Submodule.span F (ρ '' (u : Set V)) := by
      apply LinearIndepOn.notMem_span_of_insert _ hn
      simpa only [← Finset.coe_insert, hu] using hi
    obtain ⟨c, hc0, he⟩ := vertex_mul_basis v u hn
    rw [hu] at he
    have hmem : boundary V (vertex V v * basis u) ∈ chains (F := F) ρ (t : Set V) (k+1) := by
      rw [boundary_cone]
      apply Submodule.sub_mem
      · rw [← hcu]
        exact basis_mem_chains ρ u (Finset.erase_subset v t) hiu
      · have hm := cone_mem_chains ρ v hout (ih u hcu hiu)
        simpa only [← Finset.coe_insert, hu] using hm
    rw [he, map_smul] at hmem
    exact (Submodule.smul_mem_iff _ hc0).mp hmem

lemma boundary_mem_chains (ρ : V → W) {s : Set V} {k : ℕ} {x : Ambient V}
    (hx : x ∈ chains (F := F) ρ s (k+1)) :
    boundary V x ∈ chains (F := F) ρ s k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    exact chains_mono ρ ht k (boundary_basis_mem ρ k t hc hi)
  | zero => simpa only [map_zero] using (chains (F := F) ρ s k).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma vertex_mem_chains (ρ : V → W) {s : Set V} (v : V) (hv : v ∈ s) (hn : ρ v ≠ 0) :
    vertex V v ∈ chains (F := F) ρ s 1 := by
  rw [← basis_singleton]
  simpa using basis_mem_chains ρ {v} (by simpa using hv)
    (by simpa using ((linearIndepOn_singleton_iff F).mpr hn : LinearIndepOn F ρ {v}))

section EnoughRank
variable (ρ : V → W) [FiniteDimensional F W]

omit [LinearOrder V] [FiniteDimensional F W] in
lemma exists_outside_labels (hρ : Submodule.span F (Set.range ρ) = ⊤)
    (s : Finset V) (hs : s.card < Module.finrank F W) :
    ∃ v, ρ v ∉ Submodule.span F (ρ '' (s : Set V)) := by
  by_contra! hn
  have ht : Submodule.span F (ρ '' (s : Set V)) = ⊤ := by
    apply top_unique
    rw [← hρ]
    exact Submodule.span_le.mpr (by rintro x ⟨v, rfl⟩; exact hn v)
  have hc := finrank_span_finset_le_card (R := F) (s.image ρ)
  change Module.finrank F (Submodule.span F ((s.image ρ : Finset W) : Set W)) ≤ _ at hc
  rw [Finset.coe_image, ht] at hc
  have : Module.finrank F W ≤ s.card := by
    simpa using hc.trans (Finset.card_image_le)
  omega

structure ConeSupply (N : ℕ) where
  pick : Finset V → V
  outside : ∀ s : Finset V, s.card ≤ N →
    ρ (pick s) ∉ Submodule.span F (ρ '' (s : Set V))

end EnoughRank

variable (ρ : V → W) (C : ConeSupply (F := F) ρ 10)

def baseLabel : V := C.pick ∅

omit [LinearOrder V] in
lemma baseLabel_ne_zero : ρ (baseLabel ρ C) ≠ 0 := by
  have h := C.outside ∅ (by simp)
  simpa [baseLabel] using h

def cone0 (v : V) : V := C.pick {baseLabel ρ C, v}

def support0 (s : Finset V) : Finset V := insert (baseLabel ρ C) (s ∪ s.image (cone0 ρ C))

lemma subset_support0 (s : Finset V) : s ⊆ support0 ρ C s := by
  intro v hv
  simp [support0, hv]

lemma support0_mono {s t : Finset V} (h : s ⊆ t) : support0 ρ C s ⊆ support0 ρ C t :=
  Finset.insert_subset_insert _ (Finset.union_subset_union h (Finset.image_subset_image h))

lemma card_support0 (s : Finset V) : (support0 ρ C s).card ≤ 1+2*s.card := by
  calc
    _ ≤ (s ∪ s.image (cone0 ρ C)).card+1 := Finset.card_insert_le _ _
    _ ≤ s.card+(s.image (cone0 ρ C)).card+1 := Nat.add_le_add_right (Finset.card_union_le _ _) 1
    _ ≤ s.card+s.card+1 := Nat.add_le_add_right (Nat.add_le_add_left Finset.card_image_le _) 1
    _ = _ := by omega

def homotopy0Vertex (v : V) : Ambient V :=
  vertex V (cone0 ρ C v) * (vertex V v - vertex V (baseLabel ρ C))

lemma boundary_homotopy0Vertex (v : V) :
    boundary V (homotopy0Vertex ρ C v) = vertex V v - vertex V (baseLabel ρ C) := by
  simp [homotopy0Vertex, boundary_cone]

def homotopy0 : Ambient V →ₗ[ℚ] Ambient V :=
  (basis (V := V)).constr ℚ (fun t => ∑ v ∈ t, homotopy0Vertex ρ C v)

@[simp] lemma homotopy0_vertex (v : V) : homotopy0 ρ C (vertex V v) = homotopy0Vertex ρ C v := by
  unfold homotopy0
  rw [← basis_singleton, Basis.constr_basis, Finset.sum_singleton]

lemma boundary_homotopy0 {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 1) :
    boundary V (homotopy0 ρ C x) = x - vertex V (baseLabel ρ C) * boundary V x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    simp [boundary_homotopy0Vertex]
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy, mul_add]; abel
  | smul c x hx ih => simp only [map_smul, ih, smul_sub, mul_smul_comm]

lemma homotopy0Vertex_mem (v : V) (hv : ρ v ≠ 0) :
    homotopy0Vertex ρ C v ∈ chains (F := F) ρ (support0 ρ C {v} : Set V) 2 := by
  have hout : ρ (cone0 ρ C v) ∉
      Submodule.span F (ρ '' ({baseLabel ρ C, v} : Set V)) := by
    simpa only [cone0, Finset.coe_insert, Finset.coe_singleton] using
      C.outside {baseLabel ρ C, v} (Finset.card_le_two.trans (by decide : 2 ≤ 10))
  have h1 : vertex V v - vertex V (baseLabel ρ C) ∈
      chains (F := F) ρ ({baseLabel ρ C, v} : Set V) 1 :=
    Submodule.sub_mem _ (vertex_mem_chains ρ v (by simp) hv)
      (vertex_mem_chains ρ _ (by simp) (baseLabel_ne_zero ρ C))
  have h2 : homotopy0Vertex ρ C v ∈
      chains (F := F) ρ (insert (cone0 ρ C v) {baseLabel ρ C, v}) 2 :=
    cone_mem_chains ρ (cone0 ρ C v) hout h1
  refine chains_mono ρ (t := (support0 ρ C {v} : Set V)) ?_ 2 h2
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> simp [support0, cone0]

lemma homotopy0_mem {s : Finset V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ (s : Set V) 1) :
    homotopy0 ρ C x ∈ chains (F := F) ρ (support0 ρ C s : Set V) 2 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
    rw [basis_singleton, homotopy0_vertex]
    have hn : ρ v ≠ 0 := (linearIndepOn_singleton_iff F).mp (by simpa using hi)
    exact chains_mono ρ (support0_mono ρ C ht) 2 (homotopy0Vertex_mem ρ C v hn)
  | zero => simpa only [map_zero] using (chains (F := F) ρ (support0 ρ C s : Set V) 2).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

def cone1 (t : Finset V) : V := C.pick (support0 ρ C t)

def support1 (s : Finset V) : Finset V :=
  support0 ρ C s ∪ (s.powersetCard 2).image (cone1 ρ C)

lemma subset_support1 (s : Finset V) : s ⊆ support1 ρ C s :=
  (subset_support0 ρ C s).trans Finset.subset_union_left

lemma small_support1 {s : Finset V} (hs : s.card = 3) : (support1 ρ C s).card ≤ 10 := by
  have h0 := card_support0 ρ C s
  have h1 := Finset.card_image_le (s := s.powersetCard 2) (f := cone1 ρ C)
  have h2 : (s.powersetCard 2).card = 3 := by rw [Finset.card_powersetCard, hs]; decide
  have h3 := Finset.card_union_le (support0 ρ C s) ((s.powersetCard 2).image (cone1 ρ C))
  change (support0 ρ C s ∪ _).card ≤ 10
  omega

def homotopy1Basis (t : Finset V) : Ambient V :=
  vertex V (cone1 ρ C t) * (basis t - homotopy0 ρ C (boundary V (basis t)))

def homotopy1 : Ambient V →ₗ[ℚ] Ambient V :=
  (basis (V := V)).constr ℚ (homotopy1Basis ρ C)

@[simp] lemma homotopy1_basis (t : Finset V) :
    homotopy1 ρ C (basis t) = homotopy1Basis ρ C t := by
  exact Basis.constr_basis _ _ _ _

lemma boundary_homotopy1Basis (t : Finset V) (ht : t.card = 2)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    boundary V (homotopy1Basis ρ C t) = basis t - homotopy0 ρ C (boundary V (basis t)) := by
  have hd := boundary_basis_mem ρ 1 t ht hi
  have he := boundary_homotopy0 ρ C hd
  simp only [boundary_boundary, mul_zero, sub_zero] at he
  simp only [homotopy1Basis, boundary_cone, map_sub, he, sub_self, mul_zero, sub_zero]

lemma boundary_homotopy1 {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 2) :
    boundary V (homotopy1 ρ C x) = x - homotopy0 ρ C (boundary V x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    rw [homotopy1_basis]
    exact boundary_homotopy1Basis ρ C t hc hi
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]; abel
  | smul c x hx ih => simp only [map_smul, ih, smul_sub]

lemma homotopy1Basis_mem (t : Finset V) (ht : t.card = 2)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    homotopy1Basis ρ C t ∈
      chains (F := F) ρ (insert (cone1 ρ C t) (support0 ρ C t : Set V)) 3 := by
  have hd := boundary_basis_mem ρ 1 t ht hi
  have h0 := homotopy0_mem ρ C hd
  have hcard : (support0 ρ C t).card ≤ 10 := by have := card_support0 ρ C t; omega
  have hout : ρ (cone1 ρ C t) ∉ Submodule.span F (ρ '' (support0 ρ C t : Set V)) :=
    C.outside _ hcard
  have hb : basis t ∈ chains (F := F) ρ (support0 ρ C t : Set V) 2 := by
    rw [← ht]
    exact basis_mem_chains ρ t (subset_support0 ρ C t) hi
  exact cone_mem_chains ρ _ hout (Submodule.sub_mem _ hb h0)

lemma homotopy1_mem {s : Finset V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ (s : Set V) 2) :
    homotopy1 ρ C x ∈ chains (F := F) ρ (support1 ρ C s : Set V) 3 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    rw [homotopy1_basis]
    have h2 := homotopy1Basis_mem ρ C t hc hi
    refine chains_mono ρ ?_ 3 h2
    intro v hv
    rcases hv with rfl | hv
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t, Finset.mem_powersetCard.mpr ⟨ht, hc⟩, rfl⟩)
    · exact Finset.mem_union_left _ (support0_mono ρ C ht hv)
  | zero => simpa only [map_zero] using (chains (F := F) ρ (support1 ρ C s : Set V) 3).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

def cone2 (t : Finset V) : V := C.pick (support1 ρ C t)

def homotopy2Basis (t : Finset V) : Ambient V :=
  vertex V (cone2 ρ C t) * (basis t - homotopy1 ρ C (boundary V (basis t)))

def homotopy2 : Ambient V →ₗ[ℚ] Ambient V :=
  (basis (V := V)).constr ℚ (homotopy2Basis ρ C)

@[simp] lemma homotopy2_basis (t : Finset V) :
    homotopy2 ρ C (basis t) = homotopy2Basis ρ C t := by
  exact Basis.constr_basis _ _ _ _

lemma boundary_homotopy2Basis (t : Finset V) (ht : t.card = 3)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    boundary V (homotopy2Basis ρ C t) = basis t - homotopy1 ρ C (boundary V (basis t)) := by
  have hd := boundary_basis_mem ρ 2 t ht hi
  have he := boundary_homotopy1 ρ C hd
  simp only [boundary_boundary, map_zero, sub_zero] at he
  simp only [homotopy2Basis, boundary_cone, map_sub, he, sub_self, mul_zero, sub_zero]

lemma boundary_homotopy2 {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 3) :
    boundary V (homotopy2 ρ C x) = x - homotopy1 ρ C (boundary V x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    rw [homotopy2_basis]
    exact boundary_homotopy2Basis ρ C t hc hi
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]; abel
  | smul c x hx ih => simp only [map_smul, ih, smul_sub]

lemma homotopy2Basis_mem (t : Finset V) (ht : t.card = 3)
    (hi : LinearIndepOn F ρ (t : Set V)) :
    homotopy2Basis ρ C t ∈ chains (F := F) ρ Set.univ 4 := by
  have hd := boundary_basis_mem ρ 2 t ht hi
  have h1 := homotopy1_mem ρ C hd
  have hout : ρ (cone2 ρ C t) ∉ Submodule.span F (ρ '' (support1 ρ C t : Set V)) :=
    C.outside _ (small_support1 ρ C ht)
  have hb : basis t ∈ chains (F := F) ρ (support1 ρ C t : Set V) 3 := by
    rw [← ht]
    exact basis_mem_chains ρ t (subset_support1 ρ C t) hi
  have hcone : homotopy2Basis ρ C t ∈
      chains (F := F) ρ (insert (cone2 ρ C t) (support1 ρ C t : Set V)) 4 :=
    cone_mem_chains ρ _ hout (Submodule.sub_mem _ hb h1)
  exact chains_mono ρ (Set.subset_univ _) 4 hcone

lemma homotopy2_mem {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 3) :
    homotopy2 ρ C x ∈ chains (F := F) ρ Set.univ 4 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    rw [homotopy2_basis]
    exact homotopy2Basis_mem ρ C t hc hi
  | zero => simpa only [map_zero] using (chains (F := F) ρ Set.univ 4).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma homotopy0_mem_univ {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 1) :
    homotopy0 ρ C x ∈ chains (F := F) ρ Set.univ 2 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    have hb : basis t ∈ chains (F := F) ρ (t : Set V) 1 := by
      rw [← hc]; exact basis_mem_chains ρ t (Set.Subset.refl _) hi
    exact chains_mono ρ (Set.subset_univ _) 2 (homotopy0_mem ρ C hb)
  | zero => simpa only [map_zero] using (chains (F := F) ρ Set.univ 2).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma homotopy1_mem_univ {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 2) :
    homotopy1 ρ C x ∈ chains (F := F) ρ Set.univ 3 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    have hb : basis t ∈ chains (F := F) ρ (t : Set V) 2 := by
      rw [← hc]; exact basis_mem_chains ρ t (Set.Subset.refl _) hi
    exact chains_mono ρ (Set.subset_univ _) 3 (homotopy1_mem ρ C hb)
  | zero => simpa only [map_zero] using (chains (F := F) ρ Set.univ 3).zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

lemma degreeZero_support {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 0) :
    x ∈ chains (F := F) ρ ∅ 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    have : t = ∅ := Finset.card_eq_zero.mp hc
    subst t
    exact Submodule.subset_span ⟨∅, by simp, rfl, hi, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => exact Submodule.smul_mem _ c ih

lemma boundary_degreeZero {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 0) :
    boundary V x = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, hc, hi, rfl⟩ := hx
    have : t = ∅ := Finset.card_eq_zero.mp hc
    subst t
    simp
  | zero => simp
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul c x hx ih => simp [ih]

include C in
lemma degreeZero_lift {s : Set V} {x : Ambient V} (hx : x ∈ chains (F := F) ρ s 0) :
    ∃ y ∈ chains (F := F) ρ Set.univ 1, boundary V y = x := by
  have ho : ρ (baseLabel ρ C) ∉ Submodule.span F (ρ '' (∅ : Set V)) := by
    simpa only [baseLabel, Finset.coe_empty] using C.outside ∅ (by simp)
  have hm := cone_mem_chains ρ (baseLabel ρ C) ho (degreeZero_support ρ hx)
  exact ⟨vertex V (baseLabel ρ C) * x, chains_mono ρ (Set.subset_univ _) 1 hm,
    by rw [boundary_cone, boundary_degreeZero ρ hx, mul_zero, sub_zero]⟩

def differential (k : ℕ) : chains (F := F) ρ Set.univ (k+1) →ₗ[ℚ] chains (F := F) ρ Set.univ k :=
  LinearMap.codRestrict _ ((boundary V).domRestrict _) (fun z => boundary_mem_chains ρ z.property)

@[simp] lemma differential_val (k : ℕ) (z : chains (F := F) ρ Set.univ (k+1)) :
    (differential (F := F) ρ k z).val = boundary V z.val := rfl

end
end SourceBurnside.Stability.Frames

end
section
namespace SourceBurnside.Stability.Frames
noncomputable section
open Classical Module
variable {V : Type*}

def labelMap (f : V → V) : Ambient V →ₐ[ℚ] Ambient V :=
  ExteriorAlgebra.map (Finsupp.lmapDomain ℚ ℚ f)

@[simp] lemma labelMap_vertex (f : V → V) (v : V) :
    labelMap f (vertex V v) = vertex V (f v) := by
  simp [labelMap,vertex,Finsupp.lmapDomain_apply]

@[simp] lemma labelMap_id : labelMap (V := V) id = AlgHom.id ℚ _ := by
  simp [labelMap,Finsupp.lmapDomain_id]

lemma labelMap_comp (f g : V → V) : labelMap (g ∘ f) = (labelMap g).comp (labelMap f) := by
  simp [labelMap,Finsupp.lmapDomain_comp]

variable [LinearOrder V]

lemma basis_insert_inverse (v : V) (s : Finset V) (hv : v∉s) :
    ∃c : ℚ, c≠0 ∧ basis (insert v s) = c • (vertex V v * basis s) := by
  obtain ⟨c,hc,he⟩ := vertex_mul_basis v s hv
  refine ⟨c⁻¹,inv_ne_zero hc,?_⟩
  rw [he,smul_smul,inv_mul_cancel₀ hc,one_smul]

lemma labelMap_basis (f : V → V) (hf : Function.Injective f) (s : Finset V) :
    ∃c : ℚ, c≠0 ∧ labelMap f (basis s) = c • basis (s.image f) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,one_ne_zero,by simp⟩
  | @insert v s hv ih =>
    obtain ⟨c,hc,he⟩ := basis_insert_inverse v s hv
    obtain ⟨d,hd,hde⟩ := ih
    have hv' : f v ∉ s.image f := by simpa only [Finset.mem_image, hf.eq_iff, exists_eq_right] using hv
    obtain ⟨e,he0,hee⟩ := vertex_mul_basis (f v) (s.image f) hv'
    refine ⟨c*(d*e),mul_ne_zero hc (mul_ne_zero hd he0),?_⟩
    rw [he,map_smul,map_mul,labelMap_vertex,hde,mul_smul_comm,hee,smul_smul,smul_smul,
      Finset.image_insert]
    simp only [mul_assoc]

lemma boundary_labelMap (f : V → V) (x : Ambient V) :
    boundary V (labelMap f x) = labelMap f (boundary V x) := by
  suffices h : (boundary V).comp (labelMap f).toLinearMap =
      (labelMap f).toLinearMap.comp (boundary V) from DFunLike.congr_fun h x
  apply (basis (V := V)).ext
  intro s
  change boundary V (labelMap f (basis s)) = labelMap f (boundary V (basis s))
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
    obtain ⟨c,hc,he⟩ := basis_insert_inverse v s hv
    rw [he,map_smul,map_smul,map_smul,map_smul,map_mul,labelMap_vertex,
      boundary_cone,boundary_cone,map_sub,map_mul,labelMap_vertex,ih]

variable (G : Type*) [Group G] [MulAction G V]

def ambientAction : Representation ℚ G (Ambient V) where
  toFun g := (labelMap (g • ·)).toLinearMap
  map_one' := by
    change (labelMap (fun v : V => 1 • v)).toLinearMap = LinearMap.id
    simp only [one_smul]
    change (labelMap (V := V) id).toLinearMap = LinearMap.id
    rw [labelMap_id]
    rfl
  map_mul' g h := by
    change (labelMap (fun v : V => (g*h) • v)).toLinearMap =
      (labelMap (g • ·)).toLinearMap.comp (labelMap (h • ·)).toLinearMap
    have he : (fun v : V => (g*h) • v) = (g • ·) ∘ (h • ·) := funext (mul_smul g h)
    rw [he,labelMap_comp]
    rfl

variable {F W : Type*} [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)
variable (hind : ∀(g : G) (s : Set V), LinearIndepOn F ρ s →
  LinearIndepOn F ρ ((g • ·) '' s))

include hind in
lemma labelMap_chains (g : G) (k : ℕ) {x : Ambient V}
    (hx : x ∈ chains (F := F) ρ Set.univ k) :
    labelMap (g • ·) x ∈ chains (F := F) ρ Set.univ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s,hs,hcard,hi,rfl⟩ := hx
    obtain ⟨c,hc,he⟩ := labelMap_basis (g • ·) (MulAction.injective g) s
    rw [he]
    apply (chains (F := F) ρ Set.univ k).smul_mem c
    have hc : (s.image (g • ·)).card = k := by
      rw [Finset.card_image_of_injective _ (MulAction.injective g),hcard]
    rw [←hc]
    exact basis_mem_chains (F := F) ρ (s.image (g • ·)) (Set.subset_univ _)
      (by simpa using hind g (s : Set V) hi)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (chains (F := F) ρ Set.univ k).add_mem ihx ihy
  | smul a x hx ih => simpa using (chains (F := F) ρ Set.univ k).smul_mem a ih

def chainSubrepresentation (k : ℕ) : Subrepresentation (ambientAction (V := V) G) where
  toSubmodule := chains (F := F) ρ Set.univ k
  apply_mem_toSubmodule g := fun {_} hx => labelMap_chains G ρ hind g k hx

def chainRep (k : ℕ) : Rep ℚ G := Rep.of (chainSubrepresentation G (ρ := ρ) hind k).toRepresentation

end
end SourceBurnside.Stability.Frames

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

namespace SourceBurnside.Stability.Frames
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits Module
variable {V : Type} [LinearOrder V] (G : Type) [Group G] [MulAction G V]
variable {F W : Type} [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)
variable (hind : ∀(g : G) (s : Set V), LinearIndepOn F ρ s →
  LinearIndepOn F ρ ((g • ·) '' s))
def differentialRep (k : ℕ) : chainRep G (ρ := ρ) hind (k+1) ⟶ chainRep G (ρ := ρ) hind k :=
  Rep.ofHom
    { toLinearMap := differential (F := F) ρ k
      isIntertwining' := by
        intro g
        ext x
        change boundary V (labelMap (g • ·) x.val) = labelMap (g • ·) (boundary V x.val)
        exact boundary_labelMap (g • ·) x.val }

@[simp] lemma differentialRep_val (k : ℕ) (x : chainRep G (ρ := ρ) hind (k+1)) :
    ((differentialRep G ρ hind k).hom x).val = boundary V x.val := rfl

def repComplex : ChainComplex (Rep ℚ G) ℕ :=
  ChainComplex.of (chainRep G (ρ := ρ) hind) (differentialRep G ρ hind)
    (fun k => by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact boundary_boundary _)

@[simp] lemma repComplex_d (k : ℕ) : (repComplex G ρ hind).d (k+1) k =
    differentialRep G ρ hind k := by
  exact ChainComplex.of_d _ _ k

lemma degreeZero_scalar (x : chains (F := F) ρ Set.univ 0) :
    x.val = (basis.repr x.val ∅) • basis (∅ : Finset V) := by
  rcases x with ⟨x,hx⟩
  change x = _
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t,ht,hc,hi,rfl⟩ := hx
    have he : t = ∅ := Finset.card_eq_zero.mp hc
    subst t
    simp only [Basis.repr_self,Finsupp.single_eq_same,one_smul]
  | zero => simp
  | add x y hx hy ihx ihy =>
    simp only [map_add,Finsupp.add_apply,add_smul]
    exact congrArg₂ (· + ·) ihx ihy
  | smul a x hx ih =>
    change x = (basis.repr x ∅) • basis ∅ at ih
    simpa only [map_smul,Finsupp.smul_apply,smul_eq_mul,smul_smul] using congrArg (a • ·) ih
def degreeZeroIso : chainRep G (ρ := ρ) hind 0 ≅ Rep.trivial ℚ G ℚ where
  hom := Rep.ofHom
    { toLinearMap := ((Finsupp.lapply ∅).comp basis.repr.toLinearMap).domRestrict _
      isIntertwining' := by
        intro g
        ext x
        change basis.repr (labelMap (g • ·) x.val) ∅ = basis.repr x.val ∅
        conv_lhs => rw [degreeZero_scalar ρ x]
        have hb : labelMap (g • ·) (basis (∅ : Finset V)) = basis ∅ := by simp
        simp only [map_smul,hb,Basis.repr_self,Finsupp.smul_apply,Finsupp.single_eq_same,smul_eq_mul,mul_one] }
  inv := Rep.ofHom
    { toLinearMap :=
        { toFun c := ⟨c • basis (∅ : Finset V), (chains (F := F) ρ Set.univ 0).smul_mem c
            (basis_mem_chains ρ ∅ (by simp) (by simp [LinearIndepOn]))⟩
          map_add' c d := Subtype.ext (add_smul _ _ _)
          map_smul' c d := Subtype.ext (mul_smul _ _ _) }
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro c
        apply Subtype.ext
        change c • basis ∅ = labelMap (g • ·) (c • basis ∅)
        simp }
  hom_inv_id := by ext x; exact Subtype.ext (degreeZero_scalar ρ x).symm
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    change basis.repr (c • basis (∅ : Finset V)) ∅ = c
    simp only [map_smul, Basis.repr_self,Finsupp.smul_apply,Finsupp.single_eq_same,smul_eq_mul,mul_one]

end

noncomputable section
open Classical Module CategoryTheory
variable {V : Type} [LinearOrder V]
variable {F W : Type} [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)

def Index (k : ℕ) := {t : Finset V // t.card=k ∧ LinearIndepOn F ρ (t : Set V)}

lemma span_index (k : ℕ) :
    Submodule.span ℚ (Set.range (fun t : Index (F := F) ρ k => basis t.val)) =
      chains (F := F) ρ Set.univ k := by
  congr 1
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨t.val,Set.subset_univ _,t.property.1,t.property.2,rfl⟩
  · rintro ⟨t,ht,hc,hi,rfl⟩
    exact ⟨⟨t,hc,hi⟩,rfl⟩

def frameBasis (k : ℕ) : Basis (Index (F := F) ρ k) ℚ (chains (F := F) ρ Set.univ k) :=
  (Basis.span ((basis (V := V)).linearIndependent.comp (fun t : Index (F := F) ρ k => t.val)
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ (span_index ρ k))

@[simp] lemma frameBasis_val (k : ℕ) (t : Index (F := F) ρ k) :
    (frameBasis ρ k t).val = basis t.val := by
  simp [frameBasis,Basis.span_apply]

variable (G : Type) [Group G] [MulAction G V]
variable (hind : ∀(g : G) (s : Set V), LinearIndepOn F ρ s →
  LinearIndepOn F ρ ((g • ·) '' s))

@[instance_reducible] def indexAction (k : ℕ) : MulAction G (Index (F := F) ρ k) where
  smul g t := ⟨t.val.image (g • ·), by
    exact ⟨(Finset.card_image_of_injective _ (MulAction.injective g)).trans t.property.1,
      by simpa only [Finset.coe_image] using hind g _ t.property.2⟩⟩
  one_smul t := Subtype.ext (by
    change t.val.image (fun v => (1 : G) • v) = t.val
    simp)
  mul_smul g h t := Subtype.ext (by
    change t.val.image (fun v => (g*h) • v) =
      (t.val.image (fun v => h • v)).image (fun v => g • v)
    simp [Finset.image_image,mul_smul,Function.comp_def])

@[simp] lemma indexAction_val (k : ℕ) (g : G) (t : Index (F := F) ρ k) :
    letI := indexAction ρ G hind k
    (g • t).val = t.val.image (g • ·) := rfl

lemma frame_action_monomial (k : ℕ) (g : G) (t : Index (F := F) ρ k) :
    letI := indexAction ρ G hind k
    ∃c : ℚˣ, (chainRep G (ρ := ρ) hind k).ρ g (frameBasis ρ k t) =
      c.val • frameBasis ρ k (g • t) := by
  let := indexAction ρ G hind k
  obtain ⟨c,hc,he⟩ := labelMap_basis (g • ·) (MulAction.injective g) t.val
  refine ⟨Units.mk0 c hc,?_⟩
  apply Subtype.ext
  change labelMap (g • ·) (frameBasis ρ k t).val = _
  simpa only [frameBasis_val,Submodule.coe_smul,Units.val_mk0,indexAction_val] using he

end

noncomputable section
open Classical Module CategoryTheory
variable {V W U : Type}

def labelHom (f : V → W) : Ambient V →ₐ[ℚ] Ambient W :=
  ExteriorAlgebra.map (Finsupp.lmapDomain ℚ ℚ f)

@[simp] lemma labelHom_vertex (f : V → W) (v : V) :
    labelHom f (vertex V v) = vertex W (f v) := by
  simp [labelHom,vertex,Finsupp.lmapDomain_apply]

@[simp] lemma labelHom_id : labelHom (V := V) id = AlgHom.id ℚ _ := by
  simp [labelHom,Finsupp.lmapDomain_id]

lemma labelHom_comp (f : V → W) (g : W → U) :
    labelHom (g ∘ f) = (labelHom g).comp (labelHom f) := by
  simp [labelHom,Finsupp.lmapDomain_comp]

variable [LinearOrder V] [LinearOrder W] [LinearOrder U]

lemma labelHom_basis (f : V → W) (hf : Function.Injective f) (s : Finset V) :
    ∃c : ℚ, c≠0 ∧ labelHom f (basis s) = c • basis (s.image f) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,one_ne_zero,by simp⟩
  | @insert v s hv ih =>
    obtain ⟨c,hc,he⟩ := basis_insert_inverse v s hv
    obtain ⟨d,hd,hde⟩ := ih
    have hv' : f v ∉ s.image f := by simpa only [Finset.mem_image,hf.eq_iff,exists_eq_right] using hv
    obtain ⟨e,he0,hee⟩ := vertex_mul_basis (f v) (s.image f) hv'
    refine ⟨c*(d*e),mul_ne_zero hc (mul_ne_zero hd he0),?_⟩
    rw [he,map_smul,map_mul,labelHom_vertex,hde,mul_smul_comm,hee,smul_smul,smul_smul,
      Finset.image_insert]
    simp only [mul_assoc]

def labelEquiv (e : V ≃ W) : Ambient V ≃ₐ[ℚ] Ambient W :=
  { labelHom e with
    invFun := labelHom e.symm
    left_inv x := by
      have h := congrArg (fun f : Ambient V →ₐ[ℚ] Ambient V => f x) (labelHom_comp e e.symm)
      simpa using h.symm
    right_inv x := by
      have h := congrArg (fun f : Ambient W →ₐ[ℚ] Ambient W => f x) (labelHom_comp e.symm e)
      simpa using h.symm }

variable {F P Q : Type} [DivisionRing F] [AddCommGroup P] [Module F P]
variable [AddCommGroup Q] [Module F Q] (ρ : V → P) (σ : W → Q)
variable (e : V ≃ W)
variable (hi : ∀s : Set V, LinearIndepOn F ρ s → LinearIndepOn F σ (e '' s))

include hi in
lemma labelHom_chains (k : ℕ) {x : Ambient V} (hx : x∈chains (F := F) ρ Set.univ k) :
    labelHom e x∈chains (F := F) σ Set.univ k := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s,hs,hcard,hsind,rfl⟩ := hx
    obtain ⟨c,hc,he⟩ := labelHom_basis e e.injective s
    rw [he]
    apply (chains (F := F) σ Set.univ k).smul_mem c
    have hc : (s.image e).card=k := (Finset.card_image_of_injective _ e.injective).trans hcard
    rw [←hc]
    exact basis_mem_chains (F := F) σ _ (Set.subset_univ _) (by simpa using hi _ hsind)
  | zero => simp
  | add x y hx hy ihx ihy => simpa using (chains (F := F) σ Set.univ k).add_mem ihx ihy
  | smul a x hx ihx => simpa using (chains (F := F) σ Set.univ k).smul_mem a ihx

def chainLinear (k : ℕ) : chains (F := F) ρ Set.univ k →ₗ[ℚ] chains (F := F) σ Set.univ k where
  toFun x := ⟨labelHom e x.val,labelHom_chains ρ σ e hi k x.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

variable (hi' : ∀s : Set W, LinearIndepOn F σ s → LinearIndepOn F ρ (e.symm '' s))

def chainEquiv (k : ℕ) : chains (F := F) ρ Set.univ k ≃ₗ[ℚ] chains (F := F) σ Set.univ k :=
  { chainLinear ρ σ e hi k with
    invFun := chainLinear σ ρ e.symm hi' k
    left_inv x := Subtype.ext ((labelEquiv e).left_inv x.val)
    right_inv x := Subtype.ext ((labelEquiv e).right_inv x.val) }

variable {G H : Type} [Group G] [Group H] [MulAction G V] [MulAction H W]
variable (hind : ∀g : G, ∀s : Set V, LinearIndepOn F ρ s → LinearIndepOn F ρ ((g • ·) '' s))
variable (hind' : ∀g : H, ∀s : Set W, LinearIndepOn F σ s → LinearIndepOn F σ ((g • ·) '' s))
variable (eg : G ≃* H) (he : ∀(g : G) (v : V), e (g • v) = eg g • e v)

include he in
lemma chainEquiv_intertwining (k : ℕ) (g : G) :
    (chainEquiv ρ σ e hi hi' k).toLinearMap.comp ((chainRep G (ρ := ρ) hind k).ρ g) =
      ((chainRep H (ρ := σ) hind' k).ρ (eg g)).comp (chainEquiv ρ σ e hi hi' k).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change labelHom e (labelHom (g • ·) x.val) = labelHom (eg g • ·) (labelHom e x.val)
  have he' : (e ∘ (g • ·)) = (eg g • ·) ∘ e := funext (he g)
  have hh := congrArg (fun f : V → W => labelHom f) he'
  rw [labelHom_comp,labelHom_comp] at hh
  exact congrArg (fun f : Ambient V →ₐ[ℚ] Ambient W => f x.val) hh

def chainHomologyIso (k n : ℕ) :
    groupHomology (chainRep G (ρ := ρ) hind k) n ≅
      groupHomology (chainRep H (ρ := σ) hind' k) n :=
  groupHomology.mapIso eg (chainEquiv ρ σ e hi hi' k)
    (chainEquiv_intertwining ρ σ e hi hi' hind hind' eg he k) n

end
end SourceBurnside.Stability.Frames

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_MonomialPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside

def MatrixNilKernel {R : Type u} [Ring R] (ε : R →+* ZMod 2) : Prop :=
  ∀ n (A : Matrix (Fin n) (Fin n) R),
    (∀ i j, ε (A i j) = 0) → IsNilpotent A

end SourceBurnside
end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_KernelRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]
def awayCoordinates (t : Fin n) : Finset (Fin n) := Finset.univ.erase t
lemma away_disjoint (t : Fin n) : Disjoint (awayCoordinates t) {t} := by
  simp [awayCoordinates]
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]
def coordinateEquiv (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
def coordinateIndex (n : ℕ) (i : Fin n) : Fin (n+1) := coordinateEquiv n (Sum.inl i)
lemma coordinateIndex_injective (n : ℕ) : Function.Injective (coordinateIndex n) :=
  (coordinateEquiv n).injective.comp Sum.inl_injective
def spareCoordinate (n : ℕ) : Fin (n+1) := coordinateEquiv n (Sum.inr 0)

def blockUnits (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R)ˣ where
  val := Matrix.fromBlocks u.val 0 0 1
  inv := Matrix.fromBlocks u.inv 0 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]
def blockUnitsHom : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R)ˣ where
  toFun := blockUnits
  map_one' := by apply Units.ext;simp [blockUnits]
  map_mul' u v := by apply Units.ext;simp [blockUnits,Matrix.fromBlocks_multiply]
def padUnitsHom : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin (n+1)) (Fin (n+1)) R)ˣ :=
  (Units.map (Matrix.reindexRingEquiv R (coordinateEquiv n)).toMonoidHom).comp blockUnitsHom
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BlockEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def flattenRing : Matrix (Fin n) (Fin n) (Matrix (Fin N) (Fin N) R) ≃+* Matrix (Fin (n*N)) (Fin (n*N)) R :=
  (Matrix.compRingEquiv (Fin n) (Fin N) R).trans (Matrix.reindexRingEquiv R finProdFinEquiv)
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n : ℕ} {R : Type*} [Ring R]

def rowFixed (i : Fin n) : Subgroup (Matrix (Fin n) (Fin n) R)ˣ where
  carrier := {u | ∀j,u.val i j=(1 : Matrix (Fin n) (Fin n) R) i j}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv j
    change (u.val*v.val) i j=_
    change ∑ z, u.val i z*v.val z j=(1 : Matrix (Fin n) (Fin n) R) i j
    calc
      _ = ∑ z, (1 : Matrix (Fin n) (Fin n) R) i z*v.val z j :=
        Finset.sum_congr rfl (fun z _=>congrArg (fun a : R=>a*v.val z j) (hu z))
      _ = v.val i j := by simp [Matrix.one_apply]
      _ = _ := hv j
  inv_mem' := by
    intro u hu j
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) R=>M i j) u.val_inv
    change (u.val*u.inv) i j=_ at he
    change ∑ z,u.val i z*u.inv z j=(1 : Matrix (Fin n) (Fin n) R) i j at he
    calc
      _ = ∑ z,(1 : Matrix (Fin n) (Fin n) R) i z*u.inv z j := by simp [Matrix.one_apply]
      _ = ∑ z,u.val i z*u.inv z j :=
        Finset.sum_congr rfl (fun z _=>congrArg (fun a : R=>a*u.inv z j) (hu z).symm)
      _ = _ := he
def layer (height : Fin n→ℕ) (k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i=>height i=k)
def above (height : Fin n→ℕ) (k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i=>k<height i)
lemma layer_above_disjoint (height : Fin n→ℕ) (k : ℕ) : Disjoint (layer height k) (above height k) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [layer,above,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
  omega
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def innerHeight (x : Fin (n*N)) : ℕ := (finProdFinEquiv.symm x).2.val
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
def scalarEval (c : ZMod 2) : Polynomial R →+* R :=
  Polynomial.eval₂RingHom' (RingHom.id R) (algebraMap (ZMod 2) R c)
    (fun a=>(Algebra.commutes c a).symm)
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def scalarRingHom : @RingHom R (Matrix (Fin N) (Fin N) R)
    (inferInstance : Ring R).toNonAssocSemiring
    (inferInstance : Ring (Matrix (Fin N) (Fin N) R)).toNonAssocSemiring where
  toFun := Matrix.scalar (Fin N)
  map_zero' := map_zero _
  map_one' := map_one _
  map_add' := map_add _
  map_mul' := map_mul _
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
variable {A ι : Type*} [Ring A] [Fintype ι] [DecidableEq ι]

def polynomialMatrix : Polynomial (Matrix ι ι A) →+* Matrix ι ι (Polynomial A) :=
  Polynomial.eval₂RingHom' Polynomial.C.mapMatrix (Matrix.scalar ι Polynomial.X)
    (fun _ => (Matrix.scalar_commute Polynomial.X Polynomial.commute_X _).symm)
@[simp] lemma polynomialMatrix_monomial (n : ℕ) (M : Matrix ι ι A) (i j : ι) :
    polynomialMatrix (Polynomial.monomial n M) i j=Polynomial.monomial n (M i j) := by
  simp only [polynomialMatrix,Polynomial.eval₂RingHom'_apply,Polynomial.eval₂_monomial,
    ←map_pow,RingHom.mapMatrix_apply]
  simp only [Matrix.scalar_apply,Matrix.mul_diagonal,Matrix.map_apply]
  exact Polynomial.C_mul_X_pow_eq_monomial (R:=A) (a:=M i j) (n:=n)
end
end SourceBurnside.MatrixTests

namespace SourceBurnside.MatrixTests
noncomputable section
open Classical
open scoped BigOperators
variable {K A B ι : Type*} [CommRing K] [Ring A] [Ring B] [Algebra K A]
variable [Algebra (Polynomial K) B] [Fintype ι] [DecidableEq ι]
local instance instAlgebraPolynomial_solutions : Algebra (Polynomial K) (Polynomial A) := Polynomial.algebra K A
end
end SourceBurnside.MatrixTests

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_BandFactorization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {N : ℕ} {R : Type*} [Ring R]

def truncatedShift (N : ℕ) (R : Type*) [Zero R] [One R] : Matrix (Fin N) (Fin N) R :=
  fun s t=>if s.val+1=t.val then 1 else 0
def cyclicShift (N : ℕ) (R : Type*) [Zero R] [One R] : Matrix (Fin N) (Fin N) R :=
  fun s t=>if (s.val+1)%N=t.val then 1 else 0
end
end SourceBurnside.Kernel

namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]

def coefficientConj (P : (Matrix (Fin N) (Fin N) R)ˣ) :
    @RingHom (Matrix (Fin N) (Fin N) R) (Matrix (Fin N) (Fin N) R)
      (inferInstance : Ring (Matrix (Fin N) (Fin N) R)).toNonAssocSemiring
      (inferInstance : Ring (Matrix (Fin N) (Fin N) R)).toNonAssocSemiring where
  toFun A := P.val*A*P.inv
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by simp [mul_add,add_mul]
  map_mul' A B := by simp [mul_assoc]
def bigBasisUnits (P : (Matrix (Fin N) (Fin N) R)ˣ) : (Matrix (Fin (n*N)) (Fin (n*N)) R)ˣ :=
  Units.map flattenRing.toMonoidHom (Units.map (scalarRingHom (N:=n)).toMonoidHom P)
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_MatrixUnits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
def numericUnits (P : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ) : (Matrix (Fin N) (Fin N) R)ˣ :=
  Units.map (algebraMap (ZMod 2) R).mapMatrix.toMonoidHom P
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {N : ℕ}
def pascalMatrix (N : ℕ) : Matrix (Fin N) (Fin N) (ZMod 2) := fun s t=>(s.val.choose t.val : ZMod 2)
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n N : ℕ} {R : Type*} [Ring R]
def copyMatrixHom (s : Fin N) : Matrix (Fin n) (Fin n) R →* Matrix (Fin (n*N)) (Fin (n*N)) R :=
  (Matrix.reindexRingEquiv R finProdFinEquiv).toMonoidHom.comp
    ((Matrix.blockDiagonalRingHom (Fin n) (Fin N) R).toMonoidHom.comp (MonoidHom.mulSingle (fun _ : Fin N=>Matrix (Fin n) (Fin n) R) s))
def copyUnitsHom (s : Fin N) : (Matrix (Fin n) (Fin n) R)ˣ →* (Matrix (Fin (n*N)) (Fin (n*N)) R)ˣ :=
  Units.map (copyMatrixHom s)
variable [Algebra (ZMod 2) R]
def swapUnits (s t : Fin N) : (Matrix (Fin N) (Fin N) (ZMod 2))ˣ where
  val := Matrix.swap (ZMod 2) s t
  inv := Matrix.swap (ZMod 2) s t
  val_inv := Matrix.swap_mul_self s t
  inv_val := Matrix.swap_mul_self s t
end
end SourceBurnside.Kernel
namespace SourceBurnside.Kernel
noncomputable section
open Classical
variable {n m : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
def permutationUnits (σ : Equiv.Perm (Fin m)) : (Matrix (Fin m) (Fin m) (ZMod 2))ˣ where
  val := σ⁻¹.permMatrix (ZMod 2)
  inv := σ.permMatrix (ZMod 2)
  val_inv := by rw [←Matrix.permMatrix_mul];simp
  inv_val := by rw [←Matrix.permMatrix_mul];simp
end
end SourceBurnside.Kernel

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Matrices_ElementaryGenerators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R : Type*} [Ring R]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def elementary (i j : ι) (hij : i ≠ j) (a : R) : (Matrix ι ι R)ˣ where
  val := 1 + Matrix.single i j a
  inv := 1 + Matrix.single i j (-a)
  val_inv := by simp [add_mul, mul_add, hij.symm, ← Matrix.single_neg, add_assoc]
  inv_val := by simp [add_mul, mul_add, hij.symm, ← Matrix.single_neg, add_assoc]

@[simp] lemma elementary_val (i j : ι) (hij : i ≠ j) (a : R) :
    (elementary i j hij a : Matrix ι ι R) = 1 + Matrix.single i j a := rfl

def diagonal (d : ι → Rˣ) : (Matrix ι ι R)ˣ where
  val := Matrix.diagonal (fun i => (d i).val)
  inv := Matrix.diagonal (fun i => (d i).inv)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp

@[simp] lemma diagonal_val (d : ι → Rˣ) :
    (diagonal d : Matrix ι ι R) = Matrix.diagonal (fun i => (d i).val) := rfl

@[simp] lemma diagonal_one : diagonal (fun _ : ι => (1 : Rˣ)) = 1 := by
  apply Units.ext
  simp

@[simp] lemma diagonal_mul (d e : ι → Rˣ) : diagonal (fun i => d i * e i) = diagonal d * diagonal e := by
  apply Units.ext
  simp

def singleDiagonal (i : ι) (u : Rˣ) : (Matrix ι ι R)ˣ :=
  diagonal (fun j => if j = i then u else 1)

def generated : Subgroup (Matrix ι ι R)ˣ :=
  Subgroup.closure ({g | ∃i j h a, g = elementary i j h a} ∪ {g | ∃i u, g = singleDiagonal i u})

lemma elementary_mem (i j : ι) (hij : i ≠ j) (a : R) : elementary i j hij a ∈ generated :=
  Subgroup.subset_closure (Or.inl ⟨i, j, hij, a, rfl⟩)

lemma singleDiagonal_mem (i : ι) (u : Rˣ) : singleDiagonal i u ∈ generated :=
  Subgroup.subset_closure (Or.inr ⟨i, u, rfl⟩)

lemma diagonal_mem (d : ι → Rˣ) : diagonal d ∈ generated := by
  have he (s : Finset ι) : diagonal (fun i => if i ∈ s then d i else 1) ∈ generated := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have hh : diagonal (fun j => if j ∈ insert i s then d j else 1) =
          singleDiagonal i (d i) * diagonal (fun j => if j ∈ s then d j else 1) := by
        rw [singleDiagonal, ← diagonal_mul]
        congr 1
        funext j
        by_cases he : j = i
        · subst j; simp [hi]
        · simp [he]
      rw [hh]
      exact (generated (ι := ι) (R := R)).mul_mem (singleDiagonal_mem i (d i)) ih
  simpa using he Finset.univ

def relabel (e : ι ≃ κ) : (Matrix ι ι R)ˣ →* (Matrix κ κ R)ˣ :=
  Units.map (Matrix.reindexRingEquiv R e).toMonoidHom

@[simp] lemma relabel_elementary (e : ι ≃ κ) (i j : ι) (hij : i ≠ j) (a : R) :
    relabel e (elementary i j hij a) = elementary (e i) (e j) (e.injective.ne hij) a := by
  apply Units.ext
  ext x y
  simp [relabel, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Equiv.eq_symm_apply]

@[simp] lemma relabel_diagonal (e : ι ≃ κ) (d : ι → Rˣ) :
    relabel e (diagonal d) = diagonal (d ∘ e.symm) := by
  apply Units.ext
  simp [relabel, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]

@[simp] lemma relabel_singleDiagonal (e : ι ≃ κ) (i : ι) (u : Rˣ) :
    relabel e (singleDiagonal i u) = singleDiagonal (e i) u := by
  rw [singleDiagonal, relabel_diagonal, singleDiagonal]
  congr 1
  funext j
  simp [Equiv.symm_apply_eq]

lemma relabel_mem (e : ι ≃ κ) {g : (Matrix ι ι R)ˣ} (hg : g ∈ generated) :
    relabel e g ∈ generated := by
  have hh : generated (ι := ι) (R := R) ≤ (generated (ι := κ) (R := R)).comap (relabel e) := by
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨i, j, h, a, rfl⟩ | ⟨i, u, rfl⟩)
    · change relabel e (elementary i j h a) ∈ generated
      rw [relabel_elementary]
      exact elementary_mem _ _ _ _
    · change relabel e (singleDiagonal i u) ∈ generated
      rw [relabel_singleDiagonal]
      exact singleDiagonal_mem _ _
  exact hh hg

def blockInclusion : (Matrix ι ι R)ˣ →* (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ where
  toFun u :=
    { val := Matrix.fromBlocks u.val 0 0 1
      inv := Matrix.fromBlocks u.inv 0 0 1
      val_inv := by simp [Matrix.fromBlocks_multiply]
      inv_val := by simp [Matrix.fromBlocks_multiply] }
  map_one' := by apply Units.ext; simp
  map_mul' u v := by apply Units.ext; simp [Matrix.fromBlocks_multiply]

@[simp] lemma blockInclusion_val (u : (Matrix ι ι R)ˣ) :
    (blockInclusion (κ := κ) u : Matrix (ι ⊕ κ) (ι ⊕ κ) R) = Matrix.fromBlocks u.val 0 0 1 := rfl

@[simp] lemma blockInclusion_elementary (i j : ι) (hij : i ≠ j) (a : R) :
    blockInclusion (κ := κ) (elementary i j hij a) =
      elementary (Sum.inl i) (Sum.inl j) (Sum.inl_injective.ne hij) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply]

@[simp] lemma blockInclusion_diagonal (d : ι → Rˣ) :
    blockInclusion (κ := κ) (diagonal d) = diagonal (Sum.elim d (fun _ => 1)) := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;> simp [Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply]

lemma blockInclusion_mem {g : (Matrix ι ι R)ˣ} (hg : g ∈ generated) :
    blockInclusion (κ := κ) g ∈ generated := by
  have hh : generated (ι := ι) (R := R) ≤
      (generated (ι := ι ⊕ κ) (R := R)).comap blockInclusion := by
    apply (Subgroup.closure_le _).mpr
    rintro x (⟨i, j, h, a, rfl⟩ | ⟨i, u, rfl⟩)
    · change blockInclusion (κ := κ) (elementary i j h a) ∈ generated
      rw [blockInclusion_elementary]
      exact elementary_mem _ _ _ _
    · change blockInclusion (κ := κ) (singleDiagonal i u) ∈ generated
      rw [singleDiagonal, blockInclusion_diagonal]
      exact diagonal_mem _
  exact hh hg

def column (b : ι → R) : Matrix ι (Fin 1) R := Matrix.of (fun i _ => b i)
def row (c : ι → R) : Matrix (Fin 1) ι R := Matrix.of (fun _ j => c j)
def scalarOne (u : R) : Matrix (Fin 1) (Fin 1) R := Matrix.of (fun _ _ => u)

def upperStrip (b : ι → R) : (Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R)ˣ where
  val := Matrix.fromBlocks 1 (column b) 0 1
  inv := Matrix.fromBlocks 1 (-column b) 0 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

@[simp] lemma upperStrip_val (b : ι → R) :
    (upperStrip b : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R) =
      Matrix.fromBlocks 1 (column b) 0 1 := rfl

@[simp] lemma upperStrip_zero : upperStrip (fun _ : ι => (0 : R)) = 1 := by
  apply Units.ext
  exact Matrix.fromBlocks_one

lemma upperStrip_add (b c : ι → R) : upperStrip (b+c) = upperStrip b * upperStrip c := by
  apply Units.ext
  simp only [Units.val_mul, upperStrip_val, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1
  ext i j
  simp [column, Pi.add_apply, add_comm]

lemma upperStrip_single (i : ι) (a : R) :
    upperStrip (fun j => if j = i then a else 0) =
      elementary (Sum.inl i) (Sum.inr 0) (by simp) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, eq_comm, column, Fin.eq_zero]

lemma upperStrip_mem (b : ι → R) : upperStrip b ∈ generated := by
  have hs (s : Finset ι) : upperStrip (fun i => if i ∈ s then b i else 0) ∈ generated := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have he : (fun j => if j ∈ insert i s then b j else 0) =
          (fun j => if j = i then b i else 0) + (fun j => if j ∈ s then b j else 0) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [hi]
        · simp [hj]
      rw [he, upperStrip_add, upperStrip_single]
      exact (generated (ι := ι ⊕ Fin 1) (R := R)).mul_mem (elementary_mem _ _ _ _) ih
  simpa using hs Finset.univ

def lowerStrip (c : ι → R) : (Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R)ˣ where
  val := Matrix.fromBlocks 1 0 (row c) 1
  inv := Matrix.fromBlocks 1 0 (-row c) 1
  val_inv := by simp [Matrix.fromBlocks_multiply]
  inv_val := by simp [Matrix.fromBlocks_multiply]

@[simp] lemma lowerStrip_val (c : ι → R) :
    (lowerStrip c : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R) =
      Matrix.fromBlocks 1 0 (row c) 1 := rfl

@[simp] lemma lowerStrip_zero : lowerStrip (fun _ : ι => (0 : R)) = 1 := by
  apply Units.ext
  exact Matrix.fromBlocks_one

lemma lowerStrip_add (b c : ι → R) : lowerStrip (b+c) = lowerStrip b * lowerStrip c := by
  apply Units.ext
  simp only [Units.val_mul, lowerStrip_val, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1

lemma lowerStrip_single (i : ι) (a : R) :
    lowerStrip (fun j => if j = i then a else 0) =
      elementary (Sum.inr 0) (Sum.inl i) (by simp) a := by
  apply Units.ext
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.fromBlocks, Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, eq_comm, row, Fin.eq_zero]

lemma lowerStrip_mem (b : ι → R) : lowerStrip b ∈ generated := by
  have hs (s : Finset ι) : lowerStrip (fun i => if i ∈ s then b i else 0) ∈ generated := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have he : (fun j => if j ∈ insert i s then b j else 0) =
          (fun j => if j = i then b i else 0) + (fun j => if j ∈ s then b j else 0) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [hi]
        · simp [hj]
      rw [he, lowerStrip_add, lowerStrip_single]
      exact (generated (ι := ι ⊕ Fin 1) (R := R)).mul_mem (elementary_mem _ _ _ _) ih
  simpa using hs Finset.univ

lemma block_diagonal_val (U : (Matrix ι ι R)ˣ) (u : Rˣ) :
    (blockInclusion (κ := Fin 1) U * singleDiagonal (Sum.inr 0) u :
      (Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R)ˣ).val =
    Matrix.fromBlocks U.val 0 0 (scalarOne u.val) := by
  have hd : (singleDiagonal (ι := ι ⊕ Fin 1) (Sum.inr 0) u).val =
      Matrix.fromBlocks 1 0 0 (scalarOne u.val) := by
    ext x y
    cases x <;> cases y <;>
      simp [singleDiagonal, Matrix.fromBlocks, Matrix.diagonal_apply, Matrix.one_apply, scalarOne, Fin.eq_zero]
  rw [Units.val_mul, blockInclusion_val, hd]
  simp [Matrix.fromBlocks_multiply]

lemma schur_factorization (A : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) R)
    (u : Rˣ) (hu : A (Sum.inr 0) (Sum.inr 0) = u.val)
    (S : (Matrix ι ι R)ˣ)
    (hS : S.val = Matrix.of (fun i j => A (Sum.inl i) (Sum.inl j) -
      A (Sum.inl i) (Sum.inr 0) * u.inv * A (Sum.inr 0) (Sum.inl j))) :
    (upperStrip (fun i => A (Sum.inl i) (Sum.inr 0) * u.inv) *
      (blockInclusion (κ := Fin 1) S * singleDiagonal (Sum.inr 0) u) *
      lowerStrip (fun j => u.inv * A (Sum.inr 0) (Sum.inl j))).val = A := by
  rw [Units.val_mul, Units.val_mul, block_diagonal_val, upperStrip_val, lowerStrip_val]
  simp only [Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul,
    Matrix.mul_zero, add_zero, zero_add]
  ext x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      simp [Matrix.fromBlocks, Matrix.mul_apply, hS, mul_assoc, column, row, scalarOne]
    | inr j =>
      fin_cases j
      simp [Matrix.fromBlocks, Matrix.mul_apply, mul_assoc, column, row, scalarOne]
  | inr i =>
    fin_cases i
    cases y with
    | inl j =>
      simp [Matrix.fromBlocks, Matrix.mul_apply, ← mul_assoc, column, row, scalarOne]
    | inr j =>
      fin_cases j
      exact hu.symm

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.LinearAlgebra
noncomputable section
open Classical Matrix
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
include hI

lemma matrix_nil {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hA : ∀ i j, ε (A i j) = 0) : IsNilpotent A := by
  let e := Fintype.equivFin ι
  let f := Matrix.reindexRingEquiv R e
  apply (IsNilpotent.map_iff f.injective).mp
  exact hI _ (f A) (fun i j => hA (e.symm i) (e.symm j))

lemma nil_of_reduce_zero {a : R} (ha : ε a = 0) : IsNilpotent a := by
  let f : R →+* Matrix (Fin 1) (Fin 1) R := Matrix.scalar (Fin 1)
  have hf : Function.Injective f := by
    intro x y he
    simpa [f] using congrArg (fun M : Matrix (Fin 1) (Fin 1) R => M 0 0) he
  apply (IsNilpotent.map_iff hf).mp
  exact hI 1 _ (fun i j => by fin_cases i; fin_cases j; simpa [f] using ha)

lemma isUnit_of_reduce_one {a : R} (ha : ε a = 1) : IsUnit a := by
  have hn := nil_of_reduce_zero ε hI (a := a-1) (by simp [ha])
  simpa using hn.isUnit_add_one

lemma isUnit_matrix_of_reduce_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι R} (hA : ε.toRingHom.mapMatrix A = 1) : IsUnit A := by
  have hnil : IsNilpotent (A-1) := matrix_nil ε hI (A-1) (by
    intro i j
    have he := congrArg (fun M : Matrix ι ι (ZMod 2) => M i j)
      (show ε.toRingHom.mapMatrix (A-1) = 0 by rw [map_sub, hA, map_one, sub_self])
    exact he)
  simpa using hnil.isUnit_add_one

theorem isUnit_matrix_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) : IsUnit A ↔ IsUnit (ε.toRingHom.mapMatrix A) := by
  constructor
  · exact fun h => h.map ε.toRingHom.mapMatrix
  · rintro ⟨U, hU⟩
    let B : (Matrix ι ι R)ˣ := Units.map (algebraMap (ZMod 2) R).mapMatrix.toMonoidHom U⁻¹
    have hB : ε.toRingHom.mapMatrix (B : Matrix ι ι R) = (U⁻¹ : (Matrix ι ι (ZMod 2))ˣ) := by
      ext i j
      simp [B, RingHom.mapMatrix_apply]
    have hBA : ε.toRingHom.mapMatrix ((B : Matrix ι ι R)*A) = 1 := by
      rw [map_mul, hB, ← hU]
      exact U.inv_val
    have hu := isUnit_matrix_of_reduce_one ε hI hBA
    have he : (↑B⁻¹ : Matrix ι ι R) * ((B : Matrix ι ι R)*A) = A := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    rw [← he]
    exact B⁻¹.isUnit.mul hu

open MatrixGenerators

omit hI in
lemma relabel_reduce_one {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (U : (Matrix ι ι R)ˣ) (hU : ε.toRingHom.mapMatrix U.val = 1) :
    ε.toRingHom.mapMatrix (relabel e U).val = 1 := by
  ext i j
  have he := congrArg (fun M : Matrix ι ι (ZMod 2) => M (e.symm i) (e.symm j)) hU
  simpa [relabel, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply] using he

omit hI [Algebra (ZMod 2) R] in
lemma relabel_symm_apply {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (U : (Matrix κ κ R)ˣ) : relabel e (relabel e.symm U) = U := by
  apply Units.ext
  ext i j
  simp [relabel, Matrix.reindex_apply, Matrix.submatrix_apply]

lemma identity_residue_generated : ∀ (n : ℕ) (U : (Matrix (Fin n) (Fin n) R)ˣ),
    ε.toRingHom.mapMatrix U.val = 1 → U ∈ generated
  | 0, U, hU => by
    have he : U = 1 := Subsingleton.elim _ _
    rw [he]
    exact Subgroup.one_mem _
  | n+1, U, hU => by
    let e : Fin n ⊕ Fin 1 ≃ Fin (n+1) := finSumFinEquiv
    let V := relabel e.symm U
    have hV : ε.toRingHom.mapMatrix V.val = 1 := relabel_reduce_one ε e.symm U hU
    have hp : ε (V.val (Sum.inr 0) (Sum.inr 0)) = 1 := by
      have hh := congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (ZMod 2) =>
        M (Sum.inr 0) (Sum.inr 0)) hV
      simpa using hh
    obtain ⟨u, hu⟩ := isUnit_of_reduce_one ε hI hp
    let B : Matrix (Fin n) (Fin n) R := Matrix.of (fun i j =>
      V.val (Sum.inl i) (Sum.inl j) - V.val (Sum.inl i) (Sum.inr 0) * u.inv * V.val (Sum.inr 0) (Sum.inl j))
    have hB : ε.toRingHom.mapMatrix B = 1 := by
      ext i j
      have hh := congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (ZMod 2) =>
        M (Sum.inl i) (Sum.inl j)) hV
      have ho : ε (V.val (Sum.inl i) (Sum.inr 0)) = 0 := by
        have hh := congrArg (fun M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) (ZMod 2) =>
          M (Sum.inl i) (Sum.inr 0)) hV
        simpa using hh
      simpa [B, map_sub, map_mul, ho, Matrix.one_apply] using hh
    obtain ⟨S, hS⟩ := isUnit_matrix_of_reduce_one ε hI hB
    have hSgen : S ∈ generated := identity_residue_generated n S (by rw [hS]; exact hB)
    have he : upperStrip (fun i => V.val (Sum.inl i) (Sum.inr 0) * u.inv) *
        (blockInclusion (κ := Fin 1) S * singleDiagonal (Sum.inr 0) u) *
        lowerStrip (fun j => u.inv * V.val (Sum.inr 0) (Sum.inl j)) = V :=
      Units.ext (schur_factorization V.val u hu.symm S hS)
    have hvg : V ∈ generated := by
      rw [← he]
      apply Subgroup.mul_mem
      · exact Subgroup.mul_mem _ (upperStrip_mem _) (Subgroup.mul_mem _
          (blockInclusion_mem hSgen) (singleDiagonal_mem _ _))
      · exact lowerStrip_mem _
    have hh := relabel_mem e hvg
    simpa only [V, relabel_symm_apply] using hh

end
end SourceBurnside.Stability.LinearAlgebra

end

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
noncomputable section
open Classical Matrix
namespace SourceBurnside.Stability.LinearAlgebra

lemma extend_independent_map {F W κ : Type*} [Field F] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] {v w : κ → W}
    (hv : LinearIndependent F v) (hw : LinearIndependent F w) :
    ∃ T : W ≃ₗ[F] W, ∀ k, T (v k) = w k := by
  let f := hv.linearCombinationEquiv.symm.trans hw.linearCombinationEquiv
  obtain ⟨T, hT⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨T, fun k => ?_⟩
  have hh := hT (hv.linearCombinationEquiv (Finsupp.single k 1))
  simpa [f] using hh.symm

variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
include hI

theorem complete_columns {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (j : κ ↪ ι) (v : κ → ι → R)
    (hv : LinearIndependent (ZMod 2) (fun k i => ε (v k i))) :
    ∃ U : (Matrix ι ι R)ˣ, ∀ k i, U.val i (j k) = v k i := by
  have he : LinearIndependent (ZMod 2) (fun k => (Pi.basisFun (ZMod 2) ι) (j k)) :=
    (Pi.basisFun (ZMod 2) ι).linearIndependent.comp j j.injective
  obtain ⟨T, hT⟩ := extend_independent_map he hv
  let N : (Matrix ι ι (ZMod 2))ˣ :=
    Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom
      (LinearMap.GeneralLinearGroup.ofLinearEquiv T)
  have hN : ∀ k i, N.val i (j k) = ε (v k i) := by
    intro k i
    change (LinearMap.toMatrix' T.toLinearMap) i (j k) = _
    rw [LinearMap.toMatrix'_apply]
    have hh := congrFun (hT k) i
    simpa using hh
  let A : Matrix ι ι R := Matrix.of (fun i l =>
    if h : ∃k, j k = l then v h.choose i else algebraMap (ZMod 2) R (N.val i l))
  have hA : ε.toRingHom.mapMatrix A = N.val := by
    ext i l
    change ε (if h : ∃ k, j k = l then v h.choose i else _) = _
    split_ifs with h
    · rw [← hN, h.choose_spec]
    · simp
  have hu : IsUnit A := (isUnit_matrix_iff ε hI A).mpr (by rw [hA]; exact N.isUnit)
  obtain ⟨U, hU⟩ := hu
  refine ⟨U, fun k i => ?_⟩
  rw [hU]
  change (if h : ∃k', j k' = j k then v h.choose i else _) = _
  split_ifs with h
  · rw [j.injective h.choose_spec]
  · exact (h ⟨k, rfl⟩).elim

end SourceBurnside.Stability.LinearAlgebra

end

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
open Classical MatrixGenerators
variable {R : Type*} [Ring R]

inductive Generator (ι : Type*) (R : Type*) [Ring R] where
  | root (i j : ι) (h : i ≠ j) (a : R)
  | diag (i : ι) (u : Rˣ)

namespace Generator
variable {ι κ : Type*}
def support [DecidableEq ι] : Generator ι R → Finset ι
  | .root i j _ _ => {i,j}
  | .diag i _ => {i}

def map (e : ι ↪ κ) : Generator ι R → Generator κ R
  | .root i j h a => .root (e i) (e j) (e.injective.ne h) a
  | .diag i u => .diag (e i) u

variable [Fintype ι] [DecidableEq ι]
def matrix : Generator ι R → (Matrix ι ι R)ˣ
  | .root i j h a => elementary i j h a
  | .diag i u => singleDiagonal i u
end Generator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixWord : FreeGroup (Generator ι R) →* (Matrix ι ι R)ˣ :=
  FreeGroup.lift Generator.matrix

def supported (S : Finset ι) : Subgroup (FreeGroup (Generator ι R)) :=
  Subgroup.closure (FreeGroup.of '' {g | g.support ⊆ S})

def relations : Set (FreeGroup (Generator ι R)) :=
  {w | matrixWord w = 1 ∧ ∃S : Finset ι, S.card ≤ 5 ∧ w ∈ supported S}

abbrev Group := PresentedGroup (relations (ι := ι) (R := R))

def evaluate : Group (ι := ι) (R := R) →* (Matrix ι ι R)ˣ :=
  PresentedGroup.toGroup (fun _ h => h.1)

def gen (g : Generator ι R) : Group (ι := ι) (R := R) := PresentedGroup.of g

@[simp] lemma evaluate_gen (g : Generator ι R) : evaluate (gen g) = g.matrix :=
  PresentedGroup.toGroup.of _

lemma supported_univ : supported (R := R) (Finset.univ : Finset ι) = ⊤ := by
  unfold supported
  simp only [Finset.subset_univ, Set.ofPred_true, Set.image_univ, FreeGroup.closure_range_of]

theorem evaluate_injective_small (hι : Fintype.card ι ≤ 5) :
    Function.Injective (evaluate (ι := ι) (R := R)) := by
  apply (MonoidHom.ker_eq_bot_iff evaluate).mp
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective relations g
  change PresentedGroup.mk relations w = 1
  have hm : matrixWord w = 1 := hg
  apply PresentedGroup.one_of_mem
  exact ⟨hm, Finset.univ, by simpa using hι, by rw [supported_univ]; trivial⟩

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R ι κ : Type*} [Ring R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def embeddingEquiv (e : ι ↪ κ) : ι ⊕ {k // k ∉ Set.range e} ≃ κ :=
  (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

omit [Fintype κ] [DecidableEq ι] in
@[simp] lemma embeddingEquiv_inl (e : ι ↪ κ) (i : ι) : embeddingEquiv e (Sum.inl i) = e i := rfl
omit [Fintype κ] [DecidableEq ι] in
@[simp] lemma embeddingEquiv_inr (e : ι ↪ κ) (i : {k // k ∉ Set.range e}) :
    embeddingEquiv e (Sum.inr i) = i.val := rfl

def embed (e : ι ↪ κ) : (Matrix ι ι R)ˣ →* (Matrix κ κ R)ˣ :=
  (relabel (embeddingEquiv e)).comp (blockInclusion (κ := {k // k ∉ Set.range e}))

@[simp] lemma embed_elementary (e : ι ↪ κ) (i j : ι) (h : i ≠ j) (a : R) :
    embed e (elementary i j h a) = elementary (e i) (e j) (e.injective.ne h) a := by
  simp only [embed,MonoidHom.comp_apply,blockInclusion_elementary,relabel_elementary,
    embeddingEquiv_inl]

lemma blockInclusion_singleDiagonal (i : ι) (u : Rˣ) :
    blockInclusion (κ := κ) (singleDiagonal i u) = singleDiagonal (Sum.inl i) u := by
  rw [singleDiagonal,blockInclusion_diagonal,singleDiagonal]
  congr 1
  funext j
  cases j <;> simp

@[simp] lemma embed_singleDiagonal (e : ι ↪ κ) (i : ι) (u : Rˣ) :
    embed e (singleDiagonal i u) = singleDiagonal (e i) u := by
  simp only [embed,MonoidHom.comp_apply,blockInclusion_singleDiagonal,relabel_singleDiagonal,
    embeddingEquiv_inl]

lemma embed_entry (e : ι ↪ κ) (U : (Matrix ι ι R)ˣ) (i j : ι) :
    (embed e U).val (e i) (e j) = U.val i j := by
  change (Matrix.fromBlocks U.val 0 0 (1 : Matrix {k // k ∉ Set.range e} _ R))
    ((embeddingEquiv e).symm (e i)) ((embeddingEquiv e).symm (e j)) = _
  rw [← embeddingEquiv_inl e i,← embeddingEquiv_inl e j,
    Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rfl

lemma embed_injective (e : ι ↪ κ) : Function.Injective (embed (R := R) e) := by
  intro U V hh
  apply Units.ext
  ext i j
  simpa only [embed_entry] using congrArg (fun B : (Matrix κ κ R)ˣ => B.val (e i) (e j)) hh

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma generator_map_matrix (e : ι ↪ κ) (g : Generator ι R) :
    (g.map e).matrix = embed e g.matrix := by
  cases g <;> simp [Generator.map,Generator.matrix]

lemma matrixWord_map (e : ι ↪ κ) :
    matrixWord.comp (FreeGroup.map (Generator.map e)) = (embed e).comp (matrixWord (R := R)) := by
  apply FreeGroup.ext_hom
  intro g
  simpa [matrixWord] using generator_map_matrix e g

omit [Fintype ι] [Fintype κ] in
lemma supported_map (e : ι ↪ κ) (S : Finset ι) :
    supported (R := R) S ≤ (supported (S.image e)).comap (FreeGroup.map (Generator.map e)) := by
  apply (Subgroup.closure_le _).mpr
  rintro w ⟨g,hg,rfl⟩
  change FreeGroup.map (Generator.map e) (FreeGroup.of g) ∈ supported _
  rw [FreeGroup.map.of]
  apply Subgroup.subset_closure
  refine ⟨g.map e,?_,rfl⟩
  cases g with
  | root i j h a =>
    change ({i,j} : Finset ι) ⊆ S at hg
    change ({e i,e j} : Finset κ) ⊆ S.image e
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff] at hg ⊢
    exact ⟨Finset.mem_image.mpr ⟨i,hg.1,rfl⟩,Finset.mem_image.mpr ⟨j,hg.2,rfl⟩⟩
  | diag i u =>
    change ({i} : Finset ι) ⊆ S at hg
    change ({e i} : Finset κ) ⊆ S.image e
    simp only [Finset.singleton_subset_iff] at hg ⊢
    exact Finset.mem_image.mpr ⟨i,hg,rfl⟩

def inclusion (e : ι ↪ κ) : Group (ι := ι) (R := R) →* Group (ι := κ) (R := R) :=
  PresentedGroup.map (FreeGroup.map (Generator.map e)) (by
    intro w hw
    refine ⟨?_,?_⟩
    · change matrixWord (FreeGroup.map (Generator.map e) w) = 1
      rw [← MonoidHom.comp_apply,matrixWord_map,MonoidHom.comp_apply,hw.1,map_one]
    · obtain ⟨S,hS,hwS⟩ := hw.2
      exact ⟨S.image e,Finset.card_image_le.trans hS,supported_map e S hwS⟩)

@[simp] lemma inclusion_gen (e : ι ↪ κ) (g : Generator ι R) :
    inclusion e (gen g) = gen (g.map e) := by
  change PresentedGroup.mk _ (FreeGroup.map (Generator.map e) (FreeGroup.of g)) = _
  rw [FreeGroup.map.of]
  rfl

lemma evaluate_inclusion (e : ι ↪ κ) : (evaluate (R := R)).comp (inclusion e) = (embed e).comp evaluate := by
  apply PresentedGroup.ext
  intro g
  change evaluate (inclusion e (gen g)) = embed e (evaluate (gen g))
  rw [inclusion_gen,evaluate_gen,evaluate_gen,generator_map_matrix]

@[simp] lemma evaluate_inclusion_apply (e : ι ↪ κ) (g : Group (ι := ι) (R := R)) :
    evaluate (inclusion e g) = embed e (evaluate g) := DFunLike.congr_fun (evaluate_inclusion e) g

omit [Fintype ι] in
lemma supported_letter (S : Finset ι) (g : Generator ι R) (h : g.support ⊆ S) :
    FreeGroup.of g ∈ supported S := Subgroup.subset_closure ⟨g,h,rfl⟩

lemma local_equality (S : Finset ι) (hS : S.card ≤ 5)
    (w w' : FreeGroup (Generator ι R)) (hw : w ∈ supported S) (hw' : w' ∈ supported S)
    (he : matrixWord w = matrixWord w') :
    PresentedGroup.mk relations w = PresentedGroup.mk relations w' := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  exact ⟨by simp only [map_mul,map_inv,he,mul_inv_cancel],S,hS,(supported S).mul_mem hw ((supported S).inv_mem hw')⟩

end
end SourceBurnside.Stability.SmallPresentation

end
section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort

namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def localGroup (S : Finset ι) : Subgroup (Group (ι := ι) (R := R)) :=
  (supported S).map (PresentedGroup.mk relations)

lemma gen_mem_local (S : Finset ι) (g : Generator ι R) (h : g.support ⊆ S) :
    gen g ∈ localGroup S := ⟨FreeGroup.of g,supported_letter S g h,rfl⟩

lemma local_faithful (S : Finset ι) (hS : S.card ≤ 5)
    {g h : Group (ι := ι) (R := R)} (hg : g ∈ localGroup S) (hh : h ∈ localGroup S)
    (he : evaluate g = evaluate h) : g = h := by
  obtain ⟨w,hw,rfl⟩ := hg
  obtain ⟨v,hv,rfl⟩ := hh
  exact local_equality S hS w v hw hv he

lemma localGroup_eq_closure (S : Finset ι) : localGroup (R := R) S =
    Subgroup.closure (gen '' {g | g.support ⊆ S}) := by
  rw [localGroup,supported,MonoidHom.map_closure]
  congr 1
  rw [Set.image_image]
  rfl

lemma range_inclusion (S : Finset ι) :
    (inclusion (R := R) (Function.Embedding.subtype (· ∈ S))).range = localGroup S := by
  apply le_antisymm
  · rintro x ⟨g,rfl⟩
    have hh : (⊤ : Subgroup (Group (ι := {i // i ∈ S}) (R := R))) ≤
        (localGroup S).comap (inclusion (Function.Embedding.subtype _)) := by
      rw [← PresentedGroup.closure_range_of (relations (ι := {i // i ∈ S}) (R := R))]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨g,rfl⟩
      change inclusion _ (gen g) ∈ localGroup S
      rw [inclusion_gen]
      apply gen_mem_local
      cases g with
      | root i j h a => exact Finset.insert_subset_iff.mpr ⟨i.property,Finset.singleton_subset_iff.mpr j.property⟩
      | diag i u => exact Finset.singleton_subset_iff.mpr i.property
    exact hh (Subgroup.mem_top g)
  · rw [localGroup_eq_closure]
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨g,hg,rfl⟩
    cases g with
    | root i j h a =>
      obtain ⟨hi,hj⟩ := Finset.insert_subset_iff.mp hg
      have hj := Finset.singleton_subset_iff.mp hj
      refine ⟨gen (.root ⟨i,hi⟩ ⟨j,hj⟩ (fun he => h (congrArg Subtype.val he)) a),?_⟩
      rw [inclusion_gen]; rfl
    | diag i u =>
      refine ⟨gen (.diag ⟨i,Finset.singleton_subset_iff.mp hg⟩ u),?_⟩
      rw [inclusion_gen]; rfl

lemma supported_gen_all : Subgroup.closure (Set.range (gen (ι := ι) (R := R))) = ⊤ :=
  PresentedGroup.closure_range_of _

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def root (i j : ι) (h : i ≠ j) (a : R) : Group (ι := ι) (R := R) := gen (.root i j h a)
def diag (i : ι) (u : Rˣ) : Group (ι := ι) (R := R) := gen (.diag i u)

@[simp] lemma evaluate_root (i j : ι) (h : i≠j) (a : R) :
    evaluate (root i j h a) = elementary i j h a := evaluate_gen _
@[simp] lemma evaluate_diag (i : ι) (u : Rˣ) :
    evaluate (diag i u) = singleDiagonal i u := evaluate_gen _

lemma root_mem_local (S : Finset ι) (i j : ι) (h : i≠j) (a : R)
    (hi : i∈S) (hj : j∈S) : root i j h a ∈ localGroup S :=
  gen_mem_local S _ (Finset.insert_subset_iff.mpr ⟨hi,Finset.singleton_subset_iff.mpr hj⟩)
lemma diag_mem_local (S : Finset ι) (i : ι) (u : Rˣ) (hi : i∈S) : diag i u ∈ localGroup S :=
  gen_mem_local S _ (Finset.singleton_subset_iff.mpr hi)

@[simp] lemma root_add (i j : ι) (h : i≠j) (a b : R) :
    root i j h (a+b) = root i j h a * root i j h b := by
  apply local_faithful {i,j} (by have := Finset.card_insert_le i ({j} : Finset ι); simp only [Finset.card_singleton] at this; omega)
    (root_mem_local _ _ _ _ _ (by simp) (by simp))
    ((localGroup _).mul_mem (root_mem_local _ _ _ _ _ (by simp) (by simp))
      (root_mem_local _ _ _ _ _ (by simp) (by simp)))
  apply Units.ext
  simp [elementary,add_mul,mul_add,h.symm,Matrix.single_add,add_assoc]

@[simp] lemma root_zero (i j : ι) (h : i≠j) : root i j h (0:R) = 1 := by
  have hh := root_add i j h (0:R) 0
  simp only [zero_add] at hh
  exact mul_left_cancel (hh.symm.trans (mul_one _).symm)

@[simp] lemma root_neg (i j : ι) (h : i≠j) (a : R) : root i j h (-a) = (root i j h a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [←root_add,add_neg_cancel,root_zero]

lemma root_commute (i j k l : ι) (hij : i≠j) (hkl : k≠l)
    (hjk : j≠k) (hil : i≠l) (a b : R) : Commute (root i j hij a) (root k l hkl b) := by
  change root i j hij a * root k l hkl b = root k l hkl b * root i j hij a
  let S : Finset ι := {i,j,k,l}
  have hs : S.card ≤ 5 := by
    have h1 := Finset.card_insert_le i ({j,k,l} : Finset ι)
    have h2 := Finset.card_insert_le j ({k,l} : Finset ι)
    have h3 := Finset.card_insert_le k ({l} : Finset ι)
    simp only [Finset.card_singleton] at h3
    dsimp [S]; omega
  have hi := root_mem_local S i j hij a (by simp [S]) (by simp [S])
  have hk := root_mem_local S k l hkl b (by simp [S]) (by simp [S])
  apply local_faithful S hs ((localGroup S).mul_mem hi hk) ((localGroup S).mul_mem hk hi)
  simp only [map_mul,evaluate_root]
  apply Units.ext
  simp only [Units.val_mul,elementary_val,add_mul,mul_add,one_mul,mul_one,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk,
    Matrix.single_mul_single_of_ne _ _ _ _ hil.symm]
  abel

@[simp] lemma diag_inv (i : ι) (u : Rˣ) : diag i u⁻¹ = (diag i u)⁻¹ := by
  apply local_faithful {i} (by simp)
    (diag_mem_local _ _ _ (by simp)) ((localGroup _).inv_mem (diag_mem_local _ _ _ (by simp)))
  simp only [evaluate_diag,map_inv]
  apply Units.ext
  ext k l
  by_cases hk : k=i <;> simp [singleDiagonal,diagonal,Matrix.diagonal_apply,hk]

def rowHom (t : ι) : ({j : ι // j≠t} → Multiplicative R) →* Group (ι := ι) (R := R) :=
  MonoidHom.noncommPiCoprod
    (fun j => {toFun := fun a => root t j.val j.property.symm a.toAdd
               map_one' := root_zero _ _ _
               map_mul' := fun _left _right => root_add _ _ _ _ _})
    (fun i j _ _left _right => root_commute _ _ _ _ i.property.symm j.property.symm i.property j.property.symm _ _)

@[simp] lemma rowHom_single (t : ι) (j : {j : ι // j≠t}) (a : R) :
    rowHom t (Pi.mulSingle j (Multiplicative.ofAdd a)) = root t j.val j.property.symm a :=
  MonoidHom.noncommPiCoprod_mulSingle _ _ _

def rowGroup (t : ι) : Subgroup (Group (ι := ι) (R := R)) := (rowHom t).range

lemma root_mem_row (t j : ι) (h : t≠j) (a : R) : root t j h a ∈ rowGroup t :=
  ⟨Pi.mulSingle ⟨j,h.symm⟩ (Multiplicative.ofAdd a), rowHom_single _ _ _⟩

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

lemma row_mem {t : ι} {P : Subgroup (Group (ι := ι) (R := R))}
    (hP : ∀ j (h : t≠j) a, root t j h a ∈ P)
    (A : {j : ι // j≠t} → Multiplicative R) : rowHom t A ∈ P := by
  change A ∈ P.comap (rowHom t)
  apply Subgroup.pi_mem_of_mulSingle_mem
  intro j
  change rowHom t (Pi.mulSingle j (Multiplicative.ofAdd (A j).toAdd)) ∈ P
  rw [rowHom_single]
  exact hP _ _ _

lemma rowGroup_le {t : ι} {P : Subgroup (Group (ι := ι) (R := R))}
    (hP : ∀ j (h : t≠j) a, root t j h a ∈ P) : rowGroup t ≤ P := by
  rintro x ⟨A,rfl⟩
  exact row_mem hP A

def rowMatrix (t : ι) (A : {j : ι // j≠t} → Multiplicative R) : Matrix ι ι R :=
  fun i j => if i=t then if hj : j≠t then (A ⟨j,hj⟩).toAdd else 0 else 0

omit [Fintype ι] in
@[simp] lemma rowMatrix_entry (t : ι) (A : {j : ι // j≠t} → Multiplicative R)
    (j : {j : ι // j≠t}) : rowMatrix t A t j.val = (A j).toAdd := by
  simp [rowMatrix,j.property]

lemma rowMatrix_product (t : ι) (A B : {j : ι // j≠t} → Multiplicative R) :
    rowMatrix t A * rowMatrix t B = 0 := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k=t <;> simp [rowMatrix,hk]

omit [Fintype ι] in
@[simp] lemma rowMatrix_one (t : ι) : rowMatrix t (1 : {j : ι // j≠t} → Multiplicative R) = 0 := by
  ext i j; simp [rowMatrix]

omit [Fintype ι] in
@[simp] lemma rowMatrix_mul (t : ι) (A B : {j : ι // j≠t} → Multiplicative R) :
    rowMatrix t (A*B) = rowMatrix t A + rowMatrix t B := by
  ext i j
  simp only [rowMatrix,Matrix.add_apply]
  split_ifs <;> simp_all

def rowUnits (t : ι) : ({j : ι // j≠t} → Multiplicative R) →* (Matrix ι ι R)ˣ where
  toFun A :=
    { val := 1+rowMatrix t A
      inv := 1-rowMatrix t A
      val_inv := by simp [add_mul,mul_sub,rowMatrix_product]
      inv_val := by simp [sub_mul,mul_add,rowMatrix_product] }
  map_one' := by apply Units.ext; simp
  map_mul' A B := by
    apply Units.ext
    simp only [Units.val_mul,rowMatrix_mul]
    simp [add_mul,mul_add,rowMatrix_product,add_assoc]

end
end SourceBurnside.Stability.SmallPresentation

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_MatrixStabilizers
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

def rectangleLower : (κ × ι → Multiplicative R) →* (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ where
  toFun A :=
    { val := Matrix.fromBlocks 1 0 (Matrix.of (fun i j => (A (i,j)).toAdd)) 1
      inv := Matrix.fromBlocks 1 0 (Matrix.of (fun i j => -(A (i,j)).toAdd)) 1
      val_inv := by
        rw [Matrix.fromBlocks_multiply]
        ext i j
        cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
      inv_val := by
        rw [Matrix.fromBlocks_multiply]
        ext i j
        cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply] }
  map_one' := by
    apply Units.ext
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  map_mul' A B := by
    apply Units.ext
    simp only [Units.val_mul,Matrix.fromBlocks_multiply,Matrix.mul_one,Matrix.one_mul,
      Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add]
    congr 1

def rightFixer : Subgroup (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ :=
  ⨅ k : κ, MulAction.stabilizer (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ (Pi.single (Sum.inr k) (1 : R) : ι ⊕ κ → R)

lemma mem_rightFixer_iff (U : (Matrix (ι ⊕ κ) (ι ⊕ κ) R)ˣ) :
    U ∈ rightFixer ↔ ∀ i k, U.val i (Sum.inr k) = (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) R) i (Sum.inr k) := by
  simp only [rightFixer,Subgroup.mem_iInf,MulAction.mem_stabilizer_iff]
  constructor
  · intro h i k
    have hh := congrFun (h k) i
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh
  · intro h k
    ext i
    have hh := h i k
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh

lemma rightFixer_shape (U : rightFixer (ι := ι) (κ := κ) (R := R)) :
    U.val.val = Matrix.fromBlocks (U.val.val.submatrix Sum.inl Sum.inl) 0
      (U.val.val.submatrix Sum.inr Sum.inl) 1 := by
  ext i j
  cases j with
  | inl j => cases i <;> rfl
  | inr j =>
    have hh := (mem_rightFixer_iff U.val).mp U.property i j
    cases i <;> simpa [Matrix.fromBlocks,Matrix.one_apply] using hh

def rightProjection : rightFixer (ι := ι) (κ := κ) (R := R) →* (Matrix ι ι R)ˣ where
  toFun U :=
    { val := U.val.val.submatrix Sum.inl Sum.inl
      inv := U.val.inv.submatrix Sum.inl Sum.inl
      val_inv := by
        have he : U.val.val * (U⁻¹).val.val = 1 := U.val.val_inv
        rw [rightFixer_shape U,rightFixer_shape U⁻¹,Matrix.fromBlocks_multiply] at he
        ext i j
        have hh := congrArg (fun A : Matrix (ι ⊕ κ) (ι ⊕ κ) R => A (Sum.inl i) (Sum.inl j)) he
        simpa [Matrix.fromBlocks,Matrix.one_apply] using hh
      inv_val := by
        have he : (U⁻¹).val.val * U.val.val = 1 := U.val.inv_val
        rw [rightFixer_shape U⁻¹,rightFixer_shape U,Matrix.fromBlocks_multiply] at he
        ext i j
        have hh := congrArg (fun A : Matrix (ι ⊕ κ) (ι ⊕ κ) R => A (Sum.inl i) (Sum.inl j)) he
        simpa [Matrix.fromBlocks,Matrix.one_apply] using hh }
  map_one' := by apply Units.ext; ext i j; simp [Matrix.one_apply]
  map_mul' U V := by
    apply Units.ext
    change (U.val.val*V.val.val).submatrix Sum.inl Sum.inl =
      U.val.val.submatrix Sum.inl Sum.inl * V.val.val.submatrix Sum.inl Sum.inl
    ext i j
    change (U.val.val*V.val.val) (Sum.inl i) (Sum.inl j) = _
    conv_lhs => rw [rightFixer_shape U,rightFixer_shape V,Matrix.fromBlocks_multiply]
    simp

def fixer (S : Finset ι) : Subgroup (Matrix ι ι R)ˣ :=
  ⨅ k : {k // k ∈ S}, MulAction.stabilizer (Matrix ι ι R)ˣ (Pi.single k.val (1 : R) : ι → R)

lemma mem_fixer_iff (S : Finset ι) (U : (Matrix ι ι R)ˣ) :
    U ∈ fixer S ↔ ∀ k ∈ S, ∀ i, U.val i k = (1 : Matrix ι ι R) i k := by
  simp only [fixer,Subgroup.mem_iInf,MulAction.mem_stabilizer_iff]
  constructor
  · intro h k hk i
    have hh := congrFun (h ⟨k,hk⟩) i
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh
  · intro h k
    ext i
    have hh := h k.val k.property i
    simpa [Units.smul_def,Matrix.mulVec_single_one,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm] using hh

def splitEquiv (S : Finset ι) : {i // i ∉ S} ⊕ {i // i ∈ S} ≃ ι :=
  (Equiv.sumComm _ _).trans (Equiv.Set.sumCompl (S : Set ι))

omit [Fintype ι] in
@[simp] lemma splitEquiv_inl (S : Finset ι) (i : {i // i ∉ S}) : splitEquiv S (.inl i) = i.val := rfl
omit [Fintype ι] in
@[simp] lemma splitEquiv_inr (S : Finset ι) (i : {i // i ∈ S}) : splitEquiv S (.inr i) = i.val := rfl

lemma relabel_fixer_right (S : Finset ι) {U : (Matrix ι ι R)ˣ} (hU : U ∈ fixer S) :
    relabel (splitEquiv S).symm U ∈ rightFixer := by
  apply (mem_rightFixer_iff _).mpr
  intro i k
  have he := (mem_fixer_iff S U).mp hU k.val k.property (splitEquiv S i)
  change U.val (splitEquiv S i) k.val = (1 : Matrix _ _ R) i (Sum.inr k)
  rw [he]
  change (if splitEquiv S i = splitEquiv S (Sum.inr k) then (1 : R) else 0) =
    if i = Sum.inr k then 1 else 0
  congr 1
  exact propext (splitEquiv S).injective.eq_iff

lemma singleDiagonal_mem_fixer (S : Finset ι) (i : ι) (u : Rˣ) (hi : i ∉ S) :
    singleDiagonal i u ∈ fixer S := by
  apply (mem_fixer_iff S _).mpr
  intro k hk l
  have hki : k ≠ i := fun he => hi (he ▸ hk)
  by_cases hl : l = k
  · subst l; simp [singleDiagonal,diagonal,hki]
  · simp [singleDiagonal,diagonal,hl]

end
end SourceBurnside.Stability.MatrixGenerators

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma card_triple_le (i j k : ι) : ({i,j,k} : Finset ι).card ≤ 5 := by
  have h1 := Finset.card_insert_le i ({j,k} : Finset ι)
  have h2 := Finset.card_insert_le j ({k} : Finset ι)
  simp only [Finset.card_singleton] at h2
  omega

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
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.MatrixGenerators
noncomputable section
open Classical Matrix
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def permutation : Equiv.Perm ι →* (Matrix ι ι R)ˣ := Matrix.permMatrixHom.toHomUnits

@[simp] lemma permutation_val (p : Equiv.Perm ι) :
    (permutation (R := R) p).val = p⁻¹.permMatrix R := rfl

lemma permutation_entry (p : Equiv.Perm ι) (i j : ι) :
    (permutation (R := R) p).val i j = if i=p j then 1 else 0 := by
  simp only [permutation_val,Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,Option.mem_some_iff]
  congr 1
  exact propext (p.symm_apply_eq)

lemma permutation_mul (p : Equiv.Perm ι) (A : Matrix ι ι R) :
    (permutation p).val * A = A.submatrix p.symm id := by
  exact PEquiv.toMatrix_toPEquiv_mul p.symm A

lemma mul_permutation (A : Matrix ι ι R) (p : Equiv.Perm ι) :
    A * (permutation p).val = A.submatrix id p := by
  exact PEquiv.mul_toMatrix_toPEquiv A p.symm

lemma permutation_conjugate (p : Equiv.Perm ι) (U : (Matrix ι ι R)ˣ) :
    permutation p * U * (permutation p)⁻¹ = relabel p U := by
  apply Units.ext
  rw [Units.val_mul,Units.val_mul,←map_inv,permutation_mul,mul_permutation]
  rfl

lemma permutation_conjugate_diagonal (p : Equiv.Perm ι) (i : ι) (u : Rˣ) :
    permutation p * singleDiagonal i u * (permutation p)⁻¹ = singleDiagonal (p i) u := by
  rw [permutation_conjugate,relabel_singleDiagonal]

end
end SourceBurnside.Stability.MatrixGenerators

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
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_SmallSwapActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma card_quad_le (i j k l : ι) : ({i,j,k,l}:Finset ι).card ≤ 5 := by
  have h1 := Finset.card_insert_le i ({j,k,l}:Finset ι)
  have h2 := Finset.card_insert_le j ({k,l}:Finset ι)
  have h3 := Finset.card_insert_le k ({l}:Finset ι)
  simp only [Finset.card_singleton] at h3
  omega

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.FrameTransport
noncomputable section
open Classical
variable {V F W : Type*} [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)

def Edge (u v : V) : Prop := u ≠ v ∧ LinearIndepOn F ρ {u,v}

lemma Edge.symm {u v : V} (h : Edge (F := F) ρ u v) : Edge (F := F) ρ v u :=
  ⟨h.1.symm, by simpa [Set.pair_comm] using h.2⟩

lemma edge_outside {u v : V} (hu : ρ u ≠ 0)
    (hv : ρ v ∉ Submodule.span F (ρ '' {u})) : Edge (F := F) ρ u v := by
  refine ⟨?_, ?_⟩
  · intro he
    subst v
    exact hv (Submodule.subset_span ⟨u, by simp, rfl⟩)
  · have hi : LinearIndepOn F ρ ({u} : Set V) := (linearIndepOn_singleton_iff F).mpr hu
    simpa [Set.pair_comm] using hi.insert hv

lemma edge_to_cone {s : Set V} {v w : V} (hv : v ∈ s) (hn : ρ v ≠ 0)
    (hw : ρ w ∉ Submodule.span F (ρ '' s)) : Edge (F := F) ρ v w :=
  edge_outside ρ hn (fun he => hw (Submodule.span_mono (Set.image_mono (by simpa using hv)) he))

lemma triangle_to_cone {s : Set V} {u v w : V} (hu : u ∈ s) (hv : v ∈ s)
    (huv : Edge (F := F) ρ u v) (hw : ρ w ∉ Submodule.span F (ρ '' s)) :
    LinearIndepOn F ρ {u,v,w} := by
  have hx : ρ w ∉ Submodule.span F (ρ '' ({u,v} : Set V)) := by
    have hsub : ({u,v} : Set V) ⊆ s := by
      intro x hx
      rcases hx with rfl | hx
      · exact hu
      · exact Set.mem_singleton_iff.mp hx ▸ hv
    exact fun he => hw (Submodule.span_mono (Set.image_mono hsub) he)
  have hi := huv.2.insert hx
  have he : ({u,v,w} : Set V) = insert w {u,v} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [he]
  exact hi

structure FlatSystem (A : V → Type*) where
  step : ∀ (u v : V), Edge (F := F) ρ u v → A u ≃ A v
  reverse : ∀ (u v : V) (h : Edge (F := F) ρ u v),
    (step u v h).trans (step v u (h.symm ρ)) = Equiv.refl (A u)
  triangle : ∀ (u v w : V) (huv : Edge (F := F) ρ u v)
    (hvw : Edge (F := F) ρ v w) (huw : Edge (F := F) ρ u w),
    LinearIndepOn F ρ {u,v,w} → (step u v huv).trans (step v w hvw) = step u w huw

variable (hnz : ∀v, ρ v ≠ 0) (C : Frames.ConeSupply (F := F) ρ 5)
variable (o : V)

def connector (v : V) : V := C.pick {o,v}

lemma connector_outside (v : V) :
    ρ (connector ρ C o v) ∉ Submodule.span F (ρ '' ({o,v} : Set V)) := by
  simpa only [connector, Finset.coe_insert, Finset.coe_singleton] using
    C.outside {o,v} (by have h := Finset.card_insert_le o ({v} : Finset V); simp at h; omega)

include hnz

lemma base_connector (v : V) : Edge (F := F) ρ o (connector ρ C o v) :=
  edge_to_cone ρ (by simp) (hnz o) (connector_outside ρ C o v)

lemma vertex_connector (v : V) : Edge (F := F) ρ v (connector ρ C o v) :=
  edge_to_cone ρ (by simp) (hnz v) (connector_outside ρ C o v)

variable {A : V → Type*} (D : FlatSystem (F := F) ρ A)

def canonical (v : V) : A o ≃ A v :=
  (D.step o (connector ρ C o v) (base_connector ρ hnz C o v)).trans
    (D.step (connector ρ C o v) v ((vertex_connector ρ hnz C o v).symm ρ))

lemma canonical_base : canonical ρ hnz C o D o = Equiv.refl (A o) :=
  D.reverse o _ (base_connector ρ hnz C o o)

lemma canonical_to_cone {s : Set V} {v w : V}
    (ho : o ∈ s) (hv : v ∈ s) (hc : connector ρ C o v ∈ s)
    (hw : ρ w ∉ Submodule.span F (ρ '' s)) (a : A o) :
    D.step v w (edge_to_cone ρ hv (hnz v) hw) (canonical ρ hnz C o D v a) =
      D.step o w (edge_to_cone ρ ho (hnz o) hw) a := by
  have ht1 := D.triangle o (connector ρ C o v) w (base_connector ρ hnz C o v)
    (edge_to_cone ρ hc (hnz _) hw) (edge_to_cone ρ ho (hnz o) hw)
    (triangle_to_cone ρ ho hc (base_connector ρ hnz C o v) hw)
  have ht2 := D.triangle (connector ρ C o v) v w ((vertex_connector ρ hnz C o v).symm ρ)
    (edge_to_cone ρ hv (hnz _) hw) (edge_to_cone ρ hc (hnz _) hw)
    (triangle_to_cone ρ hc hv ((vertex_connector ρ hnz C o v).symm ρ) hw)
  have he2 := Equiv.congr_fun ht2 (D.step o _ (base_connector ρ hnz C o v) a)
  have he1 := Equiv.congr_fun ht1 a
  exact he2.trans he1

theorem canonical_edge (u v : V) (huv : Edge (F := F) ρ u v) (a : A o) :
    D.step u v huv (canonical ρ hnz C o D u a) = canonical ρ hnz C o D v a := by
  let s : Finset V := {o,u,v,connector ρ C o u,connector ρ C o v}
  have hs : s.card ≤ 5 := by
    have h₁ := Finset.card_insert_le o ({u,v,connector ρ C o u,connector ρ C o v} : Finset V)
    have h₂ := Finset.card_insert_le u ({v,connector ρ C o u,connector ρ C o v} : Finset V)
    have h₃ := Finset.card_insert_le v ({connector ρ C o u,connector ρ C o v} : Finset V)
    have h₄ := Finset.card_insert_le (connector ρ C o u) ({connector ρ C o v} : Finset V)
    simp only [Finset.card_singleton] at h₄
    dsimp [s]
    omega
  let w := C.pick s
  have hw : ρ w ∉ Submodule.span F (ρ '' (s : Set V)) := C.outside s hs
  have ho : o ∈ (s : Set V) := by simp [s]
  have hu : u ∈ (s : Set V) := by simp [s]
  have hv : v ∈ (s : Set V) := by simp [s]
  have hcu : connector ρ C o u ∈ (s : Set V) := by simp [s]
  have hcv : connector ρ C o v ∈ (s : Set V) := by simp [s]
  apply (D.step v w (edge_to_cone ρ hv (hnz v) hw)).injective
  have ht := D.triangle u v w huv (edge_to_cone ρ hv (hnz v) hw)
    (edge_to_cone ρ hu (hnz u) hw) (triangle_to_cone ρ hu hv huv hw)
  have ht' := Equiv.congr_fun ht (canonical ρ hnz C o D u a)
  exact ht'.trans ((canonical_to_cone ρ hnz C o D ho hu hcu hw a).trans
    (canonical_to_cone ρ hnz C o D ho hv hcv hw a).symm)

include C

theorem unique_section (a : A o) :
    ∃! f : ∀v, A v, f o = a ∧ ∀u v (h : Edge (F := F) ρ u v), D.step u v h (f u) = f v := by
  refine ⟨fun v => canonical ρ hnz C o D v a, ⟨?_, ?_⟩, ?_⟩
  · exact Equiv.congr_fun (canonical_base ρ hnz C o D) a
  · intro u v h
    exact canonical_edge ρ hnz C o D u v h a
  · intro f hf
    funext v
    rw [← hf.2 (connector ρ C o v) v ((vertex_connector ρ hnz C o v).symm ρ),
      ← hf.2 o (connector ρ C o v) (base_connector ρ hnz C o v), hf.1]
    rfl

end
end SourceBurnside.Stability.FrameTransport

end
section
namespace SourceBurnside.Stability.ColumnFrames
noncomputable section
open Classical MatrixGenerators
open scoped Matrix
variable {R ι : Type*} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

def residue (v : ι → R) : ι → ZMod 2 := fun i => ε (v i)
def Vertex := {v : ι → R // residue ε v ≠ 0}
def rho (v : Vertex (ι := ι) ε) : ι → ZMod 2 := residue ε v.val

def standard (i : ι) : Vertex (ι := ι) ε :=
  ⟨Pi.single i 1,by intro hz; have hh := congrFun hz i; simp [residue] at hh⟩

@[simp] lemma rho_standard (i : ι) : rho ε (standard ε i) = (Pi.basisFun (ZMod 2) ι) i := by
  ext j
  by_cases h : j=i <;> simp [rho,standard,residue,h]

lemma standard_injective : Function.Injective (standard (ι := ι) ε) := by
  intro i j h
  have hh := congrArg (rho ε) h
  simpa only [rho_standard] using (Pi.basisFun (ZMod 2) ι).injective (by simpa using hh)

lemma rho_spanning : Submodule.span (ZMod 2) (Set.range (rho (ι := ι) ε)) = ⊤ := by
  apply top_unique
  rw [←(Pi.basisFun (ZMod 2) ι).span_eq]
  apply Submodule.span_mono
  rintro v ⟨i,rfl⟩
  exact ⟨standard ε i,rho_standard ε i⟩

def reduce : (Matrix ι ι R)ˣ →* (Matrix ι ι (ZMod 2))ˣ := Units.map ε.toRingHom.mapMatrix.toMonoidHom

lemma residue_smul (U : (Matrix ι ι R)ˣ) (v : ι → R) :
    residue ε (U • v) = reduce ε U • residue ε v := by
  ext i
  change ε (∑ j, U.val i j * v j) = ∑ j, ε (U.val i j) * ε (v j)
  simp

instance instMulActionUnitsMatrixVertex : MulAction (Matrix ι ι R)ˣ (Vertex (ι := ι) ε) where
  smul U v := ⟨U • v.val,by
    rw [residue_smul]
    intro hz
    exact v.property ((MulAction.injective (reduce ε U)) (hz.trans (smul_zero _).symm))⟩
  one_smul v := Subtype.ext (one_smul _ _)
  mul_smul U V v := Subtype.ext (mul_smul U V v.val)

@[simp] lemma smul_val (U : (Matrix ι ι R)ˣ) (v : Vertex (ι := ι) ε) : (U • v).val = U • v.val := rfl
@[simp] lemma rho_smul (U : (Matrix ι ι R)ˣ) (v : Vertex (ι := ι) ε) :
    rho ε (U • v) = reduce ε U • rho ε v := residue_smul ε U v.val

lemma independent_map (U : (Matrix ι ι R)ˣ) {s : Set (Vertex (ι := ι) ε)}
    (hs : LinearIndepOn (ZMod 2) (rho ε) s) :
    LinearIndepOn (ZMod 2) (rho ε) ((fun v => U • v) '' s) := by
  have hh := hs.map_injOn (Matrix.mulVecLin (reduce ε U).val)
    (fun a _ b _ h => (MulAction.injective (reduce ε U)) h)
  have hh' : LinearIndepOn (ZMod 2) (rho ε ∘ fun v => U • v) s :=
    hh.congr (fun v _ => (rho_smul ε U v).symm)
  exact hh'.image_of_comp (fun v => U • v) (rho ε)

lemma edge_map (U : (Matrix ι ι R)ˣ) (u v : Vertex (ι := ι) ε)
    (h : FrameTransport.Edge (F := ZMod 2) (rho ε) u v) : FrameTransport.Edge (F := ZMod 2) (rho ε) (U • u) (U • v) := by
  refine ⟨(MulAction.injective U).ne h.1,?_⟩
  simpa only [Set.image_insert_eq,Set.image_singleton] using independent_map ε U h.2

lemma triangle_map (U : (Matrix ι ι R)ˣ) (u v w : Vertex (ι := ι) ε)
    (h : LinearIndepOn (ZMod 2) (rho ε) {u,v,w}) :
    LinearIndepOn (ZMod 2) (rho ε) {U•u,U•v,U•w} := by
  simpa only [Set.image_insert_eq,Set.image_singleton] using independent_map ε U h

lemma standard_independent (S : Set ι) : LinearIndepOn (ZMod 2) (rho ε) (standard ε '' S) := by
  have hh : LinearIndependent (ZMod 2) (rho ε ∘ standard (ι := ι) ε) := by
    simpa only [Function.comp_def,rho_standard] using (Pi.basisFun (ZMod 2) ι).linearIndependent
  exact (hh.linearIndepOn S).image_of_comp (standard ε) (rho ε)

lemma standard_edge (i j : ι) (h : i≠j) : FrameTransport.Edge (F := ZMod 2) (rho ε) (standard ε i) (standard ε j) := by
  refine ⟨(standard_injective ε).ne h,?_⟩
  simpa only [Set.image_insert_eq, Set.image_singleton] using standard_independent ε ({i,j}:Set ι)

lemma standard_triangle (i j k : ι) :
    LinearIndepOn (ZMod 2) (rho ε) {standard ε i,standard ε j,standard ε k} := by
  simpa only [Set.image_insert_eq, Set.image_singleton] using standard_independent ε ({i,j,k}:Set ι)

end
end SourceBurnside.Stability.ColumnFrames

end
section
namespace SourceBurnside.Stability.ColumnFrames
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
open scoped Matrix
variable {R ι : Type*} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

lemma pair_injective {A : Type*} (a b : A) (hab : a≠b) : Function.Injective ![a,b] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

lemma triple_injective {A : Type*} (a b c : A) (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    Function.Injective ![a,b,c] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

end
end SourceBurnside.Stability.ColumnFrames

end
section
namespace SourceBurnside.Stability.CosetTransport
noncomputable section
open Classical FrameTransport
variable {H V F W : Type*} [Group H] [MulAction H V]
variable [DivisionRing F] [AddCommGroup W] [Module F W]
variable (ρ : V → W)

structure Data where
  P : Subgroup H
  o : V
  a : V
  b : V
  s : H
  t : H
  fix : ∀p ∈ P, p • o = o
  sa : s • o = a
  ss : s*s = 1
  sb : s • b = b
  tm : t ∈ P
  ta : t • a = b
  braid : s*t*s = t*s*t
  base : LinearIndepOn F ρ {o,a,b}
  oa : Edge (F := F) ρ o a
  edge_map : ∀(g : H) u v, Edge (F := F) ρ u v → Edge (F := F) ρ (g • u) (g • v)
  tri_map : ∀(g : H) u v w, LinearIndepOn F ρ {u,v,w} → LinearIndepOn F ρ {g•u,g•v,g•w}
  edge_trans : ∀v, Edge (F := F) ρ o v → ∃p ∈ P, p • a = v
  tri_trans : ∀v w, o≠v → o≠w → v≠w → LinearIndepOn F ρ {o,v,w} →
    ∃p ∈ P, p • a = v ∧ p • b = w
  qnorm : ∀p ∈ P, p • a = a → s⁻¹*p*s ∈ P
  generates : Subgroup.closure ((P : Set H) ∪ {s}) = ⊤

variable (D : Data (H := H) (F := F) ρ)

def point : H ⧸ D.P → V := Quotient.lift (fun h : H => h • D.o) (by
  intro h k hk
  have hp := D.fix (h⁻¹*k) ((QuotientGroup.leftRel_apply).mp hk)
  calc h • D.o = h • ((h⁻¹*k) • D.o) := by rw [hp]
       _ = k • D.o := by simp [mul_smul])

@[simp] lemma point_mk (h : H) : point ρ D (QuotientGroup.mk h) = h • D.o := rfl

def Fiber (v : V) := {c : H ⧸ D.P // point ρ D c = v}

def Arrow (x y : H ⧸ D.P) : Prop := ∃h : H,
  QuotientGroup.mk h = x ∧ QuotientGroup.mk (h*D.s) = y

lemma arrow_reverse {x y : H ⧸ D.P} (h : Arrow ρ D x y) : Arrow ρ D y x := by
  obtain ⟨g,rfl,rfl⟩ := h
  refine ⟨g*D.s,rfl,?_⟩
  simp [mul_assoc,D.ss]

lemma arrow_edge {x y : H ⧸ D.P} (h : Arrow ρ D x y) :
    Edge (F := F) ρ (point ρ D x) (point ρ D y) := by
  obtain ⟨g,rfl,rfl⟩ := h
  simpa [mul_smul,D.sa] using D.edge_map g D.o D.a D.oa

lemma arrow_unique {x y z : H ⧸ D.P} (hxy : Arrow ρ D x y) (hxz : Arrow ρ D x z)
    (he : point ρ D y = point ρ D z) : y = z := by
  obtain ⟨g,rfl,rfl⟩ := hxy
  obtain ⟨h,hh,rfl⟩ := hxz
  have hp : g⁻¹*h ∈ D.P := QuotientGroup.eq.mp hh.symm
  have ha : (g⁻¹*h) • D.a = D.a := by
    have eh : g • D.a = h • D.a := by simpa [mul_smul,D.sa] using he
    simpa [mul_smul] using congrArg (fun v => g⁻¹ • v) eh.symm
  apply QuotientGroup.eq.mpr
  simpa [mul_inv_rev,mul_assoc] using D.qnorm _ hp ha

lemma arrow_exists (u v : V) (he : Edge (F := F) ρ u v) (x : Fiber ρ D u) :
    ∃y : Fiber ρ D v, Arrow ρ D x.val y.val := by
  obtain ⟨g,hg⟩ := QuotientGroup.mk_surjective (x.val)
  have hgu : g • D.o = u := by rw [← point_mk ρ D g,hg]; exact x.property
  have hne : Edge (F := F) ρ D.o (g⁻¹ • v) := by
    have hh := D.edge_map g⁻¹ u v he
    simpa [← hgu] using hh
  obtain ⟨p,hp,ep⟩ := D.edge_trans _ hne
  have hy : point ρ D (QuotientGroup.mk (g*p*D.s)) = v := by
    simp only [point_mk,mul_smul,D.sa,ep,smul_inv_smul]
  refine ⟨⟨QuotientGroup.mk (g*p*D.s),hy⟩,g*p,?_,rfl⟩
  rw [QuotientGroup.mk_mul_of_mem g hp,hg]

lemma arrow_triangle {x y z : H ⧸ D.P} (hxy : Arrow ρ D x y) (hyz : Arrow ρ D y z)
    (hn : point ρ D x ≠ point ρ D z)
    (ht : LinearIndepOn F ρ {point ρ D x, point ρ D y, point ρ D z}) :
    Arrow ρ D x z := by
  obtain ⟨g,hg⟩ := QuotientGroup.mk_surjective x
  have htri : LinearIndepOn F ρ {D.o,g⁻¹ • point ρ D y,g⁻¹ • point ρ D z} := by
    have hh := D.tri_map g⁻¹ _ _ _ ht
    simpa [← hg] using hh
  have hxg : g⁻¹ • point ρ D x = D.o := by simp [←hg]
  have h₁ := (MulAction.injective g⁻¹).ne (arrow_edge ρ D hxy).1
  have h₂ := (MulAction.injective g⁻¹).ne hn
  have h₃ := (MulAction.injective g⁻¹).ne (arrow_edge ρ D hyz).1
  rw [hxg] at h₁ h₂
  obtain ⟨p,hp,ha,hb⟩ := D.tri_trans _ _ h₁ h₂ h₃ htri
  let k := g*p
  have hk : QuotientGroup.mk k = x := by dsimp [k]; rw [QuotientGroup.mk_mul_of_mem g hp,hg]
  have hka : k • D.a = point ρ D y := by simp [k,mul_smul,ha]
  have hkb : k • D.b = point ρ D z := by simp [k,mul_smul,hb]
  have hy : QuotientGroup.mk (k*D.s) = y := by
    apply arrow_unique ρ D ⟨k,hk,rfl⟩ hxy
    simpa [point_mk,mul_smul,D.sa] using hka
  have hz : QuotientGroup.mk (k*D.s*D.t*D.s) = z := by
    refine arrow_unique ρ D ⟨k*D.s*D.t,?_,rfl⟩ hyz ?_
    · rw [QuotientGroup.mk_mul_of_mem _ D.tm,hy]
    · simpa [point_mk,mul_smul,D.sa,D.ta,D.sb] using hkb
  have he : QuotientGroup.mk (k*D.s*D.t*D.s) =
      (QuotientGroup.mk (k*D.t*D.s) : H ⧸ D.P) := by
    calc QuotientGroup.mk (k*D.s*D.t*D.s) = QuotientGroup.mk (k*(D.s*D.t*D.s)) := by
           congr 1; group
         _ = QuotientGroup.mk ((k*D.t*D.s)*D.t) := by rw [D.braid]; congr 1; group
         _ = _ := QuotientGroup.mk_mul_of_mem _ D.tm
  refine ⟨k*D.t,?_,he.symm.trans hz⟩
  rw [QuotientGroup.mk_mul_of_mem _ D.tm,hk]

def next (u v : V) (he : Edge (F := F) ρ u v) (x : Fiber ρ D u) : Fiber ρ D v :=
  (arrow_exists ρ D u v he x).choose

lemma next_arrow (u v : V) (he : Edge (F := F) ρ u v) (x : Fiber ρ D u) :
    Arrow ρ D x.val (next ρ D u v he x).val := (arrow_exists ρ D u v he x).choose_spec

lemma next_eq {u v : V} {he : Edge (F := F) ρ u v} {x : Fiber ρ D u} {y : Fiber ρ D v}
    (h : Arrow ρ D x.val y.val) : next ρ D u v he x = y :=
  Subtype.ext (arrow_unique ρ D (next_arrow ρ D u v he x) h
    ((next ρ D u v he x).property.trans y.property.symm))

lemma next_reverse (u v : V) (he : Edge (F := F) ρ u v) (x : Fiber ρ D u) :
    next ρ D v u (he.symm ρ) (next ρ D u v he x) = x :=
  next_eq ρ D (arrow_reverse ρ D (next_arrow ρ D u v he x))

def system : FlatSystem (F := F) ρ (Fiber ρ D) where
  step u v he :=
    { toFun := next ρ D u v he
      invFun := next ρ D v u (he.symm ρ)
      left_inv := next_reverse ρ D u v he
      right_inv := next_reverse ρ D v u (he.symm ρ) }
  reverse u v he := Equiv.ext (next_reverse ρ D u v he)
  triangle u v w huv hvw huw ht := by
    apply Equiv.ext
    intro x
    apply (next_eq ρ D (he := huw) (x := x) (y := next ρ D v w hvw (next ρ D u v huv x)) ?_).symm
    apply arrow_triangle ρ D (next_arrow ρ D u v huv x)
      (next_arrow ρ D v w hvw (next ρ D u v huv x))
    · simpa only [x.property,(next ρ D v w hvw (next ρ D u v huv x)).property] using huw.1
    simpa only [x.property,(next ρ D u v huv x).property,
      (next ρ D v w hvw (next ρ D u v huv x)).property] using ht

theorem point_injective (hnz : ∀v, ρ v ≠ 0) (C : Frames.ConeSupply (F := F) ρ 5) :
    Function.Injective (point ρ D) := by
  let x₀ : Fiber ρ D D.o := ⟨QuotientGroup.mk 1,by simp⟩
  obtain ⟨f,⟨hf₀,hf⟩,_⟩ := unique_section ρ hnz C D.o (system ρ D) x₀
  let ψ : V → H ⧸ D.P := fun v => (f v).val
  have hψ (v : V) : point ρ D (ψ v) = v := (f v).property
  have step_value (u v : V) (he : Edge (F := F) ρ u v) :
      Arrow ρ D (ψ u) (ψ v) := by
    have hh := next_arrow ρ D u v he (f u)
    have heq : next ρ D u v he (f u) = f v := hf u v he
    rw [heq] at hh
    exact hh
  have all (g : H) : QuotientGroup.mk g = ψ (g • D.o) := by
    have hg : g ∈ Subgroup.closure ((D.P : Set H) ∪ {D.s}) := by rw [D.generates]; trivial
    induction hg using Subgroup.closure_induction_right with
    | one => simpa only [one_smul] using (show QuotientGroup.mk 1 = ψ D.o from congrArg Subtype.val hf₀.symm)
    | mul_right g hg k hk ih =>
      rcases hk with hp | hs
      · simpa only [mul_smul,D.fix k hp] using
          (QuotientGroup.mk_mul_of_mem g hp).trans ih
      · obtain rfl := Set.mem_singleton_iff.mp hs
        have he := D.edge_map g D.o D.a D.oa
        have ha : Arrow ρ D (ψ (g • D.o)) (QuotientGroup.mk (g*D.s)) := ⟨g,ih,rfl⟩
        simpa only [mul_smul,D.sa] using (arrow_unique ρ D (step_value _ _ he) ha
          (by simp only [point_mk,hψ,mul_smul,D.sa])).symm
    | mul_inv_cancel g hg k hk ih =>
      rcases hk with hp | hs
      · simpa only [mul_smul,D.fix k⁻¹ (D.P.inv_mem hp)] using
          (QuotientGroup.mk_mul_of_mem g (D.P.inv_mem hp)).trans ih
      · obtain rfl := Set.mem_singleton_iff.mp hs
        have hsi : D.s⁻¹ = D.s := inv_eq_of_mul_eq_one_right D.ss
        rw [hsi]
        have he := D.edge_map g D.o D.a D.oa
        have ha : Arrow ρ D (ψ (g • D.o)) (QuotientGroup.mk (g*D.s)) := ⟨g,ih,rfl⟩
        simpa only [mul_smul,D.sa] using (arrow_unique ρ D (step_value _ _ he) ha
          (by simp only [point_mk,hψ,mul_smul,D.sa])).symm
  intro x y he
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨h,rfl⟩ := QuotientGroup.mk_surjective y
  rw [all g,all h]
  exact congrArg ψ he

end
end SourceBurnside.Stability.CosetTransport

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Presentation_SmallFaithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
open Classical
universe u v

end
end SourceBurnside.Stability.SmallPresentation

end
section
namespace SourceBurnside.Stability.SmallPresentation
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

variable [Algebra (ZMod 2) R]

lemma minus_one_unit : (-1 : Rˣ) = 1 := by
  apply Units.ext
  change (-1 : R) = 1
  have h := congrArg (algebraMap (ZMod 2) R) (show (-1 : ZMod 2) = 1 by decide)
  simpa only [map_neg, map_one] using h

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
lemma block_smul_right (U : (Matrix ι ι R)ˣ) (j : κ) :
    blockInclusion (κ := κ) U • (Pi.single (Sum.inr j) (1 : R) : ι ⊕ κ → R) =
      (Pi.single (Sum.inr j) 1 : ι ⊕ κ → R) := by
  ext k
  change (Matrix.mulVec (blockInclusion (κ := κ) U).val _ k) = _
  rw [Matrix.mulVec_single_one]
  cases k <;> simp [blockInclusion_val, Matrix.fromBlocks,Matrix.col,Pi.single_apply,Matrix.one_apply,eq_comm]

end SourceBurnside.Stability.MatrixK1

namespace SourceBurnside.Stability
open Classical MatrixGenerators MatrixK1 CategoryTheory
namespace ColumnRelabel
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (e : ι ≃ κ)

def coordinateEquiv {F : Type} [Semiring F] : (ι → F) ≃ₗ[F] (κ → F) where
  toFun v := v ∘ e.symm
  invFun v := v ∘ e
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' v w := rfl
  map_smul' c v := rfl

end ColumnRelabel
end SourceBurnside.Stability

end

end OAI
end


