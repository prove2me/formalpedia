-- Prove2me | Definitions.Def_OAIQ18Pg014
-- name    : OAIQ18Pg014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:13:21.742033+00:00
-- url     : https://prove2.me/theorems/7dac147b-1048-4728-8bc7-1f0f9efadae2
-- title:
--   Definitions bundle OAIQ18Pg014 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 11 definitions and 17 theorems. The definitions and types are `OAI.SourceBurnside.Stability.RationalKernel.J`, `OAI.SourceBurnside.Stability.RationalKernel.cast`, `OAI.SourceBurnside.Stability.RationalKernel.character`, `OAI.SourceBurnside.Stability.RationalKernel.kernelCast`, `OAI.SourceBurnside.Stability.RationalKernel.kernelStep`, `OAI.SourceBurnside.Stability.RationalKernel.liftKernel`, `OAI.SourceBurnside.Stability.RationalKernel.restriction`, `OAI.SourceBurnside.Stability.RationalKernel.restrictionIso`, `OAI.SourceBurnside.Stability.RationalKernel.step`, `OAI.SourceBurnside.Stability.SteinbergAction.matrixAction`, `OAI.SourceBurnside.Stability.SteinbergAction.presentationAction`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: [`PeriodicGroups_Homology_KernelStability`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Homology/KernelStability.lean), [`PeriodicGroups_Steinberg_RankActions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/PeriodicGroups/PeriodicGroups/Steinberg/RankActions.lean).
--
--   **Imports.** It imports the published bundle `Def_PeriodicGroup`; the bundles `OAIQ18Pg012` and `OAIQ18Pg013` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.SourceBurnside.thm_main`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg012
import Definitions.Def_OAIQ18Pg013

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_RankActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.SteinbergAction
section
open Classical Steinberg MatrixGenerators Kernel

variable {n : ℕ} {R : Type*} [Ring R]

lemma conj_preserves_row (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t) (a : R) :
    MulAut.conj (x p a)∈preservers (rowStrip t) := by
  have hh := away_le_row_normalizer (R := R) t
    (Subgroup.subset_closure ⟨p,a,hpt,hct,rfl⟩)
  intro g
  exact (Subgroup.mem_normalizer_iff.mp hh g).symm

end

section
open Classical Steinberg MatrixGenerators Kernel
variable {n : ℕ} {R : Type*} [Ring R]

lemma supported_row (S : Finset (Fin n)) (t : Fin n) (ht : t∉S) :
    SmallPresentation.supported (R := R) S ≤ (preservers (rowStrip t)).comap wordAction := by
  apply (Subgroup.closure_le _).mpr
  rintro w ⟨g,hg,rfl⟩
  change generatorAction g∈preservers (rowStrip t)
  cases g with
  | root i j h a =>
    have hi : i∈S := hg (by simp [SmallPresentation.Generator.support])
    have hj : j∈S := hg (by simp [SmallPresentation.Generator.support])
    exact conj_preserves_row t ⟨i,j,h⟩ (fun he => ht (he ▸ hi)) (fun he => ht (he ▸ hj)) a
  | diag i u => exact scale_preserves_strip _ _ _ _

lemma supported_relation_trivial (S : Finset (Fin n)) (t : Fin n) (ht : t∉S)
    (w : FreeGroup (GLGenerator (n := n) (R := R))) (hw : w∈SmallPresentation.supported S)
    (he : SmallPresentation.matrixWord w=1) : wordAction w=1 := by
  have hf (g : Steinberg n R) : Elementary.representation (wordAction w g) = Elementary.representation g := by
    rw [word_equivariant,he]
    simp
  apply identity_of_fixes_strips t (wordAction w)
  · intro g hg
    exact fixes_strip (wordAction w) hf _ _ _ (supported_column S t ht hw) hg
  · intro g hg
    exact fixes_strip (wordAction w) hf _ _ _ (supported_row S t ht hw) hg

lemma small_relation_trivial (hn : 6≤n) (w : FreeGroup (GLGenerator (n := n) (R := R)))
    (hw : w∈SmallPresentation.relations) : wordAction w=1 := by
  obtain ⟨he,S,hS,hs⟩ := hw
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := S) (t := Finset.univ)
    (by simpa using (by omega : S.card<n))
  exact supported_relation_trivial S t ht w hs he

def presentationAction (hn : 6≤n) : SmallPresentation.Group (ι := Fin n) (R := R) →* MulAut (Steinberg n R) :=
  PresentedGroup.toGroup (f := generatorAction) (fun w hw => small_relation_trivial hn w hw)

@[simp] lemma presentationAction_gen (hn : 6≤n) (g : GLGenerator (n := n) (R := R)) :
    presentationAction hn (SmallPresentation.gen g) = generatorAction g := PresentedGroup.toGroup.of _

end

open Classical Steinberg MatrixGenerators
variable {n : ℕ} {R : Type*} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom) (hn : 6≤n)

def matrixAction : (Matrix (Fin n) (Fin n) R)ˣ →* MulAut (Steinberg n R) :=
  (presentationAction hn).comp (SmallPresentation.equivalence ε hI (Fin n)).symm.toMonoidHom

lemma matrixAction_e (p : Root n) (a : R) :
    matrixAction ε hI hn (Elementary.e p a) = MulAut.conj (x p a) := by
  have he : SmallPresentation.equivalence ε hI (Fin n)
      (SmallPresentation.gen (.root p.row p.col p.ne a)) = Elementary.e p a := by
    rw [SmallPresentation.equivalence_apply,SmallPresentation.evaluate_gen]
    exact elementary_eq_e p a
  rw [←he]
  simp only [matrixAction,MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe,MulEquiv.symm_apply_apply,presentationAction_gen]
  rfl

lemma matrixAction_representation : (matrixAction ε hI hn).comp Elementary.representation =
    MulAut.conj (G := Steinberg n R) := by
  apply Steinberg.hom_ext
  intro p a
  simpa only [MonoidHom.comp_apply,Elementary.representation_x] using matrixAction_e ε hI hn p a

include ε hI hn in

theorem kernel_central : (Elementary.representation (n := n) (R := R)).ker ≤
    Subgroup.center (Steinberg n R) := by
  intro g hg
  have he : Elementary.representation g=1 := hg
  have hh := DFunLike.congr_fun (matrixAction_representation ε hI hn) g
  simp only [MonoidHom.comp_apply,he,map_one] at hh
  apply Subgroup.mem_center_iff.mpr
  intro h
  have hf := congrArg (fun f : MulAut (Steinberg n R) => f h) hh
  change h = g*h*g⁻¹ at hf
  exact (mul_inv_eq_iff_eq_mul.mp hf.symm).symm

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
section
open Classical CategoryTheory
namespace RationalKernel
open ElementaryRanks RationalBar
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]

abbrev J (n : ℕ) := (representation (R := R) (n := n)).ker
abbrev step (n : ℕ) : Steinberg n R →* Steinberg (n+1) R :=
  Steinberg.coordinateMap Fin.castSucc (Fin.castSucc_injective n)

variable (ε : R →ₐ[ZMod 2] ZMod 2)

def kernelStep (n : ℕ) : J (R := R) n →* J (R := R) (n+1) where
  toFun j := ⟨step n j.val,by
    change representation (step n j.val)=1
    have he := DFunLike.congr_fun (next_representation ε) j.val
    change (next ε n) (representation j.val)=representation (step n j.val) at he
    rw [j.property,map_one] at he
    exact he.symm⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' j k := Subtype.ext (map_mul _ _ _)

variable {ε}
lemma central (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 6≤n) :
    J (R := R) n ≤ Subgroup.center (Steinberg n R) := by
  rw [J,rep_kernel]
  exact SteinbergAction.kernel_central ε hI hn

variable {n : ℕ} {X : Type} [Group X] (S : RationalExtension X (Group (R := R) n))

def liftKernel : J (R := R) n →* S.rightHom.ker where
  toFun j := ⟨ExtensionRootLift.hom S j.val,by
    have h := DFunLike.congr_fun (ExtensionRootLift.hom_projection S) j.val
    exact h.trans j.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' j k := Subtype.ext (map_mul _ _ _)

def character : J (R := R) n →* QGroup := S.kernelEquiv.symm.toMonoidHom.comp (liftKernel S)
lemma inl_character (j : J (R := R) n) : S.inl (character S j)=ExtensionRootLift.hom S j.val := by
  exact congrArg Subtype.val (S.kernelEquiv.apply_symm_apply (liftKernel S j))

variable (ε)

theorem restriction_surjective (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n) :
    Function.Surjective (fun ψ : J (R := R) (n+1) →* QGroup => ψ.comp (kernelStep ε n)) := by
  intro φ
  let p := representation (R := R) (n := n)
  have hc : p.ker ≤ Subgroup.center (Steinberg n R) := central hI n (by omega)
  let S := CentralPushout.extension p hc φ (representation_surjective n)
  let c := S.cocycle
  let f := next ε n
  have : IsIso (RationalHomology.map f 2) := next_h2_isIso ε hI n hn
  obtain ⟨d,b,hb⟩ := extend f c
  let D := extension d
  let M : CentralPushout.Extension p hc φ →* Extension d :=
    (morphism f c d b hb).comp S.modelEquiv.symm.toMulEquiv.toMonoidHom
  have Minl (q : QGroup) : M (S.inl q)=D.inl q := by
    change morphism f c d b hb (S.modelEquiv.symm (S.inl q))=inclusion d q
    rw [S.modelEquiv.symm.map_inl]
    exact morphism_inclusion f c d b hb q
  have Mprojection (x : CentralPushout.Extension p hc φ) : D.rightHom (M x)=f (S.rightHom x) := by
    change projection d (morphism f c d b hb (S.modelEquiv.symm x))=f (S.rightHom x)
    rw [morphism_projection]
    exact congrArg f (S.modelEquiv.symm.rightHom_map x)
  let F := M.comp (CentralPushout.canonical p hc φ)
  let L := (ExtensionRootLift.hom D).comp (step n)
  have he : F=L := by
    apply ExtensionRootLift.unique_over D
    apply MonoidHom.ext
    intro u
    change D.rightHom (M (CentralPushout.canonical p hc φ u))=D.rightHom (ExtensionRootLift.hom D (step n u))
    rw [Mprojection]
    have hx := DFunLike.congr_fun (ExtensionRootLift.hom_projection D) (step n u)
    change D.rightHom (ExtensionRootLift.hom D (step n u))=representation (step n u) at hx
    rw [hx]
    exact DFunLike.congr_fun (next_representation ε) u
  refine ⟨character D,?_⟩
  ext j
  apply D.inl_injective
  change D.inl (character D (kernelStep ε n j))=D.inl (φ j)
  rw [inl_character]
  change L j.val = _
  rw [←he]
  change M (CentralPushout.canonical p hc φ j.val)=_
  rw [CentralPushout.canonical_kernel]
  exact Minl (φ j)

end RationalKernel
end

open Classical
end SourceBurnside.Stability

namespace SourceBurnside.Stability.RationalKernel
section
open Classical CategoryTheory ElementaryRanks RationalBar
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

def restriction (n : ℕ) : (J (R := R) (n+1) →* QGroup) →* (J (R := R) n →* QGroup) where
  toFun ψ := ψ.comp (kernelStep ε n)
  map_one' := by apply MonoidHom.ext; intro j; rfl
  map_mul' ψ χ := by apply MonoidHom.ext; intro j; rfl

lemma restriction_eq_one (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n)
    (ψ : J (R := R) (n+1) →* QGroup) (hψ : ψ.comp (kernelStep ε n)=1) : ψ=1 := by
  let p := representation (R := R) (n := n+1)
  have hc : p.ker ≤ Subgroup.center (Steinberg (n+1) R) := central hI (n+1) (by omega)
  let S := CentralPushout.extension p hc ψ (representation_surjective (n+1))
  let c := S.cocycle
  let F := (CentralPushout.canonical p hc ψ).comp (step n)
  have hk : (representation (R := R) (n := n)).ker ≤ F.ker := by
    intro u hu
    let j : J (R := R) n := ⟨u,hu⟩
    have he : ψ (kernelStep ε n j)=1 := DFunLike.congr_fun hψ j
    have hh := CentralPushout.canonical_kernel p hc ψ (kernelStep ε n j)
    change F u=1
    change CentralPushout.canonical p hc ψ (step n u)=1
    exact hh.trans (by rw [he,map_one])
  let s₀ := SurjectiveDescent.descend representation (representation_surjective n) F hk
  let s := S.modelEquiv.symm.toMulEquiv.toMonoidHom.comp s₀
  have hs : (projection c).comp s=next ε n := by
    apply MonoidHom.ext
    intro g
    obtain ⟨u,rfl⟩ := representation_surjective n g
    change projection c (S.modelEquiv.symm (SurjectiveDescent.descend representation
      (representation_surjective n) F hk (representation u)))=next ε n (representation u)
    rw [SurjectiveDescent.descend_apply]
    exact (S.modelEquiv.symm.rightHom_map (F u)).trans
      (DFunLike.congr_fun (next_representation ε) u).symm
  have : IsIso (RationalHomology.map (next ε n) 2) := next_h2_isIso ε hI n hn
  obtain ⟨b,hb⟩ := (pull_coboundary_iff (next ε n) c).mp (coboundary_of_lift (next ε n) c s hs)
  have hb' : (pull (MonoidHom.id _) c).val=b.comp (d2 _) := by rw [pull_id]; exact hb
  let t := liftOfCoboundary (MonoidHom.id _) c b hb'
  let L := (S.modelHom.comp t).comp p
  have he : CentralPushout.canonical p hc ψ=L := by
    apply ExtensionRootLift.unique_over S
    apply MonoidHom.ext
    intro u
    change S.rightHom (CentralPushout.canonical p hc ψ u)=S.rightHom (S.modelHom (t (p u)))
    rw [S.modelHom_projection]
    rfl
  apply MonoidHom.ext
  intro j
  apply S.inl_injective
  change S.inl (ψ j)=S.inl 1
  change CentralPushout.inclusion p hc ψ (ψ j)=CentralPushout.inclusion p hc ψ 1
  rw [←CentralPushout.canonical_kernel,he]
  change S.modelHom (t (p j.val))=CentralPushout.inclusion p hc ψ 1
  rw [j.property,map_one,map_one,map_one]

lemma restriction_injective (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n) :
    Function.Injective (restriction ε n) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro ψ hψ
  change ψ=1
  exact restriction_eq_one ε hI n hn ψ hψ

def restrictionIso (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n) :
    (J (R := R) (n+1) →* QGroup) ≃* (J (R := R) n →* QGroup) :=
  MulEquiv.ofBijective (restriction ε n)
    ⟨restriction_injective ε hI n hn,restriction_surjective ε hI n hn⟩

@[simp] lemma restrictionIso_apply (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n)
    (ψ : J (R := R) (n+1) →* QGroup) : restrictionIso ε hI n hn ψ = ψ.comp (kernelStep ε n) := rfl

end

open Classical ElementaryRanks
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

abbrev cast {n q : ℕ} (h : n≤q) : Steinberg n R →* Steinberg q R :=
  Steinberg.coordinateMap (Fin.castLE h) (Fin.castLE_injective h)

omit [Algebra (ZMod 2) R] in
lemma cast_refl (n : ℕ) : cast (R := R) (le_refl n)=MonoidHom.id _ := by
  apply Steinberg.hom_ext
  intro p a
  rfl
omit [Algebra (ZMod 2) R] in
lemma cast_succ {n q : ℕ} (h : n≤q) : cast (R := R) (h.trans (Nat.le_succ q)) =
    (step q).comp (cast h) := by
  apply Steinberg.hom_ext
  intro p a
  rfl

include ε in
lemma cast_mem {n q : ℕ} (hnq : n≤q) (j : J (R := R) n) : cast hnq j.val∈J (R := R) q := by
  induction q,hnq using Nat.le_induction with
  | base => simpa only [cast_refl,MonoidHom.id_apply] using j.property
  | succ q hnq ih =>
    rw [cast_succ,MonoidHom.comp_apply]
    exact (kernelStep ε q ⟨cast hnq j.val,ih⟩).property

def kernelCast {n q : ℕ} (hnq : n≤q) : J (R := R) n →* J (R := R) q where
  toFun j := ⟨cast hnq j.val,cast_mem ε hnq j⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _left _right := Subtype.ext (map_mul _ _ _)

end SourceBurnside.Stability.RationalKernel

end

end OAI
end


