-- Prove2me | Definitions.Def_OAIQ124K004
-- name    : OAIQ124K004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:46:29.578935+00:00
-- url     : https://prove2.me/theorems/92513c72-f788-4ee6-85e0-5f80a5e29550
-- title:
--   Definitions bundle OAIQ124K004 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 270 declarations of OpenAI's Lean: 88 definitions, 8 inductive types or structures, 3 instances and 171 theorems. The definitions and types are `OAI.KLInvariance.BruhatGraph.ActualBoundary`, `OAI.KLInvariance.BruhatGraph.EdgeRing`, `OAI.KLInvariance.BruhatGraph.FreeSheaf`, `OAI.KLInvariance.BruhatGraph.FreeSheaf.SectionDuality`, `OAI.KLInvariance.BruhatGraph.FreeSheaf.costalkEquivDual`, `OAI.KLInvariance.BruhatGraph.FreeSheaf.dualityOfPairing`, `OAI.KLInvariance.BruhatGraph.FreeSheaf.kernelDual`, `OAI.KLInvariance.BruhatGraph.FreeSheaf.kernelEquivSingleSupport`, `OAI.KLInvariance.BruhatGraph.FreeSuffixes`, `OAI.KLInvariance.BruhatGraph.SectionDuality`, `OAI.KLInvariance.BruhatGraph.actualEdges`, `OAI.KLInvariance.BruhatGraph.actualInterval`, `OAI.KLInvariance.BruhatGraph.boundarySheaf`, `OAI.KLInvariance.BruhatGraph.chronologicalSchedule`, `OAI.KLInvariance.BruhatGraph.edgeModule`, `OAI.KLInvariance.BruhatGraph.edgeRingEquiv`, `OAI.KLInvariance.BruhatGraph.intervalBoundary`, `OAI.KLInvariance.BruhatGraph.polynomialRoot`, `OAI.KLInvariance.BruhatGraph.remainingConditions`, `OAI.KLInvariance.BruhatGraph.restrictBoundary`, `OAI.KLInvariance.BruhatGraph.transportedEdge`, `OAI.KLInvariance.BruhatGraph.transportedSchedule`, `OAI.KLInvariance.BruhatGraph.transportedScore`, `OAI.KLInvariance.BruhatGraph.upperInclusion`, `OAI.KLInvariance.EdgeAlgebra.quotientBackward`, `OAI.KLInvariance.EdgeAlgebra.quotientRootMap`, `OAI.KLInvariance.EdgeAlgebra.rootQuotientEquiv`, `OAI.KLInvariance.Graded.ModuleData.Hom.inverse`, `OAI.KLInvariance.Graded.ModuleData.change`, `OAI.KLInvariance.Graded.ModuleData.changeHom`, `OAI.KLInvariance.Graded.ModuleData.changePiece`, `OAI.KLInvariance.Graded.ModuleData.changeTopInclusion`, `OAI.KLInvariance.Graded.ModuleData.changeTopProjection`, `OAI.KLInvariance.Graded.ModuleData.changeUnitHom`, `OAI.KLInvariance.Graded.ModuleData.changeUnitInvHom`, `OAI.KLInvariance.Graded.ModuleData.equivOfEq`, `OAI.KLInvariance.Graded.ModuleData.homOfEq`, `OAI.KLInvariance.MomentGraph.BoundarySheaf.pullback`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Endomorphism`, `OAI.KLInvariance.MomentGraph.GradedSheaf.PerfectPairing` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `KazhdanLusztig_BottSamelson`, `KazhdanLusztig_Bruhat`, `KazhdanLusztig_CharacterReciprocity`, `KazhdanLusztig_Decomposition`, `KazhdanLusztig_Dihedral`, `KazhdanLusztig_DihedralIntervals`, `KazhdanLusztig_DyerPaths`, `KazhdanLusztig_EdgeLocalization`, `KazhdanLusztig_Frobenius`, `KazhdanLusztig_GradedModules`, `KazhdanLusztig_GradedSheaves`, `KazhdanLusztig_MinimalExtensions`, `KazhdanLusztig_PlaneLocalization`, `KazhdanLusztig_PositiveTransfer`, `KazhdanLusztig_ReflectionOrders`, `KazhdanLusztig_ReflectionSchedules`, `KazhdanLusztig_SheafMorphisms`, `KazhdanLusztig_Sheaves`, `KazhdanLusztig_SimultaneousInvariance`, `KazhdanLusztig_Support`, `KazhdanLusztig_TerminalKernels`, `KazhdanLusztig_Tits`.
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K000` and `OAIQ124K001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K008`, `OAIQ124K009`, `OAIQ124K010` and `OAIQ124K011`; the statement `OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K000
import Definitions.Def_OAIQ124K001

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedModules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded polynomial modules, projective presentations, finite homogeneous generators and uniqueness of minimal covers.
-/

section

namespace KLInvariance.Graded
open scoped Pointwise
universe uk ua um
variable {k : Type uk} {A : Type ua} {M : Type um} [Field k] [CommRing A] [klPreservedInstance9 : Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [klPreservedInstance8 : IsScalarTower k A M]

/-- A finite free cover of a projective module, minimal at any proper
augmentation ideal of a noetherian domain, is injective. The determinant
form of Nakayama removes the complementary torsion-free kernel. -/
theorem linearIndependent_of_projective_cover {ι : Type*} [Fintype ι]
    [IsDomain A] [IsNoetherianRing A] [Module.Projective A M]
    (I : Ideal A) (hI : I ≠ ⊤)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ I)
    (v : ι → M) (hspan : Submodule.span A (Set.range v) = ⊤)
    (hind : LinearIndependent k
      (fun i => (I • (⊤ : Submodule A M)).mkQ (v i))) :
    LinearIndependent A v := by
  classical
  let J := I • (⊤ : Submodule A M)
  let f := Fintype.linearCombination A v
  have hsurj : Function.Surjective f := by
    intro m
    exact (Submodule.mem_span_range_iff_exists_fun A).mp (hspan ▸ Submodule.mem_top)
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : M →ₗ[A] M) hsurj
  have hmin : LinearMap.ker f ≤ I • (⊤ : Submodule A (ι → A)) := by
    intro a ha
    choose c hc using fun i => hscalar (a i)
    have heq : ∑ i, c i • J.mkQ (v i) = 0 := by
      calc
        _ = J.mkQ (∑ i, a i • v i) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact (quotient_smul_of_scalar_mod I (a i) (c i) (hc i) (v i)).symm
        _ = 0 := congrArg J.mkQ (LinearMap.mem_ker.mp ha) |>.trans (map_zero _)
    have hc0 : ∀ i, c i=0 := (Fintype.linearIndependent_iff.mp hind) c heq
    have hai (i : ι) : a i ∈ I := by simpa [hc0 i] using hc i
    have hrebuild : a = ∑ i, a i • Pi.single i (1 : A) := by
      ext j
      simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [hrebuild]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem_smul (hai i) Submodule.mem_top
  have htop := positive_smul_kernel_of_minimal_split I f s hs hmin
  have hfg : (⊤ : Submodule A (LinearMap.ker f)).FG := IsNoetherian.noetherian _
  obtain ⟨r,hr,hkill⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    I (⊤ : Submodule A (LinearMap.ker f)) hfg (by rw [htop])
  have hr0 : r ≠ 0 := by
    intro heq
    have hone : (1 : A) ∈ I := by simpa [heq] using I.neg_mem hr
    exact hI (Ideal.eq_top_of_isUnit_mem I hone isUnit_one)
  have hker : LinearMap.ker f = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    have hz : r • (⟨a,ha⟩ : LinearMap.ker f) = 0 := hkill _ Submodule.mem_top
    have ha0 : (⟨a,ha⟩ : LinearMap.ker f) = 0 := (smul_eq_zero.mp hz).resolve_left hr0
    exact congrArg Subtype.val ha0
  exact linearIndependent_iff_injective_fintypeLinearCombination.mpr
    (LinearMap.ker_eq_bot.mp hker)


theorem exists_homogeneous_basis_of_scalar_mod
    [IsDomain A] [IsNoetherianRing A] [Module.Projective A M] [Module.Finite A M]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥)
    (hproper : positiveIdeal 𝓐 ≠ ⊤)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐) :
    ∃ (ι : Type um), Finite ι ∧ ∃ b : Module.Basis ι A M,
      ∀ i, ∃ d : ℤ, b i ∈ 𝓜 d := by
  classical
  obtain ⟨t,ht,hth⟩ := exists_finite_homogeneous_generators (A := A) 𝓜
  let v : t → M := Subtype.val
  have hv : Submodule.span A (Set.range v) = ⊤ := by
    simpa [v] using ht
  let I := positiveIdeal 𝓐
  let J := I • (⊤ : Submodule A M)
  have hq := quotient_span_of_scalar_mod I hscalar v hv
  obtain ⟨ι,a,ha,hsp,hli⟩ := exists_linearIndependent' k (fun i => J.mkQ (v i))
  let : Finite ι := Finite.of_injective a ha
  let : Fintype ι := Fintype.ofFinite ι
  let w : ι → M := v ∘ a
  have hw : ∀ i, ∃ d : ℤ, w i ∈ 𝓜 d := fun i => hth _ (a i).property
  choose d hd using hw
  have hqw : Submodule.span k (Set.range (fun i => J.mkQ (w i))) = ⊤ := hsp.trans hq
  let N := Submodule.span A (Set.range w)
  have hN : ∀ n m, m ∈ N → (DirectSum.decompose 𝓜 m n : M) ∈ N :=
    homogeneous_span_components 𝓐 𝓜 w d hd
  have hgen : N ⊔ I • (⊤ : Submodule A M) = ⊤ := by
    apply top_unique
    intro m _
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp
      (hqw ▸ Submodule.mem_top : J.mkQ m ∈
        Submodule.span k (Set.range (fun i => J.mkQ (w i))))
    let z : M := ∑ i, algebraMap k A (c i) • w i
    have hz : z ∈ N := by
      apply Submodule.sum_mem
      intro i _
      exact N.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    have hqz : J.mkQ z = J.mkQ m := by
      change J.mkQ (∑ i, algebraMap k A (c i) • w i) = J.mkQ m
      rw [map_sum]
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro i _
      exact (map_smul J.mkQ _ _).trans (IsScalarTower.algebraMap_smul A (c i) _)
    have hdiff : m-z ∈ J := by
      apply (Submodule.Quotient.mk_eq_zero J).mp
      change J.mkQ (m-z)=0
      rw [map_sub,hqz,sub_self]
    exact Submodule.mem_sup.mpr ⟨z,hz,m-z,hdiff,by abel⟩
  have hspan : N=⊤ := eq_top_of_positive_smul_sup 𝓐 𝓜 d₀ hbound N hN hgen
  have hliA : LinearIndependent A w :=
    linearIndependent_of_projective_cover I hproper hscalar w hspan hli
  refine ⟨ι,inferInstance,Module.Basis.mk hliA hspan.ge,?_⟩
  intro i
  exact ⟨d i, by simpa only [Module.Basis.mk_apply] using hd i⟩


theorem exists_homogeneous_basis_connected
    [IsDomain A] [IsNoetherianRing A] [Module.Projective A M] [Module.Finite A M]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜]
    (hneg : ∀ j < 0, 𝓐 j = ⊥)
    (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥) :
    ∃ (ι : Type um), Finite ι ∧ ∃ b : Module.Basis ι A M,
      ∀ i, ∃ d : ℤ, b i ∈ 𝓜 d := by
  apply exists_homogeneous_basis_of_scalar_mod 𝓐 𝓜 d₀ hbound
  · rw [positiveIdeal_eq_augmentation_ker 𝓐 hneg]
    exact RingHom.ker_ne_top _
  · intro a
    obtain ⟨c,hc⟩ := hzero _ (DirectSum.decompose 𝓐 a 0).property
    refine ⟨c,?_⟩
    rw [positiveIdeal_eq_augmentation_ker 𝓐 hneg]
    change component 𝓐 0 (a-algebraMap k A c)=0
    rw [map_sub,hc]
    rw [show component 𝓐 0 (DirectSum.decompose 𝓐 a 0 : A) =
      (DirectSum.decompose 𝓐 a 0 : A) from
      DirectSum.decompose_of_mem_same 𝓐 (DirectSum.decompose 𝓐 a 0).property]
    exact sub_self _

end KLInvariance.Graded


end


section

namespace KLInvariance.Graded
universe uk ua um

attribute [instance] ModuleData.kModule ModuleData.tower ModuleData.decomposition
  ModuleData.graded ModuleData.finite

end KLInvariance.Graded

end


section

/-! Homogeneous projectivity and uniqueness of the actual minimal graded
covers. These are recognition dependencies, not assumptions of the main. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

 theorem Hom.mem_of_map_mem {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N)
    (hi : Function.Injective f.map) (n : ℤ) (m : M) (hm : f.map m ∈ N.piece n) :
    m ∈ M.piece n := by
  have h : f.map (Graded.component M.piece n m) = f.map m := by
    rw [← f.component]
    exact DirectSum.decompose_of_mem_same N.piece hm
  rw [← hi h]
  exact (DirectSum.decompose M.piece m n).property

 theorem Hom.homogeneous_preimage {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N)
    (hs : Function.Surjective f.map) (n : ℤ) (v : N) (hv : v ∈ N.piece n) :
    ∃ m : M, m ∈ M.piece n ∧ f.map m = v := by
  obtain ⟨m,rfl⟩ := hs v
  refine ⟨Graded.component M.piece n m,(DirectSum.decompose M.piece m n).property,?_⟩
  rw [← f.component]
  exact DirectSum.decompose_of_mem_same N.piece hv

variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

include hneg in
 theorem exists_hom_lift_of_basis [Nontrivial A] {F N P : ModuleData.{uk,ua,um} 𝓐}
    {ι : Type (max ua um)} [Fintype ι] (b : Module.Basis ι A F)
    (d : ι → ℤ) (hd : ∀ i, b i ∈ F.piece (d i))
    (f : Hom N P) (hs : Function.Surjective f.map) (g : Hom F P) :
    ∃ l : Hom F N, f.map.comp l.map = g.map := by
  classical
  have hd0 (i : ι) : 0 ≤ d i := by
    by_contra h
    have hz : b i = 0 := by simpa [F.nonneg (d i) (lt_of_not_ge h)] using hd i
    exact b.ne_zero i hz
  let H := free.{uk,ua,um} hneg d hd0
  let e : Hom H F :=
    { map := b.equivFun.symm.toLinearMap
      graded := by
        intro n v hv
        change ι → A at v
        change v ∈ shiftedPiece 𝓐 d n at hv
        change b.equivFun.symm v ∈ F.piece n
        rw [b.equivFun_symm_apply]
        apply Submodule.sum_mem
        intro i _
        simpa using SetLike.GradedSMul.smul_mem (hv i) (hd i) }
  have he : Function.Injective e.map := b.equivFun.symm.injective
  have hcoeff (n : ℤ) (v : F) (hv : v ∈ F.piece n) :
      b.equivFun v ∈ shiftedPiece 𝓐 d n := by
    apply e.mem_of_map_mem he n
    change b.equivFun.symm (b.equivFun v) ∈ F.piece n
    simpa only [LinearEquiv.symm_apply_apply] using hv
  have hlifts (i : ι) : ∃ v : N, v ∈ N.piece (d i) ∧ f.map v = g.map (b i) :=
    f.homogeneous_preimage hs (d i) _ (g.graded (d i) _ (hd i))
  choose v hvg hvf using hlifts
  let l : Hom F N :=
    { map := b.constr A v
      graded := by
        intro n m hm
        rw [b.constr_apply]
        apply Submodule.sum_mem
        intro i _
        simpa using SetLike.GradedSMul.smul_mem (hcoeff n m hm i) (hvg i) }
  refine ⟨l,?_⟩
  apply b.ext
  intro i
  change f.map ((b.constr A v) (b i)) = g.map (b i)
  rw [b.constr_basis,hvf]

variable [IsDomain A] [IsNoetherianRing A]
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)

include hneg hzero in
 theorem exists_hom_lift {F N P : ModuleData.{uk,ua,um} 𝓐}
    [Module.Free A F] (f : Hom N P) (hs : Function.Surjective f.map) (g : Hom F P) :
    ∃ l : Hom F N, f.map.comp l.map = g.map := by
  classical
  obtain ⟨ι,hι,b,hd⟩ := exists_homogeneous_basis_connected 𝓐 F.piece hneg hzero 0 F.nonneg
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  choose d hd using hd
  exact exists_hom_lift_of_basis hneg b d hd f hs g

omit [IsDomain A] [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐] hneg hzero in
 theorem Hom.bijective_of_mod_positive {M : ModuleData.{uk,ua,um} 𝓐} (f : Hom M M)
    (hm : ∀ m, m-f.map m ∈ positiveIdeal 𝓐 • (⊤ : Submodule A M)) :
    Function.Bijective f.map := by
  have hr : LinearMap.range f.map = ⊤ :=
    eq_top_of_positive_smul_sup 𝓐 M.piece 0 M.nonneg (LinearMap.range f.map)
      (range_homogeneous M.piece M.piece f.map 0 (by simpa using f.graded))
      (by
        apply top_unique
        intro m _
        exact Submodule.mem_sup.mpr ⟨f.map m,⟨m,rfl⟩,m-f.map m,hm m,add_sub_cancel _ _⟩)
  have hs := LinearMap.range_eq_top.mp hr
  exact ⟨IsNoetherian.injective_of_surjective_endomorphism f.map hs,hs⟩

end KLInvariance.Graded.ModuleData

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

section


namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


/-! Exchange consequences required for the source's finite-rank reduction
and for consistency of the equal-parameter Hecke recursion. -/

/-- Precisely the finite-support part used by the manuscript's finite-rank
reduction: all lower elements are words in the generators of any reduced top
word. Equality of parabolic polynomial normalizations remains a later step. -/
theorem lower_ideal_finite_generator_support (cs : CoxeterSystem M W) (b : W) :
    ∃ J : Set B, J.Finite ∧ ∀ x, BruhatLE cs x b →
      ∃ ν : List B, (∀ i ∈ ν, i ∈ J) ∧ cs.wordProd ν = x := by
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced b
  refine ⟨{i | i ∈ ω}, ω.finite_toSet, ?_⟩
  intro x hx
  obtain ⟨ν, hsub, _, hprod⟩ := reduced_subword_of_bruhat cs hx hω heq.symm
  exact ⟨ν, fun i hi => hsub.subset hi, hprod⟩


theorem bruhatStep_mul_simple (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatStep cs x y) (i : B) (hne : y ≠ x * cs.simple i) :
    BruhatStep cs (x * cs.simple i) (y * cs.simple i) := by
  have hinv := bruhatStep_inv cs hxy
  have hne' : y⁻¹ ≠ cs.simple i * x⁻¹ := by
    intro heq
    apply hne
    have := congrArg Inv.inv heq
    simpa [mul_inv_rev] using this
  have h := bruhatStep_inv cs (bruhatStep_simple_mul cs hinv i hne')
  simpa [mul_inv_rev] using h

/-- The noncollapsed left/right simple square has consistent orientations. -/
theorem left_descent_mul_simple_iff (cs : CoxeterSystem M W) (i j : B) (x : W)
    (hne : cs.simple i * x ≠ x * cs.simple j) :
    cs.length (cs.simple i * (x * cs.simple j)) < cs.length (x * cs.simple j) ↔
      cs.length (cs.simple i * x) < cs.length x := by
  by_cases hx : cs.length (cs.simple i * x) < cs.length x
  · have hedge : BruhatStep cs (cs.simple i * x) x :=
      ⟨hx, cs.simple i, cs.isReflection_simple i, by simp⟩
    have hne' : x ≠ cs.simple i * x * cs.simple j := by
      intro heq
      apply hne
      have := congrArg (fun z => z * cs.simple j) heq
      simpa using this.symm
    have h := (bruhatStep_mul_simple cs hedge j hne').1
    simpa only [mul_assoc, hx, iff_true] using h
  · have hedge : BruhatStep cs x (cs.simple i * x) :=
      ⟨by have := cs.length_simple_mul x i; omega, cs.simple i,
        cs.isReflection_simple i, rfl⟩
    have h := (bruhatStep_mul_simple cs hedge j hne).1
    rw [mul_assoc] at h
    exact iff_of_false (by omega) hx

theorem right_descent_simple_mul_iff (cs : CoxeterSystem M W) (i j : B) (x : W)
    (hne : cs.simple i * x ≠ x * cs.simple j) :
    cs.length (cs.simple i * x * cs.simple j) < cs.length (cs.simple i * x) ↔
      cs.length (x * cs.simple j) < cs.length x := by
  have hne' : cs.simple j * x⁻¹ ≠ x⁻¹ * cs.simple i := by
    intro heq
    apply hne
    have h := congrArg Inv.inv heq
    simpa [mul_inv_rev] using h.symm
  have h := left_descent_mul_simple_iff cs j i x⁻¹ hne'
  have h1 : cs.length (cs.simple i * x * cs.simple j) =
      cs.length (cs.simple j * (x⁻¹ * cs.simple i)) := by
    rw [← cs.length_inv (cs.simple i * x * cs.simple j)]
    simp [mul_inv_rev]
  have h2 : cs.length (cs.simple i * x) = cs.length (x⁻¹ * cs.simple i) := by
    rw [← cs.length_inv (cs.simple i * x)]
    simp [mul_inv_rev]
  have h3 : cs.length (x * cs.simple j) = cs.length (cs.simple j * x⁻¹) := by
    rw [← cs.length_inv (x * cs.simple j)]
    simp [mul_inv_rev]
  rw [h1, h2, h3]
  simpa using h


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

namespace KLInvariance.Dihedral

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

theorem reduced_alt_take (cs : CoxeterSystem M W) {i : Bool} {k n : ℕ}
    (h : cs.IsReduced (alt i n)) (hk : k ≤ n) : cs.IsReduced (alt i k) := by
  simpa only [take_alt, Nat.min_eq_left hk] using h.take k

end KLInvariance.Dihedral

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Sheaves
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.instAddCommGroupCarrierObj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Ordered moment graphs, sheaves, flabbiness, sections and boundary images.
-/

section


/-! The finite-section extension argument required by source §4.3. No BMP
character theorem is postulated. These definitions are ordinary module-valued
sheaves on a directed ordered graph; labels enter later through which edge
modules vanish after localization. -/

namespace KLInvariance.MomentGraph

universe u v w z

variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}

namespace Sheaf
variable {G : OrderedGraph V E} (B : Sheaf (R := R) G)

/-- Extension of ordinary sections over ambient upper sets. -/
def Flabby : Prop :=
  ∀ Ω : Set V, IsUpperSet Ω → ∀ f : B.Assignment, B.CompatibleOn Ω f →
    ∃ g : B.Assignment, B.IsGlobal g ∧ ∀ x ∈ Ω, g x = f x

end Sheaf
end KLInvariance.MomentGraph

end

section

namespace KLInvariance.MomentGraph.Sheaf

universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}
  {G : OrderedGraph V E} (B : Sheaf.{u,v,w,z} (R := R) G)

abbrev Outgoing (x : V) := {e : E // G.source e = x}

abbrev Boundary (x : V) := ∀ e : Outgoing (G := G) x, B.edge e.val

/-- The lower-end stalk map on all upward edges. -/
def stalkMap (x : V) : B.vertex x →ₗ[R] B.Boundary x where
  toFun b e := B.lower e.val (e.property.symm ▸ b)
  map_add' b c := by ext e; cases e with | mk e he => subst x; simp
  map_smul' r b := by ext e; cases e with | mk e he => subst x; simp

/-- Boundary values supplied by sections strictly above a vertex. -/
def boundaryMap (x : V) : B.sections (Set.Ioi x) →ₗ[R] B.Boundary x where
  toFun f e := B.upper e.val (f.val (G.target e.val))
  map_add' f g := by ext e; simp
  map_smul' r f := by ext e; simp

end KLInvariance.MomentGraph.Sheaf


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Tits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual Bruhat graph labels, Tits realizations and extended root spaces, cotangent coordinates and standard parabolic support.
-/

section

namespace KLInvariance
namespace BruhatGraph
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
  (cs : CoxeterSystem M W) (u b : W)

theorem eq_of_label_source_eq {e f : Edge cs u b}
    (hl : label cs u b e = label cs u b f)
    (hs : source cs u b e = source cs u b f) : e = f := by
  have ht : target cs u b e = target cs u b f := by
    apply Subtype.ext
    rw [← label_mul_source cs u b e, ← label_mul_source cs u b f, hl, hs]
  apply Subtype.ext
  exact Prod.ext hs ht

theorem eq_of_label_target_eq {e f : Edge cs u b}
    (hl : label cs u b e = label cs u b f)
    (ht : target cs u b e = target cs u b f) : e = f := by
  have hs : source cs u b e = source cs u b f := by
    apply Subtype.ext
    rw [← label_mul_target cs u b e, ← label_mul_target cs u b f, hl, ht]
  exact eq_of_label_source_eq cs u b hl hs

theorem source_ne_target_of_label_eq {e f : Edge cs u b}
    (hl : label cs u b e = label cs u b f) :
    source cs u b e ≠ target cs u b f := by
  intro h
  have ht : target cs u b e = source cs u b f := by
    apply Subtype.ext
    rw [← label_mul_source cs u b e, hl, h, label_mul_target]
  have he := (graph cs u b).increasing e
  have hf := (graph cs u b).increasing f
  change source cs u b e < target cs u b e at he
  change source cs u b f < target cs u b f at hf
  rw [h, ht] at he
  exact lt_asymm he hf


end BruhatGraph
end KLInvariance


/-! The finite Coxeter relations for the actual real geometric reflection
operators required in `bg:realization`. Faithfulness is not assumed or claimed. -/

namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Rank of the moving subspace is unchanged by conjugacy. -/
theorem finrank_moving_conj (g h : V ≃ₗ[ℝ] V) :
    Module.finrank ℝ (LinearMap.range ((h * g * h⁻¹).toLinearMap - LinearMap.id)) =
      Module.finrank ℝ (LinearMap.range (g.toLinearMap - LinearMap.id)) := by
  have heq : (h * g * h⁻¹).toLinearMap - LinearMap.id =
      h.toLinearMap.comp ((g.toLinearMap - LinearMap.id).comp h.symm.toLinearMap) := by
    ext v
    simp
  rw [heq, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ h.symm.range,
    h.finrank_map_eq]

/-- An orthogonal rank-one map negating a norm-two vector is its exact reflection. -/
theorem rank_one_eq_reflection_of_negates [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (g : V ≃ₗ[ℝ] V)
    (hg : ∀ v w, B (g v) (g w) = B v w)
    (hr : Module.finrank ℝ (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1)
    (e : V) (he : B e e = 2) (hge : g e = -e) :
    ∀ v, g v = Module.preReflection e (B e) v := by
  let d : V →ₗ[ℝ] V := g.toLinearMap - LinearMap.id
  have he0 : e ≠ 0 := by intro h; simp [h] at he
  have hemem : e ∈ LinearMap.range d := by
    refine ⟨(- (1 / 2 : ℝ)) • e, ?_⟩
    change g (- (1 / 2 : ℝ) • e) - (- (1 / 2 : ℝ) • e) = e
    rw [map_smul, hge]
    module
  have hspan : Submodule.span ℝ {e} = LinearMap.range d := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simpa using hemem)
    · rw [finrank_span_singleton he0]
      exact hr.symm
  intro v
  have hv : d v ∈ Submodule.span ℝ {e} := by rw [hspan]; exact LinearMap.mem_range_self _ v
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  have hgform : g v = v + c • e := by
    change c • e = g v - v at hc
    rw [hc]
    abel
  have hB := hg e v
  rw [hge, hgform] at hB
  simp only [map_neg, LinearMap.neg_apply, map_add, map_smul, he, smul_eq_mul] at hB
  have hc' : c = - B e v := by linarith
  rw [hgform, hc', Module.preReflection_apply, neg_smul, sub_eq_add_neg]

/-- Commutation with a reflection makes its negative eigenspace invariant;
a nonpositive coordinate selects the negative, rather than positive, sign. -/
theorem negates_of_commutes_nonpos
    (B : LinearMap.BilinForm ℝ V) (g : V ≃ₗ[ℝ] V)
    (hg : ∀ v w, B (g v) (g w) = B v w)
    (e : V) (he : B e e = 2)
    (hcomm : g * Module.reflection he = Module.reflection he * g)
    (f : Module.Dual ℝ V) (hfe : f e = 1) (hfg : f (g e) ≤ 0) :
    g e = -e := by
  have h := LinearEquiv.congr_fun hcomm e
  simp only [LinearEquiv.mul_apply, Module.reflection_apply_self, map_neg,
    Module.reflection_apply] at h
  let c : ℝ := B e (g e) / 2
  have hge : g e = c • e := by
    dsimp [c]
    linear_combination (norm := module) (- (1 / 2 : ℝ)) • h
  have hc : c ≤ 0 := by simpa [hge, hfe] using hfg
  have hnorm := hg e e
  rw [hge] at hnorm
  simp only [map_smul, LinearMap.smul_apply, he, smul_eq_mul] at hnorm
  have hc' : c = -1 := by nlinarith [sq_nonneg (c + 1)]
  rw [hge, hc', neg_one_smul]

theorem finrank_reflection_sub_id (e : V) (f : Module.Dual ℝ V) (h : f e = 2) :
    Module.finrank ℝ (LinearMap.range
      ((Module.reflection h).toLinearMap - LinearMap.id)) = 1 := by
  rw [range_reflection_sub_id]
  apply finrank_span_singleton
  intro he
  simp [he] at h

end KLInvariance.Realization

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- A rank-one element of the actual extended action is an involution. -/
theorem involution_of_moving_rank_one (w : W)
    (hr : Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1) : w⁻¹ = w := by
  obtain ⟨e, he, hform⟩ := Realization.orthogonal_finrank_one
    (extendedForm M) (extendedForm_spec M).1 (extendedForm_spec M).2.1
    (extendedAction M cs w) (extendedAction_preserves M cs w) hr
  have he2 : ((2 / extendedForm M e e) • extendedForm M e) e = 2 := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    field_simp
  have hw2 : w * w = 1 := by
    apply extendedAction_injective M cs
    apply LinearEquiv.ext
    intro v
    simp only [map_mul, map_one, LinearEquiv.mul_apply, hform]
    change _ = v
    exact Module.involutive_preReflection he2 v
  exact inv_eq_of_mul_eq_one_left hw2

/-- Reflection faithfulness, the difficult converse, proved by length descent.
This avoids assuming the finite-subgroup theorem cited in the manuscript. -/
theorem isReflection_of_moving_rank_one (w : W)
    (hr : Module.finrank ℝ (LinearMap.range
      ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1) :
    cs.IsReflection w := by
  suffices ∀ n : ℕ, ∀ w : W, cs.length w = n →
      Module.finrank ℝ (LinearMap.range
        ((extendedAction M cs w).toLinearMap - LinearMap.id)) = 1 →
      cs.IsReflection w from this (cs.length w) w rfl hr
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hlen hr
    have hwne : w ≠ 1 := by
      intro h
      subst w
      have heq : (extendedAction M cs 1).toLinearMap - LinearMap.id = 0 := by
        apply LinearMap.ext
        intro v
        change (extendedAction M cs 1) v - v = 0
        rw [map_one]
        change v - v = 0
        abel
      rw [heq, LinearMap.range_zero, finrank_bot] at hr
      omega
    have hwinv := involution_of_moving_rank_one M cs w hr
    obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hwne
    change cs.length (w * cs.simple i) < cs.length w at hi
    have hleft : cs.length (cs.simple i * w) < cs.length w := by
      have h := cs.length_inv (w * cs.simple i)
      simp only [mul_inv_rev, cs.inv_simple, hwinv] at h
      omega
    by_cases hcomm : cs.simple i * w = w * cs.simple i
    · have hcomm' : extendedAction M cs w * Module.reflection (extendedForm_root_self M i) =
          Module.reflection (extendedForm_root_self M i) * extendedAction M cs w := by
        rw [← extendedAction_simple_eq M cs i, ← map_mul, ← map_mul, hcomm]
      let f : Module.Dual ℝ (Extended M) := (LinearMap.proj i).comp
        (LinearMap.fst ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))
      have hf : f (extendedRoot M i) = 1 := by simp [f, extendedRoot, root]
      have hfg : f (extendedAction M cs w (extendedRoot M i)) ≤ 0 := by
        have hn := action_root_nonpos_of_descent M cs w i hi i
        simpa only [f, LinearMap.comp_apply, extendedRoot, extendedAction_restrict,
          LinearMap.fst_apply, LinearMap.proj_apply] using hn
      have hneg := Realization.negates_of_commutes_nonpos (extendedForm M)
        (extendedAction M cs w) (extendedAction_preserves M cs w)
        (extendedRoot M i) (extendedForm_root_self M i) hcomm' f hf hfg
      have heq : extendedAction M cs w = extendedAction M cs (cs.simple i) := by
        apply LinearEquiv.ext
        intro v
        rw [extendedAction_simple]
        exact Realization.rank_one_eq_reflection_of_negates (extendedForm M)
          (extendedAction M cs w) (extendedAction_preserves M cs w) hr
          (extendedRoot M i) (extendedForm_root_self M i) hneg v
      rw [extendedAction_injective M cs heq]
      exact cs.isReflection_simple i
    · let z := cs.simple i * w * cs.simple i
      have hzlt : cs.length z < n := by
        have hz := (right_descent_simple_mul_iff cs i i w hcomm).2 hi
        dsimp [z]
        omega
      have hzrank : Module.finrank ℝ (LinearMap.range
          ((extendedAction M cs z).toLinearMap - LinearMap.id)) = 1 := by
        have hc := Realization.finrank_moving_conj (extendedAction M cs w)
          (extendedAction M cs (cs.simple i))
        have hgi : (extendedAction M cs (cs.simple i))⁻¹ = extendedAction M cs (cs.simple i) := by
          rw [← map_inv, cs.inv_simple]
        have heq : extendedAction M cs z =
            extendedAction M cs (cs.simple i) * extendedAction M cs w *
              (extendedAction M cs (cs.simple i))⁻¹ := by
          dsimp [z]
          rw [map_mul, map_mul, hgi]
        rw [heq]
        exact hc.trans hr
      have hz := ih (cs.length z) hzlt z rfl hzrank
      have hc := hz.conj (w := cs.simple i)
      simpa [z, mul_assoc] using hc

end
end KLInvariance.TitsSpace

/-! Coordinate-dual geometric action. This exists in arbitrary rank and is
used only to prove the finite standard-parabolic reduction of the main goal. -/

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

variable {M cs}

theorem IsRoot.neg {a : I → ℝ} (ha : IsRoot M cs a) : IsRoot M cs (-a) := by
  obtain ⟨w,i,rfl⟩ := ha
  refine ⟨w * cs.simple i, i, ?_⟩
  simp only [map_mul, LinearEquiv.mul_apply, action_simple_root, map_neg]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem Represents.extended_independent_of_ne {t s : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hts : t ≠ s) :
    LinearIndependent ℝ ![embed M a,embed M b] := by
  have h := (ha.independent_of_ne hb hts).map'
    (LinearMap.inl ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))
    (LinearMap.ker_eq_bot.mpr LinearMap.inl_injective)
  have heq : (⇑(LinearMap.inl ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M)))) ∘
      ![a,b]) = ![embed M a,embed M b] := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at h

theorem Represents.extendedAction_eq {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    extendedAction M cs t = Module.reflection
      (show extendedForm M (embed M a) (embed M a) = 2 by
        rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm) := by
  apply LinearEquiv.ext
  intro v
  exact ha.formula v


theorem Represents.plane_eq_of_product_eq {t s r q : W} {a b c d : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b)
    (hc : Represents M cs r c) (hd : Represents M cs q d)
    (hts : t ≠ s) (hrq : r ≠ q) (heq : t*s=r*q) :
    Submodule.span ℝ {embed M a, embed M b} =
      Submodule.span ℝ {embed M c, embed M d} := by
  apply ReflectionPlane.plane_eq_of_reflection_product_eq (extendedForm M)
    (extendedForm_spec M).2.1 (embed M a) (embed M b) (embed M c) (embed M d)
    (by rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hb.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hc.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hd.isRoot.norm)
    (ha.extended_independent_of_ne hb hts) (hc.extended_independent_of_ne hd hrq)
  have h := congrArg (extendedAction M cs) heq
  rw [map_mul, map_mul, ha.extendedAction_eq, hb.extendedAction_eq,
    hc.extendedAction_eq, hd.extendedAction_eq] at h
  exact congrArg LinearEquiv.toLinearMap h

variable (M) (cs)

theorem card_rootInversions (w : W) : Nat.card (RootInversions M cs w) = cs.length w := by
  classical
  obtain ⟨ω,hω,heq⟩ := cs.exists_isReduced w
  rw [heq, Nat.card_congr (rootInversionEquiv M cs _),
    Nat.card_congr (leftInversionListEquiv M cs hω),
    ← Nat.card_congr (List.Nodup.getEquiv (cs.leftInvSeq ω) hω.nodup_leftInvSeq),
    Nat.card_fin, cs.length_leftInvSeq, hω.eq]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Least ambient length in each actual left plane-subgroup coset. No
uniqueness or rank-two Coxeter presentation is smuggled into this definition. -/
theorem planeCoset_exists_minimal (P : Submodule ℝ (I → ℝ)) (a : W) :
    ∃ a₀ g : W, g ∈ planeSubgroup M cs P ∧ a = g*a₀ ∧
      ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀) := by
  classical
  have hex : ∃ n : ℕ, ∃ a₀ g : W, g ∈ planeSubgroup M cs P ∧
      a = g*a₀ ∧ cs.length a₀ = n :=
    ⟨cs.length a,a,1,(planeSubgroup M cs P).one_mem,by simp,rfl⟩
  obtain ⟨a₀,g,hg,ha,hlen⟩ := Nat.find_spec hex
  refine ⟨a₀,g,hg,ha,fun z hz => ?_⟩
  rw [hlen]
  apply Nat.find_min' hex
  refine ⟨z*a₀,g*z⁻¹,(planeSubgroup M cs P).mul_mem hg
    ((planeSubgroup M cs P).inv_mem hz),?_,rfl⟩
  simpa [mul_assoc] using ha

variable {M cs}

/-- A least coset representative sends every positive plane root to a
positive ambient root under its inverse, by the proved inversion criterion. -/
theorem root_nonneg_of_coset_minimal {P : Submodule ℝ (I → ℝ)} {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a : I → ℝ} (ha : IsRoot M cs a) (hp : ∀ i, 0 ≤ a i) (haP : a ∈ P) :
    ∀ i, 0 ≤ action M cs a₀⁻¹ a i := by
  let r : PositiveRoot M cs := ⟨a,ha,hp⟩
  have hr := rootReflection_represents M cs r
  have htP := (Represents.planeSubgroup_mem_iff M cs hr).mpr haP
  rcases (ha.act a₀⁻¹).sign with hpos|hneg
  · exact hpos
  · have hi := (hr.inversion_iff hp a₀).mp hneg
    exact (not_lt_of_ge (hmin _ htP) hi.2).elim


theorem root_nonpos_coset_minimal_iff {P : Submodule ℝ (I → ℝ)} {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {a : I → ℝ} (ha : IsRoot M cs a) (haP : a ∈ P) :
    (∀ i, action M cs a₀⁻¹ a i ≤ 0) ↔ ∀ i, a i ≤ 0 := by
  rcases ha.sign with hp|hn
  · have hnew := root_nonneg_of_coset_minimal hmin ha hp haP
    exact iff_of_false ((ha.act _).not_both hnew) (ha.not_both hp)
  · have hnp : ∀ i, 0 ≤ (-a) i := fun i => neg_nonneg.mpr (hn i)
    have hh := root_nonneg_of_coset_minimal hmin ha.neg hnp (P.neg_mem haP)
    have hnew : ∀ i, action M cs a₀⁻¹ a i ≤ 0 := by
      intro i
      simpa only [map_neg, Pi.neg_apply, neg_nonneg] using hh i
    exact iff_of_true hnew hn

theorem root_inversion_coset_iff {P : Submodule ℝ (I → ℝ)} {a₀ g : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (hg : g ∈ planeSubgroup M cs P) {a : I → ℝ} (ha : IsRoot M cs a)
    (haP : a ∈ P) :
    (∀ i, action M cs (g*a₀)⁻¹ a i ≤ 0) ↔
      ∀ i, action M cs g⁻¹ a i ≤ 0 := by
  rw [mul_inv_rev, map_mul]
  change (∀ i, action M cs a₀⁻¹ (action M cs g⁻¹ a) i ≤ 0) ↔ _
  exact root_nonpos_coset_minimal_iff hmin (ha.act _)
    (planeSubgroup_preserves ((planeSubgroup M cs P).inv_mem hg) haP)

theorem leftInversion_coset_iff {P : Submodule ℝ (I → ℝ)} {a₀ g t : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (hg : g ∈ planeSubgroup M cs P) (ht : t ∈ planeSubgroup M cs P)
    (hr : cs.IsReflection t) :
    cs.IsLeftInversion (g*a₀) t ↔ cs.IsLeftInversion g t := by
  let a := positiveRoot M cs ⟨t,hr⟩
  have ha := positiveRoot_represents M cs ⟨t,hr⟩
  rw [← ha.inversion_iff a.property.2, ← ha.inversion_iff a.property.2]
  exact root_inversion_coset_iff hmin hg a.property.1
    ((Represents.planeSubgroup_mem_iff M cs ha).mp ht)

/-- The directed ambient reflection graph on any plane-subgroup coset is
exactly transported from that on the subgroup by a least coset representative.
Identifying this graph with a *dihedral Coxeter* graph still requires the
canonical rank-two reflection-subgroup theorem. -/
theorem bruhatStep_coset_iff {P : Submodule ℝ (I → ℝ)} {a₀ g h : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (hg : g ∈ planeSubgroup M cs P) (hh : h ∈ planeSubgroup M cs P) :
    BruhatStep cs (g*a₀) (h*a₀) ↔ BruhatStep cs g h := by
  have hn : ∀ {t : W}, h=t*g → cs.IsReflection t →
      (cs.length (g*a₀) < cs.length (h*a₀) ↔ cs.length g < cs.length h) := by
    intro t heq ht
    have htP : t ∈ planeSubgroup M cs P := by
      have htgh : t=h*g⁻¹ := by rw [heq]; group
      rw [htgh]
      exact (planeSubgroup M cs P).mul_mem hh ((planeSubgroup M cs P).inv_mem hg)
    have hi := leftInversion_coset_iff hmin hh htP ht
    have hth : t*h=g := by rw [heq,← mul_assoc,ht.mul_self,one_mul]
    simpa only [CoxeterSystem.IsLeftInversion, ht, true_and, ← mul_assoc, hth] using hi
  constructor
  · rintro ⟨hlen,t,ht,heq⟩
    have htg : h=t*g := by apply mul_right_cancel (b := a₀); simpa only [mul_assoc] using heq
    exact ⟨(hn htg ht).mp hlen,t,ht,htg⟩
  · rintro ⟨hlen,t,ht,heq⟩
    exact ⟨(hn heq ht).mpr hlen,t,ht,by rw [heq,mul_assoc]⟩

end
end KLInvariance.TitsSpace

/-! Construction of the source's geometric reflection schedule. The moment
curve avoids every forbidden hyperplane of a countable root set, using only
finite polynomial root sets and uncountability of the real field. -/

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionSchedules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Reflection schedules, decreasing paths, root-space and edge algebra, and dihedral path recursions.
-/

section

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions
theorem inversionVector_sum (w : W) : (inversionVector (M := M) (cs := cs) w).sum
    (fun _ n => n) = (cs.length w : ℤ) := by
  classical
  let f := inversionVector (M := M) (cs := cs) w
  have hh : f.support.card = cs.length w := by
    have heq : (f.support : Set (PositiveRoot M cs)) = {a | rootInverted w a} := by
      ext a
      simp [f]
    rw [← Set.ncard_coe_finset, heq, ← Nat.card_coe_set_eq]
    exact card_rootInversions M cs w
  rw [Finsupp.sum]
  calc
    ∑ a ∈ f.support, f a = ∑ _a ∈ f.support, (1:ℤ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hm := Finsupp.mem_support_iff.mp ha
      by_cases hi : rootInverted w a
      · simp [f,hi]
      · simp [f,hi] at hm
    _ = _ := by simp [hh]


theorem planeDefect_sum (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    (planeDefect x (rootRef a*x) a).sum (fun _ n => n) =
      (cs.length (rootRef a*x) : ℤ) - cs.length x - 1 := by
  classical
  rw [planeDefect, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl),
    Finsupp.erase_eq_sub_single, Finsupp.sum_sub_index (fun _ _ _ => rfl),
    Finsupp.sum_single_index rfl, rootChange_distinguished x a hx,
    rootChange, Finsupp.sum_sub_index (fun _ _ _ => rfl),
    inversionVector_sum, inversionVector_sum]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_2
theorem planeWeight_nonneg (x : W) (a : PositiveRoot M cs) (P : Submodule ℝ (I → ℝ)) :
    0 ≤ planeWeight x a P := by
  classical
  rw [planeWeight,Finsupp.mapDomain,Finsupp.sum_apply]
  apply Finset.sum_nonneg
  intro b _
  simp only [Finsupp.single_apply,halfVector,rootIndicator_apply]
  split_ifs <;> norm_num

/-- Exact ambient degree formula, with actual roots, finite support and
nonnegative integral planar weights; no labeled interval isomorphism enters. -/
theorem sum_planeWeight (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    2 * (planeWeight x a).sum (fun _ n => n) =
      (cs.length (rootRef a*x) : ℤ) - cs.length x - 1 := by
  have h := planeDefect_sum x a hx
  rw [planeDefect_eq_double_weight x a hx,
    Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at h
  linarith

end
end KLInvariance.TitsSpace

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

def quotientRootMap (a : V) : V ⧸ rootLine (k := k) a →ₗ[k]
    (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) :=
  (rootLine (k := k) a).liftQ ((Ideal.Quotient.mkₐ k (rootIdeal (k := k) a)).toLinearMap.comp (SymmetricAlgebra.ι k V)) (by
    apply Submodule.span_le.mpr
    intro v hv
    have hv' := Set.mem_singleton_iff.mp hv
    subst v
    apply LinearMap.mem_ker.mpr
    change Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

def quotientBackward (a : V) : SymmetricAlgebra k (V ⧸ rootLine (k := k) a) →ₐ[k]
    (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) := SymmetricAlgebra.lift (quotientRootMap a)

@[simp] theorem quotientBackward_ι_mk (a v : V) :
    quotientBackward a (SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a) ((rootLine (k := k) a).mkQ v)) =
      Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v) := by
  rw [quotientBackward,SymmetricAlgebra.lift_ι_apply]
  rfl

/-- Exact coefficient-ring identification used for the manuscript's C=A/(alpha).
This is an isomorphism of the actual quotient, not a replacement invariant. -/
def rootQuotientEquiv (a : V) : (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) ≃ₐ[k]
    SymmetricAlgebra k (V ⧸ rootLine (k := k) a) :=
  AlgEquiv.ofAlgHom (quotientForward a) (quotientBackward a)
    (by
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      obtain ⟨v,rfl⟩ := (rootLine (k := k) a).mkQ_surjective v
      change quotientForward a (quotientBackward a (SymmetricAlgebra.ι k _ ((rootLine (k := k) a).mkQ v))) =
        SymmetricAlgebra.ι k _ ((rootLine (k := k) a).mkQ v)
      rw [quotientBackward_ι_mk,quotientForward_mk,symQuotientMap_ι])
    (by
      apply Ideal.Quotient.algHom_ext
      apply SymmetricAlgebra.algHom_ext
      apply LinearMap.ext
      intro v
      change quotientBackward a (quotientForward a (Ideal.Quotient.mk (rootIdeal (k := k) a)
        (SymmetricAlgebra.ι k V v))) = Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)
      rw [quotientForward_mk,symQuotientMap_ι,quotientBackward_ι_mk])


@[simp] theorem rootQuotientEquiv_mk_ι (a v : V) :
    rootQuotientEquiv a (Ideal.Quotient.mk (rootIdeal (k := k) a) (SymmetricAlgebra.ι k V v)) =
      SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a) ((rootLine (k := k) a).mkQ v) := by
  exact symQuotientMap_ι a v

end
end KLInvariance.EdgeAlgebra

namespace KLInvariance.TitsSpace
open Module EdgeAlgebra
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_5_ra211ce_1 (p : Prop) : Decidable p := Classical.propDecidable p
abbrev EdgeCoefficient (a : PositiveRoot M cs) :=
  SymmetricAlgebra ℝ (Extended M) ⧸ rootIdeal (k := ℝ) (embed M a.val)

end
end KLInvariance.TitsSpace

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem rootIdeal_eq_ker (a : V) : rootIdeal (k := k) a = RingHom.ker (symQuotientMap (k := k) a) := by
  apply le_antisymm (rootIdeal_le_ker a)
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (rootQuotientEquiv (k := k) a).injective
  change quotientForward a (Ideal.Quotient.mk (rootIdeal (k := k) a) z) = _
  rw [quotientForward_mk,map_zero]
  exact hz

theorem rootIdeal_isPrime (a : V) : (rootIdeal (k := k) a).IsPrime := by
  rw [rootIdeal_eq_ker]
  exact RingHom.ker_isPrime _

theorem symmetric_ι_prime (a : V) (ha : a ≠ 0) : Prime (SymmetricAlgebra.ι k V a) := by
  have hn : SymmetricAlgebra.ι k V a ≠ 0 := by
    intro h
    apply ha
    apply symmetric_ι_injective (k := k)
    simpa only [map_zero] using h
  exact (Ideal.span_singleton_prime hn).mp (rootIdeal_isPrime a)

end
end KLInvariance.EdgeAlgebra

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem symmetric_ι_dvd_iff (a v : V) :
    SymmetricAlgebra.ι k V a ∣ SymmetricAlgebra.ι k V v ↔ v ∈ rootLine (k := k) a := by
  rw [← Ideal.mem_span_singleton]
  change SymmetricAlgebra.ι k V v ∈ rootIdeal (k := k) a ↔ _
  rw [rootIdeal_eq_ker]
  change symQuotientMap a (SymmetricAlgebra.ι k V v) = 0 ↔ _
  rw [symQuotientMap_ι]
  constructor
  · intro h
    apply (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mp
    change (rootLine (k := k) a).mkQ v = 0
    apply symmetric_ι_injective (k := k)
    simpa only [map_zero] using h
  · intro h
    have h0 : (rootLine (k := k) a).mkQ v = 0 :=
      (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mpr h
    rw [h0,map_zero]

end
end KLInvariance.EdgeAlgebra

namespace KLInvariance.ReflectionPlane
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The product of three normalized reflections in a root plane is again
an actual orthogonal reflection. The plane itself need not be nondegenerate. -/
theorem reflection_triple_in_plane
    (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (a b c : V) (ha : B a a = 2) (hb : B b b = 2) (hc : B c c = 2)
    (hplane : c ∈ Submodule.span ℝ {a,b}) :
    ∃ d : V, ∃ hd : B d d = 2,
      Module.reflection ha * Module.reflection hb * Module.reflection hc =
        Module.reflection hd := by
  obtain ⟨x,y,hxy⟩ := Submodule.mem_span_pair.mp hplane
  subst c
  let p := B a b
  let r := p*x+y
  let d := x • b - r • a
  have hba : B b a = p := hB.eq b a
  have hnorm : x^2+p*x*y+y^2=1 := by
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      smul_eq_mul,ha,hb,hba] at hc
    dsimp [p]
    nlinarith [hc]
  have hd : B d d = 2 := by
    dsimp [d,r]
    simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,
      smul_eq_mul,ha,hb,hba]
    change x*(x*2-(p*x+y)*p)-(p*x+y)*(x*p-(p*x+y)*2)=2
    nlinarith [hnorm]
  refine ⟨d,hd,?_⟩
  apply LinearEquiv.ext
  intro v
  let A := B a v
  let C := B b v
  have h₁ : -A+p*C+(x-p*r)*(x*A+y*C)= r*(x*C-r*A) := by
    dsimp [r]
    linear_combination (A-p*C)*hnorm
  have h₂ : -C+r*(x*A+y*C)= -x*(x*C-r*A) := by
    dsimp [r]
    linear_combination C*hnorm
  calc
    (Module.reflection ha * Module.reflection hb * Module.reflection hc) v =
        v + (-A+p*C+(x-p*r)*(x*A+y*C)) • a +
          (-C+r*(x*A+y*C)) • b := by
      simp only [LinearEquiv.mul_apply,Module.reflection_apply,map_sub,map_smul,
        map_add,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,ha,hb,hba]
      dsimp [A,C,r,p]
      module
    _ = v + (r*(x*C-r*A)) • a + (-x*(x*C-r*A)) • b := by rw [h₁,h₂]
    _ = Module.reflection hd v := by
      simp only [Module.reflection_apply]
      dsimp [d]
      simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
      dsimp [A,C]
      module

end KLInvariance.ReflectionPlane

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

/-- A product of three genuine Coxeter reflections in one root plane is a
Coxeter reflection, using the proved reflection faithfulness of the actual
Tits extension. This is the sufficiency direction of graph diamond closure. -/
theorem Represents.triple_isReflection {t s r : W} {a b c : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hc : Represents M cs r c)
    (hplane : c ∈ Submodule.span ℝ {a,b}) : cs.IsReflection (t*s*r) := by
  have hplane' : embed M c ∈ Submodule.span ℝ {embed M a,embed M b} := by
    obtain ⟨x,y,hxy⟩ := Submodule.mem_span_pair.mp hplane
    apply Submodule.mem_span_pair.mpr
    refine ⟨x,y,?_⟩
    ext
    · exact congrFun hxy _
    · simp [embed]
  obtain ⟨d,hd,he⟩ := ReflectionPlane.reflection_triple_in_plane (extendedForm M)
    (extendedForm_spec M).1 (embed M a) (embed M b) (embed M c)
    (by rw [(extendedForm_spec M).2.2]; exact ha.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hb.isRoot.norm)
    (by rw [(extendedForm_spec M).2.2]; exact hc.isRoot.norm) hplane'
  apply isReflection_of_moving_rank_one M cs
  have heq : extendedAction M cs (t*s*r) = Module.reflection hd := by
    rw [map_mul,map_mul,ha.extendedAction_eq,hb.extendedAction_eq,hc.extendedAction_eq]
    exact he
  rw [heq]
  exact Realization.finrank_reflection_sub_id _ _ hd

end
end KLInvariance.TitsSpace

/-! NEW GRAPH CLOSURE -/
namespace KLInvariance
universe u v
variable {I : Type u} [klPreservedInstance7 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

 theorem BruhatStep.composable_labels_ne {x y z : W}
    (h : BruhatStep cs x y) (h' : BruhatStep cs y z) :
    y*x⁻¹ ≠ z*y⁻¹ := by
  intro he
  have hh : z*x⁻¹=1 := by
    calc
      z*x⁻¹ = (z*y⁻¹)*(y*x⁻¹) := by group
      _ = (y*x⁻¹)*(y*x⁻¹) := by rw [← he]
      _ = 1 := h.label_reflection.mul_self
  have hzx : z = x := by simpa using congrArg (fun w => w*x) hh
  have hlen := lt_trans h.1 h'.1
  simp [hzx] at hlen

namespace TitsSpace
open Module

 theorem graphRoot_represents {x y : W} (h : BruhatStep cs x y) :
    Represents M cs (y*x⁻¹) (graphRoot h).val :=
  positiveRoot_represents M cs ⟨y*x⁻¹,h.label_reflection⟩

 theorem graphRoot_ne_of_same_source {x a b : W}
    (ha : BruhatStep cs x a) (hb : BruhatStep cs x b) (hab : a ≠ b) :
    graphRoot ha ≠ graphRoot hb := by
  intro he
  have hl := (graphRoot_represents ha).reflection_unique
    (he.symm ▸ graphRoot_represents hb)
  exact hab ((mul_right_cancel_iff).mp hl)

 theorem graphRoot_ne_of_path {x a z : W}
    (ha : BruhatStep cs x a) (hb : BruhatStep cs a z) :
    graphRoot ha ≠ graphRoot hb := by
  intro he
  exact ha.composable_labels_ne hb ((graphRoot_represents ha).reflection_unique
    (he.symm ▸ graphRoot_represents hb))

 theorem graphRoot_square_plane {x a b z : W}
    (hxa : BruhatStep cs x a) (hxb : BruhatStep cs x b)
    (haz : BruhatStep cs a z) (hbz : BruhatStep cs b z) (hab : a ≠ b) :
    rootPlane (graphRoot hxa) (graphRoot haz) =
      rootPlane (graphRoot hxa) (graphRoot hxb) := by
  have hp := (graphRoot_represents haz).plane_eq_of_product_eq
    (graphRoot_represents hxa) (graphRoot_represents hbz) (graphRoot_represents hxb)
    (Ne.symm (hxa.composable_labels_ne haz)) (Ne.symm (hxb.composable_labels_ne hbz))
    (by group : (z*a⁻¹)*(a*x⁻¹)=(z*b⁻¹)*(b*x⁻¹))
  have hp' := congrArg (Submodule.map
    (LinearMap.fst ℝ (I → ℝ) (Module.Dual ℝ (LinearMap.ker (form M))))) hp
  have hp'' : rootPlane (graphRoot haz) (graphRoot hxa) =
      rootPlane (graphRoot hbz) (graphRoot hxb) := by
    simpa only [rootPlane,Submodule.map_span,Set.image_insert_eq,
      Set.image_singleton,LinearMap.fst_apply,embed] using hp'
  have hm : (graphRoot hxb).val ∈ rootPlane (graphRoot hxa) (graphRoot haz) := by
    rw [rootPlane,Set.pair_comm]
    change (graphRoot hxb).val ∈ rootPlane (graphRoot haz) (graphRoot hxa)
    rw [hp'']
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  exact ((rootPlane_eq_iff (graphRoot hxa) (graphRoot haz) (graphRoot hxb)
    (graphRoot_ne_of_path hxa haz)).mpr
    ⟨Ne.symm (graphRoot_ne_of_same_source hxa hxb hab),hm⟩).symm

/-- Soundness of the eight-edge diamond closure rule for the genuine Bruhat
reflection graph. Vertex ranks need not be consecutive; the proof uses actual
root planes and reflection faithfulness, not a labeled graph isomorphism. -/
 theorem bruhatStep_diamond_closure {x a b c d z : W}
    (hxa : BruhatStep cs x a) (hxb : BruhatStep cs x b)
    (hac : BruhatStep cs a c) (had : BruhatStep cs a d)
    (hbc : BruhatStep cs b c) (hbd : BruhatStep cs b d)
    (hcz : BruhatStep cs c z) (hdz : BruhatStep cs d z)
    (hab : a ≠ b) (hcd : c ≠ d) : BruhatStep cs x z := by
  let P := rootPlane (graphRoot hxa) (graphRoot hxb)
  let Q := rootPlane (graphRoot hac) (graphRoot had)
  have hPc := graphRoot_square_plane hxa hxb hac hbc hab
  have hPd := graphRoot_square_plane hxa hxb had hbd hab
  have hacP : (graphRoot hac).val ∈ P := by
    change (graphRoot hac).val ∈ rootPlane (graphRoot hxa) (graphRoot hxb)
    rw [← hPc]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hadP : (graphRoot had).val ∈ P := by
    change (graphRoot had).val ∈ rootPlane (graphRoot hxa) (graphRoot hxb)
    rw [← hPd]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hQP : Q=P := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro v hv
      rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact hacP
      · have hv' := Set.mem_singleton_iff.mp hv
        rw [hv']
        exact hadP
    · dsimp [Q,P]
      rw [rootPlane_finrank _ _ (graphRoot_ne_of_same_source hac had hcd),
        rootPlane_finrank _ _ (graphRoot_ne_of_same_source hxa hxb hab)]
  have hQc := graphRoot_square_plane hac had hcz hdz hcd
  have hm : (graphRoot hxa).val ∈
      Submodule.span ℝ {(graphRoot hcz).val,(graphRoot hac).val} := by
    rw [Set.pair_comm]
    change (graphRoot hxa).val ∈ rootPlane (graphRoot hac) (graphRoot hcz)
    rw [hQc]
    change (graphRoot hxa).val ∈ Q
    rw [hQP]
    exact Submodule.subset_span (Set.mem_insert _ _)
  have href := (graphRoot_represents hcz).triple_isReflection
    (graphRoot_represents hac) (graphRoot_represents hxa) hm
  have heq : (z*c⁻¹)*(c*a⁻¹)*(a*x⁻¹)=z*x⁻¹ := by group
  rw [heq] at href
  exact ⟨lt_trans hxa.1 (lt_trans hac.1 hcz.1), z*x⁻¹,href,by group⟩

end TitsSpace
end
end KLInvariance

namespace KLInvariance
universe u

 theorem bruhatStep_of_interval_covBy
    {I W : Type*} {M : CoxeterMatrix I} [Group W] (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (h : x ⋖ y) : BruhatStep cs x.val y.val := by
  rcases Relation.ReflTransGen.cases_head h.le with heq | ⟨z,hxz,hzy⟩
  · exact (h.ne (Subtype.ext heq)).elim
  · have hle : BruhatLE cs x.val z := Relation.ReflTransGen.single hxz
    let v : Interval cs u b := ⟨z,bruhat_trans cs x.property.1 hle,
      bruhat_trans cs hzy y.property.2⟩
    have hv : v = x ∨ v = y := h.eq_or_eq hle hzy
    rcases hv with hv | hv
    · have heq : z = x.val := congrArg Subtype.val hv
      exact (lt_irrefl _ (heq ▸ hxz.1)).elim
    · have heq : z = y.val := congrArg Subtype.val hv
      exact heq ▸ hxz


 theorem diamondEdges_bruhatStep
    {I W : Type*} [Fintype I] {M : CoxeterMatrix I} [Group W]
    (cs : CoxeterSystem M W) {u b : W} {x y : Interval cs u b}
    (h : DiamondEdges x y) : BruhatStep cs x.val y.val := by
  induction h with
  | cover h => exact bruhatStep_of_interval_covBy cs h
  | diamond _ _ _ _ _ _ _ _ hab hcd hxa hxb hac had hbc hbd hcz hdz =>
    exact TitsSpace.bruhatStep_diamond_closure hxa hxb hac had hbc hbd hcz hdz
      (fun he => hab (Subtype.ext he)) (fun he => hcd (Subtype.ext he))

end KLInvariance


namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

theorem two_elements_length (cs : CoxeterSystem M W) {n : ℕ} (hn : 0 < n)
    {w : W} (hw : n < cs.length w) :
    ∃ a b : W, a ≠ b ∧ ∀ z, cs.length z = n ↔ z = a ∨ z = b := by
  obtain ⟨i,hi⟩ := exists_alt cs w
  have hr : cs.IsReduced (alt i (cs.length w)) := by
    change cs.length (cs.wordProd _) = _
    rw [← hi,length_alt]
  have hr₁ := reduced_alt_take cs hr (show n+1 ≤ cs.length w by omega)
  have hr₀ := reduced_alt_take cs hr (Nat.le_of_lt hw)
  have hr₂ : cs.IsReduced (alt (!i) n) := by simpa using hr₁.drop 1
  have hlen₀ : cs.length (cs.wordProd (alt i n)) = n := by simpa using hr₀.eq
  have hlen₂ : cs.length (cs.wordProd (alt (!i) n)) = n := by simpa using hr₂.eq
  refine ⟨cs.wordProd (alt i n),cs.wordProd (alt (!i) n),?_,?_⟩
  · intro heq
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hp : cs.wordProd (alt i (k+1+1)) = cs.wordProd (alt (!i) k) := by
      rw [alt_succ,cs.wordProd_cons,← heq,alt_succ,cs.wordProd_cons,
        cs.simple_mul_simple_cancel_left]
    have hlen := cs.length_wordProd_le (alt (!i) k)
    have hred := hr₁.eq
    rw [hp,length_alt] at hred
    rw [length_alt] at hlen
    omega
  · intro z
    constructor
    · intro hz
      obtain ⟨j,hj⟩ := exists_alt cs z
      rw [hz] at hj
      have hj' : j=i ∨ j=(!i) := by cases j <;> cases i <;> simp
      rcases hj' with rfl|rfl
      · exact Or.inl hj
      · exact Or.inr hj
    · rintro (rfl|rfl) <;> assumption

end KLInvariance.Dihedral

namespace KLInvariance
variable {I W : Type*} [Group W] {M : CoxeterMatrix I}

theorem interval_covBy_of_length_succ (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : x ≤ y)
    (hlen : cs.length y.val = cs.length x.val+1) : x ⋖ y := by
  apply covBy_iff_lt_and_eq_or_eq.mpr
  refine ⟨lt_iff_le_and_ne.mpr ⟨hxy,?_⟩,?_⟩
  · intro heq
    have := congrArg (fun z : Interval cs u b => cs.length z.val) heq
    omega
  · intro z hxz hzy
    by_cases hz : z=x
    · exact Or.inl hz
    · right
      by_contra hzy'
      have h₁ := length_lt_of_bruhat_ne cs hxz (fun he => hz (Subtype.ext he.symm))
      have h₂ := length_lt_of_bruhat_ne cs hzy (fun he => hzy' (Subtype.ext he))
      omega

end KLInvariance


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedSheaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded moment-graph sheaves, boundary sections, graded covers and morphisms.
-/

section

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

namespace GradedSheaf
variable {G} (B : GradedSheaf (𝓐 := 𝓐) G)

 theorem EdgeFlabby.flabby (h : B.EdgeFlabby) : B.forget.Flabby := by
  intro Ω hΩ f hf
  exact h Ω (fun e _ he => hΩ (G.increasing e).le he) f hf

variable [Fintype V] [Fintype E]

noncomputable def boundary (x : V) : ModuleData.{uk,ua,um} 𝓐 :=
by
  classical
  letI : Fintype (Sheaf.Outgoing (G := G) x) := inferInstanceAs (Fintype {e : E // G.source e = x})
  exact ModuleData.pi (fun e : Sheaf.Outgoing (G := G) x => B.edge e.val)

end GradedSheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E D : Type um} [PartialOrder V] (G : OrderedGraph V E)

namespace GradedSheaf
variable {G} (B : GradedSheaf (𝓐 := 𝓐) G)
  [Fintype V] [Fintype D] [IsNoetherianRing A]
  (τ : D → V) (α : D → A) (hα : ∀ d, α d ∈ 𝓐 1)

variable (C : ModuleData.MinimalCover (B.attachImage τ α hα))

 theorem extendBottom_generated (hg : B.forget.Generated) :
    (B.extendBottom τ α hα C).forget.Generated := by
  intro x
  induction x using WithBot.recBotCoe with
  | bot =>
    intro z
    obtain ⟨s,hs⟩ := (C.hom.map z).property
    refine ⟨B.attachAssignment τ α hα C z s.val,
      B.attachAssignment_global τ α hα C z s.val s.property ?_,rfl⟩
    intro d
    exact congrFun hs d |>.symm
  | coe x =>
    intro v
    obtain ⟨f,hf,hfx⟩ := hg x v
    obtain ⟨z,hz⟩ := B.lift_global τ α hα C f hf
    exact ⟨B.attachAssignment τ α hα C z f,hz,hfx⟩

end GradedSheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}

namespace GradedSheaf
variable (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)

 theorem reindex_global (f : B.forget.Assignment) (hf : B.forget.IsGlobal f) :
    (B.reindex e).forget.IsGlobal (B.reindexAssignment e f) := by
  intro a _ _
  rw [B.reindex_lower, B.reindex_upper]
  exact hf (e.edge a) (Set.mem_univ _) (Set.mem_univ _)

 theorem reindex_generated (hg : B.forget.Generated) : (B.reindex e).forget.Generated := by
  intro x v
  obtain ⟨f,hf,hfx⟩ := hg (e.vertex x) v
  exact ⟨B.reindexAssignment e f,B.reindex_global e f hf,hfx⟩

 theorem reindex_edgeFlabby (hb : B.EdgeFlabby) : (B.reindex e).EdgeFlabby := by
  intro Ω hΩ f hf
  let Ω' := e.vertex '' Ω
  have hc : B.forget.ClosedUnder Set.univ Ω' := by
    intro a _ hs
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    obtain ⟨x,hx,hxs⟩ := hs
    have hx' : x = G.source a := e.vertex.injective (hxs.trans (e.source a).symm)
    exact ⟨G.target a,hΩ a (Set.mem_univ _) (hx' ▸ hx),e.target a⟩
  have hcf : B.forget.CompatibleOn Ω' (B.unreindexAssignment e f) := by
    intro a hs ht
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    have hh (x : V) (h : e.vertex x ∈ Ω') : x ∈ Ω := by
      obtain ⟨y,hy,hyx⟩ := h
      exact (e.vertex.injective hyx) ▸ hy
    have hfa := hf a (hh _ ((e.source a).symm ▸ hs)) (hh _ ((e.target a).symm ▸ ht))
    rw [← B.reindex_unreindexAssignment e f] at hfa
    exact (B.reindex_lower e a (B.unreindexAssignment e f)).symm.trans
      (hfa.trans (B.reindex_upper e a (B.unreindexAssignment e f)))
  obtain ⟨g,hg,hgf⟩ := hb Ω' hc (B.unreindexAssignment e f) hcf
  refine ⟨B.reindexAssignment e g,B.reindex_global e g hg,?_⟩
  intro x hx
  have hh := hgf (e.vertex x) ⟨x,hx,rfl⟩
  change g (e.vertex x) = f x
  rw [hh]
  exact congrFun (B.reindex_unreindexAssignment e f) x

end GradedSheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

theorem Hom.ofEq_bijective {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) :
    Function.Bijective (Hom.ofEq h).map := by subst N; exact Function.bijective_id

instance unit_free [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hneg : ∀ n < 0, 𝓐 n = ⊥) : Module.Free A (unit.{uk,ua,um} hneg) :=
  inferInstanceAs (Module.Free A (PUnit.{max ua um + 1} → A))

end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}

 theorem kernelMinimal_iff (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    B.KernelMinimal x ↔ LinearMap.ker (B.forget.stalkMap x) ≤
      positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x)) := by
  classical
  constructor
  · intro h v hv
    let f : B.forget.Assignment := Function.update 0 x v
    have hf : f x = v := by simp [f]
    rw [← hf]
    apply h f
    intro e he
    have hh := congrFun (LinearMap.mem_ker.mp hv) (⟨e,he⟩ : Sheaf.Outgoing x)
    subst x
    simpa [Sheaf.stalkMap,f] using hh
  · intro h f hf
    apply h
    apply LinearMap.mem_ker.mpr
    funext e
    rcases e with ⟨e,he⟩
    subst x
    exact hf e rfl

 theorem reindex_freeStalks (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    (h : B.FreeStalks) : (B.reindex e).FreeStalks := fun x => h (e.vertex x)

 theorem reindex_upperQuotient (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    {α : F → A} (h : B.UpperQuotient α) : (B.reindex e).UpperQuotient (α ∘ e.edge) := by
  intro a
  let j := ModuleData.Hom.ofEq (congrArg B.vertex (e.target a))
  have hj := ModuleData.Hom.ofEq_bijective (congrArg B.vertex (e.target a))
  refine ⟨(h (e.edge a)).1.comp hj.2,?_⟩
  intro v
  change (B.upper (e.edge a)).map (j.map v) = 0 ↔ ∃ w, v = α (e.edge a) • w
  rw [(h (e.edge a)).2]
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨z,rfl⟩ := hj.2 w
    exact ⟨z,hj.1 (hw.trans (map_smul j.map (α (e.edge a)) z).symm)⟩
  · rintro ⟨w,rfl⟩
    exact ⟨j.map w,map_smul _ _ _⟩

 theorem reindex_kernelMinimal (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)
    (x : V) (h : B.KernelMinimal (e.vertex x)) : (B.reindex e).KernelMinimal x := by
  intro f hf
  have hh : ∀ a, H.source a = e.vertex x →
      B.forget.lower a (B.unreindexAssignment e f (H.source a)) = 0 := by
    intro a ha
    obtain ⟨a,rfl⟩ := e.edge.surjective a
    have hs : G.source a = x := e.vertex.injective ((e.source a).trans ha)
    have hv := hf a hs
    rw [← B.reindex_unreindexAssignment e f] at hv
    exact (B.reindex_lower e a (B.unreindexAssignment e f)).symm.trans hv
  have hm := h (B.unreindexAssignment e f) hh
  have he := congrFun (B.reindex_unreindexAssignment e f) x
  exact he ▸ hm

variable {D : Type um} [Fintype V] [Fintype D] [IsNoetherianRing A]
  (B : GradedSheaf (𝓐 := 𝓐) G) (τ : D → V) (α : D → A)
  (hα : ∀ d, α d ∈ 𝓐 1) (C : ModuleData.MinimalCover (B.attachImage τ α hα))

 theorem extendBottom_freeStalks (hb : B.FreeStalks) :
    (B.extendBottom τ α hα C).FreeStalks := by
  intro x
  induction x using WithBot.recBotCoe with
  | bot => exact C.free
  | coe x => exact hb x

 theorem extendBottom_upperQuotient {αold : E → A} (hb : B.UpperQuotient αold) :
    (B.extendBottom τ α hα C).UpperQuotient (Sum.elim αold α) := by
  intro e
  cases e with
  | inl e => exact hb e
  | inr d =>
    let S := LinearMap.range (LinearMap.lsmul A (B.vertex (τ d)) (α d))
    refine ⟨S.mkQ_surjective,?_⟩
    intro v
    change S.mkQ v = 0 ↔ ∃ w, v = α d • w
    refine (Submodule.Quotient.mk_eq_zero S).trans ?_
    change (∃ w, α d • w = v) ↔ ∃ w, v = α d • w
    exact ⟨fun ⟨w,hw⟩ => ⟨w,hw.symm⟩,fun ⟨w,hw⟩ => ⟨w,hw.symm⟩⟩

 theorem extendBottom_kernelMinimal_bot : (B.extendBottom τ α hα C).KernelMinimal ⊥ := by
  intro f hf
  apply C.minimal
  apply LinearMap.mem_ker.mpr
  apply Subtype.ext
  funext d
  exact hf (Sum.inr d) rfl

 theorem extendBottom_kernelMinimal_coe (x : V) (h : B.KernelMinimal x) :
    (B.extendBottom τ α hα C).KernelMinimal (x : WithBot V) := by
  intro f hf
  apply h (fun y => f (y : WithBot V))
  intro a ha
  exact hf (Sum.inl a) (congrArg (fun y : V => (y : WithBot V)) ha)

end KLInvariance.MomentGraph.GradedSheaf

end


section


namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}

variable (B : Sheaf.{u,v,w,z} (R := R) G)

def upwardKernel (x : V) (F : Set (Outgoing (G := G) x)) : Submodule R (B.vertex x) where
  carrier := {v | ∀ e ∈ F, B.stalkMap x v e = 0}
  zero_mem' := by intro e _; simp
  add_mem' := by intro v w hv hw e he; simp [hv e he,hw e he]
  smul_mem' := by intro r v hv e he; simp [hv e he]

end KLInvariance.MomentGraph.Sheaf

end


section


namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G) (x : V)

/-- An isomorphism already constructed strictly above `x`, including the edge
modules whose upper endpoints are above `x`. The latter are canonically supplied
by the upper quotient rule in the local decomposition. -/
structure AboveIso where
  vertex : ∀ y, x < y → B.vertex y ≃ₗ[R] C.vertex y
  edge : ∀ e, x < G.target e → B.edge e ≃ₗ[R] C.edge e
  lower : ∀ e (h : x < G.source e) v,
    edge e (h.trans (G.increasing e)) (B.lower e v) =
      C.lower e (vertex (G.source e) h v)
  upper : ∀ e (h : x < G.target e) v,
    edge e h (B.upper e v) = C.upper e (vertex (G.target e) h v)

namespace AboveIso
variable {B C x} (j : AboveIso B C x)

noncomputable def mapAssignment (f : B.Assignment) : C.Assignment :=
by
  classical
  exact fun y => if h : x < y then j.vertex y h (f y) else 0

lemma mapAssignment_at (f : B.Assignment) (y : V) (h : x < y) :
    j.mapAssignment f y = j.vertex y h (f y) := by
  classical
  simp [mapAssignment,h]

lemma compatible (f : B.Assignment) (hf : B.CompatibleOn (Set.Ioi x) f) :
    C.CompatibleOn (Set.Ioi x) (j.mapAssignment f) := by
  intro e hs ht
  change x < G.source e at hs
  change x < G.target e at ht
  rw [j.mapAssignment_at f _ hs,j.mapAssignment_at f _ ht,← j.lower e hs,← j.upper e ht]
  exact congrArg (j.edge e ht) (hf e hs ht)

noncomputable def boundary : B.Boundary x ≃ₗ[R] C.Boundary x :=
  LinearEquiv.piCongrRight (fun e => j.edge e.val (lt_of_eq_of_lt e.property.symm (G.increasing e.val)))

lemma boundaryMap (f : B.sections (Set.Ioi x)) :
    j.boundary (B.boundaryMap x f) =
      C.boundaryMap x ⟨j.mapAssignment f.val,j.compatible f.val f.property⟩ := by
  funext e
  change j.edge e.val _ (B.upper e.val (f.val (G.target e.val))) =
    C.upper e.val (j.mapAssignment f.val (G.target e.val))
  rw [j.mapAssignment_at _ _ (lt_of_eq_of_lt e.property.symm (G.increasing e.val)),j.upper]

end AboveIso
end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.QuotientEdge
variable {R M N E F : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

@[simp] lemma iso_apply (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : M ≃ₗ[R] N) (hk : (LinearMap.ker f).map h.toLinearMap = LinearMap.ker g) (v : M) :
    iso f g hf hg h hk (f v) = g (h v) := by
  simp [iso,Submodule.Quotient.equiv]

lemma map_kernel_scalar (f : M →ₗ[R] E) (g : N →ₗ[R] F) (r : R)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v = r • w)
    (hg : ∀ v, g v = 0 ↔ ∃ w, v = r • w) (h : M ≃ₗ[R] N) :
    (LinearMap.ker f).map h.toLinearMap = LinearMap.ker g := by
  ext v
  constructor
  · rintro ⟨w,hw,rfl⟩
    obtain ⟨u,rfl⟩ := (hf w).mp hw
    exact (hg _).mpr ⟨h u,h.map_smul r u⟩
  · intro hv
    obtain ⟨w,rfl⟩ := (hg v).mp hv
    refine ⟨r • h.symm w,(hf _).mpr ⟨h.symm w,rfl⟩,?_⟩
    simp

/-- No separate choice of edge data or scalar compatibility hypothesis is needed. -/
theorem exists_scalar_iso (f : M →ₗ[R] E) (g : N →ₗ[R] F) (r : R)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v = r • w)
    (hg : ∀ v, g v = 0 ↔ ∃ w, v = r • w) (h : M ≃ₗ[R] N) :
    ∃ j : E ≃ₗ[R] F, ∀ v, j (f v) = g (h v) :=
  ⟨iso f g hfs hgs h (map_kernel_scalar f g r hf hg h),iso_apply f g hfs hgs h _⟩

end KLInvariance.QuotientEdge

end


section

/-! Partial sheaf isomorphisms on upper sets, and their actual descending
extension. In particular the incoming edge component is induced by the upper
scalar quotient, not independently assumed. -/
namespace KLInvariance.MomentGraph.Sheaf
universe u v w z z'
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V]
  {E : Type w} {G : OrderedGraph V E}
  (B : Sheaf.{u,v,w,z} (R := R) G) (C : Sheaf.{u,v,w,z'} (R := R) G)

 def UpperQuotient (α : E → R) : Prop :=
  ∀ e, Function.Surjective (B.upper e) ∧
    ∀ v, B.upper e v = 0 ↔ ∃ w, v = α e • w

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.MomentGraph
universe um
variable {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

 def removeGraph (x : V) (ht : ∀ e, G.target e ≠ x) :
    OrderedGraph {y : V // y ≠ x} {e : E // G.source e ≠ x} where
  source e := ⟨G.source e.val,e.property⟩
  target e := ⟨G.target e.val,ht e.val⟩
  increasing e := G.increasing e.val

 def removeTarget (x : V) (ht : ∀ e, G.target e ≠ x) :
    {e : E // G.source e = x} → {y : V // y ≠ x} := fun e => ⟨G.target e.val,ht e.val⟩

noncomputable def splitVertex (x : V) : V ≃ WithBot {y : V // y ≠ x} := by
  classical
  exact
    { toFun := fun y => if h : y=x then ⊥ else (⟨y,h⟩ : {y : V // y ≠ x})
      invFun := WithBot.recBotCoe x Subtype.val
      left_inv := by intro y; by_cases h : y=x <;> simp [h]
      right_inv := by
        intro y
        induction y using WithBot.recBotCoe with
        | bot => simp
        | coe y => simp [y.property] }

noncomputable def splitEdge (x : V) : E ≃ {e : E // G.source e ≠ x} ⊕ {e : E // G.source e = x} := by
  classical
  exact
    { toFun := fun e => if h : G.source e=x then Sum.inr ⟨e,h⟩ else Sum.inl ⟨e,h⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := by intro e; by_cases h : G.source e=x <;> simp [h]
      right_inv := by
        intro e
        cases e with
        | inl e => simp [e.property]
        | inr e => simp [e.property] }

omit [PartialOrder V] in
@[simp] theorem splitVertex_self (x : V) : splitVertex x x = ⊥ := by
  classical
  simp [splitVertex]

omit [PartialOrder V] in
 theorem splitVertex_ne (x y : V) (hy : y ≠ x) :
    splitVertex x y = (⟨y,hy⟩ : {y : V // y ≠ x}) := by
  classical
  simp [splitVertex,hy]

noncomputable def splitGraph (x : V) (ht : ∀ e, G.target e ≠ x) :
    GraphEquiv G (bottomGraph (removeGraph G x ht) (removeTarget G x ht)) where
  vertex := splitVertex x
  edge := splitEdge G x
  source := by
    classical
    intro e
    by_cases h : G.source e=x
    · simp [splitEdge,splitVertex,h,bottomGraph]
    · simp [splitEdge,splitVertex,h,bottomGraph,removeGraph]
  target := by
    classical
    intro e
    by_cases h : G.source e=x
    · simp [splitEdge,splitVertex,h,ht e,bottomGraph,removeTarget]
    · simp [splitEdge,splitVertex,h,ht e,bottomGraph,removeGraph]

 theorem splitEdge_labels {A : Type*} (α : E → A) (x : V) :
    (Sum.elim (fun e : {e : E // G.source e ≠ x} => α e.val)
      (fun e : {e : E // G.source e = x} => α e.val)) ∘ (splitEdge G x) = α := by
  classical
  funext e
  by_cases h : G.source e=x <;> simp [splitEdge,h]

end KLInvariance.MomentGraph

end


section

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

variable {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

noncomputable def singletonSheaf [IsEmpty E] : GradedSheaf (𝓐 := 𝓐) G where
  vertex := fun _ => ModuleData.unit hneg
  edge := isEmptyElim
  lower := isEmptyElim
  upper := isEmptyElim

 theorem singleton_boundarySheaf (b : V) (hV : ∀ x, x=b) (α : E → A) :
    Nonempty (BoundarySheaf hneg G α b) := by
  have hempty : IsEmpty E := ⟨fun e => (G.increasing e).ne ((hV _).trans (hV _).symm)⟩
  let := hempty
  let B := singletonSheaf hneg G
  refine ⟨⟨B,?_,?_,?_,?_,rfl,?_⟩⟩
  · intro x
    exact ModuleData.unit_free hneg
  · intro e
    exact isEmptyElim e
  · intro Ω _ f _
    exact ⟨f,fun e => isEmptyElim e,fun _ _ => rfl⟩
  · intro x v
    exact ⟨fun _ => v,fun e => isEmptyElim e,rfl⟩
  · intro x hx
    exact (hx (hV x)).elim

variable [IsNoetherianRing A]
  (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐)

include hscalar in
 theorem exists_boundarySheaf_card (n : ℕ)
    [Fintype V] [Fintype E] (b : V) (hb : ∀ x, x ≤ b)
    (α : E → A) (hα : ∀ e, α e ∈ 𝓐 1) (hn : Fintype.card V = n) :
    Nonempty (BoundarySheaf hneg G α b) := by
  classical
  induction n using Nat.strong_induction_on generalizing V E with
  | h n ih =>
    by_cases hV : ∀ x : V, x=b
    · exact singleton_boundarySheaf hneg G b hV α
    obtain ⟨y,hy⟩ := not_forall.mp hV
    obtain ⟨x,hx⟩ := exists_minimal_of_wellFoundedLT (fun _ : V => True) ⟨b,trivial⟩
    have hxb : x ≠ b := by
      intro he
      have hlt : y < x := he ▸ lt_of_le_of_ne (hb y) hy
      exact hx.not_lt trivial hlt
    have ht (e : E) : G.target e ≠ x := by
      intro he
      exact hx.not_lt trivial (he ▸ G.increasing e)
    let V' := {y : V // y ≠ x}
    let E' := {e : E // G.source e ≠ x}
    let D := {e : E // G.source e = x}
    let G' := removeGraph G x ht
    let τ := removeTarget G x ht
    let b' : V' := ⟨b,hxb.symm⟩
    let α' : E' → A := fun e => α e.val
    let β : D → A := fun e => α e.val
    have hβ : ∀ e : D, β e ∈ 𝓐 1 := fun e => hα e.val
    have hcard : Fintype.card V' < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (x := x) (not_not.mpr rfl)
    obtain ⟨B⟩ := ih (Fintype.card V') hcard G' b' (fun y => hb y.val)
      α' (fun e => hα e.val) rfl
    obtain ⟨C⟩ := ModuleData.exists_minimalCover hneg hscalar (B.sheaf.attachImage τ β hβ)
    let H := B.sheaf.extendBottom τ β hβ C
    let e := splitGraph G x ht
    refine ⟨⟨H.reindex e,?_,?_,?_,?_,?_,?_⟩⟩
    · exact H.reindex_freeStalks e (B.sheaf.extendBottom_freeStalks τ β hβ C B.free)
    · have hh := H.reindex_upperQuotient e
        (B.sheaf.extendBottom_upperQuotient τ β hβ C B.quotient)
      have he : (Sum.elim α' β) ∘ e.edge = α := splitEdge_labels G α x
      exact he ▸ hh
    · exact H.reindex_edgeFlabby e (B.sheaf.extendBottom_edgeFlabby τ β hβ C B.flabby)
    · exact H.reindex_generated e (B.sheaf.extendBottom_generated τ β hβ C B.generated)
    · change H.vertex (splitVertex x b) = _
      rw [splitVertex_ne x b hxb.symm]
      exact B.top
    · intro z hz
      apply H.reindex_kernelMinimal e z
      by_cases hzx : z=x
      · subst z
        change H.KernelMinimal (splitVertex x x)
        rw [splitVertex_self]
        exact B.sheaf.extendBottom_kernelMinimal_bot τ β hβ C
      · change H.KernelMinimal (splitVertex x z)
        rw [splitVertex_ne x z hzx]
        apply B.sheaf.extendBottom_kernelMinimal_coe τ β hβ C ⟨z,hzx⟩
        apply B.minimal
        intro hzz
        exact hz (congrArg Subtype.val hzz)

include hscalar in
 theorem exists_boundarySheaf [Fintype V] [Fintype E] (b : V) (hb : ∀ x, x ≤ b)
    (α : E → A) (hα : ∀ e, α e ∈ 𝓐 1) : Nonempty (BoundarySheaf hneg G α b) :=
  exists_boundarySheaf_card hneg G hscalar (Fintype.card V) b hb α hα rfl

end KLInvariance.MomentGraph

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

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G)

/-- The actual lower restriction, with its source explicitly identified. -/
def lowerAt (x : V) (e : Sheaf.Outgoing (G := G) x) :
    ModuleData.Hom (B.vertex x) (B.edge e.val) := by
  rcases e with ⟨e,rfl⟩
  exact B.lower e

 theorem lowerAt_map (x : V) (e : Sheaf.Outgoing (G := G) x) (v : B.vertex x) :
    (B.lowerAt x e).map v = B.forget.stalkMap x v e := by
  rcases e with ⟨e,rfl⟩
  rfl

/-- The same kernel, typed in the graded stalk so base-field instances are explicit. -/
def upwardSubmodule (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) :
    Submodule A (B.vertex x) := B.forget.upwardKernel x F

 theorem upwardKernel_homogeneous (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) :
    ∀ n v, v ∈ B.upwardSubmodule x F →
      component (B.vertex x).piece n v ∈ B.upwardSubmodule x F := by
  intro n v hv e he
  rw [← B.lowerAt_map]
  rw [← (B.lowerAt x e).component]
  rw [B.lowerAt_map,hv e he]
  exact map_zero (component (B.edge e.val).piece n)

noncomputable def upwardKernel [IsNoetherianRing A]
    (x : V) (F : Set (Sheaf.Outgoing (G := G) x)) : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.sub (B.vertex x) (B.upwardSubmodule x F) (B.upwardKernel_homogeneous x F)

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Graded uniqueness/recognition for the genuinely constructed minimal
boundary covers. Character and self-duality are not included in this data. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} [Fintype V] [Fintype E]
  (B : GradedSheaf (𝓐 := 𝓐) G)

noncomputable def stalkHom (x : V) : ModuleData.Hom (B.vertex x) (B.boundary x) where
  map := B.forget.stalkMap x
  graded := by
    intro n v hv e _
    change B.forget.stalkMap x v e ∈ (B.edge e.val).piece n
    rw [← B.lowerAt_map]
    exact (B.lowerAt x e).graded n v hv

end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

def equivOfEq {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) : M ≃ₗ[A] N :=
  h ▸ LinearEquiv.refl A M

 theorem equivOfEq_graded {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N)
    (n : ℤ) (v : M) (hv : v ∈ M.piece n) : equivOfEq h v ∈ N.piece n := by
  subst N
  exact hv

end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.MomentGraph.Sheaf
open TensorProduct
universe ur us uv ue um
variable {R : Type ur} [CommRing R] (S : Type us) [CommRing S] [Algebra R S]
  {V : Type uv} [PartialOrder V] {E : Type ue} {G : OrderedGraph V E}
  (B : Sheaf.{ur,uv,ue,um} (R := R) G)

noncomputable def baseChange : Sheaf (R := S) G where
  vertex x := ModuleCat.of S (S ⊗[R] B.vertex x)
  edge e := ModuleCat.of S (S ⊗[R] B.edge e)
  lower e := AlgebraTensorModule.lTensor S S (B.lower e)
  upper e := AlgebraTensorModule.lTensor S S (B.upper e)

noncomputable def tensorAssignments : S ⊗[R] B.Assignment →ₗ[S] (B.baseChange S).Assignment :=
  TensorProduct.piRightHom R S S (fun x => B.vertex x)

@[simp] theorem tensorAssignments_tmul (s : S) (f : B.Assignment) (x : V) :
    B.tensorAssignments S (s ⊗ₜ f) x = s ⊗ₜ f x := rfl

lemma baseChange_tmul_compatible (Ω : Set V) (s : S) (f : B.Assignment)
    (hf : B.CompatibleOn Ω f) : (B.baseChange S).CompatibleOn Ω (fun x => s ⊗ₜ f x) := by
  intro e hs ht
  change s ⊗ₜ[R] B.lower e (f (G.source e)) = s ⊗ₜ[R] B.upper e (f (G.target e))
  rw [hf e hs ht]

noncomputable def tensorSections (Ω : Set V) :
    S ⊗[R] B.sections Ω →ₗ[S] (B.baseChange S).sections Ω :=
  ((B.tensorAssignments S).comp (AlgebraTensorModule.lTensor S S (B.sections Ω).subtype)).codRestrict
    ((B.baseChange S).sections Ω) (by
      intro z
      induction z using OAI.tensorInductionOn with
      | tmul s f => exact B.baseChange_tmul_compatible S Ω s f.val f.property
      | add z t hz ht => simpa only [map_add] using Submodule.add_mem _ hz ht)

@[simp] theorem tensorSections_tmul (Ω : Set V) (s : S) (f : B.sections Ω) (x : V) :
    (B.tensorSections S Ω (s ⊗ₜ f)).val x = s ⊗ₜ f.val x := rfl

end KLInvariance.MomentGraph.Sheaf

end


section

/-! Pullback along a directed graph map. Relative-order flabbiness requires
only outgoing completeness for the surviving edges, not equality of the two
orders on a coset. -/
namespace KLInvariance.MomentGraph
universe ur uv ue uw uf um
variable {V : Type uv} [PartialOrder V] {E : Type ue}
  {W : Type uw} [PartialOrder W] {F : Type uf}

structure GraphMap (G : OrderedGraph V E) (H : OrderedGraph W F) where
  vertex : V → W
  edge : E → F
  source : ∀ e, vertex (G.source e) = H.source (edge e)
  target : ∀ e, vertex (G.target e) = H.target (edge e)

namespace Sheaf
variable {R : Type ur} [CommRing R] {G : OrderedGraph V E} {H : OrderedGraph W F}
  (B : Sheaf.{ur,uw,uf,um} (R := R) H) (f : GraphMap G H)
noncomputable section

 def pullback : Sheaf (R := R) G where
  vertex x := B.vertex (f.vertex x)
  edge e := B.edge (f.edge e)
  lower e := (B.lower (f.edge e)).comp (moduleEq (congrArg B.vertex (f.source e))).toLinearMap
  upper e := (B.upper (f.edge e)).comp (moduleEq (congrArg B.vertex (f.target e))).toLinearMap

 def pullAssignment (s : B.Assignment) : (B.pullback f).Assignment := fun x => s (f.vertex x)

@[simp] theorem pull_lower (e : E) (s : B.Assignment) :
    (B.pullback f).lower e (B.pullAssignment f s (G.source e)) =
      B.lower (f.edge e) (s (H.source (f.edge e))) := by
  exact congrArg (B.lower (f.edge e)) (moduleEq_apply B.vertex (f.source e) s)

@[simp] theorem pull_upper (e : E) (s : B.Assignment) :
    (B.pullback f).upper e (B.pullAssignment f s (G.target e)) =
      B.upper (f.edge e) (s (H.target (f.edge e))) := by
  exact congrArg (B.upper (f.edge e)) (moduleEq_apply B.vertex (f.target e) s)

 theorem pull_global (s : B.Assignment) (hs : B.IsGlobal s) :
    (B.pullback f).IsGlobal (B.pullAssignment f s) := by
  intro e _ _
  rw [pull_lower,pull_upper]
  exact hs (f.edge e) (Set.mem_univ _) (Set.mem_univ _)

 theorem pullback_generated (hg : B.Generated) : (B.pullback f).Generated := by
  intro x v
  obtain ⟨s,hs,hx⟩ := hg (f.vertex x) v
  exact ⟨B.pullAssignment f s,B.pull_global f s hs,hx⟩

 def pushAssignment (s : (B.pullback f).Assignment) : B.Assignment := by
  classical
  exact fun y => if h : ∃ x, f.vertex x=y then
    moduleEq (congrArg B.vertex h.choose_spec) (s h.choose) else 0

 theorem pull_push (hi : Function.Injective f.vertex) (s : (B.pullback f).Assignment) :
    B.pullAssignment f (B.pushAssignment f s) = s := by
  classical
  change (∀ x, B.vertex (f.vertex x)) at s
  funext x
  have h : ∃ z, f.vertex z=f.vertex x := ⟨x,rfl⟩
  change @Eq (B.vertex (f.vertex x))
    (if hh : ∃ z, f.vertex z=f.vertex x then
      moduleEq (congrArg B.vertex hh.choose_spec) (s hh.choose) else 0) (s x)
  rw [dite_eq_left h]
  have hx : h.choose=x := hi h.choose_spec
  exact moduleEq_apply (fun z => B.vertex (f.vertex z)) hx s

 theorem pullback_quotient (α : F → R) (hq : B.UpperQuotient α) :
    (B.pullback f).UpperQuotient (fun e => α (f.edge e)) := by
  intro e
  let j := moduleEq (congrArg B.vertex (f.target e))
  refine ⟨?_,?_⟩
  · exact (hq (f.edge e)).1.comp j.surjective
  · intro v
    change B.upper (f.edge e) (j v) = 0 ↔ _
    rw [(hq (f.edge e)).2]
    constructor
    · rintro ⟨w,hw⟩
      refine ⟨j.symm w,?_⟩
      apply j.injective
      change j v = j (α (f.edge e) • j.symm w)
      rw [map_smul,LinearEquiv.apply_symm_apply]
      exact hw
    · rintro ⟨w,rfl⟩
      exact ⟨j w,j.map_smul _ _⟩

end
end Sheaf
end KLInvariance.MomentGraph

end


section

/-! Restriction along an outgoing-complete actual graph embedding.  In
particular this supports passage from [1,b] to [u,b] without changing stalks. -/
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}
namespace GradedSheaf
variable (B : GradedSheaf (𝓐 := 𝓐) H) (f : GraphMap G H)

 theorem moduleEq_graded {x y : W} (h : x=y) (n : ℤ)
    (v : B.vertex x) (hv : v ∈ (B.vertex x).piece n) :
    Sheaf.moduleEq (congrArg B.forget.vertex h) v ∈ (B.vertex y).piece n := by
  subst y
  exact hv

 def pullback : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := B.vertex (f.vertex x)
  edge e := B.edge (f.edge e)
  lower e := ⟨(B.forget.pullback f).lower e,fun n v hv =>
    (B.lower (f.edge e)).graded n _ (B.moduleEq_graded (f.source e) n v hv)⟩
  upper e := ⟨(B.forget.pullback f).upper e,fun n v hv =>
    (B.upper (f.edge e)).graded n _ (B.moduleEq_graded (f.target e) n v hv)⟩

@[simp] theorem forget_pullback : (B.pullback f).forget = B.forget.pullback f := rfl

 theorem pullback_edgeFlabby (hb : B.EdgeFlabby)
    (hi : Function.Injective f.vertex)
    (hlift : ∀ e x, f.vertex x = H.source e → ∃ a, f.edge a=e ∧ G.source a=x) :
    (B.pullback f).EdgeFlabby := by
  intro Ω hΩ s hs
  have hc : B.forget.ClosedUnder Set.univ (f.vertex '' Ω) := by
    intro e _ hsource
    obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e x hxe
    exact ⟨G.target a,hΩ a (Set.mem_univ a) hx,f.target a⟩
  have hcompat : B.forget.CompatibleOn (f.vertex '' Ω) (B.forget.pushAssignment f s) := by
    intro e hsource htarget
    obtain ⟨x,hx,hxe⟩ := hsource
    obtain ⟨a,rfl,rfl⟩ := hlift e x hxe
    obtain ⟨y,hy,hye⟩ := htarget
    have hya : y=G.target a := hi (hye.trans (f.target a).symm)
    subst y
    have hh := hs a hx hy
    change (B.forget.pullback f).lower a (s (G.source a)) =
      (B.forget.pullback f).upper a (s (G.target a)) at hh
    rw [← B.forget.pull_push f hi s] at hh
    rw [Sheaf.pull_lower,Sheaf.pull_upper] at hh
    exact hh
  obtain ⟨t,ht,hts⟩ := hb (f.vertex '' Ω) hc (B.forget.pushAssignment f s) hcompat
  refine ⟨B.forget.pullAssignment f t,B.forget.pull_global f t ht,?_⟩
  intro x hx
  change t (f.vertex x) = s x
  rw [hts (f.vertex x) ⟨x,hx,rfl⟩]
  exact congrFun (B.forget.pull_push f hi s) x

 theorem pullback_kernelMinimal (hi : Function.Injective f.vertex)
    (hlift : ∀ e x, f.vertex x = H.source e → ∃ a, f.edge a=e ∧ G.source a=x)
    (x : V) (hx : B.KernelMinimal (f.vertex x)) :
    (B.pullback f).KernelMinimal x := by
  intro s hs
  have h := hx (B.forget.pushAssignment f s) (by
    intro e he
    obtain ⟨a,rfl,hax⟩ := hlift e x he.symm
    have hh := hs a hax
    change (B.forget.pullback f).lower a (s (G.source a)) = 0 at hh
    rw [← B.forget.pull_push f hi s,Sheaf.pull_lower] at hh
    exact hh)
  have he : B.forget.pushAssignment f s (f.vertex x)=s x :=
    congrFun (B.forget.pull_push f hi s) x
  rwa [he] at h

end GradedSheaf

namespace BoundarySheaf
variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  {hneg : ∀ n < 0, 𝓐 n = ⊥} {α : F → A} {b : W}
  (B : BoundarySheaf hneg H α b) (f : GraphMap G H)
  (hi : Function.Injective f.vertex)
  (hlift : ∀ e x, f.vertex x = H.source e → ∃ a, f.edge a=e ∧ G.source a=x)
  (c : V) (hc : f.vertex c=b)

 def pullback : BoundarySheaf hneg G (fun e => α (f.edge e)) c where
  sheaf := B.sheaf.pullback f
  free x := B.free (f.vertex x)
  quotient := B.sheaf.forget.pullback_quotient f α B.quotient
  flabby := B.sheaf.pullback_edgeFlabby f B.flabby hi hlift
  generated := B.sheaf.forget.pullback_generated f B.generated
  top := by change B.sheaf.vertex (f.vertex c)=_; rw [hc,B.top]
  minimal x hx := B.sheaf.pullback_kernelMinimal f hi hlift x
    (B.minimal (f.vertex x) (fun h => hx (hi (h.trans hc.symm))))

end BoundarySheaf
end KLInvariance.MomentGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section


omit [Fintype σ] in
 theorem polynomialLabel_ne_zero (e : Edge cs u b) :
    polynomialLabel cs u b basis e ≠ 0 := by
  intro he
  have h0 : SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b e).val) = 0 :=
    (SymmetricAlgebra.equivMvPolynomial basis).injective
      (he.trans (map_zero _).symm)
  have h1 : embed M (root cs u b e).val = 0 :=
    EdgeAlgebra.symmetric_ι_injective (k := ℝ) (h0.trans (map_zero _).symm)
  have h2 := congrArg Prod.fst h1
  exact (root cs u b e).property.1.ne_zero h2


 theorem exists_boundarySheaf (hub : BruhatLE cs u b) :
    Nonempty (BoundarySheaf (polynomialGrading_negative ℝ σ)
      (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩) := by
  classical
  let : Finite (Interval cs u b) := interval_finite cs u b
  let : Fintype (Interval cs u b) := Fintype.ofFinite _
  let : Fintype (Edge cs u b) := Fintype.ofFinite _
  exact MomentGraph.exists_boundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomial_scalar_mod_positive ℝ σ)
    ⟨b,hub,bruhat_refl cs b⟩ (fun x => x.property.2)
    (polynomialLabel cs u b basis) (polynomialLabel_homogeneous cs u b basis)

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
noncomputable section

def boundarySheaf : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩ :=
  (exists_boundarySheaf cs u b basis hub).some

end
end KLInvariance.BruhatGraph

end


section

/-! Parity matching in finite lower Bruhat intervals, used only to construct
actual dihedral interpolation sections. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem one_bruhat (x : W) : BruhatLE cs 1 x := by
  obtain ⟨ω,hω,hx⟩ := cs.exists_isReduced x
  simpa only [cs.wordProd_nil,← hx] using bruhat_of_subword cs (List.nil_sublist ω) hω

end
end KLInvariance

end


section

/-! The actual minimal boundary sheaf is indecomposable: it has no nontrivial
homogeneous idempotent. No KL character or costalk freeness is used here. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}

structure Endomorphism (B : GradedSheaf (𝓐 := 𝓐) G) where
  vertex : ∀ x, ModuleData.Hom (B.vertex x) (B.vertex x)
  edge : ∀ e, ModuleData.Hom (B.edge e) (B.edge e)
  lower : ∀ e v, (edge e).map ((B.lower e).map v) =
    (B.lower e).map ((vertex (G.source e)).map v)
  upper : ∀ e v, (edge e).map ((B.upper e).map v) =
    (B.upper e).map ((vertex (G.target e)).map v)

end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! A genuine homogeneous self-map of a minimal cover is invertible when its
map on the covered module is invertible. Used for the integral summand bridge. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

include hneg hzero in
 theorem MinimalCover.bijective_of_boundaryIso {M : ModuleData.{uk,ua,um} 𝓐}
    (C : MinimalCover M) (f : Hom C.source C.source) (g : M ≃ₗ[A] M)
    (hg : ∀ n v, v ∈ M.piece n → g v ∈ M.piece n)
    (hcomm : ∀ v, C.hom.map (f.map v) = g (C.hom.map v)) :
    Function.Bijective f.map := by
  let gh : Hom M M := ⟨g.toLinearMap,hg⟩
  let gi : Hom M M :=
    { map := g.symm.toLinearMap
      graded := by
        intro n v hv
        apply gh.mem_of_map_mem g.injective n
        change g (g.symm v) ∈ M.piece n
        simpa only [LinearEquiv.apply_symm_apply] using hv }
  let := C.free
  obtain ⟨l,hl⟩ := exists_hom_lift hneg hzero C.hom C.surjective (gi.comp C.hom)
  have hla (v : C.source) : C.hom.map (l.map v) = g.symm (C.hom.map v) :=
    LinearMap.congr_fun hl v
  have hfl : Function.Bijective (f.comp l).map := by
    apply Hom.bijective_of_mod_positive
    intro v
    apply C.minimal
    change C.hom.map (v-f.map (l.map v))=0
    rw [map_sub,hcomm,hla,LinearEquiv.apply_symm_apply,sub_self]
  have hlf : Function.Bijective (l.comp f).map := by
    apply Hom.bijective_of_mod_positive
    intro v
    apply C.minimal
    change C.hom.map (v-l.map (f.map v))=0
    rw [map_sub,hla,hcomm,LinearEquiv.symm_apply_apply,sub_self]
  exact ⟨Function.Injective.of_comp hlf.1,Function.Surjective.of_comp hfl.2⟩

end
end KLInvariance.Graded.ModuleData

end


section

/-! A graded endomorphism of the actual normalized minimal boundary sheaf
is an automorphism as soon as its top component is one. -/
namespace KLInvariance.MomentGraph.GradedSheaf.Endomorphism
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} {B : GradedSheaf (𝓐 := 𝓐) G}
  (f : Endomorphism B)

 theorem edge_bijective_of_vertex {α : E → A}
    (hBq : B.forget.UpperQuotient α) (e : E)
    (hv : Function.Bijective (f.vertex (G.target e)).map) :
    Function.Bijective (f.edge e).map := by
  obtain ⟨j,hj⟩ := QuotientEdge.exists_scalar_iso
    (B.upper e).map (B.upper e).map (α e)
    (hBq e).1 (hBq e).1 (hBq e).2 (hBq e).2
    (LinearEquiv.ofBijective (f.vertex (G.target e)).map hv)
  have heq : (f.edge e).map = j.toLinearMap := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := (hBq e).1 v
    exact (f.upper e w).trans (hj w).symm
  rw [heq]
  exact j.bijective

end KLInvariance.MomentGraph.GradedSheaf.Endomorphism

end


section

namespace KLInvariance.Graded.ModuleData.Hom
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {M N : ModuleData.{uk,ua,um} 𝓐}
noncomputable section

 def inverse (f : Hom M N) (hf : Function.Bijective f.map) : Hom N M where
  map := (LinearEquiv.ofBijective f.map hf).symm.toLinearMap
  graded := by
    intro n v hv
    apply f.mem_of_map_mem hf.1 n
    change (LinearEquiv.ofBijective f.map hf) ((LinearEquiv.ofBijective f.map hf).symm v) ∈ N.piece n
    simpa only [LinearEquiv.apply_symm_apply] using hv

 theorem map_inverse (f : Hom M N) (hf : Function.Bijective f.map) (v : N) :
    f.map ((f.inverse hf).map v)=v := (LinearEquiv.ofBijective f.map hf).apply_symm_apply v

end
end KLInvariance.Graded.ModuleData.Hom

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded decomposition characters, reflection-plane algebras and reflection Frobenius structures.
-/


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

/-- Any two distinct positive roots in a two-dimensional root plane span it. -/
theorem rootPlane_eq_of_mem (a b l r : PositiveRoot M cs) (hab : a ≠ b)
    (hl : l.val ∈ rootPlane a b) (hr : r.val ∈ rootPlane a b) (hlr : l ≠ r) :
    rootPlane l r = rootPlane a b := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro z hz
    change z ∈ rootPlane a b
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · rw [hz]; exact hl
    · rw [Set.mem_singleton_iff.mp hz]; exact hr
  · rw [rootPlane_finrank _ _ hlr, rootPlane_finrank _ _ hab]

/-- A root plane has an extreme positive root. Finiteness of inversion sets
replaces the false assertion that the (real-valued) root heights are discrete. -/
theorem exists_plane_extreme_inverted (a b : PositiveRoot M cs) (hab : a ≠ b) :
    ∃ p : PositiveRoot M cs, p.val ∈ rootPlane a b ∧ rootInverted (rootRef a) p ∧
      ((∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope p ≤ geometricSlope r) ∨
       (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope r ≤ geometricSlope p)) := by
  classical
  let S := (finite_rootInverted (M := M) (cs := cs) (rootRef a)).toFinset.filter
    (fun r => r.val ∈ rootPlane a b)
  have hS (r : PositiveRoot M cs) : r ∈ S ↔
      rootInverted (rootRef a) r ∧ r.val ∈ rootPlane a b := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have haP : a.val ∈ rootPlane a b := Submodule.subset_span (Set.mem_insert _ _)
  have haS : a ∈ S := (hS a).mpr ⟨rootInverted_ref_self a, haP⟩
  obtain ⟨p, hp, hmin⟩ := S.exists_min_image geometricSlope ⟨a, haS⟩
  obtain ⟨q, hq, hmax⟩ := S.exists_max_image geometricSlope ⟨a, haS⟩
  by_cases hleft : ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      geometricSlope p ≤ geometricSlope r
  · exact ⟨p, (hS p).mp hp |>.2, (hS p).mp hp |>.1, Or.inl hleft⟩
  by_cases hright : ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      geometricSlope r ≤ geometricSlope q
  · exact ⟨q, (hS q).mp hq |>.2, (hS q).mp hq |>.1, Or.inr hright⟩
  push Not at hleft hright
  obtain ⟨l, hlP, hlp⟩ := hleft
  obtain ⟨r, hrP, hqr⟩ := hright
  have hla := lt_of_lt_of_le hlp (hmin a haS)
  have har := lt_of_le_of_lt (hmax a haS) hqr
  have hlr : l ≠ r := fun h => (lt_trans hla har).ne (congrArg geometricSlope h)
  have hplane := rootPlane_eq_of_mem a b l r hab hlP hrP hlr
  have hlam : ¬ rootInverted (rootRef a) l := by
    intro hi
    exact (not_le_of_gt hlp) (hmin l ((hS l).mpr ⟨hi, hlP⟩))
  have hram : ¬ rootInverted (rootRef a) r := by
    intro hi
    exact (not_le_of_gt hqr) (hmax r ((hS r).mpr ⟨hi, hrP⟩))
  obtain ⟨c, d, hc, hd, he⟩ := positive_combination_of_slope_between l r a
    (hplane.symm ▸ haP) hla har
  exact False.elim ((noninverted_of_positive_combination (rootRef a) l r a
    hc.le hd.le he hlam hram) (rootInverted_ref_self a))

theorem PlaneSimple.partner_val {P : Submodule ℝ (I → ℝ)}
    {a : PositiveRoot M cs} (ha : PlaneSimple P a)
    {b : PositiveRoot M cs} (hb : b.val ∈ P) (hba : b ≠ a) :
    (partner a b).val = action M cs (rootRef a) b.val := by
  have hn : ¬ rootInverted (rootRef a) b := fun h => hba ((ha.2 b hb).mp h)
  have hp := (not_rootInverted_iff (rootRef a) b).mp hn
  rw [(rootReflection M cs a).property.inv] at hp
  exact positiveAction_eq_of_nonneg _ _ hp

theorem PlaneSimple.exists_nonpositive_pair {P : Submodule ℝ (I → ℝ)}
    {a : PositiveRoot M cs} (ha : PlaneSimple P a)
    {b : PositiveRoot M cs} (hb : b.val ∈ P) (hba : b ≠ a) :
    ∃ c : PositiveRoot M cs, c.val ∈ P ∧ c ≠ a ∧ form M a.val c.val ≤ 0 := by
  by_cases hn : form M a.val b.val ≤ 0
  · exact ⟨b, hb, hba, hn⟩
  · refine ⟨partner a b, partner_mem a b ha.1 hb,
      fun h => hba ((partner_eq_self_of_eq a b).mp h), ?_⟩
    rw [ha.partner_val hb hba, (rootReflection_represents M cs a).action_formula]
    simp only [map_sub, map_smul, smul_eq_mul, a.property.1.norm]
    linarith

theorem noninverted_ref_of_pairing_nonpos (a b : PositiveRoot M cs)
    (hab : form M a.val b.val ≤ 0) : ¬ rootInverted (rootRef b) a := by
  rw [not_rootInverted_iff, (rootReflection M cs b).property.inv,
    (rootReflection_represents M cs b).action_formula]
  have hba : form M b.val a.val ≤ 0 := by rwa [(form_symm M).eq]
  intro i
  exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hba (b.property.2 i)).trans
    (a.property.2 i))

/-- The other endpoint exists even in an infinite or degenerate plane. -/
theorem exists_opposite_plane_extreme (a b p : PositiveRoot M cs) (hab : a ≠ b)
    (hp : p.val ∈ rootPlane a b)
    (hext : (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
        geometricSlope p ≤ geometricSlope r) ∨
      (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
        geometricSlope r ≤ geometricSlope p)) :
    ∃ q : PositiveRoot M cs, q.val ∈ rootPlane a b ∧ q ≠ p ∧
      (((∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope p ≤ geometricSlope r) ∧
        (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope r ≤ geometricSlope q)) ∨
       ((∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope q ≤ geometricSlope r) ∧
        (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope r ≤ geometricSlope p))) := by
  have hs := planeSimple_of_extreme p hp hext
  have hother : ∃ r : PositiveRoot M cs, r.val ∈ rootPlane a b ∧ r ≠ p := by
    by_cases hap : a = p
    · refine ⟨b, Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)), ?_⟩
      exact fun h => hab (hap.trans h.symm)
    · exact ⟨a, Submodule.subset_span (Set.mem_insert _ _), hap⟩
  obtain ⟨r, hrP, hrp⟩ := hother
  obtain ⟨c, hcP, hcp, hcpair⟩ := hs.exists_nonpositive_pair hrP hrp
  have hn := noninverted_ref_of_pairing_nonpos p c hcpair
  have hplane := rootPlane_eq_of_mem a b c p hab hcP hp hcp
  obtain ⟨q, hqP, hqinv, hqext⟩ := exists_plane_extreme_inverted c p hcp
  rw [hplane] at hqP hqext
  have hqp : q ≠ p := fun h => hn (h ▸ hqinv)
  refine ⟨q, hqP, hqp, ?_⟩
  rcases hext with hmin | hmax
  · refine Or.inl ⟨hmin, ?_⟩
    rcases hqext with hqmin | hqmax
    · exact False.elim (hqp (geometricSlope_injective (le_antisymm
        (hqmin p hp) (hmin q hqP))))
    · exact hqmax
  · refine Or.inr ⟨?_, hmax⟩
    rcases hqext with hqmin | hqmax
    · exact hqmin
    · exact False.elim (hqp (geometricSlope_injective (le_antisymm
        (hmax q hqP) (hqmax p hp))))

theorem nonempty_planeBasis (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Nonempty (PlaneBasis (M := M) (cs := cs) (rootPlane a b)) := by
  obtain ⟨p, hp, _, hext⟩ := exists_plane_extreme_inverted a b hab
  obtain ⟨q, hq, hqp, hpair⟩ := exists_opposite_plane_extreme a b p hab hp hext
  rcases hpair with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact ⟨⟨p, q, hqp.symm, rootPlane_eq_of_mem a b p q hab hp hq hqp.symm, hl, hr⟩⟩
  · exact ⟨⟨q, p, hqp, rootPlane_eq_of_mem a b q p hab hq hp hqp, hl, hr⟩⟩

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem simpleRoot_simple (i : Bool) : PlaneSimple P (B.simpleRoot i) := by
  cases i
  · exact B.left_simple
  · exact B.right_simple

/-- The positive simple-sign criterion for the induced plane root system. -/
theorem simple_sign {t : planeSubgroup M cs P} {a : I → ℝ}
    (ha : Represents M cs t.val a) (haP : a ∈ P) (hp : ∀ k, 0 ≤ a k) (i : Bool) :
    ((∀ k, action M cs (B.system.simple i : W) a k ≤ 0) ↔ t = B.system.simple i) ∧
    ((∀ k, 0 ≤ action M cs (B.system.simple i : W) a k) ↔ t ≠ B.system.simple i) := by
  let r : PositiveRoot M cs := ⟨a, ha.isRoot, hp⟩
  have hneg : (∀ k, action M cs (B.system.simple i : W) a k ≤ 0) ↔ t = B.system.simple i := by
    rw [B.system_simple]
    change flipped (B.simpleRoot i) r ↔ _
    rw [← rootInverted_ref_iff_flipped, (B.simpleRoot_simple i).2 r haP]
    constructor
    · intro he
      apply Subtype.ext
      rw [B.system_simple]
      exact ha.reflection_unique (he ▸ rootReflection_represents M cs r)
    · intro he
      apply Subtype.ext
      have hr : Represents M cs (rootRef (B.simpleRoot i)) a := by
        simpa only [he, B.system_simple] using ha
      exact hr.unique_positive (rootReflection_represents M cs _) hp (B.simpleRoot i).property.2
  refine ⟨hneg, ?_⟩
  constructor
  · intro h he
    exact (ha.isRoot.act (B.system.simple i : W)).not_both h (hneg.mpr he)
  · intro h
    exact (ha.isRoot.act (B.system.simple i : W)).sign.resolve_right (fun hn => h (hneg.mp hn))

/-- Signed roots for the induced system. The vectors are the original ambient
roots, and membership in the actual plane is part of the relation. -/
structure InducedSigned (p : planeSubgroup M cs P × ZMod 2) (a : I → ℝ) : Prop where
  represents : Represents M cs p.1.val a
  plane_mem : a ∈ P
  sign : (p.2 = 0 ∧ ∀ i, 0 ≤ a i) ∨ (p.2 = 1 ∧ ∀ i, a i ≤ 0)

theorem InducedSigned.simple {p : planeSubgroup M cs P × ZMod 2} {a : I → ℝ}
    (ha : InducedSigned p a) (i : Bool) :
    InducedSigned (CoxeterSupport.simpleAction B.system i p)
      (action M cs (B.system.simple i : W) a) := by
  rcases p with ⟨t,z⟩
  rw [CoxeterSupport.simpleAction_apply]
  refine ⟨?_, planeSubgroup_preserves (B.system.simple i).property ha.plane_mem, ?_⟩
  · have h := ha.represents.act (B.system.simple i : W)
    have he : (B.system.simple i : W)⁻¹ = (B.system.simple i : W) :=
      congrArg Subtype.val (B.system.inv_simple i)
    simpa only [he, Subgroup.coe_mul] using h
  · rcases ha.sign with ⟨rfl,hp⟩ | ⟨rfl,hn⟩
    · by_cases heq : t = B.system.simple i
      · exact Or.inr ⟨by simp [heq],
          (B.simple_sign ha.represents ha.plane_mem hp i).1.mpr heq⟩
      · exact Or.inl ⟨by simp [heq, ZModModule.add_self],
          (B.simple_sign ha.represents ha.plane_mem hp i).2.mpr heq⟩
    · have hp : ∀ k, 0 ≤ (-a) k := fun k => neg_nonneg.mpr (hn k)
      by_cases heq : t = B.system.simple i
      · refine Or.inl ⟨by simp [heq, ZModModule.add_self], ?_⟩
        have h := (B.simple_sign ha.represents.neg (P.neg_mem ha.plane_mem) hp i).1.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonpos] using h
      · refine Or.inr ⟨by simp [heq], ?_⟩
        have h := (B.simple_sign ha.represents.neg (P.neg_mem ha.plane_mem) hp i).2.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonneg] using h

theorem InducedSigned.act {p : planeSubgroup M cs P × ZMod 2} {a : I → ℝ}
    (ha : InducedSigned p a) (w : planeSubgroup M cs P) :
    InducedSigned (CoxeterSupport.reflectionAction B.system w p)
      (action M cs (w : W) a) := by
  obtain ⟨ω,rfl⟩ := B.system.wordProd_surjective w
  induction ω with
  | nil => simpa using ha
  | cons i ω ih =>
    simpa only [B.system.wordProd_cons, map_mul, Equiv.Perm.mul_apply,
      CoxeterSupport.reflectionAction_simple, Subgroup.coe_mul,
      LinearEquiv.mul_apply] using ih.simple B i

/-- The induced positive roots have precisely the intrinsic Coxeter inversion
signs. No change of realization or extra canonical-system assumption is used. -/
theorem inversion_iff {t : planeSubgroup M cs P} {a : I → ℝ}
    (ha : Represents M cs t.val a) (haP : a ∈ P) (hp : ∀ i, 0 ≤ a i)
    (w : planeSubgroup M cs P) :
    (∀ i, action M cs (w : W)⁻¹ a i ≤ 0) ↔ B.system.IsLeftInversion w t := by
  classical
  let : BEq (planeSubgroup M cs P) := @instBEqOfDecidableEq _ (Classical.decEq _)
  obtain ⟨ω,hω,heq⟩ := B.system.exists_isReduced w
  rw [heq]
  let c : ZMod 2 := if t ∈ B.system.leftInvSeq ω then 1 else 0
  have hrec := CoxeterSupport.wordAction_record B.system ω t c
  rw [← CoxeterSupport.reflectionAction_wordProd] at hrec
  have hrec' : CoxeterSupport.reflectionAction B.system (B.system.wordProd ω)
      ((B.system.wordProd ω)⁻¹ * t * B.system.wordProd ω, c) = (t,0) := by
    by_cases hm : t ∈ B.system.leftInvSeq ω
    · have hc : c = 1 := ite_eq_left hm
      simpa only [hc, List.count_eq_one_of_mem hω.nodup_leftInvSeq hm,
        Nat.cast_one, ZModModule.add_self] using hrec
    · have hc : c = 0 := ite_eq_right hm
      simpa only [hc, List.count_eq_zero.mpr hm, Nat.cast_zero, add_zero] using hrec
  have hinv : CoxeterSupport.reflectionAction B.system (B.system.wordProd ω)⁻¹ (t,0) =
      ((B.system.wordProd ω)⁻¹ * t * B.system.wordProd ω,c) := by
    rw [map_inv, ← hrec']
    exact Equiv.symm_apply_apply _ _
  have hs : InducedSigned (t,0) a := ⟨ha,haP,Or.inl ⟨rfl,hp⟩⟩
  have hsi := hs.act B (B.system.wordProd ω)⁻¹
  rw [hinv] at hsi
  have hcount : c = if t ∈ B.system.leftInvSeq ω then 1 else 0 := rfl
  have hmem : (∀ i, action M cs (B.system.wordProd ω : W)⁻¹ a i ≤ 0) ↔
      t ∈ B.system.leftInvSeq ω := by
    by_cases hm : t ∈ B.system.leftInvSeq ω
    · have hc1 : c=1 := by simpa [hm] using hcount
      have hh := hsi.sign
      simp only [hc1] at hh
      rcases hh with ⟨hbad,_⟩ | ⟨_,hn⟩
      · norm_num at hbad
      · exact iff_of_true hn hm
    · have hc0 : c=0 := by simpa [hm] using hcount
      have hh := hsi.sign
      simp only [hc0] at hh
      rcases hh with ⟨_,hpos⟩ | ⟨hbad,_⟩
      · exact iff_of_false (fun hn => (ha.isRoot.act _).not_both hpos hn) hm
      · norm_num at hbad
  rw [hmem]
  exact ⟨B.system.isLeftInversion_of_mem_leftInvSeq hω,
    CoxeterSupport.mem_leftInvSeq_of_inversion B.system hω⟩

/-- The intrinsic reflections are exactly the ambient reflections in the
actual maximal plane subgroup. -/
theorem reflection_iff (t : planeSubgroup M cs P) :
    B.system.IsReflection t ↔ cs.IsReflection (t : W) := by
  constructor
  · rintro ⟨w,i,he⟩
    obtain ⟨z,j,hz⟩ := (rootReflection M cs (B.simpleRoot i)).property
    refine ⟨(w : W) * z,j,?_⟩
    have he' := congrArg Subtype.val he
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, B.system_simple] at he'
    change rootRef (B.simpleRoot i) = _ at hz
    rw [he', hz]
    group
  · intro ht
    let a := positiveRoot M cs ⟨(t:W),ht⟩
    have ha := positiveRoot_represents M cs ⟨(t:W),ht⟩
    have haP : a.val ∈ P := (ha.planeSubgroup_mem_iff M cs).mp t.property
    have hinv := (B.inversion_iff ha haP a.property.2 t).mp
      ((ha.inversion_iff a.property.2 (t:W)).mpr
        ⟨ht, by
          rw [ht.mul_self, cs.length_one]
          obtain ⟨k,hk⟩ := ht.odd_length
          omega⟩)
    exact hinv.1

/-- The true ambient plane inversions are in bijection with the inversions
of the canonical induced system. -/
def inversionEquiv (w : planeSubgroup M cs P) :
    {a : PositiveRoot M cs // a.val ∈ P ∧ rootInverted (w:W) a} ≃
      {t : planeSubgroup M cs P // B.system.IsLeftInversion w t} where
  toFun a := ⟨⟨rootRef a.val,
    ((rootReflection_represents M cs a.val).planeSubgroup_mem_iff M cs).mpr a.property.1⟩,
    (B.inversion_iff (rootReflection_represents M cs a.val) a.property.1
      a.val.property.2 w).mp a.property.2⟩
  invFun t :=
    let a := positiveRoot M cs ⟨(t.val:W),(B.reflection_iff t.val).mp t.property.1⟩
    let ha := positiveRoot_represents M cs
      ⟨(t.val:W),(B.reflection_iff t.val).mp t.property.1⟩
    let haP := (ha.planeSubgroup_mem_iff M cs).mp t.val.property
    ⟨a,haP,(B.inversion_iff ha haP a.property.2 w).mpr t.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (positiveRootEquiv M cs).apply_symm_apply a.val
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : {r : W // cs.IsReflection r} => r.val)
      ((positiveRootEquiv M cs).symm_apply_apply
        ⟨(t.val:W),(B.reflection_iff t.val).mp t.property.1⟩)

/-- Relative inversion count is the actual Coxeter length, completing the
length identification, not merely a rank-two presentation. -/
theorem length_eq (w : planeSubgroup M cs P) :
    planeLength (M := M) (cs := cs) P (w:W) = (B.system.length w : ℤ) := by
  classical
  let f := inversionVector (M := M) (cs := cs) (w:W)
  let F := f.support.filter (fun a => a.val ∈ P)
  have hF : (F : Set (PositiveRoot M cs)) =
      {a | a.val ∈ P ∧ rootInverted (w:W) a} := by
    ext a
    simp only [F, Finset.mem_coe, Finset.mem_filter, Finsupp.mem_support_iff,
      f, inversionVector_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not,
      Set.mem_ofPred_eq, and_comm]
  have hcard : F.card = B.system.length w := by
    rw [← Set.ncard_coe_finset, hF, ← Nat.card_coe_set_eq]
    change Nat.card {a : PositiveRoot M cs // a.val ∈ P ∧ rootInverted (w:W) a} = _
    rw [Nat.card_congr (B.inversionEquiv w)]
    obtain ⟨ω,hω,he⟩ := B.system.exists_isReduced w
    rw [he, Nat.card_congr (leftInversionListEquiv B.matrix B.system hω),
      ← Nat.card_congr (List.Nodup.getEquiv (B.system.leftInvSeq ω) hω.nodup_leftInvSeq),
      Nat.card_fin, B.system.length_leftInvSeq, hω.eq]
  change f.sum (fun a n => if a.val ∈ P then n else 0) = _
  rw [Finsupp.sum, ← Finset.sum_filter]
  calc
    ∑ a ∈ F, f a = ∑ _a ∈ F, (1:ℤ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hm : rootInverted (w:W) a := by
        have hm := (Finset.mem_filter.mp ha).1
        simpa only [Finsupp.mem_support_iff, f, inversionVector_apply,
          ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hm
      simp [f,hm]
    _ = _ := by simp [hcard]

/-- Intrinsic and ambient left inversions coincide on the plane subgroup. -/
theorem leftInversion_iff (w t : planeSubgroup M cs P) :
    B.system.IsLeftInversion w t ↔ cs.IsLeftInversion (w:W) (t:W) := by
  by_cases ht : cs.IsReflection (t:W)
  · let a := positiveRoot M cs ⟨(t:W),ht⟩
    have ha := positiveRoot_represents M cs ⟨(t:W),ht⟩
    have haP := (ha.planeSubgroup_mem_iff M cs).mp t.property
    exact (B.inversion_iff ha haP a.property.2 w).symm.trans
      (ha.inversion_iff a.property.2 (w:W))
  · exact iff_of_false (fun h => ht ((B.reflection_iff t).mp h.1)) (fun h => ht h.1)

/-- The intrinsic directed dihedral graph is the actual ambient graph
restricted to the maximal plane subgroup. -/
theorem bruhatStep_iff (g h : planeSubgroup M cs P) :
    BruhatStep cs (g:W) (h:W) ↔ BruhatStep B.system g h := by
  constructor
  · rintro ⟨hlen,t,ht,he⟩
    have htP : t ∈ planeSubgroup M cs P := by
      have he' : t = (h:W) * (g:W)⁻¹ := by rw [he]; group
      rw [he']
      exact (planeSubgroup M cs P).mul_mem h.property
        ((planeSubgroup M cs P).inv_mem g.property)
    let tr : planeSubgroup M cs P := ⟨t,htP⟩
    have htr : B.system.IsReflection tr := (B.reflection_iff tr).mpr ht
    have het : h=tr*g := Subtype.ext he
    have htg : t*(h:W)=(g:W) := by rw [he, ← mul_assoc, ht.mul_self, one_mul]
    have hi := (B.leftInversion_iff h tr).mpr ⟨ht,by
      change cs.length (t*(h:W)) < cs.length (h:W)
      simpa only [htg] using hlen⟩
    have htg' : tr*h=g := by rw [het, ← mul_assoc, htr.mul_self, one_mul]
    exact ⟨by simpa only [htg'] using hi.2,tr,htr,het⟩
  · rintro ⟨hlen,t,ht,he⟩
    have het : t*h=g := by rw [he, ← mul_assoc, ht.mul_self, one_mul]
    have hi := (B.leftInversion_iff h t).mp ⟨ht,by simpa only [het] using hlen⟩
    refine ⟨?_,(t:W),(B.reflection_iff t).mp ht,congrArg Subtype.val he⟩
    simpa only [← Subgroup.coe_mul, het] using hi.2

/-- The exact canonical coset graph theorem needed by the reconstruction. -/
theorem coset_step_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (g h : planeSubgroup M cs P) :
    BruhatStep cs ((g:W)*a₀) ((h:W)*a₀) ↔ BruhatStep B.system g h :=
  (bruhatStep_coset_iff hmin g.property h.property).trans (B.bruhatStep_iff g h)

/-- The source inversion-count characterization holds on every minimal
representative coset, with its actual induced length. -/
theorem coset_length_eq {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (w : planeSubgroup M cs P) :
    planeLength (M := M) (cs := cs) P ((w:W)*a₀) = (B.system.length w : ℤ) := by
  classical
  rw [← B.length_eq w]
  let f := inversionVector (M := M) (cs := cs) ((w:W)*a₀)
  let g := inversionVector (M := M) (cs := cs) (w:W)
  change f.sum (fun a n => if a.val ∈ P then n else 0) =
    g.sum (fun a n => if a.val ∈ P then n else 0)
  rw [Finsupp.sum_of_support_subset f Finset.subset_union_left _ (by intro a; simp),
    Finsupp.sum_of_support_subset g Finset.subset_union_right _ (by intro a; simp)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases haP : a.val ∈ P
  · simp only [ite_eq_left haP, f, g, inversionVector_apply]
    congr 1
    exact propext (root_inversion_coset_iff hmin w.property a.property.1 haP)
  · simp [haP]

end PlaneBasis

/-- Every nonsaturated reflection edge has a genuine rank-two contribution
whose induced relative edge gap is at least three. -/
theorem exists_positive_plane (x : W) (a : PositiveRoot M cs)
    (hx : ¬ rootInverted x a)
    (hlen : cs.length x + 1 < cs.length (rootRef a*x)) :
    ∃ b : PositiveRoot M cs, a ≠ b ∧ 0 < planeWeight x a (rootPlane a b) := by
  classical
  have hsum := sum_planeWeight x a hx
  have hp : 0 < (planeWeight x a).sum (fun _ n => n) := by omega
  obtain ⟨P,hP,hpos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun P _ => planeWeight_nonneg x a P)).mp hp
  obtain ⟨b,hb,hbP⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hP)
  have hb' : halfRoot x a b := by
    simpa only [Finsupp.mem_support_iff, halfVector, rootIndicator_apply,
      ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hb
  exact ⟨b,hb'.1.1.symm,hbP ▸ hpos⟩


end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
variable {G : Type*} [Group G] {N : CoxeterMatrix Bool}

/-- Every nonsaturated dihedral edge contains a full eight-edge rectangle. -/
theorem edge_diamond (ds : CoxeterSystem N G) {x y : G}
    (hxy : BruhatStep ds x y) (hlen : ds.length x + 1 < ds.length y) :
    ∃ a b c d : G, a ≠ b ∧ c ≠ d ∧
      BruhatStep ds x a ∧ BruhatStep ds x b ∧
      BruhatStep ds a c ∧ BruhatStep ds a d ∧
      BruhatStep ds b c ∧ BruhatStep ds b d ∧
      BruhatStep ds c y ∧ BruhatStep ds d y := by
  have hodd := ((step_iff_odd ds x y).mp hxy).2
  have hthree : ds.length x+2 < ds.length y := by
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨a,b,hab,hlev₁⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+1) hlen
  obtain ⟨c,d,hcd,hlev₂⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+2) hthree
  have ha := (hlev₁ a).mpr (Or.inl rfl)
  have hb := (hlev₁ b).mpr (Or.inr rfl)
  have hc := (hlev₂ c).mpr (Or.inl rfl)
  have hd := (hlev₂ d).mpr (Or.inr rfl)
  have hsucc (p q : G) (h : ds.length q=ds.length p+1) : BruhatStep ds p q := by
    rw [step_iff_odd, Nat.odd_iff]
    constructor <;> omega
  have htop (p : G) (hp : ds.length p=ds.length x+2) : BruhatStep ds p y := by
    rw [step_iff_odd, Nat.odd_iff]
    rw [Nat.odd_iff] at hodd
    constructor <;> omega
  exact ⟨a,b,c,d,hab,hcd,hsucc x a ha,hsucc x b hb,
    hsucc a c (by omega),hsucc a d (by omega),
    hsucc b c (by omega),hsucc b d (by omega),htop c hc,htop d hd⟩

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}

/-- Every genuine ambient reflection edge of length gap greater than one
contains a full eight-edge diamond. The chosen plane comes from an actual
positive inversion contribution, avoiding the false arbitrary-plane claim. -/
theorem ambient_edge_diamond {x y : W} (hxy : BruhatStep cs x y)
    (hlen : cs.length x+1 < cs.length y) :
    ∃ a b c d : W, a ≠ b ∧ c ≠ d ∧
      BruhatStep cs x a ∧ BruhatStep cs x b ∧
      BruhatStep cs a c ∧ BruhatStep cs a d ∧
      BruhatStep cs b c ∧ BruhatStep cs b d ∧
      BruhatStep cs c y ∧ BruhatStep cs d y := by
  rcases hxy.2 with ⟨t,ht,het⟩
  let a := positiveRoot M cs ⟨t,ht⟩
  have ha := positiveRoot_represents M cs ⟨t,ht⟩
  have hta : rootRef a=t := congrArg (fun r : {r : W // cs.IsReflection r} => r.val)
    ((positiveRootEquiv M cs).symm_apply_apply ⟨t,ht⟩)
  have hx : ¬ rootInverted x a := by
    intro hi
    have h := (ha.inversion_iff a.property.2 x).mp hi
    have hh : cs.length (t*x) < cs.length x := h.2
    rw [← het] at hh
    exact (not_lt_of_gt hxy.1) hh
  have hae : rootRef a*x=y := by rw [hta]; exact het.symm
  obtain ⟨b,hab,hpos⟩ := exists_positive_plane x a hx (by rwa [hae])
  obtain ⟨B⟩ := nonempty_planeBasis a b hab
  let P := rootPlane a b
  have haP : a.val ∈ P := Submodule.subset_span (Set.mem_insert _ _)
  obtain ⟨a₀,g,hg,hgx,hmin⟩ := planeCoset_exists_minimal M cs P x
  let X : planeSubgroup M cs P := ⟨g,hg⟩
  let T : planeSubgroup M cs P := ⟨rootRef a,
    ((rootReflection_represents M cs a).planeSubgroup_mem_iff M cs).mpr haP⟩
  let Y := T*X
  have hxEq : (X:W)*a₀=x := hgx.symm
  have hyEq : (Y:W)*a₀=y := by
    change (rootRef a*g)*a₀=y
    rw [mul_assoc, ← hgx, hae]
  have hrel : BruhatStep B.system X Y := (B.coset_step_iff hmin X Y).mp
    (by simpa only [hxEq,hyEq] using hxy)
  have hLx := B.coset_length_eq hmin X
  have hLy := B.coset_length_eq hmin Y
  rw [hxEq] at hLx
  rw [hyEq] at hLy
  have hdegree := planeWeight_relative_degree x a b hab hx
  rw [hae,hLx,hLy] at hdegree
  have hlen' : B.system.length X+1 < B.system.length Y := by omega
  obtain ⟨p,q,r,s,hpq,hrs,hXp,hXq,hpr,hps,hqr,hqs,hrY,hsY⟩ :=
    Dihedral.edge_diamond B.system hrel hlen'
  have hinj : Function.Injective (fun z : planeSubgroup M cs P => (z:W)*a₀) := by
    intro p q hpq
    exact Subtype.ext (mul_right_cancel hpq)
  refine ⟨(p:W)*a₀,(q:W)*a₀,(r:W)*a₀,(s:W)*a₀,
    fun h => hpq (hinj h),fun h => hrs (hinj h),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hxEq] using (B.coset_step_iff hmin X p).mpr hXp
  · simpa only [hxEq] using (B.coset_step_iff hmin X q).mpr hXq
  · exact (B.coset_step_iff hmin p r).mpr hpr
  · exact (B.coset_step_iff hmin p s).mpr hps
  · exact (B.coset_step_iff hmin q r).mpr hqr
  · exact (B.coset_step_iff hmin q s).mpr hqs
  · simpa only [hyEq] using (B.coset_step_iff hmin r Y).mpr hrY
  · simpa only [hyEq] using (B.coset_step_iff hmin s Y).mpr hsY

end KLInvariance.TitsSpace

namespace KLInvariance
variable {I W : Type*} [Fintype I] [Group W] {M : CoxeterMatrix I}

/-- General unlabelled Bruhat graph reconstruction completeness, for genuine
finite-rank Coxeter systems and arbitrary bottoms and interval ranks. -/
theorem diamondEdges_of_bruhatStep (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : BruhatStep cs x.val y.val) :
    DiamondEdges x y := by
  suffices ∀ n : ℕ, ∀ x y : Interval cs u b,
      cs.length y.val-cs.length x.val=n → BruhatStep cs x.val y.val →
      DiamondEdges x y by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hxy
    by_cases he : cs.length y.val=cs.length x.val+1
    · exact DiamondEdges.cover (interval_covBy_of_length_succ cs
        (Relation.ReflTransGen.single hxy) he)
    · have hn' : cs.length x.val+1 < cs.length y.val := by have := hxy.1; omega
      obtain ⟨a,bm,c,d,hab,hcd,hxa,hxb,hac,had,hbc,hbd,hcy,hdy⟩ :=
        TitsSpace.ambient_edge_diamond hxy hn'
      have leOf {p q : W} (h : BruhatStep cs p q) : BruhatLE cs p q :=
        Relation.ReflTransGen.single h
      let A : Interval cs u b := ⟨a,bruhat_trans cs x.property.1 (leOf hxa),
        bruhat_trans cs (leOf hac) (bruhat_trans cs (leOf hcy) y.property.2)⟩
      let B : Interval cs u b := ⟨bm,bruhat_trans cs x.property.1 (leOf hxb),
        bruhat_trans cs (leOf hbc) (bruhat_trans cs (leOf hcy) y.property.2)⟩
      let C : Interval cs u b := ⟨c,
        bruhat_trans cs x.property.1 (bruhat_trans cs (leOf hxa) (leOf hac)),
        bruhat_trans cs (leOf hcy) y.property.2⟩
      let D : Interval cs u b := ⟨d,
        bruhat_trans cs x.property.1 (bruhat_trans cs (leOf hxa) (leOf had)),
        bruhat_trans cs (leOf hdy) y.property.2⟩
      have hsmall {p q : Interval cs u b} (hpq : BruhatStep cs p.val q.val)
          (hp : cs.length x.val ≤ cs.length p.val)
          (hq : cs.length q.val ≤ cs.length y.val)
          (hs : cs.length x.val < cs.length p.val ∨ cs.length q.val < cs.length y.val) :
          DiamondEdges p q := by
        exact ih _ (by omega) p q rfl hpq
      have h₁ := hxa.1
      have h₂ := hxb.1
      have h₃ := hac.1
      have h₄ := had.1
      have h₅ := hbc.1
      have h₆ := hbd.1
      have h₇ := hcy.1
      have h₈ := hdy.1
      refine DiamondEdges.diamond
        (hsmall (p := x) (q := A) hxa ?_ ?_ ?_)
        (hsmall (p := x) (q := B) hxb ?_ ?_ ?_)
        (hsmall (p := A) (q := C) hac ?_ ?_ ?_)
        (hsmall (p := A) (q := D) had ?_ ?_ ?_)
        (hsmall (p := B) (q := C) hbc ?_ ?_ ?_)
        (hsmall (p := B) (q := D) hbd ?_ ?_ ?_)
        (hsmall (p := C) (q := y) hcy ?_ ?_ ?_)
        (hsmall (p := D) (q := y) hdy ?_ ?_ ?_)
        (fun h => hab (congrArg Subtype.val h))
        (fun h => hcd (congrArg Subtype.val h))
      all_goals first | omega | (dsimp only [A,B,C,D]; omega)

end KLInvariance

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coxeter Frobenius extensions, tensor duality and translation across reflection pairs.
-/

section

namespace KLInvariance.TitsSpace
open Module ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 abbrev SymmetricCoefficient := SymmetricAlgebra ℝ (Extended M)

 def coefficientAction (w : W) : SymmetricCoefficient (M := M) ≃ₐ[ℝ]
    SymmetricCoefficient (M := M) := symmetricAction (extendedAction M cs w)

@[simp] theorem coefficientAction_ι (w : W) (v : Extended M) :
    coefficientAction cs w (SymmetricAlgebra.ι ℝ (Extended M) v) =
      SymmetricAlgebra.ι ℝ (Extended M) (extendedAction M cs w v) :=
  symmetricAction_ι _ _

 theorem coefficientAction_simple (i : I) : coefficientAction cs (cs.simple i) =
    reflectionAction (extendedRoot M i) (extendedForm M (extendedRoot M i))
      (extendedForm_root_self M i) := by
  rw [coefficientAction,extendedAction_simple_eq]

 def simpleFixed (i : I) : Subalgebra ℝ (SymmetricCoefficient (M := M)) :=
  fixed (coefficientAction cs (cs.simple i))

 abbrev simpleRootPolynomial (i : I) : SymmetricCoefficient (M := M) :=
  SymmetricAlgebra.ι ℝ (Extended M) (extendedRoot M i)

 theorem simple_involutive (i : I) : Function.Involutive (coefficientAction cs (cs.simple i)) := by
  rw [coefficientAction_simple]
  exact reflectionAction_involutive _ _ _

 theorem simpleRootPolynomial_ne_zero (i : I) : simpleRootPolynomial (M := M) i ≠ 0 :=
  reflectionRoot_ne_zero _ _ (extendedForm_root_self M i)

 theorem simple_anti (i : I) : coefficientAction cs (cs.simple i)
    (simpleRootPolynomial (M := M) i) = -simpleRootPolynomial (M := M) i := by
  rw [coefficientAction_simple]
  exact reflectionAction_anti _ _ _

 theorem simple_divisible (i : I) (a : SymmetricCoefficient (M := M)) :
    simpleRootPolynomial (M := M) i ∣ a-coefficientAction cs (cs.simple i) a := by
  rw [coefficientAction_simple]
  exact reflectionAction_divisible _ _ _ a

 def simpleCoordinates (i : I) : SymmetricCoefficient (M := M) ≃ₗ[simpleFixed cs i]
    (simpleFixed cs i × simpleFixed cs i) :=
  coordinates _ _ (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
    (simple_anti cs i) (simple_divisible cs i)

 instance simpleFixed_free (i : I) : Module.Free (simpleFixed cs i) (SymmetricCoefficient (M := M)) :=
  Module.Free.of_equiv (simpleCoordinates cs i).symm

 instance simpleFixed_finite (i : I) : Module.Finite (simpleFixed cs i) (SymmetricCoefficient (M := M)) :=
  Module.Finite.equiv (simpleCoordinates cs i).symm

 def simpleTrace (i : I) : SymmetricCoefficient (M := M) →ₗ[simpleFixed cs i] simpleFixed cs i :=
  trace _ _ (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
    (simple_anti cs i) (simple_divisible cs i)

 def simpleDuality (i : I) : SymmetricCoefficient (M := M) ≃ₗ[simpleFixed cs i]
    Dual (simpleFixed cs i) (SymmetricCoefficient (M := M)) :=
  duality _ _ (simple_involutive cs i) (simpleRootPolynomial_ne_zero i)
    (simple_anti cs i) (simple_divisible cs i)

 theorem simpleDuality_apply (i : I) (a b : SymmetricCoefficient (M := M)) :
    simpleDuality cs i a b = simpleTrace cs i (a*b) :=
  duality_apply _ _ _ _ _ _ a b

end
end KLInvariance.TitsSpace

end


section

/-! Tensor induction of integral self-dual bimodules across a Frobenius
extension. All pairings refer to actual integral modules. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

attribute [instance] PairedModule.add PairedModule.module PairedModule.free PairedModule.finite

end
end KLInvariance.FrobeniusDuality

end


section

/-! Genuine tensor-defined Bott--Samelson bimodules for the extended real
Coxeter realization. The perfect pairing is integral and balanced. This
construction alone does not identify indecomposable BMP summands or prove
the Elias--Williamson character theorem. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def bottSamelson : List I → PairedBimodule.{u,u} (SymmetricCoefficient (M := M))
  | [] => unitBimodule _
  | i :: l => inducedBimodule (simpleTrace cs i) (simpleDuality cs i)
    (simpleDuality_apply cs i) (bottSamelson l)

 abbrev BottSamelsonModule (l : List I) := (bottSamelson cs l).obj

end
end KLInvariance.TitsSpace

end


section

/-! The exact simple-wall kernel for the actual integral tensor word module.
This is a step toward word-sheaf recognition, not a character theorem or a
proof of combinatorial invariance. No stalk freeness is assumed. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct FrobeniusDuality ReflectionFrobenius
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

/-- The reflection is linear over its actual invariant subalgebra. -/
def simpleFixedAction (i : I) : SymmetricCoefficient (M := M) →ₗ[simpleFixed cs i]
    SymmetricCoefficient (M := M) where
  toFun := coefficientAction cs (cs.simple i)
  map_add' := map_add _
  map_smul' c a := by
    change coefficientAction cs (cs.simple i) ((c : SymmetricCoefficient (M := M))*a) =
      (c : SymmetricCoefficient (M := M))*coefficientAction cs (cs.simple i) a
    rw [map_mul, show coefficientAction cs (cs.simple i)
      (c : SymmetricCoefficient (M := M)) = c from c.property]

/-- Reflect the first tensor factor. It is not asserted to be left A-linear. -/
def bottSimpleFlip (i : I) (l : List I) : BottSamelsonModule cs (i::l) →ₗ[simpleFixed cs i]
    BottSamelsonModule cs (i::l) :=
  TensorProduct.map (simpleFixedAction cs i)
    (LinearMap.id : BottSamelsonModule cs l →ₗ[simpleFixed cs i] BottSamelsonModule cs l)

@[simp] theorem bottSimpleFlip_tmul (i : I) (l : List I)
    (a : SymmetricCoefficient (M := M)) (m : BottSamelsonModule cs l) :
    bottSimpleFlip cs i l (a ⊗ₜ[simpleFixed cs i] m) =
      coefficientAction cs (cs.simple i) a ⊗ₜ[simpleFixed cs i] m := rfl

end
end KLInvariance.TitsSpace

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

/-! Grading-preserving coefficient change on the actual finite modules. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
noncomputable section

 def changePiece (M : ModuleData.{uk,ua,um} 𝓐) : ℤ → Submodule k (CoefficientChange e M) :=
  fun n => (M.piece n).map (CoefficientChange.kEquiv e M).toLinearMap

 theorem mem_changePiece (M : ModuleData.{uk,ua,um} 𝓐) (n : ℤ) (m : CoefficientChange e M) :
    m ∈ changePiece e M n ↔ m.val ∈ M.piece n := by
  constructor
  · rintro ⟨x,hx,hxm⟩
    change CoefficientChange.mk x=m at hxm
    exact (congrArg CoefficientChange.val hxm) ▸ hx
  · intro hm
    exact ⟨m.val,hm,rfl⟩

 def change (M : ModuleData.{uk,ua,um} 𝓐) : ModuleData.{uk,ua,um} 𝓑 where
  obj := ModuleCat.of B (CoefficientChange e M)
  kModule := inferInstance
  tower := inferInstance
  piece := changePiece e M
  decomposition := by
    apply DirectSum.IsInternal.chooseDecomposition
    apply image_isInternal M.piece (CoefficientChange.kEquiv e M).toLinearMap
      (CoefficientChange.kEquiv e M).surjective
    intro n m hm
    have hz : m=0 := congrArg CoefficientChange.val hm
    subst m
    simp only [map_zero]
  graded := by
    constructor
    intro i j b m hb hm
    apply (mem_changePiece e M (i+j) _).mpr
    change e.symm b • m.val ∈ M.piece (i+j)
    have ha : e.symm b ∈ 𝓐 i := (he i _).mpr (by simpa using hb)
    exact SetLike.GradedSMul.smul_mem ha ((mem_changePiece e M j m).mp hm)
  nonneg n hn := by simp only [changePiece,M.nonneg n hn,Submodule.map_bot]
  finite := inferInstance

 def changeHom {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N) :
    Hom (change e he M) (change e he N) where
  map := CoefficientChange.map e f.map
  graded n m hm := (mem_changePiece e N n _).mpr
    (f.graded n m.val ((mem_changePiece e M n m).mp hm))

end
end KLInvariance.Graded.ModuleData

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

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

 def homOfEq {M N : ModuleData.{uk,ua,um} 𝓐} (h : M=N) : Hom M N :=
  ⟨(equivOfEq h).toLinearMap,equivOfEq_graded h⟩

end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)

/-- A common edge annihilator makes all the scaled coordinate idempotents
integral endomorphisms of the section module. -/
 theorem scaled_single_section [DecidableEq V] {p : R}
    (hp : ∀ e (v : B.edge e), p • v = 0) (x : V) (m : B.sections Set.univ) :
    p • Pi.single x (m.val x) ∈ B.sections Set.univ := by
  intro e _ _
  simp only [Pi.smul_apply,map_smul,hp]

variable [Fintype E] (α : E → R)

 theorem labelProduct_annihilates (hα : ∀ e (v : B.edge e), α e • v = 0)
    (e : E) (v : B.edge e) : labelProduct α • v = 0 := by
  obtain ⟨r,hr⟩ := Finset.dvd_prod_of_mem α (Finset.mem_univ e)
  change (∏ e, α e) • v = 0
  rw [hr,mul_comm, mul_smul,hα,smul_zero]

omit [Fintype E] in
 theorem projection_surjective (hg : B.Generated) (x : V) :
    Function.Surjective (IntegralSupport.projection (B.sections Set.univ) x) := by
  intro a
  obtain ⟨m,hm,hx⟩ := hg x a
  exact ⟨⟨m,hm⟩,hx⟩

variable [DecidableEq V] [IsDomain R] [∀ x, Module.IsTorsionFree R (B.vertex x)]
  (hα : ∀ e, α e ≠ 0) (ha : ∀ e (v : B.edge e), α e • v = 0)
  (d : B.sections Set.univ ≃ₗ[R] Module.Dual R (B.sections Set.univ))
  (hbalanced : ∀ x m n,
    d (IntegralSupport.cut (B.sections Set.univ) (labelProduct α)
      (B.scaled_single_section (B.labelProduct_annihilates α ha)) x m) n =
    d m (IntegralSupport.cut (B.sections Set.univ) (labelProduct α)
      (B.scaled_single_section (B.labelProduct_annihilates α ha)) x n))


noncomputable def singleSupportEquivDual (hg : B.Generated) (x : V) :
    IntegralSupport.supported (B.sections Set.univ) x ≃ₗ[R] Module.Dual R (B.vertex x) :=
  IntegralSupport.supportEquivDual (B.sections Set.univ) (labelProduct α)
    (B.scaled_single_section (B.labelProduct_annihilates α ha))
    (labelProduct_ne_zero α hα) d hbalanced x (B.projection_surjective hg x)

end KLInvariance.MomentGraph.Sheaf

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} (B : GradedSheaf (𝓐 := 𝓐) G) {α : E → A}

 theorem UpperQuotient.annihilates (h : B.UpperQuotient α) (e : E) (v : B.edge e) :
    α e • v = 0 := by
  obtain ⟨w,rfl⟩ := (h e).1 v
  rw [← map_smul]
  exact (h e).2 _ |>.mpr ⟨w,rfl⟩

end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um ui
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} {G : OrderedGraph V E} (B : Sheaf.{ur,uv,ue,um} (R := R) G)

 theorem stalkMap_eq_zero_iff (x : V) (v : B.vertex x) :
    B.stalkMap x v = 0 ↔ ∀ e (h : G.source e = x), B.lower e (h.symm ▸ v) = 0 := by
  constructor
  · intro hv e he
    exact congrFun hv ⟨e,he⟩
  · intro hv
    funext e
    exact hv e.val e.property

 theorem single_section_iff [DecidableEq V] (x : V) (v : B.vertex x) :
    Pi.single x v ∈ B.sections Set.univ ↔
      B.stalkMap x v = 0 ∧ ∀ e (h : G.target e = x), B.upper e (h.symm ▸ v) = 0 := by
  constructor
  · intro hv
    constructor
    · apply (B.stalkMap_eq_zero_iff x v).mpr
      intro e he
      subst x
      have hc := hv e (Set.mem_univ _) (Set.mem_univ _)
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_gt (G.increasing e)),map_zero] using hc
    · intro e he
      subst x
      have hc := hv e (Set.mem_univ _) (Set.mem_univ _)
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_lt (G.increasing e)),map_zero] using hc.symm
  · rintro ⟨hu,hd⟩ e _ _
    by_cases hs : G.source e = x
    · subst x
      simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_gt (G.increasing e)),map_zero]
        using (B.stalkMap_eq_zero_iff _ _).mp hu e rfl
    · by_cases ht : G.target e = x
      · subst x
        simpa only [Pi.single_eq_same, Pi.single_eq_of_ne (ne_of_lt (G.increasing e)),map_zero]
          using (hd e rfl).symm
      · simp only [Pi.single_eq_of_ne hs,Pi.single_eq_of_ne ht,map_zero]

variable [Fintype E] [DecidableEq V]

def incoming (x : V) : Finset E := Finset.univ.filter (fun e => G.target e = x)

@[simp] theorem mem_incoming (x : V) (e : E) : e ∈ incoming (G := G) x ↔ G.target e = x := by
  simp [incoming]

def incomingProduct (α : E → R) (x : V) : R := ∏ e ∈ incoming (G := G) x, α e

variable [IsDomain R] (α : E → R)
  (hα : ∀ e, Prime (α e))
  (hq : ∀ e, Function.Surjective (B.upper e))
  (hk : ∀ e v, B.upper e v = 0 ↔ ∃ w, v = α e • w)
  {ι : V → Type ui} [∀ x, Fintype (ι x)] (bs : ∀ x, Module.Basis (ι x) R (B.vertex x))

include hα in
 theorem incomingProduct_ne_zero (x : V) : incomingProduct (G := G) α x ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => (hα e).ne_zero)

omit [IsDomain R] in
include hα hq hk bs in
 theorem outgoing_product_regular (x : V)
    (hsep : ∀ e f, G.source e = x → G.target f = x → ¬ α e ∣ α f)
    (e : E) (he : G.source e = x) :
    Function.Injective (fun v : B.edge e => incomingProduct (G := G) α x • v) := by
  apply FiniteFreeScalar.scalar_quotient_regular (bs (G.target e)) (B.upper e) (hq e)
    (α e) (incomingProduct (G := G) α x) (hα e) _ (hk e)
  intro hdiv
  obtain ⟨f,hf,hfdiv⟩ := ((hα e).dvd_finsetProd_iff α).mp hdiv
  exact hsep e f he ((mem_incoming (G := G) x f).mp hf) hfdiv

omit [IsDomain R] in
include hk bs in
/-- The actual integral single-support conditions. Downward labels impose
product divisibility, and they are regular at every upward edge. -/
 theorem single_section_iff_prod [DecompositionMonoid R] (x : V)
    (hrel : (incoming (G := G) x : Set E).Pairwise (Function.onFun IsRelPrime α))
    (hreg : ∀ e, G.source e = x → Function.Injective
      (fun v : B.edge e => incomingProduct (G := G) α x • v)) (v : B.vertex x) :
    Pi.single x v ∈ B.sections Set.univ ↔
      ∃ w : B.vertex x, v = incomingProduct (G := G) α x • w ∧ B.stalkMap x w = 0 := by
  constructor
  · intro hv
    obtain ⟨hu,hd⟩ := (B.single_section_iff x v).mp hv
    have hdiv : ∀ e ∈ incoming (G := G) x, ∃ w : B.vertex x, α e • w = v := by
      intro e he
      have ht := (mem_incoming (G := G) x e).mp he
      subst x
      obtain ⟨w,hw⟩ := (hk e v).mp (hd e rfl)
      exact ⟨w,hw.symm⟩
    obtain ⟨w,hw⟩ := FiniteFreeScalar.exists_prod_smul (bs x) (incoming (G := G) x) α hrel v hdiv
    refine ⟨w,hw.symm,?_⟩
    apply (B.stalkMap_eq_zero_iff x w).mpr
    intro e he
    apply hreg e he
    change incomingProduct (G := G) α x • _ = incomingProduct (G := G) α x • (0 : B.edge e)
    rw [smul_zero]
    have hz := (B.stalkMap_eq_zero_iff x v).mp hu e he
    subst x
    rw [← hw,map_smul] at hz
    exact hz
  · rintro ⟨w,rfl,hw⟩
    apply (B.single_section_iff x _).mpr
    constructor
    · rw [map_smul,hw,smul_zero]
    · intro e he
      subst x
      obtain ⟨r,hr⟩ := Finset.dvd_prod_of_mem α ((mem_incoming (G := G) _ e).mpr rfl)
      apply (hk e _).mpr
      exact ⟨r • w, by rw [incomingProduct,hr,mul_smul]⟩

/-- The single-support part as an actual submodule of its stalk. -/
def singleStalk (x : V) : Submodule R (B.vertex x) :=
  (B.sections Set.univ).comap (LinearMap.single R (fun y => B.vertex y) x)

noncomputable def singleStalkEquivSupport (x : V) :
    B.singleStalk x ≃ₗ[R] IntegralSupport.supported (B.sections Set.univ) x := by
  let f : B.singleStalk x →ₗ[R] IntegralSupport.supported (B.sections Set.univ) x :=
    { toFun := fun v => ⟨⟨Pi.single x v.val,v.property⟩,by
                        intro y hy; exact Pi.single_eq_of_ne hy _⟩
      map_add' := by intro v w; apply Subtype.ext; apply Subtype.ext; exact Pi.single_add _ _ _
      map_smul' := by intro r v; apply Subtype.ext; apply Subtype.ext; exact Pi.single_smul _ _ _ }
  apply LinearEquiv.ofBijective f
  constructor
  · intro v w hvw
    apply Subtype.ext
    have hv := congrArg (fun s : IntegralSupport.supported (B.sections Set.univ) x => s.val.val x) hvw
    change (Pi.single x v.val : B.Assignment) x = (Pi.single x w.val : B.Assignment) x at hv
    simpa only [Pi.single_eq_same] using hv
  · intro m
    have he : Pi.single x (m.val.val x) = m.val.val := by
      funext y
      by_cases hy : y=x
      · subst y; simp only [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hy, m.property y hy]
    refine ⟨⟨m.val.val x,?_⟩,?_⟩
    · change Pi.single x (m.val.val x) ∈ B.sections Set.univ
      rw [he]; exact m.val.property
    · apply Subtype.ext; apply Subtype.ext; exact he


noncomputable def kernelEquivSingleStalk [DecompositionMonoid R] (x : V)
    (hrel : (incoming (G := G) x : Set E).Pairwise (Function.onFun IsRelPrime α))
    (hreg : ∀ e, G.source e = x → Function.Injective
      (fun v : B.edge e => incomingProduct (G := G) α x • v)) :
    LinearMap.ker (B.stalkMap x) ≃ₗ[R] B.singleStalk x := by
  let p := incomingProduct (G := G) α x
  let f : LinearMap.ker (B.stalkMap x) →ₗ[R] B.singleStalk x :=
    (p • (LinearMap.ker (B.stalkMap x)).subtype).codRestrict (B.singleStalk x) (by
      intro v
      exact (B.single_section_iff_prod α hk bs x hrel hreg _).mpr ⟨v.val,rfl,v.property⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro v w hvw
    apply Subtype.ext
    let : Module.Free R (B.vertex x) := Module.Free.of_basis (bs x)
    exact smul_right_injective (B.vertex x) (incomingProduct_ne_zero α hα x)
      (congrArg Subtype.val hvw)
  · intro v
    obtain ⟨w,hw,hz⟩ := (B.single_section_iff_prod α hk bs x hrel hreg v.val).mp v.property
    exact ⟨⟨w,hz⟩,Subtype.ext hw.symm⟩

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem root_injective_on_labels {e f : Edge cs u b} (h : root cs u b e = root cs u b f) :
    label cs u b e = label cs u b f := by
  exact congrArg Subtype.val ((positiveRootEquiv M cs).injective h)

 theorem polynomialLabel_prime (e : Edge cs u b) : Prime (polynomialLabel cs u b basis e) := by
  apply (MulEquiv.prime_iff (SymmetricAlgebra.equivMvPolynomial basis)).mpr
  apply EdgeAlgebra.symmetric_ι_prime
  intro h
  exact (root cs u b e).property.1.ne_zero (congrArg Prod.fst h)

 theorem label_eq_of_polynomialLabel_dvd {e f : Edge cs u b}
    (h : polynomialLabel cs u b basis e ∣ polynomialLabel cs u b basis f) :
    label cs u b e = label cs u b f := by
  apply root_injective_on_labels cs u b
  by_contra hn
  have hd : SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b e).val) ∣
      SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b f).val) := by
    obtain ⟨z,hz⟩ := h
    exact ⟨(SymmetricAlgebra.equivMvPolynomial basis).symm z, by
      apply (SymmetricAlgebra.equivMvPolynomial basis).injective
      simpa only [map_mul,AlgEquiv.apply_symm_apply,polynomialLabel] using hz⟩
  have hm := (EdgeAlgebra.symmetric_ι_dvd_iff _ _).mp hd
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hm
  have he : r • (root cs u b e).val = (1 : ℝ) • (root cs u b f).val := by
    have hfst := congrArg Prod.fst hr
    change r • (root cs u b e).val = (root cs u b f).val at hfst
    simpa only [one_smul] using hfst
  exact one_ne_zero ((positiveRoots_independent _ _ hn).eq_zero_of_pair' he).2

 theorem incoming_pairwise_relPrime [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)] (x : Interval cs u b) :
    (Sheaf.incoming (G := graph cs u b) x : Set (Edge cs u b)).Pairwise
      (Function.onFun IsRelPrime (polynomialLabel cs u b basis)) := by
  intro e he f hf hne
  apply ((polynomialLabel_prime cs u b basis e).irreducible.isRelPrime_iff_not_dvd).mpr
  intro hdiv
  apply hne
  apply eq_of_label_target_eq cs u b (label_eq_of_polynomialLabel_dvd cs u b basis hdiv)
  exact ((Sheaf.mem_incoming x e).mp he).trans ((Sheaf.mem_incoming x f).mp hf).symm

 theorem outgoing_incoming_not_dvd (x : Interval cs u b) (e f : Edge cs u b)
    (he : (graph cs u b).source e = x) (hf : (graph cs u b).target f = x) :
    ¬ polynomialLabel cs u b basis e ∣ polynomialLabel cs u b basis f := by
  intro h
  apply source_ne_target_of_label_eq cs u b (label_eq_of_polynomialLabel_dvd cs u b basis h)
  exact he.trans hf.symm

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section


structure SectionDuality where
  pairing : B.sheaf.forget.sections Set.univ ≃ₗ[Coefficient (σ := σ)]
    Dual (Coefficient (σ := σ)) (B.sheaf.forget.sections Set.univ)
  balanced : ∀ x m n,
    pairing (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x m) n =
    pairing m (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x n)

end
end KLInvariance.BruhatGraph

end


section

/-! A genuine homogeneous integral perfect pairing with vertex-support
orthogonality on both sides. Transport does not identify unequal lattices. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 structure PerfectPairing (S : GradedSheaf (𝓐 := 𝓐) G) (d : ℤ) where
  pairing : S.forget.sections Set.univ ≃ₗ[A] Dual A (S.forget.sections Set.univ)
  homogeneous : ∀ i j (m n : S.forget.sections Set.univ),
    (∀ x, m.val x∈(S.vertex x).piece i) → (∀ x, n.val x∈(S.vertex x).piece j) →
    pairing m n∈𝓐 (i+j-d)
  left_orthogonal : ∀ (x : V) (m n : S.forget.sections Set.univ),
    (∀ y, y≠x → m.val y=0) → n.val x=0 → pairing m n=0
  right_orthogonal : ∀ (x : V) (m n : S.forget.sections Set.univ),
    m.val x=0 → (∀ y, y≠x → n.val y=0) → pairing m n=0

end
end KLInvariance.MomentGraph.GradedSheaf

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

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Module
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E} [IsDomain A] [DecidableEq V]
  {S : GradedSheaf (𝓐 := 𝓐) G} {d : ℤ} (p : PerfectPairing S d)
  (a : A) (ha : a≠0)
  (hcut : ∀ x (m : S.forget.sections Set.univ), a • Pi.single x (m.val x)∈S.forget.sections Set.univ)
noncomputable section

 include ha in
 theorem PerfectPairing.cut_balanced (x : V) (m n : S.forget.sections Set.univ) :
    p.pairing (IntegralSupport.cut _ a hcut x m) n =
      p.pairing m (IntegralSupport.cut _ a hcut x n) := by
  apply BalancedCuts.balanced_two p.pairing.toLinearMap
    (IntegralSupport.projection (S.forget.sections Set.univ) x)
    (IntegralSupport.cut _ a hcut x) a ha
    (IntegralSupport.cut_self _ a hcut x)
  · intro v w hw
    exact p.left_orthogonal x _ w (fun y hy => IntegralSupport.cut_other _ a hcut x y hy v) hw
  · intro v w hv
    exact p.right_orthogonal x v _ hv (fun y hy => IntegralSupport.cut_other _ a hcut x y hy w)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Integral costalk duality only uses free stalks, the genuine edge quotients,
generation and a perfect support-orthogonal section form. No top/minimality or
KL character assumption is needed. This extension applies to genuine words. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))

structure FreeSheaf where
  sheaf : GradedSheaf (𝓐 := polynomialGrading ℝ σ) (graph cs u b)
  free : sheaf.FreeStalks
  quotient : sheaf.UpperQuotient (polynomialLabel cs u b basis)
  generated : sheaf.forget.Generated

namespace FreeSheaf
variable (B : FreeSheaf cs u b basis)
  [Fintype (Edge cs u b)] [DecidableEq (Interval cs u b)]
noncomputable section
 def kernelEquivSingleSupport (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      IntegralSupport.supported (B.sheaf.forget.sections Set.univ) x := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (x : Interval cs u b) : Module.Finite (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) :=
    (B.sheaf.vertex x).finite
  let _ (x : Interval cs u b) : Fintype (Module.Free.ChooseBasisIndex
      (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)) := Fintype.ofFinite _
  let bs := fun x : Interval cs u b =>
    Module.Free.chooseBasis (Coefficient (σ := σ)) (B.sheaf.forget.vertex x)
  exact (B.sheaf.forget.kernelEquivSingleStalk (polynomialLabel cs u b basis)
    (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).2) bs x
    (incoming_pairwise_relPrime cs u b basis x)
    (B.sheaf.forget.outgoing_product_regular (polynomialLabel cs u b basis)
      (polynomialLabel_prime cs u b basis) (fun e => (B.quotient e).1)
      (fun e => (B.quotient e).2) bs x
      (outgoing_incoming_not_dvd cs u b basis x))).trans
        (B.sheaf.forget.singleStalkEquivSupport x)


structure SectionDuality where
  pairing : B.sheaf.forget.sections Set.univ ≃ₗ[Coefficient (σ := σ)]
    Dual (Coefficient (σ := σ)) (B.sheaf.forget.sections Set.univ)
  balanced : ∀ x m n,
    pairing (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x m) n =
    pairing m (IntegralSupport.cut (B.sheaf.forget.sections Set.univ)
      (Sheaf.labelProduct (polynomialLabel cs u b basis))
      (B.sheaf.forget.scaled_single_section
        (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
          (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient))) x n)

 def costalkEquivDual (d : SectionDuality cs u b basis B) (x : Interval cs u b) :
    LinearMap.ker (B.sheaf.forget.stalkMap x) ≃ₗ[Coefficient (σ := σ)]
      Dual (Coefficient (σ := σ)) (B.sheaf.vertex x) := by
  let _ (x : Interval cs u b) : Module.Free (Coefficient (σ := σ)) (B.sheaf.forget.vertex x) := B.free x
  let _ (y : Interval cs u b) : Module.IsTorsionFree (Coefficient (σ := σ))
      (B.sheaf.forget.vertex y) := inferInstance
  exact (kernelEquivSingleSupport cs u b basis B x).trans
    (B.sheaf.forget.singleSupportEquivDual (polynomialLabel cs u b basis)
      (polynomialLabel_ne_zero cs u b basis)
      (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)
      d.pairing d.balanced B.generated x)

 variable [Fintype σ] [Fintype (Interval cs u b)]


 def dualityOfPairing {l : ℤ} (p : GradedSheaf.PerfectPairing B.sheaf l) :
    SectionDuality cs u b basis B where
  pairing := p.pairing
  balanced := p.cut_balanced
    (Sheaf.labelProduct (polynomialLabel cs u b basis))
    (Sheaf.labelProduct_ne_zero _ (polynomialLabel_ne_zero cs u b basis))
    (B.sheaf.forget.scaled_single_section
      (B.sheaf.forget.labelProduct_annihilates (polynomialLabel cs u b basis)
        (GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient)))

end
end FreeSheaf
end KLInvariance.BruhatGraph

end


section

/-! Actual full upward kernels commute with finite graded sums, shifts and
sheaf isomorphisms. No freeness is inferred without a free model. -/
namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 abbrev kernelData (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :=
  B.upwardKernel x Set.univ

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  [IsNoetherianRing A] {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section
 def kernelEquivFull (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) :
    kernelData B x ≃ₗ[A] LinearMap.ker (B.forget.stalkMap x) where
  toFun m := ⟨m.val,funext (fun e => m.property e (Set.mem_univ e))⟩
  invFun m := ⟨m.val,fun e _ => congrFun m.property e⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end
end KLInvariance.MomentGraph.GradedSheaf

namespace KLInvariance.BruhatGraph.FreeSheaf
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (B : FreeSheaf cs 1 b basis)
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 def kernelDual (d : SectionDuality cs 1 b basis B) (x : Interval cs 1 b) :
    Dual (Coefficient (σ := σ)) (B.sheaf.vertex x) ≃ₗ[Coefficient (σ := σ)]
      GradedSheaf.kernelData B.sheaf x :=
  (costalkEquivDual cs 1 b basis B d x).symm.trans (B.sheaf.kernelEquivFull x).symm

omit [Fintype (Interval cs 1 b)] in
 theorem kernel_free (d : SectionDuality cs 1 b basis B) (x : Interval cs 1 b) :
    Module.Free (Coefficient (σ := σ)) (GradedSheaf.kernelData B.sheaf x) := by
  let := B.free x
  exact Module.Free.of_equiv (kernelDual cs b basis B d x)

end
end KLInvariance.BruhatGraph.FreeSheaf

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [DirectSum.Decomposition 𝓑] [SetLike.GradedMonoid 𝓑]
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  (hA : ∀ n<0,𝓐 n=⊥) (hB : ∀ n<0,𝓑 n=⊥)
noncomputable section

 def changeUnitHom : Hom (change e he (unit.{uk,ua,um} hA)) (unit hB) where
  map :=
    { toFun m j := e (m.val j)
      map_add' m n := funext fun j => map_add e (m.val j) (n.val j)
      map_smul' b m := by
        funext j
        change e (e.symm b * m.val j)=b * e (m.val j)
        rw [map_mul,e.apply_symm_apply] }
  graded := by
    intro n m hm j
    exact (he (n-0) _).mp ((mem_changePiece e (unit hA) n m).mp hm j)

 def changeUnitInvHom : Hom (unit.{uk,ua,um} hB) (change e he (unit hA)) where
  map :=
    { toFun m := CoefficientChange.mk (fun j => e.symm (m j))
      map_add' m n := CoefficientChange.ext (funext fun j => map_add e.symm (m j) (n j))
      map_smul' b m := by
        apply CoefficientChange.ext
        funext j
        exact map_mul e.symm b (m j) }
  graded := by
    intro n m hm
    apply (mem_changePiece e (unit hA) n _).mpr
    intro j
    apply (he (n-0) _).mpr
    change e (e.symm (m j)) ∈ 𝓑 (n-0)
    rw [e.apply_symm_apply]
    exact hm j

 theorem changeUnitHom_inv (m : unit.{uk,ua,um} hB) :
    (changeUnitHom e he hA hB).map ((changeUnitInvHom e he hA hB).map m)=m :=
  funext fun j => e.apply_symm_apply (m j)

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A B : Type ua} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]
  {𝓐 : ℤ → Submodule k A} {𝓑 : ℤ → Submodule k B}
  [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [DirectSum.Decomposition 𝓑] [SetLike.GradedMonoid 𝓑]
  (e : A ≃ₐ[k] B) (he : ∀ n a, a∈𝓐 n ↔ e a∈𝓑 n)
  {hA : ∀ n<0,𝓐 n=⊥} {hB : ∀ n<0,𝓑 n=⊥}
  {M : ModuleData.{uk,ua,um} 𝓐} (hM : M=unit hA)
  {N : ModuleData.{uk,ua,um} 𝓑} (hN : N=unit hB)
noncomputable section

 def changeTopInclusion : Hom N (change e he M) :=
  (changeHom e he (homOfEq hM.symm)).comp
    ((changeUnitInvHom e he hA hB).comp (homOfEq hN))

 def changeTopProjection : Hom (change e he M) N :=
  (homOfEq hN.symm).comp
    ((changeUnitHom e he hA hB).comp (changeHom e he (homOfEq hM)))

 theorem changeTop_split (n : N) :
    (changeTopProjection e he hM hN).map ((changeTopInclusion e he hM hN).map n)=n := by
  subst M
  subst N
  change (changeUnitHom e he hA hB).map ((changeUnitInvHom e he hA hB).map n)=n
  exact changeUnitHom_inv e he hA hB n

end
end KLInvariance.Graded.ModuleData

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

/-! Removing the finite-rank restriction from the actual graph bridge,
using the already established standard-parabolic embedding. -/
namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I)
noncomputable section

theorem leftInvSeq_inclusion (ω : List J) :
    ((system (M := M) J).leftInvSeq ω).map (inclusion cs J) =
      cs.leftInvSeq (ω.map Subtype.val) := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    simp only [CoxeterSystem.leftInvSeq, List.map_cons, List.map_map,
      inclusion_simple]
    rw [← ih, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp only [Function.comp_apply, MulAut.conj_apply, map_mul, map_inv,
      inclusion_simple]

theorem reflection_inclusion {t : (matrix (M := M) J).Group}
    (ht : (system (M := M) J).IsReflection t) :
    cs.IsReflection (inclusion cs J t) := by
  obtain ⟨w, i, rfl⟩ := ht
  exact ⟨inclusion cs J w, i.val, by simp only [map_mul, map_inv, inclusion_simple]⟩

theorem bruhatStep_inclusion_iff [Fintype J] (x y : (matrix (M := M) J).Group) :
    BruhatStep cs (inclusion cs J x) (inclusion cs J y) ↔
      BruhatStep (system (M := M) J) x y := by
  constructor
  · rintro ⟨hlen, t, ht, heq⟩
    obtain ⟨ω, hω, hprod⟩ := (system (M := M) J).exists_isReduced y
    have hi : cs.IsLeftInversion (inclusion cs J y) t := by
      refine ⟨ht, ?_⟩
      rw [heq, ← mul_assoc, ht.mul_self, one_mul]
      simpa only [heq] using hlen
    have hr := (reduced_map_iff cs J ω).2 hω
    have hw : cs.wordProd (ω.map Subtype.val) = inclusion cs J y := by
      rw [← inclusion_word, hprod]
    have hm := CoxeterSupport.mem_leftInvSeq_of_inversion cs hr (hw ▸ hi)
    rw [← leftInvSeq_inclusion] at hm
    obtain ⟨r, hr, hrt⟩ := List.mem_map.mp hm
    refine ⟨by simpa only [length_inclusion] using hlen,
      r, (system (M := M) J).isReflection_of_mem_leftInvSeq ω hr, ?_⟩
    apply inclusion_injective cs J
    simpa only [map_mul, hrt] using heq
  · rintro ⟨hlen, t, ht, heq⟩
    refine ⟨by simpa only [length_inclusion] using hlen,
      inclusion cs J t, reflection_inclusion cs J ht, ?_⟩
    rw [heq, map_mul]

end
end KLInvariance.StandardParabolic

namespace KLInvariance
universe u v u' v'
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}

/-- The graph reconstruction input in its source scope: the Coxeter system
can have infinitely many generators. The interval determines every reflection
edge without being supplied the reflection labels. -/
theorem diamondEdges_of_bruhatStep_general (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : BruhatStep cs x.val y.val) :
    DiamondEdges x y := by
  classical
  obtain ⟨J, hJ, hwords⟩ := lower_ideal_finite_generator_support cs b
  let : Fintype J := hJ.fintype
  obtain ⟨ω, hω, hprod⟩ := hwords b (bruhat_refl cs b)
  obtain ⟨ν, rfl⟩ := StandardParabolic.lift_word J hω
  let bb := (StandardParabolic.system (M := M) J).wordProd ν
  have hb : StandardParabolic.inclusion cs J bb = b :=
    (StandardParabolic.inclusion_word cs J ν).trans hprod
  have hub : BruhatLE cs u b := (bruhat_trans cs x.property.1 x.property.2)
  obtain ⟨ub, hu⟩ := StandardParabolic.lower_range cs J bb (hb ▸ hub)
  subst u
  clear hprod
  subst b
  let e := StandardParabolic.intervalIso cs J ub bb
  let xx := e.symm x
  let yy := e.symm y
  have hx : StandardParabolic.inclusion cs J xx.val = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hy : StandardParabolic.inclusion cs J yy.val = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hh : BruhatStep (StandardParabolic.system (M := M) J) xx.val yy.val := by
    apply (StandardParabolic.bruhatStep_inclusion_iff cs J _ _).mp
    rwa [hx, hy]
  have hg := (diamondEdges_of_bruhatStep (StandardParabolic.system (M := M) J) hh).map e
  simpa only [xx, yy, e.apply_symm_apply] using hg

theorem diamondEdges_bruhatStep_general (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : DiamondEdges x y) :
    BruhatStep cs x.val y.val := by
  classical
  obtain ⟨J, hJ, hwords⟩ := lower_ideal_finite_generator_support cs b
  let : Fintype J := hJ.fintype
  obtain ⟨ω, hω, hprod⟩ := hwords b (bruhat_refl cs b)
  obtain ⟨ν, rfl⟩ := StandardParabolic.lift_word J hω
  let bb := (StandardParabolic.system (M := M) J).wordProd ν
  have hb : StandardParabolic.inclusion cs J bb = b :=
    (StandardParabolic.inclusion_word cs J ν).trans hprod
  have hub : BruhatLE cs u b := (bruhat_trans cs x.property.1 x.property.2)
  obtain ⟨ub, hu⟩ := StandardParabolic.lower_range cs J bb (hb ▸ hub)
  subst u
  clear hprod
  subst b
  let e := StandardParabolic.intervalIso cs J ub bb
  let xx := e.symm x
  let yy := e.symm y
  have hx : StandardParabolic.inclusion cs J xx.val = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  have hy : StandardParabolic.inclusion cs J yy.val = y.val :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hh : DiamondEdges xx yy := hxy.map e.symm
  have hg := diamondEdges_bruhatStep (StandardParabolic.system (M := M) J) hh
  have hs := (StandardParabolic.bruhatStep_inclusion_iff cs J xx.val yy.val).mpr hg
  rwa [hx, hy] at hs

/-- Exact unlabelled directed graph invariance, also for arbitrary infinite
Coxeter systems. This is not yet KL polynomial invariance. -/
theorem intervalIso_bruhatStep_iff_general
    {I' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix I'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (e : Interval cs u b ≃o Interval cs' u' b')
    (x y : Interval cs u b) :
    BruhatStep cs' (e x).val (e y).val ↔ BruhatStep cs x.val y.val := by
  constructor
  · intro h
    exact diamondEdges_bruhatStep_general cs ((DiamondEdges.map_iff e).mp
      (diamondEdges_of_bruhatStep_general cs' h))
  · intro h
    exact diamondEdges_bruhatStep_general cs' ((diamondEdges_of_bruhatStep_general cs h).map e)

end KLInvariance

end


section


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- Geometric label of an intrinsic graph edge, taken in the actual ambient
root plane rather than an abstract alternate representation. -/
def edgeRoot {x y : planeSubgroup M cs P} (h : BruhatStep B.system x y) :
    PositiveRoot M cs := graphRoot ((B.bruhatStep_iff x y).mpr h)

end PlaneBasis
end
end KLInvariance.TitsSpace

end


section

/-! Rank-two path reversal in the actual induced root plane, for every finite
full interval. This is a required Dyer wall-crossing relation, not the Dyer
identification itself. -/
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

local instance instDecidable_solutions_5_ra211ce_2 (p : Prop) : Decidable p := Classical.propDecidable p
@[simp] theorem edgeFlip_involutive (cs : CoxeterSystem M W) (lo hi : W) :
    Function.Involutive (edgeFlip cs lo hi) := by
  intro e
  apply Subtype.ext
  change (intervalFlip cs lo hi (intervalFlip cs lo hi e.val.1),
    intervalFlip cs lo hi (intervalFlip cs lo hi e.val.2)) = e.val
  exact Prod.ext (intervalFlip_involutive cs lo hi e.val.1)
    (intervalFlip_involutive cs lo hi e.val.2)

end
end KLInvariance.Dihedral

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

/-! Linear coordinates on the actual normalized root line. These give the
rank-two geometry of finite wall crossings for genuine root schedules. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_9_ra211ce_1 (p : Prop) : Decidable p := Classical.propDecidable p
@[simp] theorem dual_normalizedRoot (f : Module.Dual ℝ (I → ℝ)) (a : PositiveRoot M cs) :
    f (normalizedRoot a) = f a.val / height a.val := by
  simp [normalizedRoot,div_eq_mul_inv,mul_comm]

@[simp] theorem geometricFunctional_normalizedRoot (a : PositiveRoot M cs) :
    geometricFunctional (M := M) (cs := cs) (normalizedRoot a) = geometricSlope a :=
  dual_normalizedRoot _ a

end
end KLInvariance.TitsSpace

end


section

/-! Localization of genuine directed paths in a maximal root-plane coset.
The full relative interval is proved to contain every such path. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module SchedulePaths
open AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

local instance instDecidable_2_ra211ce_1 (p : Prop) : Decidable p := Classical.propDecidable p
def edgeToAmbient {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) : AdaptedDyer.Edge cs :=
  ⟨(B.intervalToAmbient e.val.1, B.intervalToAmbient e.val.2),
    (B.coset_step_iff hmin e.val.1.val e.val.2.val).mpr e.property⟩

@[simp] theorem edgeToAmbient_source {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) :
    source cs (B.edgeToAmbient hmin e) = B.intervalToAmbient (a₀ := a₀) (BruhatGraph.source B.system g k e) := rfl

@[simp] theorem edgeToAmbient_target {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) :
    target cs (B.edgeToAmbient hmin e) = B.intervalToAmbient (a₀ := a₀) (BruhatGraph.target B.system g k e) := rfl

@[simp] theorem edgeToAmbient_root {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g k : planeSubgroup M cs P} (e : BruhatGraph.Edge B.system g k) :
    rootLabel cs (B.edgeToAmbient hmin e) = B.edgeRoot e.property := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change rootRef (rootLabel cs (B.edgeToAmbient hmin e)) = rootRef (B.edgeRoot e.property)
  rw [rootRef_rootLabel]
  have hr : rootRef (B.edgeRoot e.property) = (e.val.2.val:W)*(e.val.1.val:W)⁻¹ :=
    (rootReflection_represents M cs _).reflection_unique
      (graphRoot_represents ((B.bruhatStep_iff _ _).mpr e.property))
  rw [hr]
  change ((e.val.2.val:W)*a₀)*((e.val.1.val:W)*a₀)⁻¹ = _
  group

end
end KLInvariance.TitsSpace.PlaneBasis

end


section

/-! Algebra and finite ordered-list bookkeeping for wall crossings. -/
namespace KLInvariance.SchedulePaths
universe u v w
variable {E : Type u} {A : Type v} {Λ : Type w} [LinearOrder A] [LinearOrder Λ]
noncomputable section

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_4
attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidableEq_solutions
@[simp] theorem mem_sortedSchedule (F : Finset E) (score : E → Λ) (e : E) :
    e ∈ sortedSchedule F score ↔ e ∈ F := by simp [sortedSchedule]

end
end KLInvariance.SchedulePaths

end


section

/-! The actual rank-two edge product is independent of every linear
functional restricted to that root plane, including a wall tie refinement. -/
namespace KLInvariance.TitsSpace
open Module SchedulePaths AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_10_ra211ce_1 (p : Prop) : Decidable p := Classical.propDecidable p
def lexRootScore (f : Module.Dual ℝ (I → ℝ)) (a : PositiveRoot M cs) : ℝ ×ₗ ℝ :=
  toLex (f (normalizedRoot a),geometricSlope a)

def lexEdgeScore (f : Module.Dual ℝ (I → ℝ)) (e : AdaptedDyer.Edge cs) : ℝ ×ₗ ℝ :=
  lexRootScore f (rootLabel cs e)

end
end KLInvariance.TitsSpace

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

/-! An elementary flabbiness criterion for the exact rank-one model. Flow-down
sections with the genuine product of outgoing labels suffice. The pairwise
relative-primality condition will be instantiated by actual root labels. -/
namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] [DecompositionMonoid R]
  {V : Type uv} [PartialOrder V] {E : Type ue}
  (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section
variable [Fintype E] [DecidableEq V]

def modelOutgoing (x : V) : Finset E := by
  classical
  exact Finset.univ.filter (fun e => G.source e = x ∧ G.target e ≤ c)

@[simp] theorem mem_modelOutgoing (x : V) (e : E) :
    e ∈ modelOutgoing G c x ↔ G.source e = x ∧ G.target e ≤ c := by
  classical
  simp [modelOutgoing]

end
end KLInvariance.MomentGraph.Sheaf

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

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

 def polynomialRoot (a : PositiveRoot M cs) : Coefficient (σ := σ) :=
  SymmetricAlgebra.equivMvPolynomial basis
    (SymmetricAlgebra.ι ℝ (Extended M) (embed M a.val))

end
end KLInvariance.BruhatGraph

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

namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 local instance instDecidable_solutions_6_ra211ce_1 (p : Prop) : Decidable p := Classical.propDecidable p
def transportedEdge (e : Edge cs u b) : AdaptedDyer.Edge cs' :=
  ⟨((φ (source cs u b e)).val,(φ (target cs u b e)).val),
    (intervalIso_bruhatStep_iff_general cs cs' φ _ _).mpr e.property⟩

 def transportedScore (e : Edge cs u b) : ℝ ×ₗ ℝ :=
  lexEdgeScore (geometricFunctional (M := M') (cs := cs')) (transportedEdge φ e)

 /-- Decreasing list, in the convention for the outermost-first matrix
 product. Its reverse is chronological increasing reflection order. -/
 def transportedSchedule : List (Edge cs u b) := by
  letI := Fintype.ofFinite (Edge cs u b)
  exact sortedSchedule Finset.univ (transportedScore φ)

end
end KLInvariance.BruhatGraph

end


section

/-! Faithful upper-interval restriction of the actual minimal boundary sheaf.
The bottom is arbitrary. No roots or labels are supplied by the interval iso. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
noncomputable section

 def upperInclusion : GraphMap (graph cs u b) (graph cs 1 b) where
  vertex x := ⟨x.val,one_bruhat cs x.val,x.property.2⟩
  edge e := ⟨(⟨(source cs u b e).val,one_bruhat cs _,(source cs u b e).property.2⟩,
    ⟨(target cs u b e).val,one_bruhat cs _,(target cs u b e).property.2⟩),e.property⟩
  source _ := rfl
  target _ := rfl

omit [Fintype I] in
 theorem upperInclusion_injective : Function.Injective (upperInclusion cs u b).vertex := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : Interval cs 1 b => z.val) h)

omit [Fintype I] in
 theorem upperInclusion_outgoing (e : Edge cs 1 b) (x : Interval cs u b)
    (hx : (upperInclusion cs u b).vertex x = source cs 1 b e) :
    ∃ a, (upperInclusion cs u b).edge a=e ∧ source cs u b a=x := by
  have hxval := congrArg Subtype.val hx
  let y : Interval cs u b := ⟨(target cs 1 b e).val,
    bruhat_trans cs x.property.1 (hxval.symm ▸ Relation.ReflTransGen.single e.property),
    (target cs 1 b e).property.2⟩
  let a : Edge cs u b := ⟨(x,y),hxval.symm ▸ e.property⟩
  refine ⟨a,?_,rfl⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hx
  · rfl

variable {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs 1 b) (polynomialLabel cs 1 b basis) ⟨b,one_bruhat cs b,bruhat_refl cs b⟩)

 def restrictBoundary : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩ :=
  B.pullback (upperInclusion cs u b) (upperInclusion_injective cs u b)
    (upperInclusion_outgoing cs u b) ⟨b,hub,bruhat_refl cs b⟩ rfl

end
end KLInvariance.BruhatGraph

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

/-! The genuine BMP local intersection map. All freeness, kernel-minimality and
inverse grading assertions here are now unconditional consequences of the
constructed integral duality. The nonvanishing/Hodge input is deliberately
NOT asserted; the last theorem records precisely how it would force the
strict KL halfdegree bound on ACTUAL homogeneous stalk generators. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  [Fintype (Edge cs 1 b)] [Fintype (Interval cs 1 b)] [DecidableEq (Interval cs 1 b)]
noncomputable section

 abbrev ActualBoundary := boundarySheaf cs 1 b basis (one_bruhat cs b)

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

 def remainingConditions (p : List (Edge cs u b)) (x : Interval cs u b) :
    Set (Sheaf.Outgoing (G := graph cs u b) x) := {f | f.val ∈ p}

end
end KLInvariance.BruhatGraph

end


section

/-! Exact identification of chronological suffix conditions with the
strictly-later root conditions used in the height-one edge-image proof.
Equal-label edges may be ordered arbitrarily and cause no extra incident
condition. -/
namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths MomentGraph
universe u v u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def chronologicalSchedule : List (Edge cs u b) := (transportedSchedule φ).reverse

end
end KLInvariance.BruhatGraph

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

namespace KLInvariance.BruhatGraph
open Module TitsSpace EdgeAlgebra
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 abbrev EdgeRing (a : PositiveRoot M cs) :=
   MvPolynomial σ ℝ ⧸ Ideal.span {polynomialRoot cs basis a}

 def edgeRingEquiv (a : PositiveRoot M cs) : EdgeRing cs basis a ≃ₐ[ℝ] EdgeCoefficient a :=
   (Ideal.quotientEquivAlg (rootIdeal (k := ℝ) (embed M a.val))
     (Ideal.span {polynomialRoot cs basis a}) (SymmetricAlgebra.equivMvPolynomial basis)
     (by simp only [rootIdeal,Ideal.map_span,Set.image_singleton,polynomialRoot]; rfl)).symm

 @[simp] theorem edgeRingEquiv_root (a β : PositiveRoot M cs) :
    edgeRingEquiv cs basis a (Ideal.Quotient.mk _ (polynomialRoot cs basis β)) =
      Ideal.Quotient.mk _ (SymmetricAlgebra.ι ℝ (Extended M) (embed M β.val)) := by
  apply (edgeRingEquiv cs basis a).symm.injective
  simp only [AlgEquiv.symm_apply_apply]
  rfl

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (hub : BruhatLE cs u b)
  (B : BoundarySheaf (polynomialGrading_negative ℝ σ)
    (graph cs u b) (polynomialLabel cs u b basis) ⟨b,hub,bruhat_refl cs b⟩)
noncomputable section

omit [Fintype σ] in
 theorem edgeTorsion (e : Edge cs u b) :
    Module.IsTorsionBy (MvPolynomial σ ℝ) (B.sheaf.edge e) (polynomialRoot cs basis (root cs u b e)) :=
   fun v => GradedSheaf.UpperQuotient.annihilates B.sheaf B.quotient e v

 @[instance_reducible] def edgeModule (e : Edge cs u b) :
    Module (EdgeRing cs basis (root cs u b e)) (B.sheaf.edge e) :=
   (edgeTorsion cs u b basis hub B e).module

end
end KLInvariance.BruhatGraph

end


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 def intervalBoundary := restrictBoundary cs u b basis hub
  (boundarySheaf cs 1 b basis (one_bruhat cs b))

end
end KLInvariance.BruhatGraph

end


section

/-! Native endpoint normalization from the ACTUAL stalk characters. Unlike the
KL-labelled endpoints, these need neither character recognition nor Hodge. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance actualInterval : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _
local instance actualEdges : Fintype (Edge cs 1 b) := Fintype.ofFinite _

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SimultaneousInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
R-first simultaneous invariance and transported-schedule terminal-kernel freeness: upper-interval freeness, lower-interval cancellation, reversal and endpoint bottom freeness; all-entry transport and KL degree rigidity.
-/


section

/-! Transport of the actual partial-kernel freeness from a smaller-bottom
interval. No change of ambient sheaf, grading, or reflection order. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph SchedulePaths
universe u v u' v' us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'} (hub : BruhatLE cs u b)
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

def FreeSuffixes : Prop :=
  ∀ q, q <:+ chronologicalSchedule φ → ∀ x : Interval cs u b,
    Module.Free (Coefficient (σ := σ))
      ((intervalBoundary basis hub).sheaf.upwardSubmodule x
        (remainingConditions cs u b q x))

end
end KLInvariance.BruhatGraph

end


end OAI
end


