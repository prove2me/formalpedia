-- Prove2me | Definitions.Def_OAIQ124K006
-- name    : OAIQ124K006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:45:21.499047+00:00
-- url     : https://prove2.me/theorems/61c39cb0-2eef-40d1-8b9d-8de34ed39288
-- title:
--   Definitions bundle OAIQ124K006 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 101 declarations of OpenAI's Lean: 45 definitions, 1 inductive type or structure, 6 instances and 49 theorems. The definitions and types are `OAI.KLInvariance.BruhatGraph.finiteInterval`, `OAI.KLInvariance.BruhatGraph.instDecidable_solutions_6`, `OAI.KLInvariance.BruhatGraph.instDecidable_solutions_7`, `OAI.KLInvariance.BruhatGraph.lowerConvInterval`, `OAI.KLInvariance.Dihedral.oppositeExternal`, `OAI.KLInvariance.Dihedral.sameExternal`, `OAI.KLInvariance.FiniteIntervalModel`, `OAI.KLInvariance.Graded.ModuleData.Hom.pi`, `OAI.KLInvariance.Graded.ModuleData.Hom.prodMap`, `OAI.KLInvariance.Graded.ModuleData.Hom.shift`, `OAI.KLInvariance.Graded.ModuleData.Hom.splitEquiv`, `OAI.KLInvariance.Graded.ModuleData.Hom.zero`, `OAI.KLInvariance.Graded.ModuleData.kernel`, `OAI.KLInvariance.Graded.ModuleData.mapNonnegativeBasis`, `OAI.KLInvariance.Graded.ModuleData.piBasis`, `OAI.KLInvariance.Graded.ModuleData.prod`, `OAI.KLInvariance.Graded.ModuleData.productBasis`, `OAI.KLInvariance.Graded.ModuleData.rangeInclusion`, `OAI.KLInvariance.Graded.ModuleData.rangeMap`, `OAI.KLInvariance.Graded.ModuleData.rangeProjection`, `OAI.KLInvariance.Graded.ModuleData.reflectedBasis`, `OAI.KLInvariance.Graded.ModuleData.shift`, `OAI.KLInvariance.Graded.ModuleData.shiftedBasis`, `OAI.KLInvariance.Graded.ModuleData.unitPolynomialBasis`, `OAI.KLInvariance.Graded.ModuleData.zero`, `OAI.KLInvariance.Graded.homogeneousPieceEquiv`, `OAI.KLInvariance.Hecke.barBasis`, `OAI.KLInvariance.Hecke.rTilde`, `OAI.KLInvariance.Hecke.standardUnit`, `OAI.KLInvariance.Hilbert.degreeKernelEquiv`, `OAI.KLInvariance.Hilbert.imageKernelEquiv`, `OAI.KLInvariance.Hilbert.imagePieceMap`, `OAI.KLInvariance.Hilbert.scalarDegreeMap`, `OAI.KLInvariance.MomentGraph.GradedSheaf.liftLowerAssignment`, `OAI.KLInvariance.MomentGraph.GradedSheaf.lowerExtend`, `OAI.KLInvariance.MomentGraph.GradedSheaf.lowerExtendVertex`, `OAI.KLInvariance.MomentGraph.GradedSheaf.projectLowerAssignment`, `OAI.KLInvariance.MomentGraph.GradedSheaf.zero`, `OAI.KLInvariance.MomentGraph.Sheaf.structureSheaf`, `OAI.KLInvariance.MomentGraph.lowerGraph` and 6 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `KazhdanLusztig_BalancedPairings`, `KazhdanLusztig_BottSamelson`, `KazhdanLusztig_Bruhat`, `KazhdanLusztig_CharacterReciprocity`, `KazhdanLusztig_DihedralIntervals`, `KazhdanLusztig_DyerPaths`, `KazhdanLusztig_EdgeLocalization`, `KazhdanLusztig_Frobenius`, `KazhdanLusztig_GradedModules`, `KazhdanLusztig_Hecke`, `KazhdanLusztig_HilbertSeries`, `KazhdanLusztig_IntegralPairings`, `KazhdanLusztig_Invariance`, `KazhdanLusztig_MinimalExtensions`, `KazhdanLusztig_ReflectionOrders`, `KazhdanLusztig_ReflectionSchedules`, `KazhdanLusztig_SheafMorphisms`, `KazhdanLusztig_Support`.
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundles `OAIQ124K000`, `OAIQ124K001`, `OAIQ124K002` and `OAIQ124K003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K009`, `OAIQ124K010` and `OAIQ124K011`; the statement `OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K000
import Definitions.Def_OAIQ124K001
import Definitions.Def_OAIQ124K002
import Definitions.Def_OAIQ124K003

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
universe uk ua um un ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem kernel_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (d : ℤ)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 (i+d)) :
    ∀ n m, m ∈ LinearMap.ker f → component 𝓜 n m ∈ LinearMap.ker f := by
  intro n m hm
  change f (component 𝓜 n m)=0
  have h := map_component 𝓜 𝓝 f d hf (n+d) m
  simpa [LinearMap.mem_ker.mp hm] using h.symm

omit [IsScalarTower k A M] in
 theorem component_homogeneous_smul
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
    (d : ℤ) (a : A) (ha : a ∈ 𝓐 d) (n : ℤ) (m : M) :
    component 𝓜 n (a • m) = a • component 𝓜 (n-d) m := by
  apply map_component 𝓜 𝓜 (LinearMap.lsmul A M a) d
  intro i v hv
  simpa [add_comm] using SetLike.GradedSMul.smul_mem ha hv

end KLInvariance.Graded

end


section

namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]

attribute [instance] ModuleData.kModule ModuleData.tower ModuleData.decomposition
  ModuleData.graded ModuleData.finite

namespace ModuleData
variable {𝓐 : ℤ → Submodule k A}

instance instModuleCarrierObj (M : ModuleData.{uk,ua,um} 𝓐) : Module A M := inferInstanceAs (Module A M.obj)

noncomputable def kernel [IsNoetherianRing A] {M N : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M N) : ModuleData.{uk,ua,um} 𝓐 :=
  sub M f.map.ker (kernel_homogeneous M.piece N.piece f.map 0
    (by simpa using f.graded))

end ModuleData
end KLInvariance.Graded

end


section

/-! Honest nonnegative grading shifts; the underlying integral module is unchanged. -/
namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
noncomputable section

 theorem shift_isInternal (M : ModuleData.{uk,ua,um} 𝓐) (d : ℤ) :
    DirectSum.IsInternal (fun n => M.piece (n-d)) := by
  classical
  apply internal_of_components _ (fun n => component M.piece (n-d))
  · intro n m
    exact (DirectSum.decompose M.piece m (n-d)).property
  · intro n m hm
    exact DirectSum.decompose_of_mem_same M.piece hm
  · intro n j m hnj hm
    apply DirectSum.decompose_of_mem_ne M.piece hm
    omega
  · intro m
    refine ⟨(DirectSum.decompose M.piece m).support.image (fun n => n+d),?_⟩
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
    simp only [add_sub_cancel_right]
    exact DirectSum.sum_support_decompose M.piece m

namespace ModuleData
 def shift (M : ModuleData.{uk,ua,um} 𝓐) (d : ℕ) : ModuleData.{uk,ua,um} 𝓐 where
  obj := M.obj
  kModule := M.kModule
  tower := M.tower
  piece n := M.piece (n-d)
  decomposition := (shift_isInternal M d).chooseDecomposition
  graded := ⟨by
    intro i j a m ha hm
    change a • m ∈ M.piece (i+j-d)
    have hh : a • m ∈ M.piece (i+(j-(d:ℤ))) := SetLike.GradedSMul.smul_mem ha hm
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    omega⟩
  nonneg n hn := M.nonneg (n-d) (by omega)
  finite := M.finite

 def Hom.shift {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N) (d : ℕ) :
    Hom (M.shift d) (N.shift d) where
  map := f.map
  graded n m hm := f.graded (n-d) m hm

 def prod (M N : ModuleData.{uk,ua,um} 𝓐) : ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (M × N)
  kModule := inferInstance
  tower := inferInstance
  piece n := (M.piece n).prod (N.piece n)
  decomposition := (show DirectSum.IsInternal (fun n => (M.piece n).prod (N.piece n)) from by
    apply internal_of_components _ (fun n =>
      (component M.piece n).prodMap (component N.piece n))
    · intro n m
      exact ⟨(DirectSum.decompose M.piece m.1 n).property,
        (DirectSum.decompose N.piece m.2 n).property⟩
    · intro n m hm
      exact Prod.ext (DirectSum.decompose_of_mem_same M.piece hm.1)
        (DirectSum.decompose_of_mem_same N.piece hm.2)
    · intro i j m hij hm
      exact Prod.ext (DirectSum.decompose_of_mem_ne M.piece hm.1 (Ne.symm hij))
        (DirectSum.decompose_of_mem_ne N.piece hm.2 (Ne.symm hij))
    · intro m
      classical
      refine ⟨(DirectSum.decompose M.piece m.1).support ∪ (DirectSum.decompose N.piece m.2).support,?_⟩
      apply Prod.ext
      · change (∑ n ∈ _, (component M.piece n).prodMap (component N.piece n) m).1=m.1
        rw [Prod.fst_sum]
        rw [← Finset.sum_subset Finset.subset_union_left]
        · exact DirectSum.sum_support_decompose M.piece m.1
        · intro n _ hn
          have hh : (DirectSum.decompose M.piece m.1) n=0 := DFinsupp.notMem_support_iff.mp hn
          exact congrArg (fun z : M.piece n => (z : M)) hh
      · change (∑ n ∈ _, (component M.piece n).prodMap (component N.piece n) m).2=m.2
        rw [Prod.snd_sum]
        rw [← Finset.sum_subset Finset.subset_union_right]
        · exact DirectSum.sum_support_decompose N.piece m.2
        · intro n _ hn
          have hh : (DirectSum.decompose N.piece m.2) n=0 := DFinsupp.notMem_support_iff.mp hn
          exact congrArg (fun z : N.piece n => (z : N)) hh).chooseDecomposition
  graded := ⟨by
    intro i j a m ha hm
    exact ⟨SetLike.GradedSMul.smul_mem ha hm.1,SetLike.GradedSMul.smul_mem ha hm.2⟩⟩
  nonneg n hn := by simp [M.nonneg n hn,N.nonneg n hn]
  finite := inferInstance

 def Hom.prodMap {M N P Q : ModuleData.{uk,ua,um} 𝓐} (f : Hom M P) (g : Hom N Q) :
    Hom (M.prod N) (P.prod Q) where
  map := f.map.prodMap g.map
  graded n _ hm := ⟨f.graded n _ hm.1,g.graded n _ hm.2⟩

end ModuleData
end
end KLInvariance.Graded

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


theorem bruhat_antisymm (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatLE cs x y) (hyx : BruhatLE cs y x) : x = y := by
  by_contra hne
  exact (not_lt_of_ge (length_le_of_bruhat cs hyx)) (length_lt_of_bruhat_ne cs hxy hne)

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


namespace Hecke

variable {C : Type*} [CommRing C]

/-- The genuine normalized standard-basis action, a unit in the regular
endomorphism algebra. No presentation relations are assumed. -/
noncomputable def standardUnit (cs : CoxeterSystem M W) (a : C) (w : W) :
    (Module.End C (Space W C))ˣ :=
  wordUnit cs a (Classical.choose (cs.exists_isReduced w))

/-- The bar image of an actual standard basis vector; inverse units give
expression independence before any polynomial coefficients are extracted. -/
noncomputable def barBasis (cs : CoxeterSystem M W) (a : C) (w : W) : Space W C :=
  ((standardUnit cs a w⁻¹)⁻¹).val (basis 1)

/-- Normalized R-polynomials, obtained from the bar action rather than
postulated with an inconsistent choice of descent. -/
noncomputable def rTilde (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  barBasis cs (-X : ℤ[X]) y x


end Hecke


end KLInvariance
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
open Module EdgeAlgebra
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

attribute [local instance] OAI.KLInvariance.TitsSpace.instDecidable_solutions_5
theorem planeWeight_support_root (x : W) (a : PositiveRoot M cs)
    (P : Submodule ℝ (I → ℝ)) (hP : P ∈ (planeWeight x a).support) :
    ∃ b : PositiveRoot M cs, b ≠ a ∧ rootPlane a b = P := by
  obtain ⟨b,hb,hbP⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hP)
  refine ⟨b,?_,hbP⟩
  have hb' := Finsupp.mem_support_iff.mp hb
  change halfVector x a b ≠ 0 at hb'
  simp only [halfVector,rootIndicator_apply] at hb'
  have hh : halfRoot x a b := by
    by_contra hn
    exact hb' (ite_eq_right hn)
  exact hh.1.1

def planeRoot (x : W) (a : PositiveRoot M cs)
    (P : (planeWeight x a).support) : PositiveRoot M cs :=
  (planeWeight_support_root x a P.val P.property).choose

end
end KLInvariance.TitsSpace

/-! NEW GRAPH CLOSURE -/


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
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- The actual degreewise kernel, not merely an equality of dimensions. -/
def degreeKernelEquiv (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n) (n : ℤ) :
    subPiece 𝓜 (LinearMap.ker f) n ≃ₗ[k] LinearMap.ker (degreeMap 𝓜 𝓝 f hf n) where
  toFun m := ⟨⟨m.val.val,m.property⟩, by
    apply Subtype.ext
    exact m.val.property⟩
  invFun m := ⟨⟨m.val.val, by
    have h := congrArg Subtype.val m.property
    exact h⟩,m.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end KLInvariance.Hilbert

end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

 def imagePieceMap (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (S : Submodule A M) (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (n : ℤ) : subPiece 𝓜 S n →ₗ[k] subPiece 𝓝 (S.map f) n where
  toFun v := ⟨⟨f v.val.val,Submodule.mem_map.mpr ⟨_,v.val.property,rfl⟩⟩,
    hf n v.val.val v.property⟩
  map_add' _ _ := by ext; exact map_add f _ _
  map_smul' c v := by ext; exact (f.restrictScalars k).map_smul c v.val.val

 def imageKernelEquiv (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    (S : Submodule A M) (f : M →ₗ[A] N) (hf : ∀ n m, m ∈ 𝓜 n → f m ∈ 𝓝 n)
    (n : ℤ) : subPiece 𝓜 (S ⊓ LinearMap.ker f) n ≃ₗ[k]
      LinearMap.ker (imagePieceMap 𝓜 𝓝 S f hf n) where
  toFun v := ⟨⟨⟨v.val.val,v.val.property.1⟩,v.property⟩,by
    apply Subtype.ext
    apply Subtype.ext
    exact v.val.property.2⟩
  invFun v := ⟨⟨v.val.val.val,⟨v.val.val.property,by
    have h := congrArg (fun z => z.val.val) v.property
    exact h⟩⟩,v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

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

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
noncomputable section
 def zero : ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A PUnit.{max ua um+1}
  kModule := inferInstance
  tower := inferInstance
  piece _ := ⊥
  decomposition := (show DirectSum.IsInternal (fun _ : ℤ => (⊥ : Submodule k PUnit.{max ua um+1})) from by
    apply internal_of_components _ (fun _ => 0)
    · intro _ _; exact Submodule.zero_mem _
    · intro _ _ _; exact Subsingleton.elim _ _
    · intro _ _ _ _ _; rfl
    · intro m; exact ⟨∅,Subsingleton.elim _ _⟩).chooseDecomposition
  graded := ⟨by intro _ _ _ _ _ _; exact Subsingleton.elim _ _⟩
  nonneg _ _ := rfl
  finite := inferInstance

 def Hom.zero (M N : ModuleData.{uk,ua,um} 𝓐) : Hom M N :=
  ⟨0,fun _ _ _ => Submodule.zero_mem _⟩

 def Hom.pi {ι : Type um} [Fintype ι] {M N : ι → ModuleData.{uk,ua,um} 𝓐}
    (f : ∀ i, Hom (M i) (N i)) : Hom (ModuleData.pi M) (ModuleData.pi N) where
  map := LinearMap.pi fun i => (f i).map.comp (LinearMap.proj i)
  graded n _ hm i hi := (f i).graded n _ (hm i hi)
end
end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  {G : OrderedGraph V E}
noncomputable section

 def zero : GradedSheaf (𝓐 := 𝓐) G where
  vertex _ := ModuleData.zero
  edge _ := ModuleData.zero
  lower _ := ModuleData.Hom.zero _ _
  upper _ := ModuleData.Hom.zero _ _

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

/-! Extension by zero from a full lower ideal. Proof-indexed finite products
avoid informal identifications of the integral stalks at boundary vertices. -/
namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} {V E : Type um} [PartialOrder V]
  (G : OrderedGraph V E) (K : Set V) (hK : IsLowerSet K)

 def lowerGraph : OrderedGraph K {e : E // G.target e ∈ K} where
  source e := ⟨G.source e.val,hK (G.increasing e.val).le e.property⟩
  target e := ⟨G.target e.val,e.property⟩
  increasing e := G.increasing e.val

namespace GradedSheaf
noncomputable section
attribute [local instance] Classical.propDecidable

variable {G K hK} (B : GradedSheaf (𝓐 := 𝓐) (lowerGraph G K hK))

 def lowerExtend : GradedSheaf (𝓐 := 𝓐) G where
  vertex x := ModuleData.pi (fun h : Witness.{um} (x ∈ K) => B.vertex ⟨x,h.down.down⟩)
  edge e := ModuleData.pi (fun h : Witness.{um} (G.target e ∈ K) => B.edge ⟨e,h.down.down⟩)
  lower e :=
    { map := LinearMap.pi (fun h => (B.lower ⟨e,h.down.down⟩).map.comp
        (LinearMap.proj ⟨⟨hK (G.increasing e).le h.down.down⟩⟩))
      graded n _v hv h _ := (B.lower ⟨e,h.down.down⟩).graded n _ (hv _ (Set.mem_univ _)) }
  upper e :=
    { map := LinearMap.pi (fun h => (B.upper ⟨e,h.down.down⟩).map.comp (LinearMap.proj h))
      graded n _v hv h _ := (B.upper ⟨e,h.down.down⟩).graded n _ (hv _ (Set.mem_univ _)) }

 def lowerExtendVertex (x : K) : (B.lowerExtend.vertex x.val) ≃ₗ[A] B.vertex x where
  toFun f := f ⟨⟨x.property⟩⟩
  invFun v _ := v
  left_inv f := by
    funext h
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem lowerExtendVertex_graded (x : K) (n : ℤ) (v : B.lowerExtend.vertex x.val)
    (hv : v ∈ (B.lowerExtend.vertex x.val).piece n) :
    B.lowerExtendVertex x v ∈ (B.vertex x).piece n := hv _ (Set.mem_univ _)

 theorem lowerExtend_support (x : V) (hx : x ∉ K) : Subsingleton (B.lowerExtend.vertex x) :=
  ⟨fun _f _g => funext (fun h => (hx h.down.down).elim)⟩

 theorem lowerExtend_free (hb : ∀ x, Module.Free A (B.vertex x)) (x : V) :
    Module.Free A (B.lowerExtend.vertex x) := by
  let : ∀ h : Witness.{um} (x ∈ K), Module.Free A (B.vertex ⟨x,h.down.down⟩) := fun h => hb _
  change Module.Free A (∀ h : Witness.{um} (x ∈ K), B.vertex ⟨x,h.down.down⟩)
  infer_instance

 def liftLowerAssignment (f : B.forget.Assignment) : B.lowerExtend.forget.Assignment :=
  fun x h => f ⟨x,h.down.down⟩

 def projectLowerAssignment (f : B.lowerExtend.forget.Assignment) : B.forget.Assignment :=
  fun x => f x.val ⟨⟨x.property⟩⟩

 theorem projectLower_compatible {U : Set V} {f : B.lowerExtend.forget.Assignment}
    (hf : B.lowerExtend.forget.CompatibleOn U f) :
    B.forget.CompatibleOn (Subtype.val ⁻¹' U) (B.projectLowerAssignment f) := by
  intro e hs ht
  exact congrFun (hf e.val hs ht) ⟨⟨e.property⟩⟩

 theorem liftLower_compatible {U : Set V} {f : B.forget.Assignment}
    (hf : B.forget.CompatibleOn (Subtype.val ⁻¹' U) f) :
    B.lowerExtend.forget.CompatibleOn U (B.liftLowerAssignment f) := by
  intro e hs ht
  funext h
  exact hf ⟨e,h.down.down⟩ hs ht

 theorem lowerExtend_generated (hb : B.forget.Generated) : B.lowerExtend.forget.Generated := by
  intro x v
  by_cases hx : x ∈ K
  · obtain ⟨f,hf,hfx⟩ := hb ⟨x,hx⟩ (v ⟨⟨hx⟩⟩)
    refine ⟨B.liftLowerAssignment f,B.liftLower_compatible hf,?_⟩
    funext h
    exact hfx
  · let : Subsingleton (B.lowerExtend.forget.vertex x) := B.lowerExtend_support x hx
    exact ⟨0,fun _ _ _ => by simp,Subsingleton.elim _ _⟩

 theorem lowerExtend_quotient (α : E → A)
    (hb : B.UpperQuotient (fun e => α e.val)) : B.lowerExtend.UpperQuotient α := by
  intro e
  constructor
  · intro v
    have hh : ∀ h : Witness.{um} (G.target e ∈ K), ∃ w, (B.upper ⟨e,h.down.down⟩).map w=v h :=
      fun h => (hb ⟨e,h.down.down⟩).1 (v h)
    choose w hw using hh
    exact ⟨w,funext hw⟩
  · intro v
    constructor
    · intro hv
      have hh : ∀ h : Witness.{um} (G.target e ∈ K), ∃ w, v h=α e • w :=
        fun h => (hb ⟨e,h.down.down⟩).2 (v h) |>.mp (congrFun hv h)
      choose w hw using hh
      exact ⟨w,funext hw⟩
    · rintro ⟨w,rfl⟩
      funext h
      exact (hb ⟨e,h.down.down⟩).2 _ |>.mpr ⟨w h,rfl⟩

 theorem lowerExtend_minimal (x : V)
    (hb : ∀ hx : x ∈ K, B.KernelMinimal ⟨x,hx⟩) : B.lowerExtend.KernelMinimal x := by
  intro f hf
  apply LocalCover.pi_mem_ideal_smul
  intro h
  apply hb h.down.down (B.projectLowerAssignment f)
  intro e he
  have hes : G.source e.val=x := congrArg Subtype.val he
  exact congrFun (hf e.val hes) ⟨⟨e.property⟩⟩

end
end GradedSheaf
end KLInvariance.MomentGraph

end


section


namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur} [CommRing R] {V : Type uv} [PartialOrder V]
  {E : Type ue} (G : OrderedGraph V E) (α : E → R) (c : V)
noncomputable section

 def structureSheaf : Sheaf (R := R) G where
  vertex x := ModuleCat.of R (PLift (x ≤ c) → R)
  edge e := ModuleCat.of R (PLift (G.target e ≤ c) → R ⧸ Ideal.span {α e})
  upper e := LinearMap.pi (fun h => (quotientLinear α e).comp (LinearMap.proj h))
  lower e := LinearMap.pi (fun h => (quotientLinear α e).comp
    (LinearMap.proj ⟨(G.increasing e).le.trans h.down⟩))

 theorem structureSheaf_support (x : V) (hx : ¬ x ≤ c) :
    Subsingleton ((structureSheaf G α c).vertex x) := by
  refine ⟨fun f g => funext fun h => False.elim (hx h.down)⟩

end
end KLInvariance.MomentGraph.Sheaf

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

namespace KLInvariance.Graded
open Polynomial
universe uk us um ui

attribute [instance] NonnegativeBasis.finite

end KLInvariance.Graded

end


section

/-! Parity matching in finite lower Bruhat intervals, used only to construct
actual dihedral interpolation sections. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 theorem simple_mul_bruhat_of_descent {c : W} (i : I)
    (hi : cs.length (cs.simple i*c) < cs.length c) {z : W} (hz : BruhatLE cs z c) :
    BruhatLE cs (cs.simple i*z) c := by
  have h := le_upperSimple cs i (cs.simple i*z)
  rw [upperSimple_mul] at h
  have htop : upperSimple cs i c = c := by simp only [upperSimple,ite_eq_left hi]
  rw [← htop]
  exact bruhat_trans cs h (upperSimple_mono cs i hz)

 theorem lower_parity_balance {c : W} (hc : c ≠ 1) {p : ℕ} (hp : p < 2) :
    ((lowerFinset cs c).filter (fun z => cs.length z % 2 = p)).card =
      ((lowerFinset cs c).filter (fun z => cs.length z % 2 ≠ p)).card := by
  classical
  obtain ⟨i,hi⟩ := cs.exists_leftDescent_of_ne_one hc
  have hmem {z : W} (hz : z ∈ lowerFinset cs c) : cs.simple i*z ∈ lowerFinset cs c :=
    (mem_lowerFinset cs c _).mpr (simple_mul_bruhat_of_descent cs i hi
      ((mem_lowerFinset cs c _).mp hz))
  refine Finset.card_bij (fun z _ => cs.simple i*z) ?_ ?_ ?_
  · intro z hz
    obtain ⟨hz,hp'⟩ := Finset.mem_filter.mp hz
    refine Finset.mem_filter.mpr ⟨hmem hz,?_⟩
    have := cs.length_simple_mul z i
    omega
  · intro z hz w hw he
    exact mul_left_cancel he
  · intro z hz
    obtain ⟨hz,hp'⟩ := Finset.mem_filter.mp hz
    refine ⟨cs.simple i*z,Finset.mem_filter.mpr ⟨hmem hz,?_⟩,
      cs.simple_mul_simple_cancel_left i⟩
    have := cs.length_simple_mul z i
    omega

end
end KLInvariance

end


section

/-! A minimal graded free cover splits out of every finite graded free cover.
The residual kernel is genuinely graded free over the connected coefficient ring.
This is the local step for decomposing actual flabby word sheaves. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  [IsDomain A] [IsNoetherianRing A]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)
  (hzero : ∀ a ∈ 𝓐 0, ∃ c : k, algebraMap k A c = a)
noncomputable section

 def Hom.splitEquiv {F C : ModuleData.{uk,ua,um} 𝓐}
    (g : Hom F C) (h : Hom C F) (hgh : g.map.comp h.map = LinearMap.id) :
    F ≃ₗ[A] C × kernel g := LocalCover.splitEquiv g.map h.map hgh

end
end KLInvariance.Graded.ModuleData

end


section

/-! Graded linear equivalence preserves the genuine free-module character.
This does not assert its identification with any KL polynomial. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ)}

noncomputable def mapNonnegativeBasis (e : M ≃ₗ[MvPolynomial σ k] N)
    (he : ∀ n v, v ∈ M.piece n → e v ∈ N.piece n)
    (b : NonnegativeBasis (σ := σ) M.piece) : NonnegativeBasis (σ := σ) N.piece where
  index := b.index
  finite := b.finite
  basis := b.basis.map e
  degree := b.degree
  homogeneous i := he _ _ (b.homogeneous i)

end KLInvariance.Graded.ModuleData

end


section

/-! Honest polynomial characters commute with actual finite graded sums and
nonnegative shifts. No Hecke or KL identification enters these lemmas. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

 def shiftedBasis (b : NonnegativeBasis (σ := σ) M.piece) (d : ℕ) :
    NonnegativeBasis (σ := σ) (M.shift d).piece where
  index := b.index
  finite := b.finite
  basis := b.basis
  degree i := b.degree i+d
  homogeneous i := by
    change b.basis i ∈ M.piece ((b.degree i+d : ℕ)-(d:ℤ))
    simpa only [Nat.cast_add,add_sub_cancel_right] using b.homogeneous i

 instance shift_free [Module.Free (MvPolynomial σ k) M] (d : ℕ) :
    Module.Free (MvPolynomial σ k) (M.shift d) := ‹Module.Free (MvPolynomial σ k) M›

 def productBasis (b : NonnegativeBasis (σ := σ) M.piece)
    (c : NonnegativeBasis (σ := σ) N.piece) :
    NonnegativeBasis (σ := σ) (M.prod N).piece where
  index := b.index ⊕ c.index
  finite := inferInstance
  basis := b.basis.prod c.basis
  degree := Sum.elim b.degree c.degree
  homogeneous i := by
    cases i with
    | inl i =>
      change ((b.basis.prod c.basis) (Sum.inl i)).1 ∈ M.piece (b.degree i) ∧
        ((b.basis.prod c.basis) (Sum.inl i)).2 ∈ N.piece (b.degree i)
      simpa only [Basis.prod_apply_inl_fst,Basis.prod_apply_inl_snd] using
        And.intro (b.homogeneous i) (Submodule.zero_mem (N.piece (b.degree i)))
    | inr i =>
      change ((b.basis.prod c.basis) (Sum.inr i)).1 ∈ M.piece (c.degree i) ∧
        ((b.basis.prod c.basis) (Sum.inr i)).2 ∈ N.piece (c.degree i)
      simpa only [Basis.prod_apply_inr_fst,Basis.prod_apply_inr_snd] using
        And.intro (Submodule.zero_mem (M.piece (c.degree i))) (c.homogeneous i)

 instance prod_free [Module.Free (MvPolynomial σ k) M] [Module.Free (MvPolynomial σ k) N] :
    Module.Free (MvPolynomial σ k) (M.prod N) :=
  (inferInstance : Module.Free (MvPolynomial σ k) (M × N))

 def piBasis {ι : Type um} [Fintype ι]
    (F : ι → ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
    (b : ∀ i, NonnegativeBasis (σ := σ) (F i).piece) :
    NonnegativeBasis (σ := σ) (pi F).piece where
  index := Σ i, (b i).index
  finite := inferInstance
  basis := Pi.basis (fun i => (b i).basis)
  degree i := (b i.1).degree i.2
  homogeneous i := by
    classical
    intro j _
    change (Pi.basis (fun i => (b i).basis)) i j ∈ (F j).piece ((b i.1).degree i.2)
    rw [Pi.basis_apply]
    by_cases h : j=i.1
    · subst j
      simpa only [Pi.single_eq_same] using (b i.1).homogeneous i.2
    · simp only [Pi.single_eq_of_ne h,Submodule.zero_mem]

 instance pi_free {ι : Type um} [Fintype ι]
    (F : ι → ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
    [∀ i, Module.Free (MvPolynomial σ k) (F i)] :
    Module.Free (MvPolynomial σ k) (pi F) :=
  (inferInstance : Module.Free (MvPolynomial σ k) (∀ i, F i))

end
end KLInvariance.Graded.ModuleData

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

/-! The integral reflection trace lowers the actual polynomial grading by one.
This is the graded rank-two Frobenius input, not a BMP character assertion. -/
namespace KLInvariance.Graded
universe uk ua
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [IsDomain A]
  [Algebra k A] (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
  [SetLike.GradedSMul 𝓐 𝓐]

 theorem homogeneous_of_mul {a b : A} {d n : ℤ}
    (ha : a ∈ 𝓐 d) (hne : a ≠ 0) (hab : a*b ∈ 𝓐 n) : b ∈ 𝓐 (n-d) := by
  have hc := component_homogeneous_smul 𝓐 𝓐 d a ha n b
  have he : component 𝓐 n (a*b)=a*b :=
    DirectSum.decompose_of_mem_same 𝓐 hab
  rw [smul_eq_mul,he,smul_eq_mul] at hc
  have hb : b=component 𝓐 (n-d) b := mul_left_cancel₀ hne hc
  rw [hb]
  exact (DirectSum.decompose 𝓐 b (n-d)).property

end KLInvariance.Graded

namespace KLInvariance.ReflectionFrobenius
open KLInvariance.Graded
universe uk ua
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

 theorem trace_difference (a : A) :
    2*α*(trace τ α hinv hα hanti hdiv a : A) = a-τ a := by
  have h := expand_coordinates τ α hinv hα hanti hdiv a
  have ht := congrArg τ h
  simp only [expand_apply,map_add,map_mul,fixed_val,hanti] at h ht
  change 2*α*((coordinates τ α hinv hα hanti hdiv a).2 : A) = a-τ a
  linear_combination h-ht

 theorem trace_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedSMul 𝓐 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    {n : ℤ} {a : A} (ha : a ∈ 𝓐 n) :
    (trace τ α hinv hα hanti hdiv a : A) ∈ 𝓐 (n-1) := by
  apply homogeneous_of_mul 𝓐 hroot hα
  have hd := (𝓐 n).sub_mem ha (hτ n a ha)
  have hal := (𝓐 n).smul_mem ((2:k)⁻¹) hd
  have ht := trace_difference τ α hinv hα hanti hdiv a
  have htwo : (2:A)*algebraMap k A ((2:k)⁻¹) = 1 := by
    rw [show (2:A)=algebraMap k A (2:k) by exact (map_ofNat (algebraMap k A) 2).symm, ← map_mul]
    simp
  have he : α*(trace τ α hinv hα hanti hdiv a : A) =
      (2:k)⁻¹ • (a-τ a) := by
    rw [Algebra.smul_def]
    linear_combination (algebraMap k A ((2:k)⁻¹))*ht -
      (α*(trace τ α hinv hα hanti hdiv a : A))*htwo
  exact he ▸ hal

end
end KLInvariance.ReflectionFrobenius

end


section

/-! The actual two-element homogeneous basis of a reflection Frobenius
extension. This basis is used in the tensor-defined Bott--Samelson modules. -/
namespace KLInvariance.ReflectionFrobenius
open Module
universe uk ua
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

 theorem reflectionBasis_homogeneous (𝓐 : ℤ → Submodule k A)
    [SetLike.GradedOne 𝓐] (hroot : α ∈ 𝓐 1) (i : Fin 2) :
    reflectionBasis τ α hinv hα hanti hdiv i ∈ 𝓐 (i.val : ℤ) := by
  fin_cases i
  · change reflectionBasis τ α hinv hα hanti hdiv (0 : Fin 2) ∈ 𝓐 0
    rw [reflectionBasis_zero]
    exact SetLike.one_mem_graded 𝓐
  · change reflectionBasis τ α hinv hα hanti hdiv (1 : Fin 2) ∈ 𝓐 1
    rw [reflectionBasis_one]
    exact hroot

end
end KLInvariance.ReflectionFrobenius

end


section

/-! Homogeneous integral Bott--Samelson pairing at the genuine tensor basis.
No indecomposable summand or character identity is postulated here. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct ReflectionFrobenius
universe uk ua um ui
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

variable [Module.Free (fixed τ) A] [Module.Finite (fixed τ) A]

variable (N : PairedModule.{ua,um} A)
  {ι : Type ui} (b : Basis ι A N)
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 theorem inducedPairing_basis (i i' : Fin 2) (j j' : ι) :
    (inducedModule (trace τ α hinv hα hanti hdiv)
      (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N).pairing
      (inducedBasis τ α hinv hα hanti hdiv N b (i,j))
      (inducedBasis τ α hinv hα hanti hdiv N b (i',j')) =
      (trace τ α hinv hα hanti hdiv
        (reflectionBasis τ α hinv hα hanti hdiv i *
          reflectionBasis τ α hinv hα hanti hdiv i' * N.pairing (b j) (b j')) : A) := by
  rw [inducedBasis_apply,inducedBasis_apply]
  let : Module.Free (fixed τ) N := Module.Free.of_basis
    ((reflectionBasis τ α hinv hα hanti hdiv).smulTower b)
  let : Module.Finite (fixed τ) N := Module.Finite.trans A N
  change extendPairing A (restrictPairing (trace τ α hinv hα hanti hdiv)
    (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N N.pairing) _ _ = _
  rw [extendPairing_tmul,restrictPairing_apply]
  simp only [one_mul]
  change ((trace τ α hinv hα hanti hdiv _) : A) = _
  apply congrArg Subtype.val
  apply congrArg (trace τ α hinv hα hanti hdiv)
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring

 theorem inducedPairing_basis_homogeneous (𝓐 : ℤ → Submodule k A)
    [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hroot : α ∈ 𝓐 1) (hτ : ∀ n a, a ∈ 𝓐 n → τ a ∈ 𝓐 n)
    (d : ι → ℤ) (l : ℤ)
    (hb : ∀ j j', N.pairing (b j) (b j') ∈ 𝓐 (d j+d j'-l))
    (i i' : Fin 2) (j j' : ι) :
    (inducedModule (trace τ α hinv hα hanti hdiv)
      (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N).pairing
      (inducedBasis τ α hinv hα hanti hdiv N b (i,j))
      (inducedBasis τ α hinv hα hanti hdiv N b (i',j')) ∈
      𝓐 ((i.val+d j)+(i'.val+d j')-(l+1)) := by
  rw [inducedPairing_basis]
  have h := trace_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot hτ
    (SetLike.GradedMul.mul_mem
      (SetLike.GradedMul.mul_mem
        (reflectionBasis_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot i)
        (reflectionBasis_homogeneous τ α hinv hα hanti hdiv 𝓐 hroot i'))
      (hb j j'))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

end
end KLInvariance.FrobeniusDuality

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

/-! Homogeneous perfect pairings on the actual integral free modules.  The
inverse grading is proved, not inferred merely after fraction-field extension. -/
namespace KLInvariance.Graded
open Module
universe uk ua um un ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {N : Type um} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
  {P : Type un} [AddCommGroup P] [Module A P] [Module k P] [IsScalarTower k A P]
noncomputable section

omit [Algebra k A] [IsScalarTower k A N] [IsScalarTower k A P] in
 theorem equiv_inverse_homogeneous
    (𝓝 : ℤ → Submodule k N) (𝓟 : ℤ → Submodule k P)
    [DirectSum.Decomposition 𝓝] [DirectSum.Decomposition 𝓟]
    (e : N ≃ₗ[A] P) (d : ℤ)
    (he : ∀ n x, x ∈ 𝓝 n → e x ∈ 𝓟 (n+d))
    (n : ℤ) (y : P) (hy : y ∈ 𝓟 n) : e.symm y ∈ 𝓝 (n-d) := by
  have hc : component 𝓝 (n-d) (e.symm y) = e.symm y := by
    apply e.injective
    change e.toLinearMap (component 𝓝 (n-d) (e.symm y)) = e.toLinearMap (e.symm y)
    rw [← map_component 𝓝 𝓟 e.toLinearMap d he n (e.symm y)]
    simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    exact DirectSum.decompose_of_mem_same 𝓟 hy
  rw [← hc]
  exact (DirectSum.decompose 𝓝 (e.symm y) (n-d)).property

end
end KLInvariance.Graded

end


section

/-! A homogeneous integral equivalence induces genuine shifted degreewise
vector-space equivalences, including its inverse grading. -/
namespace KLInvariance.Graded
universe uk um un
variable {k : Type uk} [Field k]
  {M : Type um} [AddCommGroup M] [Module k M]
  {N : Type un} [AddCommGroup N] [Module k N]
  (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
  [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
  (e : M ≃ₗ[k] N) (d : ℤ)
  (he : ∀ n m, m ∈ 𝓜 n → e m ∈ 𝓝 (n+d))
noncomputable section

 def homogeneousPieceEquiv (n : ℤ) : 𝓜 n ≃ₗ[k] 𝓝 (n+d) where
  toFun m := ⟨e m.val,he n m.val m.property⟩
  invFun v := ⟨e.symm v.val,by
    simpa only [add_sub_cancel_right] using
      equiv_inverse_homogeneous 𝓜 𝓝 e d he (n+d) v.val v.property⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)
  map_add' v w := Subtype.ext (map_add e v.val w.val)
  map_smul' r v := Subtype.ext (map_smul e r v.val)

end
end KLInvariance.Graded

end


section

/-! Finiteness of true submodule and finite product homogeneous components. -/
namespace KLInvariance.Graded
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

 instance subPiece_finite (𝓜 : ℤ → Submodule k M) (S : Submodule A M) (n : ℤ)
    [Module.Finite k (𝓜 n)] : Module.Finite k (subPiece 𝓜 S n) := by
  let f : subPiece 𝓜 S n →ₗ[k] 𝓜 n :=
    { toFun := fun v => ⟨v.val.val,v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_injective f
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : 𝓜 n => z.val) h

 variable {ι : Type ui} [Finite ι] {P : ι → Type um}
   [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]

 instance piPiece_finite (𝓟 : ∀ i, ℤ → Submodule k (P i)) (n : ℤ)
    [∀ i, Module.Finite k (𝓟 i n)] : Module.Finite k (piPiece 𝓟 n) := by
  let f : piPiece 𝓟 n →ₗ[k] (∀ i, 𝓟 i n) :=
    { toFun := fun v i => ⟨v.val i,v.property i (Set.mem_univ i)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_injective f
  intro v w h
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

end KLInvariance.Graded

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

/-! Range-valued projections to sets of coordinates and their natural
surjective restriction maps. -/
namespace KLInvariance.CoordinateProjection
universe ur un uv ux
variable {R : Type ur} [CommRing R] {N : Type un} [AddCommGroup N] [Module R N]
  {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, N →ₗ[R] X x)
noncomputable section

 theorem project_surjective (U : Set V) : Function.Surjective (project f U) :=
by
  rintro ⟨z,n,hn⟩
  exact ⟨n,Subtype.ext hn⟩

end
end KLInvariance.CoordinateProjection

end


section

namespace KLInvariance.ReflectionPairTranslation
open TensorProduct
universe uc ua un
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  (τ : A ≃+* A) (hfix : ∀ c : C, τ (algebraMap C A c)=algebraMap C A c)
noncomputable section

 theorem tensorFirst_map (e : Module.End A N) (m : A ⊗[C] N) :
    tensorFirst (C := C) (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (e.restrictScalars C) m)=
      e (tensorFirst (C := C) m) := by
  induction m using OAI.tensorInductionOn with
  | add m n hm hn => simp only [map_add,hm,hn]
  | tmul a n => simp only [AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,tensorFirst_tmul,map_smul]

 theorem tensorSecond_map (e : Module.End A N) (m : A ⊗[C] N) :
    tensorSecond τ hfix (AlgebraTensorModule.map (LinearMap.id : A →ₗ[A] A) (e.restrictScalars C) m)=
      twistMap τ e (tensorSecond τ hfix m) := by
  induction m using OAI.tensorInductionOn with
  | add m n hm hn => simp only [map_add,hm,hn]
  | tmul a n =>
    simp only [AlgebraTensorModule.map_tmul,LinearMap.id_apply,
      LinearMap.restrictScalars_apply,tensorSecond_tmul]
    apply Twist.ext
    exact (map_smul e (τ a) n).symm

end
end KLInvariance.ReflectionPairTranslation

end


section

namespace KLInvariance.ReflectionPairTranslation
open TensorProduct
universe uc ua un
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  (τ : A ≃+* A) (hfix : ∀ c : C, τ (algebraMap C A c)=algebraMap C A c)
noncomputable section
 theorem tensor_difference (α : A) (hdiv : ∀ a : A, α ∣ a-τ a)
    (m : A ⊗[C] N) :
    ∃ n : N, tensorFirst (C := C) m-(tensorSecond τ hfix m).val=α • n := by
  induction m using OAI.tensorInductionOn with
  | add m n hm hn =>
    obtain ⟨p,hp⟩ := hm
    obtain ⟨q,hq⟩ := hn
    refine ⟨p+q,?_⟩
    simp only [map_add]
    change (tensorFirst (C := C) m+tensorFirst (C := C) n)-
      ((tensorSecond τ hfix m).val+(tensorSecond τ hfix n).val)=α • (p+q)
    rw [add_sub_add_comm,hp,hq,smul_add]
  | tmul a n =>
    obtain ⟨b,hb⟩ := hdiv a
    refine ⟨b • n,?_⟩
    change a • n-τ a • n=α • (b • n)
    rw [← sub_smul,hb,mul_smul]
end
end KLInvariance.ReflectionPairTranslation

end


section

namespace KLInvariance.PairProjection
universe u v w z
variable {R : Type u} [CommRing R]
  {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y)

 theorem cross_lift (α : R) (hann : ∀ z : Edge f g, α • z=0)
    (p q : N) (h : ∃ n : N, p-q=α • n) :
    ∃ n : N, f n=f q ∧ g n=g p := by
  apply (compatible_iff f g _ _).mp
  obtain ⟨n,hn⟩ := h
  have hd := congrArg ((lower f g).comp f) hn
  simp only [LinearMap.comp_apply,map_sub,map_smul,hann] at hd
  exact (sub_eq_zero.mp hd).symm.trans (compatible f g p)

end KLInvariance.PairProjection

end


section

namespace KLInvariance
universe ur um un up
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]
noncomputable section

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace ReflectionPairTranslation.Twist
 theorem projective (τ : R ≃+* R) [Module.Projective R N] : Module.Projective R (Twist τ N) := by
  let : RingHomInvPair τ.symm.toRingHom τ.toRingHom := RingHomInvPair.of_ringEquiv_symm τ
  let : RingHomInvPair τ.toRingHom τ.symm.toRingHom := RingHomInvPair.of_ringEquiv τ
  exact Module.Projective.of_equiv (σ' := τ.toRingHom) (equiv τ N)
end ReflectionPairTranslation.Twist
end
end KLInvariance

end


section

namespace KLInvariance
universe ur um uh up us
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {H : Type uh} [AddCommGroup H] [Module R H]
  {P : Type up} [AddCommGroup P] [Module R P]
  {S : Type us} [AddCommGroup S] [Module R S]

namespace ReflectionPairTranslation
 theorem twistMap_injective (τ : R ≃+* R) (f : M →ₗ[R] P) (hf : Function.Injective f) :
    Function.Injective (twistMap τ f) := by
  intro m n h
  exact Twist.ext (hf (congrArg Twist.val h))
end ReflectionPairTranslation

end KLInvariance

end


section

namespace KLInvariance.ProjectiveRange
universe ur um uh up us
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {H : Type uh} [AddCommGroup H] [Module R H]
  {P : Type up} [AddCommGroup P] [Module R P]
  {S : Type us} [AddCommGroup S] [Module R S]
  (r : M →ₗ[R] H) (f : M →ₗ[R] P) (k : P →ₗ[R] S)
  (h : ∀ m, r m=0 → k (f m)=0)
noncomputable section

 def kernelOnKernelEquiv : ↥(LinearMap.ker r ⊓ LinearMap.ker f) ≃ₗ[R]
    LinearMap.ker (onKernel r f k h) where
  toFun z := ⟨⟨z.val,z.property.1⟩,Subtype.ext z.property.2⟩
  invFun z := ⟨z.val.val,z.val.property,congrArg Subtype.val z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem projective_of_two_stage (hr : Function.Surjective r)
    (hf : Function.Surjective (onKernel r f k h))
    [Module.Projective R H] [Module.Projective R (LinearMap.ker k)]
    [Module.Projective R ↥(LinearMap.ker r ⊓ LinearMap.ker f)] :
    Module.Projective R M := by
  let : Module.Projective R (LinearMap.ker (onKernel r f k h)) :=
    Module.Projective.of_equiv (kernelOnKernelEquiv r f k h)
  let : Module.Projective R (LinearMap.ker r) := projective_of_kernel (onKernel r f k h) hf
  exact projective_of_kernel r hr
end
end KLInvariance.ProjectiveRange

end


section

/-! Flabbiness of the genuine interval word sheaf; the extension outside the
finite support is zero, not an extra assumption on the source interval. -/
namespace KLInvariance.TitsSpace
open Module MomentGraph BruhatGraph
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def intervalUpperClosure (b : W) (U : Set (Interval cs 1 b)) : Set W :=
  {x | ∃ a : Interval cs 1 b, a∈U ∧ BruhatLE cs a.val x}

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

/-! The literal integral image sheaf of a graded projector, with its actual
splitting. Used for word-adjoint projectors; no BMP summand is assumed. -/
namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [IsNoetherianRing A]
  {M N : ModuleData.{uk,ua,um} 𝓐}
noncomputable section

 def rangeMap (e : Hom M M) (f : Hom N N) (g : Hom M N)
    (h : ∀ m, f.map (g.map m)=g.map (e.map m)) : Hom (range e) (range f) where
  map := (g.map.domRestrict e.map.range).codRestrict f.map.range (by
    rintro ⟨_,m,rfl⟩
    exact ⟨g.map m,h m⟩)
  graded n m hm := g.graded n m.val hm

 def rangeInclusion (e : Hom M M) : Hom (range e) M where
  map := e.map.range.subtype
  graded _ _ hm := hm

 def rangeProjection (e : Hom M M) : Hom M (range e) where
  map := e.map.rangeRestrict
  graded n m hm := e.graded n m hm

end
end KLInvariance.Graded.ModuleData

end


section

/-! The range of the genuine adjoint projector is integrally the dual of
the original summand, with no assumed self-duality of that summand. -/
namespace PerfectAdjoint
open Module
universe ur um un
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  (d : M ≃ₗ[R] Dual R M) (i : N →ₗ[R] M) (p : M →ₗ[R] N)
  (hpi : ∀ n, p (i n)=n)
noncomputable section

 theorem adjoint_projector_eq : adjoint d (i.comp p)=
    AdjointSummandDuality.adjointProjector d i p := by
  apply LinearMap.ext
  intro m
  rfl

 def rangeAdjointEquivDual : LinearMap.range (adjoint d (i.comp p)) ≃ₗ[R] Dual R N :=
  (LinearEquiv.ofEq _ _ (by
    rw [adjoint_projector_eq,AdjointSummandDuality.adjointProjector_range d i p hpi])).trans
    (AdjointSummandDuality.adjointEquivDual d i p hpi)

end
end PerfectAdjoint

end


section

namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  (d : M ≃ₗ[R] Dual R M) (f : End R M) (hf : ∀ m, f (f m)=f m)
noncomputable section

 def rangeAdjointEquivDualRange : LinearMap.range (adjoint d f) ≃ₗ[R] Dual R f.range :=
  rangeAdjointEquivDual d f.range.subtype f.rangeRestrict (range_projector_split f hf)

end
end PerfectAdjoint

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
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n=⊥)
noncomputable section

 theorem unit_endomorphisms_commute (f g : Hom (unit.{uk,ua,um} hneg) (unit hneg))
    (v : unit hneg) : f.map (g.map v)=g.map (f.map v) := by
  let z : unit.{uk,ua,um} hneg := fun _ => (1 : A)
  have he (w : unit.{uk,ua,um} hneg) : w=w PUnit.unit • z := by
    funext j
    change w j=w PUnit.unit * 1
    simp only [mul_one]
  have hf (w : unit.{uk,ua,um} hneg) : f.map w=w PUnit.unit • f.map z := by
    conv_lhs => rw [he w]
    exact map_smul f.map _ z
  have hg (w : unit.{uk,ua,um} hneg) : g.map w=w PUnit.unit • g.map z := by
    conv_lhs => rw [he w]
    exact map_smul g.map _ z
  rw [hf (g.map v),hg (f.map v),hg v,hf v]
  funext j
  change (v PUnit.unit * (g.map z) PUnit.unit) * (f.map z) j =
    (v PUnit.unit * (f.map z) PUnit.unit) * (g.map z) j
  have hej : j=PUnit.unit := Subsingleton.elim _ _
  subst j
  ring

 theorem unit_split_reverse (f g : Hom (unit.{uk,ua,um} hneg) (unit hneg))
    (h : ∀ v, g.map (f.map v)=v) (v : unit hneg) : f.map (g.map v)=v :=
  (unit_endomorphisms_commute hneg f g v).trans (h v)


 theorem split_reverse_of_unit {B N : ModuleData.{uk,ua,um} 𝓐}
    (hB : B=unit hneg) (o : Hom N (unit hneg)) (o' : Hom (unit hneg) N)
    (ho : ∀ v, o'.map (o.map v)=v) (i : Hom B N) (p : Hom N B)
    (hpi : ∀ v, p.map (i.map v)=v) (v : N) : i.map (p.map v)=v := by
  subst B
  have hp : ∀ a, (p.comp o').map ((o.comp i).map a)=a := by
    intro a
    change p.map (o'.map (o.map (i.map a)))=a
    rw [ho]
    exact hpi a
  have hh := unit_split_reverse hneg (o.comp i) (p.comp o') hp (o.map v)
  change o.map (i.map (p.map (o'.map (o.map v))))=o.map v at hh
  rw [ho] at hh
  exact (ho _).symm.trans ((congrArg o'.map hh).trans (ho v))

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.Graded
open Module
universe uk ua um ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul 𝓐 𝓜]
  {ι : Type ui} [Fintype ι] (b : Basis ι A M) (d : ι → ℤ)
  (hb : ∀ i, b i ∈ 𝓜 (d i))
noncomputable section

include hb in
 theorem homogeneous_basis_repr (n : ℤ) (v : M) (hv : v ∈ 𝓜 n) (i : ι) :
    b.repr v i ∈ 𝓐 (n-d i) := by
  let _ : DirectSum.Decomposition (shiftedPiece 𝓐 d) :=
    (shifted_isInternal 𝓐 d).chooseDecomposition
  have hg : ∀ n f, f ∈ shiftedPiece 𝓐 d n → b.equivFun.symm f ∈ 𝓜 (n+0) := by
    intro n f hf
    rw [add_zero,b.equivFun_symm_apply]
    apply Submodule.sum_mem
    intro j _
    simpa only [vadd_eq_add,sub_add_cancel] using SetLike.GradedSMul.smul_mem (hf j) (hb j)
  have h := equiv_inverse_homogeneous (shiftedPiece 𝓐 d) 𝓜 b.equivFun.symm 0 hg n v hv
  rw [sub_zero] at h
  exact h i

include hb in
 theorem dualBasis_homogeneous [DecidableEq ι] (i : ι) (n : ℤ) (v : M) (hv : v ∈ 𝓜 n) :
    b.dualBasis i v ∈ 𝓐 (n+(-d i)) := by
  simpa only [Basis.coe_dualBasis,Basis.coord_apply,← sub_eq_add_neg] using
    homogeneous_basis_repr 𝓐 𝓜 b d hb n v hv i

end
end KLInvariance.Graded

end


section

/-! Genuine polynomial reflection from a homogeneous perfect duality. The
nonnegative lattice supplies a weak degree bound, not the strict KL bound. -/
namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  (M N : ModuleData.{uk,max uk us,um} (polynomialGrading k σ))
noncomputable section

omit [Finite σ] in
 theorem degree_le_of_dual_equiv
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l))
    (c : NonnegativeBasis (σ := σ) M.piece) (i : c.index) : c.degree i ≤ l := by
  classical
  have h := he (-(c.degree i : ℤ)) (c.basis.dualBasis i)
    (dualBasis_homogeneous (polynomialGrading k σ) M.piece c.basis
      (fun i => (c.degree i : ℤ)) c.homogeneous i)
  by_contra hn
  have hn' : -(c.degree i : ℤ)+(l:ℤ)<0 := by omega
  rw [N.nonneg _ hn',Submodule.mem_bot] at h
  have hz := e.injective (show e (c.basis.dualBasis i)=e 0 from
    h.trans (map_zero e).symm)
  exact c.basis.dualBasis.ne_zero i hz

 def reflectedBasis
    (e : Dual (MvPolynomial σ k) M ≃ₗ[MvPolynomial σ k] N) (l : ℕ)
    (he : ∀ r lam, (∀ j (v : M), v∈M.piece j →
      lam v∈polynomialGrading k σ (j+r)) → e lam∈N.piece (r+l))
    (c : NonnegativeBasis (σ := σ) M.piece) : NonnegativeBasis (σ := σ) N.piece := by
  classical
  exact {
    index := c.index
    finite := c.finite
    basis := c.basis.dualBasis.map e
    degree := fun i => l-c.degree i
    homogeneous := fun i => by
      have hi := M.degree_le_of_dual_equiv N e l he c i
      have h := he (-(c.degree i : ℤ)) (c.basis.dualBasis i)
        (dualBasis_homogeneous (polynomialGrading k σ) M.piece c.basis
          (fun i => (c.degree i : ℤ)) c.homogeneous i)
      change e (c.basis.dualBasis i) ∈ N.piece ((l-c.degree i : ℕ):ℤ)
      have hd : ((l-c.degree i : ℕ):ℤ)=-(c.degree i : ℤ)+(l:ℤ) := by omega
      rw [hd]
      exact h }

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.Hilbert
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
  (a : A) (d : ℤ) (ha : a ∈ 𝓐 d)

 def scalarDegreeMap (n : ℤ) : 𝓜 (n-d) →ₗ[k]
    subPiece 𝓜 (LinearMap.range (LinearMap.lsmul A M a)) n :=
  { toFun := fun m => ⟨⟨a • m.val,⟨m.val,rfl⟩⟩,by
      change a • m.val ∈ 𝓜 n
      simpa using SetLike.GradedSMul.smul_mem ha m.property⟩
    map_add' := by intros; ext; exact smul_add _ _ _
    map_smul' := by intros; ext; exact smul_comm _ _ _ }

 theorem scalarDegreeMap_surjective (n : ℤ) :
    Function.Surjective (scalarDegreeMap 𝓐 𝓜 a d ha n) := by
  rintro ⟨⟨m,v,hv⟩,hm⟩
  refine ⟨DirectSum.decompose 𝓜 v (n-d), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change a • component 𝓜 (n-d) v = m
  rw [← component_homogeneous_smul 𝓐 𝓜 d a ha n v]
  change (DirectSum.decompose 𝓜 (a • v) n : M) = m
  change a • v = m at hv
  rw [hv]
  exact DirectSum.decompose_of_mem_same 𝓜 hm

omit [DirectSum.Decomposition 𝓜] in
 theorem scalarDegreeMap_injective (hinj : Function.Injective (fun m : M => a • m)) (n : ℤ) :
    Function.Injective (scalarDegreeMap 𝓐 𝓜 a d ha n) := by
  intro v w h
  apply Subtype.ext
  apply hinj
  exact congrArg (fun t => t.val.val) h

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


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section

local instance finiteInterval : Fintype (Interval cs 1 b) := by
  let := interval_finite cs 1 b
  exact Fintype.ofFinite _

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.Graded.ModuleData
open Polynomial Module
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
noncomputable section

 def unitPolynomialBasis : NonnegativeBasis (σ := σ)
    (unit.{uk,max uk us,um} (polynomialGrading_negative k σ)).piece where
  index := PUnit.{max uk us um + 1}
  finite := inferInstance
  basis := Pi.basisFun (MvPolynomial σ k) _
  degree _ := 0
  homogeneous i := by
    intro j
    change (Pi.basisFun (MvPolynomial σ k) _ i) j ∈ polynomialGrading k σ (0-0)
    cases i
    cases j
    simpa using SetLike.one_mem_graded (polynomialGrading k σ)

end
end KLInvariance.Graded.ModuleData

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
attribute [local instance] OAI.KLInvariance.BruhatGraph.instDecidable_solutions_4
local instance lowerConvInterval (c : W) : Fintype (Interval cs 1 c) := by
  let := interval_finite cs 1 c
  exact Fintype.ofFinite _

end
end KLInvariance.BruhatGraph

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

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

theorem slope_injective : Function.Injective O.slope := O.generic

end RatioOrder

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

/-! Algebra and finite ordered-list bookkeeping for wall crossings. -/
namespace KLInvariance.SchedulePaths
universe u v w
variable {E : Type u} {A : Type v} {Λ : Type w} [LinearOrder A] [LinearOrder Λ]
noncomputable section

attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidable_solutions_4
attribute [local instance] OAI.KLInvariance.SchedulePaths.instDecidableEq_solutions
def blockValues (F : Finset E) (primary : E → A) : List A :=
  (F.image primary).sort (fun a b => b ≤ a)

end
end KLInvariance.SchedulePaths

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

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem wordProd_alt_odd (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) :
    cs.wordProd (alt i (2*n+1)) = (cs.simple i * cs.simple (!i)) ^ n * cs.simple i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)+1 = (2*n+1)+2 by omega, alt_add_two]
    simp only [cs.wordProd_cons, ih, pow_succ']
    group

 theorem indexWord_odd (cs : CoxeterSystem M W) (n : ℤ) :
    indexWord cs (2*n+1) = rotation cs ^ n * cs.simple false := by
  simp only [indexWord, show (2*n+1)%2 = 1 by omega, show (1:ℤ) ≠ 0 by omega, ite_false, if_false,
    show (2*n+1)/2 = n by omega]

 theorem indexWord_nat (cs : CoxeterSystem M W) (n : ℕ) :
    indexWord cs n = cs.wordProd (alt false n) := by
  rcases Nat.even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rw [show k+k = 2*k by omega, Nat.cast_mul, Nat.cast_ofNat, indexWord_even,
      wordProd_alt_even]
    simp only [rotation, Bool.not_false, zpow_natCast]
  · rw [Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, indexWord_odd, wordProd_alt_odd]
    simp only [rotation, Bool.not_false, zpow_natCast]

 theorem indexWord_neg_nat (cs : CoxeterSystem M W) (n : ℕ) :
    indexWord cs (-(n:ℤ)) = cs.wordProd (alt true n) := by
  have hr : cs.simple true * cs.simple false = (rotation cs)⁻¹ := by
    simp only [rotation, mul_inv_rev, cs.inv_simple]
  rcases Nat.even_or_odd n with ⟨k,rfl⟩ | ⟨k,rfl⟩
  · rw [show k+k = 2*k by omega, Nat.cast_mul, Nat.cast_ofNat,
      show -(2*(k:ℤ)) = 2*(-k) by ring, indexWord_even, wordProd_alt_even]
    simp only [Bool.not_true, hr, zpow_neg, zpow_natCast, inv_pow]
  · rw [Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one,
      show -(2*(k:ℤ)+1) = 2*(-(k:ℤ)-1)+1 by ring, indexWord_odd,
      wordProd_alt_odd]
    rw [show -(k:ℤ)-1 = -(k:ℤ)+(-1) by ring, zpow_add]
    simp only [zpow_neg, zpow_natCast, zpow_one, Bool.not_true, hr, inv_pow]
    simp only [rotation, mul_inv_rev, cs.inv_simple]
    simp only [mul_assoc, cs.simple_mul_simple_self, mul_one]

end
end KLInvariance.Dihedral

end


section

/-! Polynomial interpolation on an actual dihedral reflection subgroup.
The ambient realization, including all fixed directions and degenerate root
planes, is retained; no character theorem is assumed. -/
namespace KLInvariance.Dihedral
open Module TitsSpace
universe u v w us
variable {H : Type w} [Group H] {N : CoxeterMatrix Bool} (ds : CoxeterSystem N H)
  {I : Type u} [Fintype I] {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (φ : H →* W)
  (hφ : ∀ t, ds.IsReflection t → cs.IsReflection (φ t))
  {σ : Type us} (basis : Basis σ ℝ (Extended M))
noncomputable section

 theorem reflection_of_parity {x y : H} (hp : ds.length x % 2 ≠ ds.length y % 2) :
    ds.IsReflection (x*y⁻¹) := by
  rw [reflection_iff_odd,Nat.odd_iff]
  have h := ds.length_mul_mod_two x y⁻¹
  rw [ds.length_inv] at h
  omega

 def oppositeExternal (x c : H) : Finset H := by
  classical
  exact (externalLower ds x c).filter (fun z => ds.length z % 2 ≠ ds.length x % 2)

 def sameExternal (x c : H) : Finset H := by
  classical
  exact (externalLower ds x c).filter (fun z => ds.length z % 2 = ds.length x % 2)

 theorem oppositeExternal_reflection {x c y : H} (hy : y ∈ oppositeExternal ds x c) :
    ds.IsReflection (y*x⁻¹) := by
  classical
  exact reflection_of_parity ds (Finset.mem_filter.mp hy).2

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 theorem map_not_alt (i : Bool) (n : ℕ) : (alt i n).map Bool.not = alt (!i) n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => rw [alt_succ,List.map_cons,ih,alt_succ]

 theorem swap_alt (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) :
    swap cs (cs.wordProd (alt i n)) = cs.wordProd (alt (!i) n) := by
  rw [swap_wordProd,map_not_alt]

end
end KLInvariance.Dihedral

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
local instance instDecidable_solutions_6 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.BruhatGraph

end


section

/-! Actual transported numerical R-tilde matrix and its genuine KL reciprocal
vector. No sheaf or desired invariance conclusion is assumed. -/

namespace KLInvariance.BruhatGraph
open TitsSpace SchedulePaths
universe u v u' v'
variable {I : Type u} {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section
local instance instDecidable_solutions_7 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Invariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Genuine KL invariance, finite-parabolic transport and unrestricted finite interval models; the main theorem for two arbitrary Coxeter systems in four independent universes.
-/


section

/-! The finite-rank reduction of the exact main target.  The model's interval
and genuine KL polynomial are identified with those of the unrestricted
ambient Coxeter system, not with an order-theoretically defined invariant. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W) (u b : W)
noncomputable section

structure FiniteIntervalModel where
  indices : Set I
  finite : indices.Finite
  lower : (StandardParabolic.matrix (M := M) indices).Group
  upper : (StandardParabolic.matrix (M := M) indices).Group
  lower_eq : StandardParabolic.inclusion cs indices lower = u
  upper_eq : StandardParabolic.inclusion cs indices upper = b

end
end KLInvariance

end


end OAI
end


