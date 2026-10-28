-- Prove2me | Definitions.Def_OAIQ031A031
-- name    : OAIQ031A031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:59:01.74663+00:00
-- url     : https://prove2.me/theorems/efecc2d6-f1e7-4b8f-9b02-ef1282f18dc2
-- title:
--   Definitions bundle OAIQ031A031 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 12 definitions, 3 instances and 13 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.freeEquiv`, `OAI.ArExplicit.LinearHomology.Homology`, `OAI.ArExplicit.LinearHomology.boundaries`, `OAI.ArExplicit.LinearHomology.dualCyclesToDualHomology`, `OAI.ArExplicit.LinearHomology.dualHomologyEquiv`, `OAI.ArExplicit.Resolution.vertexE`, `OAI.ArExplicit.ResolutionHomology.extEquiv`, `OAI.ArExplicit.completeCokernelResolution`, `OAI.ArExplicit.completeExtCocycleMap`, `OAI.ArExplicit.completeExtCyclesMap`, `OAI.ArExplicit.completeExtResolution`, `OAI.ArExplicit.nonnegativeTailAugmentation`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_SimpleModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/SimpleModule.lean), [`AuslanderReiten_Complete_CompleteResolutionTail`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteResolutionTail.lean), [`AuslanderReiten_Complete_CompleteShift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteShift.lean), [`AuslanderReiten_Duality_LinearHomologyDuality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/LinearHomologyDuality.lean), [`AuslanderReiten_Resolutions_ResolutionHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionHomology.lean), [`AuslanderReiten_Stable_StableExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableExt.lean), [`AuslanderReiten_Stable_StableExtEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableExtEquiv.lean), [`AuslanderReiten_Tensor_ExternalTensorComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorComplex.lean), [`AuslanderReiten_Tensor_ExternalTensorProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorProjective.lean), [`AuslanderReiten_Tensor_ExternalTensorScalar`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorScalar.lean), [`AuslanderReiten_Tensor_ExternalTensorSingle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorSingle.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A003`, `OAIQ031A004`, `OAIQ031A005`, `OAIQ031A006` and `OAIQ031A007` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A047`, `OAIQ031A048`, `OAIQ031A049`, `OAIQ031A051`, `OAIQ031A052`, `OAIQ031A053`, `OAIQ031A057` and `OAIQ031A059`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A004
import Definitions.Def_OAIQ031A005
import Definitions.Def_OAIQ031A006
import Definitions.Def_OAIQ031A007

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteResolutionTail
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u
variable {R : Type u} [Ring R]

def nonnegativeTailAugmentation (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    nonnegativeTail P ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj
      (ModuleCat.of R (CompleteCokernel P)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (LinearMap.range (P.d 1 0).hom).mkQ, by
      rw [nonnegativeTail_d]
      apply ModuleCat.hom_ext
      exact LinearMap.range_mkQ_comp _⟩

@[simp]
theorem nonnegativeTailAugmentation_f_zero (P : ChainComplex (ModuleCat.{u} R) ℤ) :
    (nonnegativeTailAugmentation P).f 0 =
      ModuleCat.ofHom (LinearMap.range (P.d 1 0).hom).mkQ := by
  apply ChainComplex.toSingle₀Equiv_symm_apply_f_zero

theorem nonnegativeTail_exactAt (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hex : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom) (n : ℕ) :
    (nonnegativeTail P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range ((nonnegativeTail P).d (n + 1 + 1) (n + 1)).hom =
    LinearMap.ker ((nonnegativeTail P).d (n + 1) n).hom
  rw [nonnegativeTail_d, nonnegativeTail_d]
  have aux (i j l : ℤ) (hi : i = j + 1) (hl : l = j - 1) :
      LinearMap.range (P.d i j).hom = LinearMap.ker (P.d j l).hom := by
    subst i
    subst l
    exact hex j
  exact aux _ _ _ (by omega) (by omega)

def completeCokernelResolution (P : ChainComplex (ModuleCat.{u} R) ℤ)
    (hproj : ∀ n : ℤ, Module.Projective R (P.X n))
    (hex : ∀ n : ℤ, LinearMap.range (P.d (n + 1) n).hom =
      LinearMap.ker (P.d n (n - 1)).hom) :
    ProjectiveResolution (ModuleCat.of R (CompleteCokernel P)) where
  complex := nonnegativeTail P
  projective n := by
    let := hproj (n : ℤ)
    exact (P.X (n : ℤ)).projective_of_categoryTheory_projective
  π := nonnegativeTailAugmentation P
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          change LinearMap.range ((nonnegativeTail P).d 1 0).hom =
            LinearMap.ker ((nonnegativeTailAugmentation P).f 0).hom
          rw [nonnegativeTail_d, nonnegativeTailAugmentation_f_zero]
          exact (Submodule.ker_mkQ _).symm
        · rw [ModuleCat.epi_iff_surjective]
          change Function.Surjective (LinearMap.range (P.d 1 0).hom).mkQ
          exact Submodule.mkQ_surjective _
      · change (nonnegativeTail P).d 0 0 = 0
        exact (nonnegativeTail P).shape _ _ (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact nonnegativeTail_exactAt P hex n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_SimpleModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

def vertexE : E q := ⟨basisVector q e, by
  change basisVector q e * basisVector q e = basisVector q e
  simpa [multiplicationTable] using basis_mul q e e⟩

theorem e_smul_vertexE : basisVector q e • vertexE q = vertexE q := by
  apply Subtype.ext
  exact (vertexE q).property

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShift
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace ExactProjectiveCochain

open CompleteComparison

theorem shift {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveCochain K) (n : ℤ) : ExactProjectiveCochain (K⟦n⟧) where
  finite i := hK.finite (i + n)
  projective i := hK.projective (i + n)
  exactAt i := ShortComplex.exact_of_iso
    ((CochainComplex.shiftShortComplexFunctorIso (ModuleCat.{u} R) n i (n + i) rfl).app K).symm
    (hK.exactAt (n + i))

end ExactProjectiveCochain

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_LinearHomologyDuality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.LinearHomology

universe u

variable {k : Type u} [Field k]
variable {U V W : Type u}
variable [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
variable [AddCommGroup W] [Module k W]

def boundaries (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :
    Submodule k (LinearMap.ker g) := LinearMap.range (cycleMap f g h)

abbrev Homology (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :=
  LinearMap.ker g ⧸ boundaries f g h

def dualCyclesToDualHomology (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :
    LinearMap.ker f.dualMap →ₗ[k] Module.Dual k (Homology f g h) where
  toFun φ := (boundaries f g h).liftQ (φ.val.comp (LinearMap.ker g).subtype) (by
    rintro _ ⟨x, rfl⟩
    exact DFunLike.congr_fun φ.property x)
  map_add' φ ψ := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    rfl
  map_smul' c φ := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    rfl

@[simp]
theorem dualCyclesToDualHomology_mk (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0)
    (φ : LinearMap.ker f.dualMap) (x : LinearMap.ker g) :
    dualCyclesToDualHomology f g h φ ((boundaries f g h).mkQ x) = φ.val x.val := rfl

theorem dualCyclesToDualHomology_surjective (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (h : g.comp f = 0) : Function.Surjective (dualCyclesToDualHomology f g h) := by
  intro l
  obtain ⟨φ, hφ⟩ := (l.comp (boundaries f g h).mkQ).exists_extend
  have hp : φ ∈ LinearMap.ker f.dualMap := by
    apply LinearMap.ext
    intro x
    have hx := DFunLike.congr_fun hφ (cycleMap f g h x)
    change φ (f x) = 0
    change φ (f x) = l ((boundaries f g h).mkQ (cycleMap f g h x)) at hx
    rw [show (boundaries f g h).mkQ (cycleMap f g h x) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero] at hx
    exact hx
  refine ⟨⟨φ, hp⟩, ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
  exact DFunLike.congr_fun hφ x

theorem dualCyclesToDualHomology_kernel (f : U →ₗ[k] V) (g : V →ₗ[k] W)
    (h : g.comp f = 0) :
    LinearMap.ker (dualCyclesToDualHomology f g h) =
      boundaries g.dualMap f.dualMap (dual_comp f g h) := by
  ext φ
  constructor
  · intro hφ
    have ha : φ.val ∈ (LinearMap.ker g).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      exact DFunLike.congr_fun hφ ((boundaries f g h).mkQ ⟨x, hx⟩)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at ha
    obtain ⟨ψ, hψ⟩ := ha
    exact ⟨ψ, Subtype.ext hψ⟩
  · rintro ⟨ψ, rfl⟩
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (boundaries f g h) z
    change ψ (g x.val) = 0
    rw [x.property, map_zero]

noncomputable def dualHomologyEquiv (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0) :
    Module.Dual k (Homology f g h) ≃ₗ[k]
      Homology g.dualMap f.dualMap (dual_comp f g h) :=
  ((Submodule.quotEquivOfEq _ _ (dualCyclesToDualHomology_kernel f g h).symm).trans
    ((dualCyclesToDualHomology f g h).quotKerEquivOfSurjective
      (dualCyclesToDualHomology_surjective f g h))).symm

@[simp]
theorem dualHomologyEquiv_symm_mk (f : U →ₗ[k] V) (g : V →ₗ[k] W) (h : g.comp f = 0)
    (φ : LinearMap.ker f.dualMap) :
    (dualHomologyEquiv f g h).symm
      (Submodule.Quotient.mk φ) =
      dualCyclesToDualHomology f g h φ := by
  simp only [dualHomologyEquiv, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

end ArExplicit.LinearHomology

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionHomology
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit.ResolutionHomology
universe u v w
variable {k : Type v} [Field k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
variable {X Y : C} (P : ProjectiveResolution X)

variable [HasExt.{w} C]

theorem cyclesToExt_kernel (n : ℕ) :
    LinearMap.ker (cyclesToExt (k := k) (Y := Y) P n) =
      LinearHomology.boundaries (differential P n) (differential P (n + 1)) (differential_comp P n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨f, hf⟩ := (P.extMk_eq_zero_iff x.val (n + 2) rfl x.property n rfl).mp hx
    exact ⟨f, Subtype.ext hf⟩
  · rintro ⟨f, hfx⟩
    apply (P.extMk_eq_zero_iff x.val (n + 2) rfl x.property n rfl).mpr
    exact ⟨f, congrArg Subtype.val hfx⟩

def extEquiv (n : ℕ) :
    LinearHomology.Homology (differential (k := k) (Y := Y) P n)
      (differential P (n + 1)) (differential_comp P n) ≃ₗ[k] Ext X Y (n + 1) :=
  (Submodule.quotEquivOfEq _ _ (cyclesToExt_kernel P n).symm).trans
    ((cyclesToExt P n).quotKerEquivOfSurjective (cyclesToExt_surjective P n))

end ArExplicit.ResolutionHomology

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison

universe u

variable {R : Type u} [Ring R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ}
variable {N : Type u} [AddCommGroup N] [Module R N]

def completeExtCocycleMap (n : ℤ) (f : P.X n →ₗ[R] N)
    (hf : f.comp (P.d (n + 1) n).hom = 0) : Cokernel P n →ₗ[R] N :=
  (LinearMap.range (P.d (n + 1) n).hom).liftQ f (LinearMap.range_le_ker_iff.mpr hf)

@[simp] theorem completeExtCocycleMap_mk (n : ℤ) (f : P.X n →ₗ[R] N)
    (hf : f.comp (P.d (n + 1) n).hom = 0) (x : P.X n) :
    completeExtCocycleMap n f hf ((LinearMap.range (P.d (n + 1) n).hom).mkQ x) = f x := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableExtEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit
open CompleteComparison
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P : ChainComplex (ModuleCat.{u} R) ℤ} (hP : TotallyAcyclicComplex P)
variable (N : ModuleCat.{u} R)

abbrev completeExtResolution := completeCokernelResolution P hP.projective hP.exactAt

theorem completeExtCycle_closed (n : ℕ)
    (f : LinearMap.ker (ResolutionHomology.differential (k := k) (Y := N)
      (completeExtResolution hP) (n+1))) :
    f.val.hom.comp (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom = 0 := by
  have hf : (nonnegativeTail P).d (n+2) (n+1) ≫ f.val = 0 := f.property
  rw [nonnegativeTail_d] at hf
  exact closed_of_indices N (by omega : ((n+2 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ)+1)
    f.val.hom (congrArg ModuleCat.Hom.hom hf)

def completeExtCyclesMap (n : ℕ) :
    LinearMap.ker (ResolutionHomology.differential (k := k) (Y := N)
      (completeExtResolution hP) (n+1)) →ₗ[k]
        (Cokernel P ((n+1 : ℕ) : ℤ) →ₗ[R] N) where
  toFun f := completeExtCocycleMap ((n+1 : ℕ) : ℤ) f.val.hom (completeExtCycle_closed hP N n f)
  map_add' f g := by
    apply LinearMap.ext
    intro z
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range
      (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
    rfl
  map_smul' a f := by
    apply LinearMap.ext
    intro z
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range
      (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
    rfl

theorem completeExtCyclesMap_surjective (n : ℕ) :
    Function.Surjective (completeExtCyclesMap (k := k) hP N n) := by
  intro f
  let π := (LinearMap.range (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom).mkQ
  let g : (completeExtResolution hP).complex.X (n+1) ⟶ N := ModuleCat.ofHom (f.comp π)
  have hg : ResolutionHomology.differential (k := k) (completeExtResolution hP) (n+1) g = 0 := by
    change (nonnegativeTail P).d (n+2) (n+1) ≫ g = 0
    rw [nonnegativeTail_d]
    apply ModuleCat.hom_ext
    change (f.comp π).comp (P.d ((n+2 : ℕ) : ℤ) ((n+1 : ℕ) : ℤ)).hom = 0
    have hi : ((n+2 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ)+1 := by omega
    rw [hi, LinearMap.comp_assoc, LinearMap.range_mkQ_comp, LinearMap.comp_zero]
  refine ⟨⟨g,hg⟩, ?_⟩
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (LinearMap.range
    (P.d (((n+1 : ℕ) : ℤ)+1) ((n+1 : ℕ) : ℤ)).hom) z
  rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.ExternalTensor

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def freeEquiv (n m : ℕ) :
    moduleObject k A B (Fin n → A) (Fin m → B) ≃ₗ[A ⊗[k] B]
      (Fin n → Fin m → A ⊗[k] B) where
  __ := (freeCoordinates k A B n m).toAddEquiv
  map_smul' a z := by
    let w : (Fin n → A) ⊗[k] (Fin m → B) := z
    change freeCoordinates k A B n m (representation k A B _ _ a w) =
      a • freeCoordinates k A B n m w
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, add_smul, ha, hb]
    | tmul a b =>
      induction w using OAI.tensorInductionOn with
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]
      | tmul x y =>
        funext i j
        change freeCoordinates k A B n m ((a • x) ⊗ₜ[k] (b • y)) i j =
          (a ⊗ₜ[k] b) * freeCoordinates k A B n m (x ⊗ₜ[k] y) i j
        simp only [freeCoordinates_tmul, Pi.smul_apply, smul_eq_mul,
          Algebra.TensorProduct.tmul_mul_tmul]

instance freeFree (n m : ℕ) :
    Module.Free (A ⊗[k] B) (moduleObject k A B (Fin n → A) (Fin m → B)) :=
  Module.Free.of_equiv (freeEquiv k A B n m).symm

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.ExternalTensor

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

instance instFintypeDiagonal (n : ℕ) : Fintype (Diagonal n) :=
  Fintype.ofFinset (Finset.HasAntidiagonal.antidiagonal n) (by intro p; exact Finset.HasAntidiagonal.mem_antidiagonal)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorScalar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
variable [Module A M] [Module B N] [mM : Module k M] [mN : Module k N]
variable [IsScalarTower k A M] [IsScalarTower k B N]

theorem canonicalScalar_eq :
    moduleCatBaseModule (k := k) (R := A) (ModuleCat.of A M) = mM := by
  apply Module.ext'
  intro a x
  exact IsScalarTower.algebraMap_smul A a x

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorSingle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

instance diagonalZeroUnique : Unique (Diagonal 0) where
  default := ⟨(0,0),rfl⟩
  uniq p := by
    apply Subtype.ext
    apply Prod.ext <;> have h := p.property <;> dsimp at * <;> omega

end ArExplicit.ExternalTensor

end

end OAI
end


