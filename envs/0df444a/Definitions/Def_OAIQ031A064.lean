-- Prove2me | Definitions.Def_OAIQ031A064
-- name    : OAIQ031A064
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:12:25.134256+00:00
-- url     : https://prove2.me/theorems/9a90b6d6-0ea4-4cbb-a01d-1a38d5580261
-- title:
--   Definitions bundle OAIQ031A064 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 14 definitions and 16 theorems. The definitions and types are `OAI.ArExplicit.A.endScalar`, `OAI.ArExplicit.A.simpleEndEquiv`, `OAI.ArExplicit.ExternalTensor.homOutTermEquiv`, `OAI.ArExplicit.ExternalTensor.scalarHorizontal`, `OAI.ArExplicit.ExternalTensor.singleTotal`, `OAI.ArExplicit.StableHomology.cyclesToStable`, `OAI.ArExplicit.StableHomology.homologyStableEquiv`, `OAI.ArExplicit.StableHomology.mapToCycle`, `OAI.ArExplicit.StableTargetHomology.cyclesToStable`, `OAI.ArExplicit.StableTargetHomology.homologyStableEquiv`, `OAI.ArExplicit.StableTargetHomology.mapToCycle`, `OAI.ArExplicit.completeExtCyclesStable`, `OAI.ArExplicit.completeExtHomologyStableEquiv`, `OAI.ArExplicit.positiveExtStableEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Stable_StableExt`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableExt.lean), [`AuslanderReiten_Stable_StableExtEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableExtEquiv.lean), [`AuslanderReiten_Stable_StableHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableHomology.lean), [`AuslanderReiten_Stable_StableTargetHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableTargetHomology.lean), [`AuslanderReiten_Stable_TensorStableEnd`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/TensorStableEnd.lean), [`AuslanderReiten_Tensor_ExternalTensorForget`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorForget.lean), [`AuslanderReiten_Tensor_ExternalTensorHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHom.lean), [`AuslanderReiten_Tensor_ExternalTensorHomComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorHomComplex.lean), [`AuslanderReiten_Tensor_ExternalTensorSingle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorSingle.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A044`, `OAIQ031A047` and `OAIQ031A048` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A079`, `OAIQ031A080`, `OAIQ031A082`, `OAIQ031A083` and `OAIQ031A090`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A044
import Definitions.Def_OAIQ031A047
import Definitions.Def_OAIQ031A048

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableExt
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem completeExtCocycleMap_stable_zero_iff (hP : TotallyAcyclicComplex P)
    (n : ℤ) (f : P.X n →ₗ[R] N) (hf : f.comp (P.d (n + 1) n).hom = 0) :
    StableHom.classOf R _ N (completeExtCocycleMap n f hf) = 0 ↔
      ∃ g : P.X (n - 1) →ₗ[R] N, g.comp (P.d n (n - 1)).hom = f := by
  rw [StableHom.classOf_eq_zero_iff_projective]
  constructor
  · rintro ⟨Q, hQ, hRQ, hproj, hfin, i, p, hip⟩
    let π := (LinearMap.range (P.d (n + 1) n).hom).mkQ
    have hi : (i.comp π).comp (P.d (n + 1) n).hom = 0 := by
      rw [LinearMap.comp_assoc, LinearMap.range_mkQ_comp, LinearMap.comp_zero]
    obtain ⟨g, hg⟩ := (hP.dualExact n).projective (i.comp π) hi
    refine ⟨p.comp g, ?_⟩
    rw [LinearMap.comp_assoc, hg, ← LinearMap.comp_assoc, hip]
    rfl
  · rintro ⟨g, hg⟩
    let := hP.finite (n - 1)
    let := hP.projective (n - 1)
    let d : Cokernel P n →ₗ[R] P.X (n - 1) :=
      completeExtCocycleMap n (P.d n (n - 1)).hom (differential_comp P _ _ _)
    refine ⟨P.X (n - 1), inferInstance, inferInstance, inferInstance, inferInstance, d, g, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
    exact DFunLike.congr_fun hg x

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableExtEquiv
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def completeExtCyclesStable (n : ℕ) :=
  (StableHom.classOfLinear k).comp (completeExtCyclesMap (k := k) hP N n)

theorem completeExtCyclesStable_surjective (n : ℕ) :
    Function.Surjective (completeExtCyclesStable (k := k) hP N n) :=
  StableHom.classOf_surjective.comp (completeExtCyclesMap_surjective hP N n)

theorem completeExtCyclesStable_kernel (n : ℕ) :
    LinearMap.ker (completeExtCyclesStable (k := k) hP N n) =
      LinearHomology.boundaries
        (ResolutionHomology.differential (k := k) (Y := N) (completeExtResolution hP) n)
        (ResolutionHomology.differential (completeExtResolution hP) (n+1))
        (ResolutionHomology.differential_comp (completeExtResolution hP) n) := by
  ext x
  change StableHom.classOf R _ N (completeExtCocycleMap ((n+1 : ℕ) : ℤ) x.val.hom
    (completeExtCycle_closed hP N n x)) = 0 ↔ _
  refine (completeExtCocycleMap_stable_zero_iff hP ((n+1 : ℕ) : ℤ)
    (show P.X ((n+1 : ℕ) : ℤ) →ₗ[R] N from x.val.hom) (completeExtCycle_closed hP N n x)).trans ?_
  have hprev : ((n+1 : ℕ) : ℤ)-1 = (n : ℤ) := by omega
  rw [hprev]
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨ModuleCat.ofHom g, Subtype.ext ?_⟩
    apply ModuleCat.hom_ext
    change ((nonnegativeTail P).d (n+1) n ≫ ModuleCat.ofHom g).hom = x.val.hom
    rw [nonnegativeTail_d]
    exact hg
  · rintro ⟨g,hg⟩
    refine ⟨g.hom, ?_⟩
    have hh := congrArg (fun y => y.val.hom) hg
    change ((nonnegativeTail P).d (n+1) n ≫ g).hom = x.val.hom at hh
    rw [nonnegativeTail_d] at hh
    exact hh

def completeExtHomologyStableEquiv (n : ℕ) :
    LinearHomology.Homology
      (ResolutionHomology.differential (k := k) (Y := N) (completeExtResolution hP) n)
      (ResolutionHomology.differential (completeExtResolution hP) (n+1))
      (ResolutionHomology.differential_comp (completeExtResolution hP) n) ≃ₗ[k]
        StableHom R (Cokernel P ((n+1 : ℕ) : ℤ)) N :=
  (Submodule.quotEquivOfEq _ _ (completeExtCyclesStable_kernel hP N n).symm).trans
    ((completeExtCyclesStable hP N n).quotKerEquivOfSurjective
      (completeExtCyclesStable_surjective hP N n))

def positiveExtStableEquiv (n : ℕ) :
    Ext (ModuleCat.of R (Cokernel P 0)) N (n+1) ≃ₗ[k]
      StableHom R (Cokernel P ((n+1 : ℕ) : ℤ)) N :=
  (ResolutionHomology.extEquiv (k := k) (Y := N) (completeExtResolution hP) n).symm.trans
    (completeExtHomologyStableEquiv hP N n)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableHomology
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.StableHomology

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P₁ P₀ Pminus N : Type u}
variable [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₀] [Module R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [AddCommGroup N] [Module R N]
variable [Module k N] [IsScalarTower k R N]

def cyclesToStable (e : P₁ →ₗ[R] P₀) :
    LinearMap.ker (precomp (k := k) (N := N) e) →ₗ[k] StableHom R (Cokernel e) N where
  toFun z := StableHom.classOf R _ _ (cycleToMap e z)
  map_add' z w := by
    have he : cycleToMap e (z + w) = cycleToMap e z + cycleToMap e w := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
      rfl
    rw [he, map_add]
  map_smul' c z := by
    have he : cycleToMap e (c • z) = c • cycleToMap e z := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
      rfl
    rw [he, StableHom.classOf_smul]
    rfl

theorem cyclesToStable_surjective (e : P₁ →ₗ[R] P₀) :
    Function.Surjective (cyclesToStable (k := k) (N := N) e) := by
  intro x
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective x
  have hz : f.comp (LinearMap.range e).mkQ ∈ LinearMap.ker (precomp (k := k) e) := by
    ext y
    change f ((LinearMap.range e).mkQ (e y)) = 0
    rw [show (LinearMap.range e).mkQ (e y) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩, map_zero]
  refine ⟨⟨f.comp (LinearMap.range e).mkQ, hz⟩, ?_⟩
  apply congrArg (StableHom.classOf R (Cokernel e) N)
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
  rfl

theorem cyclesToStable_kernel [Module.Finite R Pminus] [Module.Projective R Pminus]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hd : HomExactAt e d) :
    LinearMap.ker (cyclesToStable (k := k) (N := N) e) =
      LinearHomology.boundaries (precomp d) (precomp e) (precomp_comp e d h) := by
  ext z
  constructor
  · intro hz
    change StableHom.classOf R (Cokernel e) N (cycleToMap e z) = 0 at hz
    rcases (StableHom.classOf_eq_zero_iff_projective (cycleToMap e z)).mp hz with
      ⟨T, hT, hRT, hpT, hfT, a, b, hab⟩
    have ha : (a.comp (LinearMap.range e).mkQ).comp e = 0 := by
      ext x
      change a ((LinearMap.range e).mkQ (e x)) = 0
      rw [show (LinearMap.range e).mkQ (e x) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero]
    obtain ⟨A, hA⟩ := hd.projective (a.comp (LinearMap.range e).mkQ) ha
    refine ⟨b.comp A, ?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change b (A (d x)) = z.val x
    rw [show A (d x) = a ((LinearMap.range e).mkQ x) from DFunLike.congr_fun hA x]
    exact DFunLike.congr_fun hab ((LinearMap.range e).mkQ x)
  · rintro ⟨b, rfl⟩
    apply (StableHom.classOf_eq_zero_iff_projective _).mpr
    have he : LinearMap.range e ≤ LinearMap.ker d := LinearMap.range_le_ker_iff.mpr h
    refine ⟨Pminus, inferInstance, inferInstance, inferInstance, inferInstance,
      (LinearMap.range e).liftQ d he, b, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
    rfl

noncomputable def homologyStableEquiv [Module.Finite R Pminus] [Module.Projective R Pminus]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hd : HomExactAt e d) :
    LinearHomology.Homology (precomp (k := k) (N := N) d) (precomp e) (precomp_comp e d h)
      ≃ₗ[k] StableHom R (Cokernel e) N :=
  (Submodule.quotEquivOfEq _ _ (cyclesToStable_kernel e d h hd).symm).trans
    ((cyclesToStable e).quotKerEquivOfSurjective (cyclesToStable_surjective e))

@[simp]
theorem homologyStableEquiv_mk [Module.Finite R Pminus] [Module.Projective R Pminus]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hd : HomExactAt e d) (z : LinearMap.ker (precomp (k := k) (N := N) e)) :
    homologyStableEquiv e d h hd
      ((LinearHomology.boundaries (precomp d) (precomp e) (precomp_comp e d h)).mkQ z) =
      cyclesToStable e z := rfl

def mapToCycle (e : P₁ →ₗ[R] P₀) (f : Cokernel e →ₗ[R] N) :
    LinearMap.ker (precomp (k := k) (N := N) e) :=
  ⟨f.comp (LinearMap.range e).mkQ, by
    ext x
    change f ((LinearMap.range e).mkQ (e x)) = 0
    rw [show (LinearMap.range e).mkQ (e x) = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩, map_zero]⟩

@[simp]
theorem cyclesToStable_mapToCycle (e : P₁ →ₗ[R] P₀) (f : Cokernel e →ₗ[R] N) :
    cyclesToStable e (mapToCycle (k := k) e f) = StableHom.classOf R _ _ f := by
  apply congrArg (StableHom.classOf R (Cokernel e) N)
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range e) x
  rfl

end ArExplicit.StableHomology

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableTargetHomology
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.StableTargetHomology

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable {P₁ P₀ Pminus N : Type u}
variable [AddCommGroup P₁] [Module R P₁] [Module k P₁] [IsScalarTower k R P₁]
variable [AddCommGroup P₀] [Module R P₀] [Module k P₀] [IsScalarTower k R P₀]
variable [AddCommGroup Pminus] [Module R Pminus] [Module k Pminus] [IsScalarTower k R Pminus]
variable [AddCommGroup N] [Module R N]

def cyclesToStable (d : P₀ →ₗ[R] Pminus) :
    LinearMap.ker (postcomp (k := k) (N := N) d) →ₗ[k] StableHom R N (LinearMap.ker d) where
  toFun z := StableHom.classOf R _ _ (cycleToMap d z)
  map_add' z w := by
    have he : cycleToMap d (z + w) = cycleToMap d z + cycleToMap d w := by ext; rfl
    rw [he, map_add]
  map_smul' c z := by
    have he : cycleToMap d (c • z) = c • cycleToMap d z := by ext; rfl
    rw [he, StableHom.classOf_smul]
    rfl

theorem cyclesToStable_surjective (d : P₀ →ₗ[R] Pminus) :
    Function.Surjective (cyclesToStable (k := k) (N := N) d) := by
  intro x
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective x
  have hz : (LinearMap.ker d).subtype.comp f ∈ LinearMap.ker (postcomp (k := k) d) := by
    ext y
    exact (f y).property
  refine ⟨⟨(LinearMap.ker d).subtype.comp f, hz⟩, ?_⟩
  apply congrArg (StableHom.classOf R N (LinearMap.ker d))
  ext
  rfl

theorem cyclesToStable_kernel [Module.Finite R P₁] [Module.Projective R P₁]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hex : LinearMap.range e = LinearMap.ker d) :
    LinearMap.ker (cyclesToStable (k := k) (N := N) d) =
      LinearHomology.boundaries (postcomp e) (postcomp d) (postcomp_comp e d h) := by
  ext z
  constructor
  · intro hz
    change StableHom.classOf R N (LinearMap.ker d) (cycleToMap d z) = 0 at hz
    rcases (StableHom.classOf_eq_zero_iff_projective (cycleToMap d z)).mp hz with
      ⟨T, hT, hRT, hpT, hfT, a, b, hab⟩
    have hb : d.comp ((LinearMap.ker d).subtype.comp b) = 0 := by
      ext x
      exact (b x).property
    obtain ⟨B, hB⟩ := lift_through_exact e d hex ((LinearMap.ker d).subtype.comp b) hb
    refine ⟨B.comp a, ?_⟩
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change e (B (a x)) = z.val x
    rw [show e (B (a x)) = (b (a x)).val from DFunLike.congr_fun hB (a x)]
    exact congrArg Subtype.val (DFunLike.congr_fun hab x)
  · rintro ⟨a, rfl⟩
    apply (StableHom.classOf_eq_zero_iff_projective _).mpr
    refine ⟨P₁, inferInstance, inferInstance, inferInstance, inferInstance,
      a, e.codRestrict (LinearMap.ker d) (fun x => DFunLike.congr_fun h x), ?_⟩
    ext
    rfl

noncomputable def homologyStableEquiv [Module.Finite R P₁] [Module.Projective R P₁]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hex : LinearMap.range e = LinearMap.ker d) :
    LinearHomology.Homology (postcomp (k := k) (N := N) e) (postcomp d) (postcomp_comp e d h)
      ≃ₗ[k] StableHom R N (LinearMap.ker d) :=
  (Submodule.quotEquivOfEq _ _ (cyclesToStable_kernel e d h hex).symm).trans
    ((cyclesToStable d).quotKerEquivOfSurjective (cyclesToStable_surjective d))

@[simp]
theorem homologyStableEquiv_mk [Module.Finite R P₁] [Module.Projective R P₁]
    (e : P₁ →ₗ[R] P₀) (d : P₀ →ₗ[R] Pminus) (h : d.comp e = 0)
    (hex : LinearMap.range e = LinearMap.ker d)
    (z : LinearMap.ker (postcomp (k := k) (N := N) d)) :
    homologyStableEquiv e d h hex
      ((LinearHomology.boundaries (postcomp e) (postcomp d) (postcomp_comp e d h)).mkQ z) =
      cyclesToStable d z := rfl

def mapToCycle (d : P₀ →ₗ[R] Pminus) (f : N →ₗ[R] LinearMap.ker d) :
    LinearMap.ker (postcomp (k := k) (N := N) d) :=
  ⟨(LinearMap.ker d).subtype.comp f, by ext x; exact (f x).property⟩

@[simp]
theorem cyclesToStable_mapToCycle (d : P₀ →ₗ[R] Pminus) (f : N →ₗ[R] LinearMap.ker d) :
    cyclesToStable d (mapToCycle (k := k) d f) = StableHom.classOf R _ _ f := by
  apply congrArg (StableHom.classOf R N (LinearMap.ker d))
  ext
  rfl

end ArExplicit.StableTargetHomology

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_TensorStableEnd
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.A
universe u
variable {k : Type u} [Field k] (q : k) (hq1 : 1 + q ≠ 0)

include hq1 in
theorem simple_scalar_generator (x : Simple q) :
    x = simpleCoordinate q x • simpleGenerator q := by
  apply simpleCoordinate_injective q hq1
  erw [(simpleCoordinate q).map_smul, simpleGenerator_coordinate]
  exact (mul_one _).symm

def endScalar : (Simple q →ₗ[A k q] Simple q) →ₗ[k] k where
  toFun f := simpleCoordinate q (f (simpleGenerator q))
  map_add' left right :=
    (simpleCoordinate q).map_add (left (simpleGenerator q)) (right (simpleGenerator q))
  map_smul' scalar endomorphism :=
    (simpleCoordinate q).map_smul scalar (endomorphism (simpleGenerator q))

include hq1 in
theorem end_eq_scalar_id (f : Simple q →ₗ[A k q] Simple q) :
    f = endScalar q f • LinearMap.id := by
  apply LinearMap.ext
  intro x
  change f x = endScalar q f • x
  calc
    f x = f (simpleCoordinate q x • simpleGenerator q) := congrArg f (simple_scalar_generator q hq1 x)
    _ = simpleCoordinate q x • f (simpleGenerator q) := (f.restrictScalars k).map_smul _ _
    _ = simpleCoordinate q x • (endScalar q f • simpleGenerator q) := by
      exact congrArg (fun z => simpleCoordinate q x • z)
        (simple_scalar_generator q hq1 (f (simpleGenerator q)))
    _ = endScalar q f • (simpleCoordinate q x • simpleGenerator q) := smul_comm _ _ _
    _ = endScalar q f • x := congrArg (fun z => endScalar q f • z) (simple_scalar_generator q hq1 x).symm

def simpleEndEquiv : (Simple q →ₗ[A k q] Simple q) ≃ₗ[k] k where
  __ := endScalar q
  invFun c := c • LinearMap.id
  left_inv f := (end_eq_scalar_id q hq1 f).symm
  right_inv c := by
    change simpleCoordinate q (c • simpleGenerator q) = c
    erw [(simpleCoordinate q).map_smul, simpleGenerator_coordinate]
    exact mul_one _

end ArExplicit.A

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorForget
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

abbrev scalarHorizontal (i j n : ℕ) :=
  mapBifunctor.d₁ (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i j n

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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
variable {M N U V : Type u}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup U] [AddCommGroup V]
variable [Module k M] [Module k N] [Module k U] [Module k V]
variable [Module A M] [Module B N] [Module A U] [Module B V]
variable [IsScalarTower k A M] [IsScalarTower k B N] [IsScalarTower k A U] [IsScalarTower k B V]

theorem homMap_bijective_free (n m : ℕ) :
    Function.Bijective (homMap k A B (M := Fin n → A) (N := Fin m → B) (U := U) (V := V)) := by
  let s : (((Fin n → A) →ₗ[A] U) ⊗[k] ((Fin m → B) →ₗ[B] V)) ≃ₗ[k]
      (Fin n × Fin m → U ⊗[k] V) :=
    (TensorProduct.congr (LinearEquiv.piRing A U (Fin n) k)
      (LinearEquiv.piRing B V (Fin m) k)).trans
      ((TensorProduct.piLeft k (Fin m → V) (fun _ : Fin n => U)).trans
        ((LinearEquiv.piCongrRight fun _ => TensorProduct.piRight k k U (fun _ : Fin m => V)).trans
          (LinearEquiv.curry k (U ⊗[k] V) (Fin n) (Fin m)).symm))
  let t := homFreeCoordinates k A B (U := U) (V := V) n m
  have heq (x) : t (homMap k A B x) = s x := by
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]; rfl
    | tmul f g =>
      funext ⟨i,j⟩
      change homMap k A B (f ⊗ₜ[k] g)
        ((freeFlatEquiv k A B n m).symm (Pi.single (i,j) 1)) = _
      rw [freeFlatEquiv_symm_single, homMap_tmul, map_tmul]
      rfl
  constructor
  · intro x y hxy
    exact s.injective ((heq x).symm.trans ((congrArg t hxy).trans (heq y)))
  · intro f
    obtain ⟨x,hx⟩ := s.surjective (t f)
    exact ⟨x,t.injective ((heq x).trans hx)⟩

variable {M' N' : Type u} [AddCommGroup M'] [AddCommGroup N']
variable [Module k M'] [Module k N'] [Module A M'] [Module B N']
variable [IsScalarTower k A M'] [IsScalarTower k B N']

theorem homMap_precomp (f : M' →ₗ[A] M) (g : N' →ₗ[B] N)
    (x : (M →ₗ[A] U) ⊗[k] (N →ₗ[B] V)) :
    homMap k A B ((TensorProduct.map (LinearMap.lcomp k U f) (LinearMap.lcomp k V g)) x) =
      (homMap k A B x).comp (map k A B f g) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, LinearMap.add_comp]
  | tmul u v =>
    apply LinearMap.restrictScalars_injective k
    apply TensorProduct.ext
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro n
    rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorHomComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.diagonalZeroUnique _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

theorem homOutTerm_bijective (n : ℕ) : Function.Bijective (homOutTerm k A B P Q U V n) := by
  constructor
  · intro f g hfg
    have hh : ModuleCat.ofHom f = ModuleCat.ofHom g := by
      apply hom_ext k A B P Q
      intro i j hij
      exact ModuleCat.hom_ext (congrFun hfg ⟨(i,j),hij⟩)
    exact congrArg (fun h => h.hom) hh
  · intro f
    refine ⟨(desc k A B P Q (fun i j hij => ModuleCat.ofHom (X := moduleObject k A B (P.X i) (Q.X j))
        (Y := moduleObject k A B U V) (f ⟨(i,j),hij⟩))).hom, ?_⟩
    funext p
    exact congrArg (fun h => h.hom)
      (inclusion_desc k A B P Q (fun i j hij => ModuleCat.ofHom (X := moduleObject k A B (P.X i) (Q.X j))
        (Y := moduleObject k A B U V) (f ⟨(i,j),hij⟩))
        p.val.1 p.val.2 p.property)

def homOutTermEquiv (n : ℕ) :
    ((complex k A B P Q).X n →ₗ[A ⊗[k] B] moduleObject k A B U V) ≃ₗ[k]
      (∀ p : Diagonal n, summands k A B P Q n p →ₗ[A ⊗[k] B] moduleObject k A B U V) :=
  LinearEquiv.ofBijective (homOutTerm k A B P Q U V n) (homOutTerm_bijective k A B P Q U V n)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorSingle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

variable (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)

abbrev singleTotal := complex k A B ((ChainComplex.single₀ (ModuleCat A)).obj M)
  ((ChainComplex.single₀ (ModuleCat B)).obj N)

end ArExplicit.ExternalTensor

end

end OAI
end


