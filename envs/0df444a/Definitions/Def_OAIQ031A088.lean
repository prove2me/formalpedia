-- Prove2me | Definitions.Def_OAIQ031A088
-- name    : OAIQ031A088
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:26:42.219988+00:00
-- url     : https://prove2.me/theorems/34eb65d4-9a2b-49d0-aa3c-0448e8b4cc4f
-- title:
--   Definitions bundle OAIQ031A088 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 22 declarations of OpenAI's Lean: 8 definitions and 14 theorems. The definitions and types are `OAI.ArExplicit.ModuleBar.transport`, `OAI.ArExplicit.ModuleBar.transportHom`, `OAI.ArExplicit.ModuleBar.transportedCochain`, `OAI.ArExplicit.ModuleBar.transportedHom`, `OAI.ArExplicit.StableIsomorphism.dropRight`, `OAI.ArExplicit.TwoCone.firstProjection`, `OAI.ArExplicit.TwoCone.projection`, `OAI.ArExplicit.TwoCone.topProjection`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarAutomorphism`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarAutomorphism.lean), [`AuslanderReiten_Bar_ModuleBarHomTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarHomTwist.lean), [`AuslanderReiten_Bar_ModuleBarTwistCocycle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTwistCocycle.lean), [`AuslanderReiten_Bar_ModuleBarTwistExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTwistExtAction.lean), [`AuslanderReiten_Cones_TwoCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoCone.lean), [`AuslanderReiten_Cones_TwoConeCells`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeCells.lean), [`AuslanderReiten_Resolutions_ResolutionCubicConjugate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionCubicConjugate.lean), [`AuslanderReiten_Stable_StableProjectiveSummand`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableProjectiveSummand.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A040`, `OAIQ031A061`, `OAIQ031A062`, `OAIQ031A063`, `OAIQ031A065` and `OAIQ031A068` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A101` and `OAIQ031A102`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A040
import Definitions.Def_OAIQ031A061
import Definitions.Def_OAIQ031A062
import Definitions.Def_OAIQ031A063
import Definitions.Def_OAIQ031A065
import Definitions.Def_OAIQ031A068

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarAutomorphism
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module k M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)

def transport : (n : ℕ) → object k R M n ≃ₗ[k] object k R M n
  | 0 => e
  | n+1 => TensorProduct.congr h.toLinearEquiv (transport n)

@[simp] theorem transport_zero (m : M) : transport k R M h e 0 m = e m := rfl
@[simp] theorem transport_tmul (n : ℕ) (a : R) (x : object k R M n) :
    transport k R M h e (n+1) (a ⊗ₜ[k] x) = h a ⊗ₜ[k] transport k R M h e n x := rfl

variable [Module R M] [IsScalarTower k R M]
variable (he : ∀ a m, e (a • m) = h a • e m)
include he

theorem transport_left (n : ℕ) (a : R) (x : object k R M n) :
    transport k R M h e n (left k R M n a x) =
      left k R M n (h a) (transport k R M h e n x) := by
  cases n with
  | zero => exact he a x
  | succ n =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      rw [left_tmul, transport_tmul, transport_tmul, left_tmul, map_mul]

theorem transport_boundary (n : ℕ) (x : object k R M (n+1)) :
    transport k R M h e n (boundary k R M n x) =
      boundary k R M n (transport k R M h e (n+1) x) := by
  induction n with
  | zero =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact he a x
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
      rw [boundary_succ_tmul, map_add, transport_left k R M h e he,
        transport_tmul, transport_tmul, boundary_succ_tmul, ih]

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTwistCocycle
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (p : AbsoluteBar.Cochain3 k R) (c : k)
variable (hp : ∀ a b d m, p (h a) (h b) (h d) • e m = c • e (p a b d • m))
include hp

theorem transport_suffix3 (x : object k R M 3) :
    suffix3 k R M p (transport k R M h e 3 x) = c • e (suffix3 k R M p x) := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a x =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]
    | tmul b x =>
      induction x using OAI.tensorInductionOn with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]
      | tmul d m => exact hp a b d m

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarHomTwist
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
include he

def transportedHom (n : ℕ) (f : moduleObject k R M n →ₗ[R] M) :
    moduleObject k R M n →ₗ[R] M where
  toFun x := e.symm (f (transport k R M h e n x))
  map_add' x y := by
    exact (congrArg (fun v : object k R M n => e.symm (f v))
      ((transport k R M h e n).map_add x y)).trans
        ((congrArg e.symm (f.map_add _ _)).trans (e.symm.map_add _ _))
  map_smul' a x := by
    exact (congrArg (fun v : object k R M n => e.symm (f v))
      (transport_left k R M h e he n a x)).trans
        ((congrArg e.symm (f.map_smul (h a)
          (show moduleObject k R M n from transport k R M h e n x))).trans
            (inverse_transport_smul k R M h e he a _))

def transportHom (n : ℕ) : (moduleObject k R M n →ₗ[R] M) →ₗ[k]
    (moduleObject k R M n →ₗ[R] M) where
  toFun := transportedHom k R M h e he n
  map_add' f g := by ext x; exact e.symm.map_add _ _
  map_smul' a f := by ext x; exact e.symm.map_smul a _

@[simp] theorem transportHom_apply (n : ℕ) (f : moduleObject k R M n →ₗ[R] M)
    (x : moduleObject k R M n) :
    transportHom k R M h e he n f x = e.symm (f (transport k R M h e n x)) := rfl

theorem transportHom_differential (n : ℕ) (f : moduleObject k R M n →ₗ[R] M) :
    transportHom k R M h e he (n+1) (f.comp (differential k R M n)) =
      (transportHom k R M h e he n f).comp (differential k R M n) := by
  ext x
  change e.symm (f (boundary k R M n (transport k R M h e (n+1) x))) =
    e.symm (f (transport k R M h e n (boundary k R M n x)))
  exact congrArg (fun v : object k R M n => e.symm (f v))
    (transport_boundary k R M h e he n x).symm

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTwistExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

omit [CharP k 2] in
theorem transportedHom_closed (n : ℕ) (f : moduleObject k R M (n+1) →ₗ[R] M)
    (hf : f.comp (differential k R M (n+1))=0) :
    (transportedHom k R M h e he (n+1) f).comp (differential k R M (n+1))=0 := by
  change (transportHom k R M h e he (n+1) f).comp (differential k R M (n+1))=0
  rw [← transportHom_differential, hf, map_zero]

def transportedCochain (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M) :
    (resolution k R M).complex.X n ⟶ ModuleCat.of R M :=
  ModuleCat.ofHom (X := (resolution k R M).complex.X n) (Y := ModuleCat.of R M)
    (transportedHom k R M h e he (n+1) f.hom)

theorem transportedCochain_closed (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0) :
    (resolution k R M).complex.d (n+1) n ≫ transportedCochain k R M h e he n f=0 := by
  change (complex k R M).d (n+1) n ≫ f=0 at hf
  change (complex k R M).d (n+1) n ≫ transportedCochain k R M h e he n f=0
  rw [complex_d] at hf ⊢
  apply ModuleCat.hom_ext
  exact transportedHom_closed k R M h e he n f.hom (congrArg ModuleCat.Hom.hom hf)

variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

variable (c : k)
variable (hpc : ∀ a b d m, p (h a) (h b) (h d) • e m = c • e (p a b d • m))
include hpc

omit hpc [HasDerivedCategory (ModuleCat R)] in
theorem extMk_congr (n : ℕ)
    (f g : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0)
    (hg : (resolution k R M).complex.d (n+1) n ≫ g=0) (hfg : f=g) :
    (resolution k R M).extMk f (n+1) rfl hf =
      (resolution k R M).extMk g (n+1) rfl hg := by
  subst g
  rfl

omit hpc [HasDerivedCategory (ModuleCat R)] in
theorem extMk_smul_native (n : ℕ)
    (f : (resolution k R M).complex.X n ⟶ ModuleCat.of R M)
    (hf : (resolution k R M).complex.d (n+1) n ≫ f=0) (a : k)
    (ha : (resolution k R M).complex.d (n+1) n ≫ (a • f)=0) :
    (resolution k R M).extMk (a • f) (n+1) rfl ha =
      a • (resolution k R M).extMk f (n+1) rfl hf := by
  rw [Ext.smul_eq_comp_mk₀, ProjectiveResolution.extMk_comp_mk₀]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change a • f.hom x = (algebraMap k R a) • f.hom x
  exact (IsScalarTower.algebraMap_smul R a (f.hom x)).symm

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoCone
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R]

variable (D : Data R)

theorem cokernel_finite (hf : ∀ n, Module.Finite R (D.term n)) (N : ℕ) :
    Module.Finite R (Cokernel D N) := by
  let := term_finite D hf N
  infer_instance

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeCells
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

abbrev firstProjection (n : ℕ) : firstTerm D n →ₗ[R] D.term (n+2) :=
  LinearMap.snd R (D.term n) (D.term (n+2))

abbrev projection (n : ℕ) : term D n →ₗ[R] firstTerm D (n+2) :=
  LinearMap.snd R (firstTerm D n) (firstTerm D (n+2))

abbrev topProjection (n : ℕ) : term D n →ₗ[R] D.term (n+4) :=
  (firstProjection D (n+2)).comp (projection D n)

end ArExplicit.TwoCone

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionCubicConjugate
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace ArExplicit
universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable {B S N : ModuleCat.{u} R}

theorem resolutionExt_cubic_conjugate
    (P : ProjectiveResolution B) (Q : ProjectiveResolution N)
    (e : B ≅ S) (j : S ≅ N)
    (φ : ProjectiveResolution.Hom P Q (e.hom ≫ j.hom))
    (p : P.complex.X 3 ⟶ P.complex.X 0)
    (q : ∀ n : ℕ, Q.complex.X (n+3) ⟶ Q.complex.X n)
    (hq : ∀ n, q (n+1) ≫ Q.complex.d (n+1) n =
      Q.complex.d (n+4) (n+3) ≫ q n)
    (f : P.complex.X 3 ⟶ S) (hf : P.complex.d 4 3 ≫ f = 0)
    (hfc : f = p ≫ P.π.f 0 ≫ e.hom)
    (hc : p ≫ φ.hom.f 0 = φ.hom.f 3 ≫ q 0) :
    selfExtIso (k := k) j 3 ((Ext.mk₀ e.inv).comp
      (P.extMk f 4 rfl hf) (zero_add _)) =
      ResolutionProducts.endExt Q (ResolutionProducts.natCubicCocycle (k := k) Q q hq) := by
  rw [ResolutionProducts.natCubic_endExt_eq]
  apply resolutionExt_cover_conjugate P Q e j φ 3 f (q 0 ≫ Q.π.f 0) hf
    (ResolutionProducts.natCubic_augmented_cycle Q q hq)
  exact cubicAugmentedSquare _ _ _ _ _ _ _ _ _ φ.hom_f_zero_comp_π_f_zero hc hfc

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableProjectiveSummand
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.StableIsomorphism
universe u
variable {R M P : Type u} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]

def dropRight : StableIsomorphism R (M × P) M where
  hom := StableHom.classOf R _ _ (LinearMap.fst R M P)
  inv := StableHom.classOf R _ _ (LinearMap.inl R M P)
  hom_inv_id := by
    rw [StableHom.comp_classOf]
    change StableHom.classOf R _ _ ((LinearMap.inl R M P).comp (LinearMap.fst R M P)) =
      StableHom.classOf R _ _ LinearMap.id
    rw [StableHom.classOf_eq_iff, factorsThroughFiniteFree_iff_projective]
    refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance,
      LinearMap.snd R M P, -(LinearMap.inr R M P), ?_⟩
    ext x <;> simp
  inv_hom_id := by
    rw [StableHom.comp_classOf]
    congr 1

@[simp] theorem dropRight_hom :
    (dropRight (R := R) (M := M) (P := P)).hom =
      StableHom.classOf R _ _ (LinearMap.fst R M P) := rfl

end ArExplicit.StableIsomorphism

end OAI
end


