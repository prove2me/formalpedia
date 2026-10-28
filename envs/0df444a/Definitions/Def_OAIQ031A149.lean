-- Prove2me | Definitions.Def_OAIQ031A149
-- name    : OAIQ031A149
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:26:31.165335+00:00
-- url     : https://prove2.me/theorems/c73483ed-eb97-45b9-bd31-709734eb9337
-- title:
--   Definitions bundle OAIQ031A149 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 2 definitions and 6 theorems. The definitions and types are `OAI.ArExplicit.ModuleBar.nativeTensorTwist`, `OAI.ArExplicit.ModuleBar.twistExtAction`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ModuleBarExtTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarExtTwist.lean), [`AuslanderReiten_Bar_ModuleBarNativeTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarNativeTwist.lean), [`AuslanderReiten_Bar_ModuleBarTensorTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarTensorTwist.lean), [`AuslanderReiten_HomComplex_HomCochainNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/HomCochainNaturality.lean), [`AuslanderReiten_HomComplex_NativeHomExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/NativeHomExtAction.lean), [`AuslanderReiten_Homology_ShortExactConnectingProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ShortExactConnectingProducts.lean), [`AuslanderReiten_Resolutions_FiniteResolutionProductInclusions`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteResolutionProductInclusions.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A140`, `OAIQ031A142`, `OAIQ031A143` and `OAIQ031A144` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A153` and `OAIQ031A154`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A140
import Definitions.Def_OAIQ031A142
import Definitions.Def_OAIQ031A143
import Definitions.Def_OAIQ031A144

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_HomCochainNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable {X Y : ModuleCat.{u} R} (P : ProjectiveResolution X)

variable (F : homCochain k R P.complex Y ⟶ homCochain k R P.complex Y)

theorem homCochainEndExt_cycleClass (n : ℕ)
    (f g : LinearMap.ker (homShort k R (Y := Y) P n).g.hom)
    (hfg : (F.f n).hom f.val = g.val) :
    homCochainEndExt k R P F n
      (P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) f.val)
        (n+1) rfl (homCycle_closed k R P n f)) =
      P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := Y) g.val)
        (n+1) rfl (homCycle_closed k R P n g) := by
  rw [← homCochainExtEquiv_cycleClass k R P n f,
    ← homCochainExtEquiv_cycleClass k R P n g]
  change (homCochainExtEquiv k R P n)
    ((homologyMap F n).hom ((homCochainExtEquiv k R P n).symm
      ((homCochainExtEquiv k R P n) (homCochainCycleClass k R P n f)))) = _
  rw [LinearEquiv.symm_apply_apply, homCochainCycleClass_eq_literal,
    homCochainCycleClass_eq_literal]
  exact congrArg (homCochainExtEquiv k R P n)
    (VectorCochain.literalClass_map k F n f g hfg)

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarExtTwist
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable [CharP k 2]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

def twistExtAction (n : ℕ) :
    Ext (moduleObject k R M 0) (ModuleCat.of R M) n →ₗ[k]
      Ext (moduleObject k R M 0) (ModuleCat.of R M) n :=
  ExternalTensor.homCochainEndExt k R (resolution k R M)
    (canonicalHomTransport k R M h e he) n

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarNativeTwist
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)

theorem nativeHomTransport_ext (n : ℕ) :
    ExternalTensor.homCochainEndExt k R (nativeResolution k R M)
      (nativeHomTransport k R M h e he) n = twistExtAction k R M h e he n := rfl

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarTensorTwist
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ModuleBar
universe u
variable (k R S M N : Type u) [Field k] [CharP k 2]
  [Ring R] [Algebra k R] [Module.Finite k R] [Ring S] [Algebra k S] [Module.Finite k S]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [Module.Finite k M]
  [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N] [Module.Finite k N]
variable (h : R ≃ₐ[k] R) (j : S ≃ₐ[k] S) (e : M ≃ₗ[k] M) (f : N ≃ₗ[k] N)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (hf : ∀ a n, f (a • n) = j a • f n)

def nativeTensorTwist (n : ℕ) :
    Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n →ₗ[k]
    Ext (ExternalTensor.canonicalTensorObject k R S M N)
      (ExternalTensor.canonicalTensorObject k R S M N) n :=
  ExternalTensor.tensorHomEndExt k R S (nativeResolution k R M) (nativeResolution k S N)
    (ModuleCat.of R M) (ModuleCat.of S N)
    (nativeHomTransport k R M h e he) (nativeHomTransport k S N j f hf) n

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_NativeHomExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (Y : Type u) [AddCommGroup Y] [Module R Y] [Module k Y] [IsScalarTower k R Y]
variable (H : homCochain k R P.complex Y ⟶ homCochain k R P.complex Y)

theorem nativeHomEndExt_extMk (n : ℕ) (f g : P.complex.X n →ₗ[R] Y)
    (hf : f.comp (P.complex.d (n+1) n).hom = 0)
    (hg : g.comp (P.complex.d (n+1) n).hom = 0)
    (hfg : (H.f n).hom f = g) :
    nativeHomEndExt k R P Y H n
      (P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) f)
        (n+1) rfl (ModuleCat.hom_ext hf)) =
    P.extMk (ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) g)
      (n+1) rfl (ModuleCat.hom_ext hg) := by
  rw [← homCochainNativeExtEquiv_literal k R P Y n f hf,
    ← homCochainNativeExtEquiv_literal k R P Y n g hg]
  change (homCochainNativeExtEquiv k R P Y n)
    ((homologyMap H n).hom ((homCochainNativeExtEquiv k R P Y n).symm
      ((homCochainNativeExtEquiv k R P Y n)
        (VectorCochain.literalClass k (homCochain k R P.complex Y) n _)))) = _
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg (homCochainNativeExtEquiv k R P Y n)
    (VectorCochain.literalClass_map k H n _ _ hfg)

end ArExplicit.ExternalTensor

namespace ArExplicit.ExternalTensor
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (Y : Type u) [addY : AddCommGroup Y] [modY : Module R Y]
  [baseY : Module k Y] [towerY : IsScalarTower k R Y]
variable (P : ProjectiveResolution (ModuleCat.of R Y))
variable (H : homCochain k R P.complex Y ⟶ homCochain k R P.complex Y)
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]
  [CategoryTheory.Limits.PreservesFiniteLimits F]
  [CategoryTheory.Limits.PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (e : ModuleCat.of R Y ≅ F.obj (ModuleCat.of R Y))
variable (φ : ProjectiveResolution.Hom P (ResolutionProducts.mapResolution F P) e.hom)

theorem nativeHomEndExt_eq_exactFunctor
    (hφ : ∀ n (a : P.complex.X n ⟶ ModuleCat.of R Y),
      ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) ((H.f n).hom a.hom) =
        (φ.hom.f n ≫ F.map a) ≫ e.inv)
    (n : ℕ) (x : Ext (ModuleCat.of R Y) (ModuleCat.of R Y) n) :
    nativeHomEndExt k R P Y H n x =
      ((Ext.mk₀ e.hom).comp (x.mapExactFunctor F) (zero_add n)).comp
        (Ext.mk₀ e.inv) (add_zero n) := by
  obtain ⟨a, ha, rfl⟩ := P.extMk_surjective x (n+1) rfl
  let b : P.complex.X n →ₗ[R] Y := (H.f n).hom a.hom
  have ha' : a.hom.comp (P.complex.d (n+1) n).hom = 0 :=
    congrArg ModuleCat.Hom.hom ha
  have hb := nativeHomEnd_closed k R P Y H n a.hom ha'
  have ht := nativeHomEndExt_extMk k R P Y H n a.hom b ha' hb rfl
  refine ht.trans ?_
  exact (ResolutionProducts.map_extMk_conjugate F P e.hom e.inv φ a ha
    (ModuleCat.ofHom (X := P.complex.X n) (Y := ModuleCat.of R Y) b)
    (ModuleCat.hom_ext hb) (hφ n a)).symm

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ShortExactConnectingProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Injective R R]
variable {K F G H : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel H)
variable (he : Function.Exact (cochainCokernelMap φ) p)
variable (hK : TotallyAcyclicCochain K) (hF : TotallyAcyclicCochain F)
variable (hG : TotallyAcyclicCochain G) (hH : TotallyAcyclicCochain H)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)

theorem shortExactConnecting_product_source (n : ℤ) (u : CohomologyClass K H n)
    (s : RawCokernelAt K n →ₗ[R] CochainCokernel H)
    (hs : rawSourceAtStableEquiv (k := k) K H n hK.to_chain
      hH.to_chain.toExactProjectiveComplex u = StableHom.classOf R _ _ s)
    (A : K.X (-n) →ₗ[R] CochainCokernel G)
    (t : RawCokernelAt K (n+1) →ₗ[R] CochainCokernel F)
    (hA : p.comp A = s.comp (LinearMap.range (K.d (-(n+1)) (-n)).hom).mkQ)
    (ht : (cochainCokernelMap φ).comp t = A.comp (rawCokernelAtInclusion K n)) :
    rawSourceAtStableEquiv (k := k) K F (n+1) hK.to_chain
      hF.to_chain.toExactProjectiveComplex
      (fullHomProduct u ((fullHomShiftedHomotopyEquiv k H F 1).symm
        (shortExactTriangle φ p he hF hG hH hi hp).mor₃)) = StableHom.classOf R _ _ t := by
  let := hH.projective 0
  obtain ⟨A₀, hA₀⟩ := Module.projective_lifting_property p
    (LinearMap.range (H.d (-1) 0).hom).mkQ hp
  have hzero : p.comp (A₀.comp (rawSyzygyInclusion H)) = 0 := by
    rw [← LinearMap.comp_assoc, hA₀, rawSyzygyInclusion_cover]
  let w := (A₀.comp (rawSyzygyInclusion H)).codRestrict
    (LinearMap.range (cochainCokernelMap φ)) (fun z => by
      rw [(LinearMap.exact_iff.mp he).symm]
      exact LinearMap.congr_fun hzero z)
  let e := LinearEquiv.ofInjective (cochainCokernelMap φ) hi
  let t₀ := e.symm.toLinearMap.comp w
  have ht₀ : (cochainCokernelMap φ).comp t₀ = A₀.comp (rawSyzygyInclusion H) := by
    apply LinearMap.ext
    intro z
    exact congrArg Subtype.val (e.apply_symm_apply (w z))
  let d := (fullHomShiftedHomotopyEquiv k H F 1).symm
    (shortExactTriangle φ p he hF hG hH hi hp).mor₃
  obtain ⟨y, hy⟩ := CohomologyClass.mk_surjective d
  have hySource : StableHom.classOf R _ _ (rawSourceAt y) =
      StableHom.classOf R _ _ t₀ := by
    have hh := shortExactConnecting_source_equiv (k := k) φ p he hF hG hH hi hp A₀ t₀ hA₀ ht₀
    change rawSourceStableEquiv (k := k) H F _ _ d = _ at hh
    rw [← hy, rawSourceStableEquiv_mk] at hh
    exact hh
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective u
  rw [rawSourceAtStableEquiv_mk] at hs
  change rawSourceAtStableEquiv (k := k) K F (n+1) _ _
    (fullHomProduct (CohomologyClass.mk x) d) = _
  rw [← hy, fullHomProduct_mk, rawSourceAtStableEquiv_mk, rawSourceAt_product (k := k)]
  rw [← StableHom.comp_classOf, hySource]
  erw [StableHom.comp_classOf]
  let X₀ := (x.val.v (-n) 0 (by omega)).hom
  let x₁ := rawCokernelAtMap (k := k) x (n+1) 1 rfl
  have hfirst : p.comp (A₀.comp X₀) =
      (rawSourceAt x).comp (LinearMap.range (K.d (-(n+1)) (-n)).hom).mkQ := by
    rw [← LinearMap.comp_assoc, hA₀]
    apply LinearMap.ext
    intro z
    exact (rawSourceAt_mk (k := k) x z).symm
  have hsecond : (cochainCokernelMap φ).comp (t₀.comp x₁) =
      (A₀.comp X₀).comp (rawCokernelAtInclusion K n) := by
    rw [← LinearMap.comp_assoc, ht₀, LinearMap.comp_assoc]
    have hx := rawCokernelAtMap_cover (k := k) x n 0 (add_zero n).symm
    change (rawSyzygyInclusion H).comp x₁ = X₀.comp (rawCokernelAtInclusion K n) at hx
    rw [hx, LinearMap.comp_assoc]
  let := hK.finite (-n)
  let := hK.projective (-n)
  exact stable_connecting_congr (rawCokernelAtInclusion K n)
    (LinearMap.range (K.d (-(n+1)) (-n)).hom).mkQ (rawCokernelAtInclusion_cover K n)
    (cochainCokernelMap φ) p hi hp (LinearMap.exact_iff.mp he).symm
    (rawSourceAt x) s (A₀.comp X₀) A (t₀.comp x₁) t hfirst hA hsecond ht hs

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteResolutionProductInclusions
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory CategoryTheory.Limits
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

theorem resolutionPairInr :
    (Q).map (resolutionMap (M := N) (N := pairModule M N) τ (pairInr M N)) ≫
      (resolutionPairIso τ M N).hom = biprod.inr := by
  apply biprod.hom_ext
  · rw [Category.assoc, resolutionPairIso_hom_fst, biprod.inr_fst]
    exact (resolutionPairBicone τ M N).inr_fst
  · rw [Category.assoc, resolutionPairIso_hom_snd, biprod.inr_snd]
    exact (resolutionPairBicone τ M N).inr_snd

end ArExplicit.FiniteLeftModule

end

end OAI
end


