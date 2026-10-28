-- Prove2me | Definitions.Def_OAIQ031A066
-- name    : OAIQ031A066
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:13:38.70462+00:00
-- url     : https://prove2.me/theorems/01085156-df48-439a-bec7-058092e67d1f
-- title:
--   Definitions bundle OAIQ031A066 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 16 definitions, 2 instances and 10 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.complexMap`, `OAI.ArExplicit.BalancedTensor.complexSequence`, `OAI.ArExplicit.BalancedTensor.naturalMap`, `OAI.ArExplicit.BalancedTensor.piRightInv`, `OAI.ArExplicit.BarBalanced.bar`, `OAI.ArExplicit.DualTensor.tensorComplex`, `OAI.ArExplicit.Induction.Object`, `OAI.ArExplicit.Induction.extendHom`, `OAI.ArExplicit.TrivialInduction.dualComplex`, `OAI.ArExplicit.TrivialInduction.dualComplexIso`, `OAI.ArExplicit.TrivialInduction.dualFunctorIso`, `OAI.ArExplicit.TrivialInduction.dualInflateEquiv`, `OAI.ArExplicit.TrivialInduction.inducedComplex`, `OAI.ArExplicit.TrivialInduction.quotientComplex`, `OAI.ArExplicit.TrivialInduction.quotientScalarMap`, `OAI.ArExplicit.TrivialInduction.sequence`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarBalancedModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarBalancedModule.lean), [`AuslanderReiten_Duality_DualTensorComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Duality/DualTensorComplex.lean), [`AuslanderReiten_Modules_InductionAdjunction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/InductionAdjunction.lean), [`AuslanderReiten_Resolutions_CProjectiveResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CProjectiveResolution.lean), [`AuslanderReiten_Resolutions_Resolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/Resolution.lean), [`AuslanderReiten_Resolutions_TrivialInductionComplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/TrivialInductionComplex.lean), [`AuslanderReiten_Resolutions_TrivialInductionDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/TrivialInductionDual.lean), [`AuslanderReiten_Resolutions_TrivialInductionQuotient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/TrivialInductionQuotient.lean), [`AuslanderReiten_Tensor_BalancedTensorCategory`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorCategory.lean), [`AuslanderReiten_Tensor_BalancedTensorLeftExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorLeftExact.lean), [`AuslanderReiten_Tensor_BalancedTensorPi`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorPi.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A045`, `OAIQ031A047`, `OAIQ031A049` and `OAIQ031A050` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A081`, `OAIQ031A082` and `OAIQ031A084`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A045
import Definitions.Def_OAIQ031A047
import Definitions.Def_OAIQ031A049
import Definitions.Def_OAIQ031A050

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarBalancedModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit.BarBalanced
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

abbrev bar (n : ℕ) := EnvelopingBimodule k R (AbsoluteBar.moduleObject k R n)

end ArExplicit.BarBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorPi
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.BalancedTensor

variable {k R S F M : Type*} [CommRing k] [Ring R] [Algebra k R] [Ring S]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [Module S F] [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def piRightInv : (ι → BalancedTensor k R F M) →ₗ[S] BalancedTensor k R F (ι → M) where
  toFun z := ∑ i, mapRight (k := k) (S := S) (LinearMap.single R (fun _ : ι => M) i) (z i)
  map_add' x y := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' s z := by simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorLeftExact
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]
variable {F G H M : Type*}
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup H] [Module k H] [Module Rᵐᵒᵖ H] [IsScalarTower k Rᵐᵒᵖ H]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

variable {n : ℕ}

theorem leftRecombine_leftCoefficients (s : M →ₗ[R] (Fin n → R))
    (p : (Fin n → R) →ₗ[R] M) (h : p.comp s = LinearMap.id) (z : BalancedTensor k R F M) :
    leftRecombine p (leftCoefficients s z) = z := by
  induction z using induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul f m =>
    rw [leftRecombine_apply]
    calc
      (∑ i, tmul (leftCoefficients s (tmul f m) i) (p (Pi.single i 1))) =
          ∑ i, tmul f (p (Pi.single i (s m i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [leftCoefficients_tmul, balance, ← p.map_smul]
        congr 2
        ext j
        by_cases hij : j = i
        · subst j; simp
        · simp [hij]
      _ = tmul f (p (∑ i, Pi.single i (s m i))) := by
        simp only [map_sum]
        exact (map_sum (mk (k := k) (R := R) f) _ _).symm
      _ = tmul f m := by
        rw [Finset.univ_sum_single]
        exact congrArg (fun m => tmul (k := k) (R := R) f m) (DFunLike.congr_fun h m)

theorem leftCoefficients_natural (s : M →ₗ[R] (Fin n → R)) (a : F →ₗ[Rᵐᵒᵖ] G)
    (z : BalancedTensor k R F M) :
    leftCoefficients s (mapLeft a z) = fun i => a (leftCoefficients s z i) := by
  induction z using induction_on with
  | zero => ext i; simp
  | tmul f m => ext i; simp
  | add x y hx hy => ext i; simp only [map_add, Pi.add_apply, hx, hy]

omit [IsScalarTower k R M] in
theorem leftRecombine_natural (p : (Fin n → R) →ₗ[R] M) (a : F →ₗ[Rᵐᵒᵖ] G) (z : Fin n → F) :
    mapLeft a (leftRecombine p z) = leftRecombine (k := k) p (fun i => a (z i)) := by
  simp only [leftRecombine_apply, map_sum, mapLeft_tmul]

theorem mapLeft_exact [Module.Finite R M] [Module.Projective R M]
    (a : F →ₗ[Rᵐᵒᵖ] G) (b : G →ₗ[Rᵐᵒᵖ] H) (hex : Function.Exact a b) :
    Function.Exact (mapLeft (k := k) (M := M) a) (mapLeft b) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  intro z
  constructor
  · intro hz
    have hcoords : ∀ i, b (leftCoefficients s z i) = 0 := by
      have hnat := leftCoefficients_natural s b z
      rw [hz, map_zero] at hnat
      intro i
      exact (congrFun hnat i).symm
    choose w hw using fun i => (hex (leftCoefficients s z i)).mp (hcoords i)
    refine ⟨leftRecombine p w, ?_⟩
    rw [leftRecombine_natural]
    convert leftRecombine_leftCoefficients s p hs z using 1
    all_goals try with_reducible_and_instances rfl
    exact congrArg (leftRecombine (k := k) p) (funext hw)
  · rintro ⟨w, rfl⟩
    have hba : b.comp a = 0 := by ext f; exact (hex (a f)).mpr ⟨f, rfl⟩
    change ((mapLeft b).comp (mapLeft a)) w = 0
    rw [← mapLeft_comp, hba, mapLeft_zero, LinearMap.zero_apply]

omit [IsScalarTower k R M] in
theorem mapLeft_surjective (a : F →ₗ[Rᵐᵒᵖ] G) (ha : Function.Surjective a) :
    Function.Surjective (mapLeft (k := k) (M := M) a) :=
  map_surjective (a.restrictScalars k) LinearMap.id
    (fun r f => a.map_smul r f) (fun _ _ => rfl) ha Function.surjective_id

theorem mapLeft_injective [Module.Finite R M] [Module.Projective R M]
    (a : F →ₗ[Rᵐᵒᵖ] G) (ha : Function.Injective a) :
    Function.Injective (mapLeft (k := k) (M := M) a) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : M →ₗ[R] M) hp
  intro x y hxy
  have hc : leftCoefficients s x = leftCoefficients s y := by
    ext i
    apply ha
    have hh := congrArg (fun z => leftCoefficients s z i) hxy
    simpa only [leftCoefficients_natural] using hh
  rw [← leftRecombine_leftCoefficients s p hs x, ← leftRecombine_leftCoefficients s p hs y, hc]

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorCategory
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.BalancedTensor
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
universe u
variable {k R S : Type u} [Field k] [Ring R] [Ring S] [Algebra k R]
variable {F G H : Type u}
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F] [Module S F]
  [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F] [IsScalarTower k Rᵐᵒᵖ F]
variable [AddCommGroup G] [Module k G] [Module Rᵐᵒᵖ G] [Module S G]
  [SMulCommClass k S G] [SMulCommClass S Rᵐᵒᵖ G] [IsScalarTower k Rᵐᵒᵖ G]
variable [AddCommGroup H] [Module k H] [Module Rᵐᵒᵖ H] [Module S H]
  [SMulCommClass k S H] [SMulCommClass S Rᵐᵒᵖ H] [IsScalarTower k Rᵐᵒᵖ H]

def naturalMap (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (s : S) f, a (s • f) = s • a f) :
    functor (k := k) (R := R) (S := S) (F := F) ⟶ functor (k := k) (R := R) (S := S) (F := G) where
  app M := ModuleCat.ofHom (mapLeftLinear (k := k) a ha M)
  naturality M N b := by
    apply ModuleCat.hom_ext
    apply leftHom_ext
    intro f m
    rfl

variable {ι : Type*} {c : ComplexShape ι}

def complexMap (a : F →ₗ[Rᵐᵒᵖ] G) (ha : ∀ (s : S) f, a (s • f) = s • a f)
    (P : HomologicalComplex (ModuleCat.{u} R) c) :
    ((functor (k := k) (R := R) (S := S) (F := F)).mapHomologicalComplex c).obj P ⟶
      ((functor (k := k) (R := R) (S := S) (F := G)).mapHomologicalComplex c).obj P where
  f i := (naturalMap (k := k) a ha).app (P.X i)
  comm' i j _ := ((naturalMap (k := k) a ha).naturality (P.d i j)).symm

def complexSequence (a : F →ₗ[Rᵐᵒᵖ] G) (b : G →ₗ[Rᵐᵒᵖ] H)
    (ha : ∀ (s : S) f, a (s • f) = s • a f) (hb : ∀ (s : S) g, b (s • g) = s • b g)
    (hab : b.comp a = 0) (P : HomologicalComplex (ModuleCat.{u} R) c) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} S) c) :=
  ShortComplex.mk (complexMap (k := k) a ha P) (complexMap (k := k) b hb P) (by
    ext i : 1
    apply ModuleCat.hom_ext
    apply leftHom_ext
    intro f m
    change tmul (b (a f)) m = 0
    rw [show b (a f) = 0 from LinearMap.congr_fun hab f, zero_tmul])

theorem complexSequence_shortExact (a : F →ₗ[Rᵐᵒᵖ] G) (b : G →ₗ[Rᵐᵒᵖ] H)
    (ha : ∀ (s : S) f, a (s • f) = s • a f) (hb : ∀ (s : S) g, b (s • g) = s • b g)
    (hab : b.comp a = 0) (hinj : Function.Injective a)
    (hex : Function.Exact a b) (hsurj : Function.Surjective b)
    (P : HomologicalComplex (ModuleCat.{u} R) c)
    [∀ i, Module.Finite R (P.X i)] [∀ i, Module.Projective R (P.X i)] :
    (complexSequence (k := k) a b ha hb hab P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    exact mapLeft_exact a b hex
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact mapLeft_injective a hinj
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact mapLeft_surjective b hsurj

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualTensorComplex
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.DualTensor
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} R) ℕ)

def tensorComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ((BalancedTensor.functor (k := k) (R := R) (S := R) (F := Coinduced k R)).mapHomologicalComplex _).obj P

end ArExplicit.DualTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_InductionAdjunction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
namespace Induction

variable {k R S V W : Type*} [CommRing k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S] (ι : R →ₐ[k] S)
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
  [AddCommGroup W] [Module k W] [Module R W] [Module S W]
  [IsScalarTower k R W] [IsScalarTower k S W]

abbrev Object := BalancedTensor k R (InductionBimodule ι) V

def extendHom (hcompat : ∀ (r : R) (w : W), r • w = (ι r) • w)
    (g : V →ₗ[R] W) : Object (V := V) ι →ₗ[S] W :=
  BalancedTensor.liftLeft (extendFormula ι g)
    (by
      intro a r v
      change (a.value * ι r) • g v = a.value • g (r • v)
      rw [g.map_smul, hcompat, mul_smul])
    (by intro s a v; exact mul_smul s a.value (g v))

@[simp] theorem extendHom_tmul (hcompat : ∀ (r : R) (w : W), r • w = (ι r) • w)
    (g : V →ₗ[R] W) (a : InductionBimodule ι) (v : V) :
    extendHom ι hcompat g (BalancedTensor.tmul a v) = a.value • g v := rfl

end Induction
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_Resolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

instance instFiniteSubtypeBaseAlgebraMemSubmoduleE : Module.Finite k (E q) :=
  finite_fixedRight q _ (by simpa [multiplicationTable] using basis_mul q e e)

end ArExplicit.Resolution

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CProjectiveResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

variable {k : Type*} [Field k] [CharP k 2] (q : k)

instance complex_finite (n : ℕ) : Module.Finite k ((complex q).X n) := by
  cases n with
  | zero => exact (inferInstance : Module.Finite k (F q))
  | succ n => exact (inferInstance : Module.Finite k (E q))

end ArExplicit.Resolution

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_TrivialInductionComplex
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "T" => TrivialExtension k R

variable {ι : Type*} {c : ComplexShape ι}

def dualComplex (P : HomologicalComplex (ModuleCat.{u} R) c) :
    HomologicalComplex (ModuleCat.{u} T) c :=
  ((BalancedTensor.functor (k := k) (R := R) (S := T) (F := Coinduced k R)).mapHomologicalComplex c).obj P

def inducedComplex (P : HomologicalComplex (ModuleCat.{u} R) c) :
    HomologicalComplex (ModuleCat.{u} T) c :=
  ((BalancedTensor.functor (k := k) (R := R) (S := T) (F := Middle (k := k) (R := R))).mapHomologicalComplex c).obj P

def quotientComplex (P : HomologicalComplex (ModuleCat.{u} R) c) :
    HomologicalComplex (ModuleCat.{u} T) c :=
  ((BalancedTensor.functor (k := k) (R := R) (S := T) (F := Quotient (k := k) (R := R))).mapHomologicalComplex c).obj P

def sequence (P : HomologicalComplex (ModuleCat.{u} R) c) :
    ShortComplex (HomologicalComplex (ModuleCat.{u} T) c) :=
  BalancedTensor.complexSequence (k := k) inclusion projection inclusion_left
    projection_left projection_inclusion P

theorem sequence_shortExact (P : HomologicalComplex (ModuleCat.{u} R) c)
    [∀ i, Module.Finite R (P.X i)] [∀ i, Module.Projective R (P.X i)] :
    (sequence (k := k) P).ShortExact :=
  BalancedTensor.complexSequence_shortExact inclusion projection inclusion_left
    projection_left projection_inclusion inclusion_injective inclusion_projection_exact
    projection_surjective P

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_TrivialInductionQuotient
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def quotientScalarMap (M : ModuleCat.{u} R) :
    BalancedTensor k R (Quotient (k := k) (R := R)) M →ₗ[k] M :=
  BalancedTensor.lift
    ((BalancedTensor.leftAction (k := k) (R := R) (M := M)).comp
      (InductionBimodule.scalarEquiv (AlgHom.id k R)).toLinearMap)
    (by intro a r m; exact mul_smul a.value r m)

@[simp] theorem quotientScalarMap_tmul (M : ModuleCat.{u} R)
    (r : Quotient (k := k) (R := R)) (m : M) :
    quotientScalarMap M (BalancedTensor.tmul r m) = r.value • m := rfl

end ArExplicit.TrivialInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_TrivialInductionDual
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.TrivialInduction
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "T" => TrivialExtension k R

def dualInflateEquiv (M : ModuleCat.{u} R) :
    BalancedTensor k R (Coinduced k R) M ≃ₗ[T]
      (inflate (k := k)).obj
        (ModuleCat.of R (BalancedTensor k R (Coinduced k R) M)) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' t z := by
    change t • z = t.base • z
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, hx, hy]
    | tmul φ m => rfl

def dualFunctorIso :
    BalancedTensor.functor (k := k) (R := R) (S := T) (F := Coinduced k R) ≅
      BalancedTensor.functor (k := k) (R := R) (S := R) (F := Coinduced k R) ⋙ inflate :=
  NatIso.ofComponents (fun M => (dualInflateEquiv M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl)

def dualComplexIso {ι : Type*} {c : ComplexShape ι}
    (P : HomologicalComplex (ModuleCat.{u} R) c) :
    dualComplex (k := k) P ≅
      ((inflate (k := k)).mapHomologicalComplex c).obj
        (((BalancedTensor.functor (k := k) (R := R) (S := R)
          (F := Coinduced k R)).mapHomologicalComplex c).obj P) :=
  (NatIso.mapHomologicalComplex dualFunctorIso c).app P

end ArExplicit.TrivialInduction

end

end OAI
end


