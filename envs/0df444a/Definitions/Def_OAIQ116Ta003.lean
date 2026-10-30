-- Prove2me | Definitions.Def_OAIQ116Ta003
-- name    : OAIQ116Ta003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:36:56.004911+00:00
-- url     : https://prove2.me/theorems/7006502b-f5ac-4343-b38c-be627bb4c939
-- title:
--   Definitions bundle OAIQ116Ta003 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 191 declarations of OpenAI's Lean: 82 definitions, 1 inductive type or structure, 21 instances and 87 theorems. The definitions and types are `OAI.Tachikawa.AlgebraInduction.adjunction`, `OAI.Tachikawa.AlgebraInduction.complexExtend`, `OAI.Tachikawa.AlgebraInduction.complexInduction`, `OAI.Tachikawa.AlgebraInduction.complexRestriction`, `OAI.Tachikawa.AlgebraInduction.complexUnit`, `OAI.Tachikawa.AlgebraInduction.compositionIso`, `OAI.Tachikawa.AlgebraInduction.resUnderlyingEquiv`, `OAI.Tachikawa.BalancedTensor.commutingAction`, `OAI.Tachikawa.BalancedTensor.freeEquiv`, `OAI.Tachikawa.BalancedTensor.freeInv`, `OAI.Tachikawa.BalancedTensor.rightFreeEquiv`, `OAI.Tachikawa.BalancedTensor.rightFreeInv`, `OAI.Tachikawa.BimoduleTensorHom.curry`, `OAI.Tachikawa.BimoduleTensorHom.curryLinear`, `OAI.Tachikawa.BimoduleTensorHom.uncurry`, `OAI.Tachikawa.C.T`, `OAI.Tachikawa.C.dualCoeff`, `OAI.Tachikawa.C.j`, `OAI.Tachikawa.Construction.E`, `OAI.Tachikawa.Construction.T`, `OAI.Tachikawa.Construction.characterE`, `OAI.Tachikawa.Construction.characterT`, `OAI.Tachikawa.Construction.sigma`, `OAI.Tachikawa.Enveloping.CoindReplacement`, `OAI.Tachikawa.Enveloping.evaluation`, `OAI.Tachikawa.Enveloping.leftEnvelopingMap`, `OAI.Tachikawa.Enveloping.leftIndExtend`, `OAI.Tachikawa.Enveloping.leftIndExtendLinear`, `OAI.Tachikawa.Enveloping.leftIndObj`, `OAI.Tachikawa.Enveloping.leftIndResMap`, `OAI.Tachikawa.Enveloping.leftIndUnit`, `OAI.Tachikawa.Enveloping.ofBimoduleHom`, `OAI.Tachikawa.Enveloping.reassembleIso`, `OAI.Tachikawa.Enveloping.regular`, `OAI.Tachikawa.Enveloping.rightEvaluation`, `OAI.Tachikawa.Enveloping.rightEvaluationEquiv`, `OAI.Tachikawa.Enveloping.rightFunctor`, `OAI.Tachikawa.Enveloping.rightObjEquiv`, `OAI.Tachikawa.FiniteModule.complete`, `OAI.Tachikawa.FiniteModule.coresolution` and 43 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_Bimodule`, `Tachikawa_Coinduction`, `Tachikawa_CompleteTensor`, `Tachikawa_Coresolution`, `Tachikawa_DerivedInduction`, `Tachikawa_FiniteCoinduction`, `Tachikawa_Induction`, `Tachikawa_Nakayama`, `Tachikawa_OuterTensor`, `Tachikawa_Period`, `Tachikawa_ReverseResolution`, `Tachikawa_RightInduction`, `Tachikawa_Socle`, `Tachikawa_StableDuality`, `Tachikawa_StableLift`, `Tachikawa_Symmetry`, `Tachikawa_Tensor`, `Tachikawa_TwistHom`, `Tachikawa_Twisting`.
--
--   **Imports.** It imports the published bundle `Def_Tachikawa`; the bundles `OAIQ116Ta000` and `OAIQ116Ta001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta006`, `OAIQ116Ta007`, `OAIQ116Ta008` and `OAIQ116Ta009`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_Tachikawa
import Definitions.Def_OAIQ116Ta000
import Definitions.Def_OAIQ116Ta001

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Symmetry
attribute [-instance] _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
namespace Tachikawa

namespace DualBimodule
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

instance instSMulCommClassMulOpposite : SMulCommClass R Rᵐᵒᵖ (DualBimodule k R) where
  smul_comm a b φ := by ext x; simp [mul_assoc]

instance instIsScalarTowerMulOpposite : IsScalarTower k Rᵐᵒᵖ (DualBimodule k R) where
  smul_assoc a b φ := by
    ext x
    simp [Algebra.smul_mul_assoc]

end DualBimodule
end Tachikawa



namespace Tachikawa.DualBimodule
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

instance injective : Module.Injective R (DualBimodule k R) where
  out {X Y} _ _ _ _ f hf g := by
    let : Module k X := Module.compHom X (algebraMap k R)
    let : Module k Y := Module.compHom Y (algebraMap k R)
    let : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let : IsScalarTower k R Y := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let g₀ : X →ₗ[k] k :=
      { toFun := fun x => g x 1
        map_add' := fun x y => by simp
        map_smul' := fun c x => by
          change g (algebraMap k R c • x) 1 = c • g x 1
          rw [map_smul]
          simp [Algebra.algebraMap_eq_smul_one] }
    obtain ⟨s, hs⟩ := (f.restrictScalars k).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr hf)
    refine ⟨coinduce (g₀.comp s), ?_⟩
    intro x
    ext r
    change g₀ (s (r • f x)) = g x r
    rw [← f.map_smul]
    have hs' : s (f (r • x)) = r • x := LinearMap.congr_fun hs (r • x)
    rw [hs']
    change g (r • x) 1 = g x r
    rw [map_smul]
    simp

end Tachikawa.DualBimodule



namespace Tachikawa



variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R))

include t in
lemma injective [FiniteDimensional k R] : Module.Injective R R := by
  constructor
  intro X Y _ _ _ _ f hf g
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R (DualBimodule k R) X Y f hf
    (t.dualEquiv.toLinearMap.comp g)
  refine ⟨t.dualEquiv.symm.toLinearMap.comp h, ?_⟩
  intro x
  change t.dualEquiv.symm (h (f x)) = g x
  have hhx := LinearMap.congr_fun hh x
  change h (f x) = t.dualEquiv (g x) at hhx
  rw [hhx]
  exact t.dualEquiv.symm_apply_apply (g x)

end SymmetrizingForm

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableDuality
attribute [-instance] _root_.OAI.Tachikawa.FiniteModule.instAddCommGroupCarrierObj _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {R M P : Type} [Ring R] [AddCommGroup M] [Module R M]
  [AddCommGroup P] [Module R P]

variable {k : Type} [Field k] [Algebra k R] [FiniteDimensional k R]
  [Module k M] [IsScalarTower k R M] [FiniteDimensional k M]

def finiteCoinducedEmbedding : M →ₗ[R] (Fin (Module.finrank k M) → DualBimodule k R) :=
  LinearMap.pi (fun i => DualBimodule.coinduce ((Module.finBasis k M).coord i))

omit [FiniteDimensional k R] in
lemma finiteCoinducedEmbedding_injective :
    Function.Injective (finiteCoinducedEmbedding (k := k) (R := R) (M := M)) := by
  intro x y h
  apply (Module.finBasis k M).repr.injective
  ext i
  have hi := congrArg (fun F : Fin (Module.finrank k M) → DualBimodule k R => F i 1) h
  simpa only [finiteCoinducedEmbedding, LinearMap.pi_apply, DualBimodule.coinduce_apply,
    one_smul, Module.Basis.coord_apply] using hi

end Tachikawa



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M : Type} [AddCommGroup M] [Module R M]

namespace SymmetrizingForm
variable [FiniteDimensional k R] (t : SymmetrizingForm (k := k) (R := R))
variable [Module k M] [IsScalarTower k R M] [FiniteDimensional k M]

def freeEmbedding : M →ₗ[R] (Fin (Module.finrank k M) → R) :=
  (LinearEquiv.piCongrRight (fun _ : Fin (Module.finrank k M) =>
    t.dualEquiv.symm)).toLinearMap.comp (finiteCoinducedEmbedding (k := k) (R := R))

lemma freeEmbedding_injective : Function.Injective (t.freeEmbedding (M := M)) :=
  (LinearEquiv.piCongrRight (fun _ : Fin (Module.finrank k M) =>
    t.dualEquiv.symm)).injective.comp finiteCoinducedEmbedding_injective

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits

variable {R : Type*} [Ring R]

def resolutionOfExact (M : ModuleCat R) (P : ℕ → ModuleCat R)
    (d : ∀ n, P (n+1) ⟶ P n) (ε : P 0 ⟶ M)
    (hd : ∀ n, Function.Exact (d (n+1)) (d n))
    (hε : Function.Exact (d 0) ε) (surj : Function.Surjective ε)
    (proj : ∀ n, Projective (P n)) : ProjectiveResolution M := by
  let sq : ∀ n, d (n+1) ≫ d n = 0 := fun n => ModuleCat.hom_ext <| LinearMap.ext <|
    (hd n).apply_apply_eq_zero
  let K := ChainComplex.of P d sq
  let π : K ⟶ (ChainComplex.single₀ (ModuleCat R)).obj M :=
    (ChainComplex.toSingle₀Equiv _ _).symm ⟨ε, by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact hε.apply_apply_eq_zero⟩
  refine {complex := K, π := π, projective := proj, quasiIso := ⟨fun n => ?_⟩}
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) (by simp; rfl) (by rfl)]
    · constructor
      · apply (ShortComplex.moduleCat_exact_iff _).2
        change ∀ x : P 0, ε x = 0 → ∃ y : P 1, K.d 1 0 y = x
        have hk : K.d 1 0 = d 0 := ChainComplex.of_d P d 0
        rw [hk]
        exact fun x => (hε x).mp
      · change Epi ε
        exact (ModuleCat.epi_iff_surjective ε).2 surj
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
      apply (ShortComplex.moduleCat_exact_iff _).2
      change ∀ x : P (n+1), K.d (n+1) n x = 0 → ∃ y, K.d (n+2) (n+1) y = x
      have hk₁ : K.d (n+1) n = d n := ChainComplex.of_d _ _ _
      have hk₂ : K.d (n+2) (n+1) = d (n+1) := ChainComplex.of_d _ _ _
      rw [hk₁, hk₂]
      exact fun x => (hd n x).mp
    · exact ChainComplex.exactAt_succ_single_obj _ _

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Tensor
attribute [-instance] _root_.OAI.Tachikawa.BalancedTensor.rightModule _root_.OAI.Tachikawa.FiniteModule.instAddCommGroupCarrierObj _root_.OAI.Tachikawa.FiniteModule.instIsScalarTowerCarrierObj _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped TensorProduct
open TensorProduct
namespace Tachikawa

namespace BalancedTensor
variable {k R S M N P : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N]

variable [AddCommGroup P] [Module k P] [Module S P] [IsScalarTower k S P]

instance instFiniteDimensionalT [FiniteDimensional k M] [FiniteDimensional k N] :
    FiniteDimensional k (T (k := k) (R := R) (S := S) (M := M) (N := N)) := by
  change FiniteDimensional k
    ((M ⊗[k] N) ⧸ relations (k := k) (R := R) (S := S))
  exact Module.Finite.quotient k (relations (k := k) (R := R) (S := S))

end BalancedTensor
end Tachikawa

end


noncomputable section
open scoped TensorProduct
namespace Tachikawa.BalancedTensor
variable {k R S M N N' N'' : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
  [AddCommGroup N''] [Module k N''] [Module R N''] [IsScalarTower k R N'']

lemma mapRight_split (f : N →ₗ[R] N') (g : N' →ₗ[R] N) (h : g.comp f = LinearMap.id) :
    (mapRight (k := k) (S := S) (M := M) g).comp (mapRight (k := k) (S := S) f) = LinearMap.id := by
  rw [← mapRight_comp, h, mapRight_id]

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R N N' : Type*} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']

variable (ι : Type*) [Fintype ι]

def freeInv : (ι → N) →ₗ[k] T (k := k) (R := R) (S := k) (M := ι → R) (N := N) := by
  classical
  exact ∑ i, (mk (k := k) (R := R) (S := k) (Pi.single i (1:R))).comp (LinearMap.proj i)

lemma freeEval_freeInv (x : ι → N) : freeEval (k := k) (R := R) ι (freeInv (k := k) (R := R) ι x) = x := by
  classical
  ext i
  simp [freeInv, freeEval_mk, Pi.single_apply]

lemma freeInv_freeEval (x : T (k := k) (R := R) (S := k) (M := ι → R) (N := N)) :
    freeInv ι (freeEval ι x) = x := by
  classical
  induction x using induction_on with
  | h0 => simp
  | ht m n =>
    simp only [freeInv, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, freeEval_mk]
    change (∑ i, (mk (k := k) (R := R) (S := k) (Pi.single i (1:R))) (m i • n)) = mk m n
    simp_rw [← balance]
    have hm : (∑ i, (MulOpposite.op (m i)) • (Pi.single i (1:R))) = m := by
      ext j
      simp [Pi.single_apply, apply_ite]
    rw [← LinearMap.sum_apply, ← map_sum, hm]
  | ha x y hx hy => simp only [map_add, hx, hy]

def freeEquiv : T (k := k) (R := R) (S := k) (M := ι → R) (N := N) ≃ₗ[k] (ι → N) :=
  LinearEquiv.ofLinearMap (freeEval ι) (freeInv ι)
    (by apply LinearMap.ext; exact freeEval_freeInv (k := k) (R := R) ι)
    (by apply LinearMap.ext; exact freeInv_freeEval ι)

lemma freeEquiv_mapRight (f : N →ₗ[R] N')
    (x : T (k := k) (R := R) (S := k) (M := ι → R) (N := N)) (i : ι) :
    freeEquiv ι (mapRight (k := k) (S := k) f x) i = f (freeEquiv ι x i) := by
  induction x using induction_on with
  | h0 => simp
  | ht m n => exact (f.map_smul (m i) n).symm
  | ha x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Tachikawa.BalancedTensor

end


noncomputable section
namespace Tachikawa.BalancedTensor
variable {k R S M M' N N' N'' : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k S M']
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
  [AddCommGroup N''] [Module k N''] [Module R N''] [IsScalarTower k R N'']

omit [IsScalarTower k Rᵐᵒᵖ M] in
lemma mapLeft_mapRight (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) (g : N →ₗ[R] N') :
    (mapLeft (k := k) f hf).comp (mapRight (k := k) (S := S) g) =
      (mapRight (k := k) (S := S) g).comp (mapLeft (k := k) f hf) := by
  apply hom_ext
  intro m n
  rfl

lemma free_mapRight_exact (ι : Type) [Fintype ι]
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (he : Function.Exact f g) :
    Function.Exact (mapRight (k := k) (S := k) (M := ι → R) f)
      (mapRight (k := k) (S := k) (M := ι → R) g) := by
  intro x
  constructor
  · intro hx
    have hz : ∀ i, g (freeEquiv ι x i) = 0 := by
      intro i
      rw [← freeEquiv_mapRight, hx, map_zero]
      rfl
    choose y hy using fun i => (he (freeEquiv ι x i)).mp (hz i)
    refine ⟨(freeEquiv (k := k) (R := R) ι).symm y, ?_⟩
    apply (freeEquiv (k := k) (R := R) ι).injective
    ext i
    rw [freeEquiv_mapRight, LinearEquiv.apply_symm_apply]
    exact hy i
  · rintro ⟨y,rfl⟩
    apply (freeEquiv (k := k) (R := R) ι).injective
    ext i
    rw [freeEquiv_mapRight, freeEquiv_mapRight, map_zero]
    exact (he _).mpr ⟨_,rfl⟩

lemma field_mapRight_exact [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (he : Function.Exact f g) :
    Function.Exact (mapRight (k := k) (S := k) (M := M) f)
      (mapRight (k := k) (S := k) (M := M) g) := by
  let c := finiteFreeCover (R := Rᵐᵒᵖ) (M := M)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let e := oppositeFree (R := R) (Fin c.rank)
  let u := e.toLinearMap.comp i
  let p := c.map.comp e.symm.toLinearMap
  have hp : p.comp u = LinearMap.id := by
    ext x
    exact LinearMap.congr_fun hi x
  let U {L : Type} [AddCommGroup L] [Module k L] [Module R L] :=
    mapLeft (k := k) (R := R) (S := k) (N := L) (u.restrictScalars k) u.map_smul
  let P {L : Type} [AddCommGroup L] [Module k L] [Module R L] :=
    mapLeft (k := k) (R := R) (S := k) (N := L) (p.restrictScalars k) p.map_smul
  have hPU {L : Type} [AddCommGroup L] [Module k L] [Module R L] :
      (P (L := L)).comp (U (L := L)) = LinearMap.id := by
    apply hom_ext
    intro m n
    change mk (k := k) (R := R) (S := k) (p (u m)) n = mk m n
    exact congrArg (fun z => mk (k := k) (R := R) (S := k) z n) (LinearMap.congr_fun hp m)
  intro x
  constructor
  · intro hx
    have hUx : mapRight (k := k) (S := k) g (U x) = 0 := by
      dsimp only [U]
      rw [← LinearMap.comp_apply, ← mapLeft_mapRight (u.restrictScalars k) u.map_smul g]
      change U (mapRight (k := k) (S := k) g x) = 0
      rw [hx,map_zero]
    obtain ⟨y,hy⟩ := (free_mapRight_exact (k := k) (Fin c.rank) f g he (U x)).mp hUx
    refine ⟨P y, ?_⟩
    dsimp only [P]
    rw [← LinearMap.comp_apply, ← mapLeft_mapRight (p.restrictScalars k) p.map_smul f]
    change P (mapRight (k := k) (S := k) f y) = x
    rw [hy]
    exact LinearMap.congr_fun hPU x
  · rintro ⟨y,rfl⟩
    rw [← LinearMap.comp_apply, ← mapRight_comp, he.linearMap_comp_eq_zero, mapRight_zero]
    rfl

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R S M : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  (ι : Type) [Fintype ι]

def rightFreeInv : (ι → M) →ₗ[S] T (k := k) (R := R) (S := S) (M := M) (N := ι → R) := by
  classical
  exact ∑ i, ((mk (k := k) (R := R) (S := S)).flip (Pi.single i (1:R))).comp (LinearMap.proj i)

lemma rightFreeEval_inv (x : ι → M) : rightFreeEval (k := k) (R := R) (S := S) ι (rightFreeInv (k := k) (R := R) (S := S) ι x) = x := by
  classical
  ext i
  simp only [rightFreeInv, map_sum, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, LinearMap.proj_apply, rightFreeEval_mk, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ h
    simp [Ne.symm h]
  · simp

lemma rightFreeInv_eval (x : T (k := k) (R := R) (S := S) (M := M) (N := ι → R)) :
    rightFreeInv ι (rightFreeEval ι x) = x := by
  classical
  induction x using induction_on with
  | h0 => simp
  | ht m n =>
    simp only [rightFreeInv, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, rightFreeEval_mk, LinearMap.flip_apply]
    simp_rw [balance]
    have hn : (∑ i, n i • Pi.single i (1:R)) = n := by
      ext j
      simp [Pi.single_apply, apply_ite]
    rw [← map_sum, hn]
  | ha x y hx hy => simp only [map_add, hx, hy]

def rightFreeEquiv : T (k := k) (R := R) (S := S) (M := M) (N := ι → R) ≃ₗ[S] (ι → M) :=
  { rightFreeEval (k := k) (R := R) (S := S) (M := M) ι with
    invFun := rightFreeInv (k := k) (R := R) (S := S) (M := M) ι
    left_inv := rightFreeInv_eval ι
    right_inv := rightFreeEval_inv ι }

variable {N : Type} [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]

lemma map_projective [Module.Projective S M] [Module.Finite R N] [Module.Projective R N] :
    Module.Projective S (T (k := k) (R := R) (S := S) (M := M) (N := N)) := by
  let c := finiteFreeCover (R := R) (M := N)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let : Module.Projective S (Fin c.rank → M) :=
    Module.Projective.of_equiv' DFinsupp.linearEquivFunOnFintype
  let : Module.Projective S (T (k := k) (R := R) (S := S) (M := M) (N := Fin c.rank → R)) :=
    Module.Projective.of_equiv' (rightFreeEquiv (k := k) (R := R) (S := S) (M := M) (Fin c.rank)).symm
  exact Module.Projective.of_split (mapRight (k := k) (S := S) i)
    (mapRight (k := k) (S := S) c.map) (mapRight_split i c.map hi)

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S M : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M] [IsScalarTower k S M]

instance instAdditiveModuleCatFunctor : (functor (k := k) (R := R) (S := S) (M := M)).Additive where
  map_add {_X _Y f g} := ModuleCat.hom_ext (mapRight_add f.hom g.hom)




instance instLinearModuleCatFunctor : (functor (k := k) (R := R) (S := S) (M := M)).Linear k where
  map_smul {X Y} f c := by
    apply ModuleCat.hom_ext
    apply hom_ext
    intro m x
    change mk (k := k) (R := R) (S := S) m ((algebraMap k R c) • f x) =
      (algebraMap k S c) • mk m (f x)
    rw [IsScalarTower.algebraMap_smul R,IsScalarTower.algebraMap_smul S]
    exact (mk m).map_smul c (f x)
end Tachikawa.BalancedTensor



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace Enveloping
variable (k R S : Type) [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

variable {k R S}

lemma tmul_smul (M : ModuleCat (Alg k R S)) (r : R) (s : Sᵐᵒᵖ) (x : Obj M) :
    (r ⊗ₜ[k] s) • x = r • s • x := by
  change _ = (r ⊗ₜ[k] (1:Sᵐᵒᵖ)) • ((1:R) ⊗ₜ[k] s) • x
  rw [← mul_smul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
end Enveloping

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def rightFunctor : ModuleCat (Alg k R S) ⥤ ModuleCat Sᵐᵒᵖ where
  obj M := ModuleCat.of Sᵐᵒᵖ (Obj M)
  map f := ModuleCat.ofHom (rightMap f)

end Tachikawa.Enveloping

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
attribute [-instance] _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

namespace FiniteModule

variable (M : FiniteModule k R)

variable (t : SymmetrizingForm (k := k) (R := R))

def embed : M →ₗ[R] (Fin (Module.finrank k M) → R) := t.freeEmbedding
lemma embed_injective : Function.Injective (M.embed t) := t.freeEmbedding_injective

def cosyzygy : FiniteModule k R where
  obj := ModuleCat.of R ((Fin (Module.finrank k M) → R) ⧸ LinearMap.range (M.embed t))
  finite := inferInstanceAs (Module.Finite R ((Fin (Module.finrank k M) → R) ⧸ LinearMap.range (M.embed t)))

def negative : ℕ → FiniteModule k R
  | 0 => M
  | n+1 => (negative n).cosyzygy t

abbrev negTerm (n : ℕ) := Fin (Module.finrank k (M.negative t n)) → R

def negDifferential (n : ℕ) : M.negTerm t n →ₗ[R] M.negTerm t (n+1) :=
  ((M.negative t (n+1)).embed t).comp (LinearMap.range ((M.negative t n).embed t)).mkQ

def middle : M.posTerm 0 →ₗ[R] M.negTerm t 0 := (M.embed t).comp M.cover.map

lemma neg_exact (n : ℕ) : Function.Exact (M.negDifferential t n) (M.negDifferential t (n+1)) := by
  intro x
  constructor
  · intro hx
    have hz : (LinearMap.range ((M.negative t (n+1)).embed t)).mkQ x = 0 :=
      (M.negative t (n+2)).embed_injective t (hx.trans ((M.negative t (n+2)).embed t).map_zero.symm)
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨z, hz⟩ := (Submodule.mkQ_surjective (LinearMap.range ((M.negative t n).embed t))) y
    refine ⟨z, ?_⟩
    change (M.negative t (n+1)).embed t ((LinearMap.range ((M.negative t n).embed t)).mkQ z) = x
    exact (congrArg ((M.negative t (n+1)).embed t) hz).trans hy
  · rintro ⟨y, rfl⟩
    apply ((M.negative t (n+2)).embed t).map_eq_zero_iff ((M.negative t (n+2)).embed_injective t) |>.mpr
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨_, rfl⟩

lemma middle_exact_left : Function.Exact (M.posDifferential 0) (M.middle t) := by
  intro x
  change M.embed t (M.cover.map x) = 0 ↔ _
  rw [map_eq_zero_iff _ (M.embed_injective t)]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (M.positive 1).cover.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, rfl⟩
    exact ((M.positive 1).cover.map y).property

lemma middle_exact_right : Function.Exact (M.middle t) (M.negDifferential t 0) := by
  intro x
  constructor
  · intro hx
    have hz : (LinearMap.range (M.embed t)).mkQ x = 0 :=
      (M.negative t 1).embed_injective t (hx.trans ((M.negative t 1).embed t).map_zero.symm)
    obtain ⟨y, rfl⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨z, rfl⟩ := M.cover.surjective y
    exact ⟨z, rfl⟩
  · rintro ⟨y, rfl⟩
    apply ((M.negative t 1).embed t).map_eq_zero_iff ((M.negative t 1).embed_injective t) |>.mpr
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨M.cover.map y, rfl⟩

def term : ℤ → ModuleCat R
  | .ofNat n => ModuleCat.of R (M.posTerm n)
  | .negSucc n => ModuleCat.of R (M.negTerm t n)

def differential (j : ℤ) : M.term t (j+1) ⟶ M.term t j := by
  cases j with
  | ofNat n => exact ModuleCat.ofHom (M.posDifferential n)
  | negSucc n =>
    cases n with
    | zero => exact ModuleCat.ofHom (M.middle t)
    | succ n =>
      exact ModuleCat.ofHom (M.negDifferential t n)

lemma differential_exact (j : ℤ) :
    Function.Exact (M.differential t (j+1)) (M.differential t j) := by
  cases j with
  | ofNat n => exact M.pos_exact n
  | negSucc n =>
    cases n with
    | zero => exact M.middle_exact_left t
    | succ n =>
      cases n with
      | zero => exact M.middle_exact_right t
      | succ n =>
        exact M.neg_exact t n

def complete : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (M.term t) (M.differential t) (fun j =>
    ModuleCat.hom_ext <| LinearMap.ext <| (M.differential_exact t j).apply_apply_eq_zero)

@[simp] lemma complete_d (j : ℤ) : (M.complete t).d (j+1) j = M.differential t j :=
  ChainComplex.of_d _ _ j

end FiniteModule
end Tachikawa



namespace Tachikawa.FiniteModule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R)

lemma pos_augmentation_exact : Function.Exact (M.posDifferential 0) M.cover.map := by
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := (M.positive 1).cover.surjective ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩
  · rintro ⟨y,rfl⟩
    exact ((M.positive 1).cover.map y).property

def projectiveResolution : ProjectiveResolution M.obj :=
  resolutionOfExact M.obj (fun n => ModuleCat.of R (M.posTerm n))
    (fun n => ModuleCat.ofHom (M.posDifferential n)) (ModuleCat.ofHom M.cover.map)
    M.pos_exact M.pos_augmentation_exact M.cover.surjective (fun _ => by infer_instance)

end Tachikawa.FiniteModule



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace BalancedTensor
variable {k R S U M N : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N] [Module Uᵐᵒᵖ N]
  [IsScalarTower k R N] [IsScalarTower k Uᵐᵒᵖ N] [SMulCommClass R Uᵐᵒᵖ N]

instance rightTower : IsScalarTower k Uᵐᵒᵖ (T (k := k) (R := R) (S := S) (M := M) (N := N)) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    induction x using induction_on with
    | h0 => simp
    | ht m n =>
      rw [right_smul_mk, IsScalarTower.algebraMap_smul]
      exact (mk m).map_smul c n
    | ha x y hx hy => simp only [smul_add, hx, hy]

instance rightComm : SMulCommClass S Uᵐᵒᵖ (T (k := k) (R := R) (S := S) (M := M) (N := N)) where
  smul_comm s u x := by
    change s • (rightAction (k := k) (R := R) (S := S) (M := M) (N := N) u) x =
      (rightAction (k := k) (R := R) (S := S) (M := M) (N := N) u) (s • x)
    exact ((rightAction (k := k) (R := R) (S := S) (M := M) (N := N) u).map_smul s x).symm

end BalancedTensor
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable {M N : Type} [AddCommGroup M] [Module k M] [Module R M] [Module Sᵐᵒᵖ M]
  [IsScalarTower k R M] [IsScalarTower k Sᵐᵒᵖ M] [SMulCommClass R Sᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module R N] [Module Sᵐᵒᵖ N]
  [IsScalarTower k R N] [IsScalarTower k Sᵐᵒᵖ N] [SMulCommClass R Sᵐᵒᵖ N]

def ofBimoduleHom (f : M →ₗ[R] N) (hf : ∀ (s : Sᵐᵒᵖ) m, f (s • m) = s • f m) :
    ofBimodule (k := k) (R := R) (S := S) M ⟶ ofBimodule (k := k) (R := R) (S := S) N :=
  ModuleCat.ofHom (X := ofBimodule (k := k) (R := R) (S := S) M)
    (Y := ofBimodule (k := k) (R := R) (S := S) N)
  { toFun := fun x => f x
    map_add' := f.map_add
    map_smul' a x := by
      change f ((action (k := k) (R := R) (S := S) M a) (show M from x)) =
        (action (k := k) (R := R) (S := S) N a) (f x)
      induction a using OAI.tensorInductionOn with
      | tmul r s =>
        change f (r • s • (show M from x)) = r • s • (show N from f x)
        exact (f.map_smul r _).trans (congrArg (fun z => r • z) (hf s x))
      | add a b ha hb =>
        rw [map_add, map_add]
        change f ((action (k := k) (R := R) (S := S) M a) x +
          (action (k := k) (R := R) (S := S) M b) x) = _
        exact (f.map_add _ _).trans (congrArg₂ (fun x y : N => x+y) ha hb) }

def reassembleIso (M : ModuleCat (Alg k R S)) :
    ofBimodule (k := k) (R := R) (S := S) (Obj M) ≅ M :=
  LinearEquiv.toModuleIso (show (ofBimodule (k := k) (R := R) (S := S) (Obj M)) ≃ₗ[Alg k R S] M from
  { toFun := fun x => x
    invFun := fun x => x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' a x := by
      change (show M from (action (k := k) (R := R) (S := S) (Obj M) a) x) = a • (show M from x)
      induction a using OAI.tensorInductionOn with
      | tmul r s => exact (tmul_smul M r s x).symm
      | add a b ha hb =>
        rw [map_add, add_smul]
        exact congrArg₂ (fun x y : M => x+y) ha hb })

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R)

def evaluation : ModuleCat (Alg k S R) ⥤ ModuleCat S where
  obj := evalObj X
  map := evalMap X
  map_id M := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Twisting
attribute [-instance] _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

instance instIsScalarTowerMulOppositeBimod (φ : R →ₐ[k] S) : IsScalarTower k Rᵐᵒᵖ (Bimod φ) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (show S from x) * φ (algebraMap k R c) = c • (show S from x)
    rw [φ.commutes, Algebra.smul_def, Algebra.commutes]
instance instProjectiveBimod (φ : R →ₐ[k] S) : Module.Projective S (Bimod φ) :=
  inferInstanceAs (Module.Projective S S)
instance instFiniteDimensionalBimod (φ : R →ₐ[k] S) [FiniteDimensional k S] : FiniteDimensional k (Bimod φ) :=
  inferInstanceAs (FiniteDimensional k S)

variable (φ : R →ₐ[k] S)

lemma unit_naturality {N N' : ModuleCat.{0} R} (f : N ⟶ N') :
    f ≫ unit φ N' = unit φ N ≫ (res φ).map ((functor φ).map f) := by
  ext n
  rfl

instance instProjectiveCarrierObjModuleCatFunctorOfFinite (N : ModuleCat.{0} R) [Module.Finite R N] [Module.Projective R N] :
    Module.Projective S ((functor φ).obj N) := BalancedTensor.map_projective

instance instFiniteDimensionalCarrierObjModuleCatFunctor [FiniteDimensional k S] (N : ModuleCat.{0} R) [FiniteDimensional k N] :
    FiniteDimensional k ((functor φ).obj N) := Module.Finite.equiv (underlyingEquiv φ N).symm

end Tachikawa.AlgebraInduction



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def regular : ModuleCat (Alg k R R) := ofBimodule (k := k) (R := R) (S := R) R

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.FiniteModule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))

lemma embed_exact : Function.Exact (M.embed t) (M.negDifferential t 0) := by
  intro x
  constructor
  · intro hx
    have hz : (LinearMap.range (M.embed t)).mkQ x = 0 :=
      (M.negative t 1).embed_injective t (hx.trans ((M.negative t 1).embed t).map_zero.symm)
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  · rintro ⟨y,rfl⟩
    change (M.negative t 1).embed t ((LinearMap.range (M.embed t)).mkQ (M.embed t y)) = 0
    have hz : (LinearMap.range (M.embed t)).mkQ (M.embed t y) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨y,rfl⟩
    exact (congrArg ((M.negative t 1).embed t) hz).trans
      ((M.negative t 1).embed t).map_zero

def coresolution : InjectiveResolution M.obj :=
  coresolutionOfExact M.obj (fun n => ModuleCat.of R (M.negTerm t n))
    (fun n => ModuleCat.ofHom (M.negDifferential t n)) (ModuleCat.ofHom (M.embed t))
    (M.neg_exact t) (M.embed_exact t) (M.embed_injective t) (by
      intro n
      let : Module.Injective R R := t.injective
      exact Module.injective_object_of_injective_module R (M.negTerm t n))

@[simp] lemma coresolution_d (n : ℕ) :
    (M.coresolution t).cocomplex.d n (n+1) = ModuleCat.ofHom (M.negDifferential t n) := by
  dsimp only [coresolution,coresolutionOfExact]
  exact CochainComplex.of_d _ _ n

@[simp] lemma coresolution_ι :
    (M.coresolution t).ι.f 0 = ModuleCat.ofHom (M.embed t) := rfl
end Tachikawa.FiniteModule



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_TwistHom
attribute [-instance] _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.FiniteModule
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
open SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]
  (M : FiniteModule k R) (t : SymmetrizingForm (k := k) (R := R))

@[simp] lemma projectiveResolution_d (n : ℕ) :
    M.projectiveResolution.complex.d (n+1) n = ModuleCat.ofHom (M.posDifferential n) := by
  dsimp only [projectiveResolution,resolutionOfExact]
  exact ChainComplex.of_d _ _ n
@[simp] lemma projectiveResolution_π : M.projectiveResolution.π.f 0 = ModuleCat.ofHom M.cover.map := rfl

end Tachikawa.FiniteModule



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterTensor
attribute [-instance] _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
set_option backward.isDefEq.respectTransparency true



namespace Tachikawa.AlgebraInduction
open CategoryTheory CategoryTheory.Limits
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)

lemma res_map_exact (T : ShortComplex (ModuleCat.{0} S)) (h : T.Exact) :
    (T.map (res φ)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

instance instPreservesFiniteLimitsModuleCatRes : PreservesFiniteLimits (res φ) := by
  have h := ((Functor.exact_tfae (res φ)).out (2-1) (4-1)).mp (res_map_exact φ)
  exact h.1
instance instPreservesFiniteColimitsModuleCatRes : PreservesFiniteColimits (res φ) := by
  have h := ((Functor.exact_tfae (res φ)).out (2-1) (4-1)).mp (res_map_exact φ)
  exact h.2

end Tachikawa.AlgebraInduction



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B S T : Type} [Field k] [Ring A] [Ring B] [Ring S] [Ring T]
  [Algebra k A] [Algebra k B] [Algebra k S] [Algebra k T]
  (φ : A →ₐ[k] S) (ψ : B →ₐ[k] T) (M : ModuleCat A) (N : ModuleCat B)

def inductionPure : AlgebraInduction.Bimod φ →ₗ[k] M →ₗ[k]
    AlgebraInduction.Bimod ψ →ₗ[k] N →ₗ[k] inductionSource φ ψ M N where
  toFun s :=
    { toFun := fun x =>
        { toFun := fun t =>
            { toFun := fun y => inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
              map_add' := by
                intro y z
                simp only [TensorProduct.tmul_add, map_add]
              map_smul' := by
                intro c y
                simp only [TensorProduct.tmul_smul, map_smul]
                rfl }
          map_add' := by
            intro t u
            ext y
            change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] ((show T from t)+(show T from u))) (x ⊗ₜ[k] y) = _
            erw [TensorProduct.tmul_add, map_add, LinearMap.add_apply]
          map_smul' := by
            intro c t
            ext y
            change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (c • (show T from t))) (x ⊗ₜ[k] y) = _
            erw [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply] }
      map_add' := by
        intro x z
        ext t y
        change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) ((x+z) ⊗ₜ[k] y) = _
        simp only [TensorProduct.add_tmul, map_add]
        rfl
      map_smul' := by
        intro c x
        ext t y
        change inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) ((c • x) ⊗ₜ[k] y) = _
        simp only [← TensorProduct.smul_tmul', map_smul]
        rfl }
  map_add' s u := by
    refine LinearMap.ext fun x => LinearMap.ext fun t => LinearMap.ext fun y => ?_
    change inductionSourceMk φ ψ M N (((show S from s)+(show S from u)) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y) =
      inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y) +
        inductionSourceMk φ ψ M N ((show S from u) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
    rw [TensorProduct.add_tmul, map_add, LinearMap.add_apply]
  map_smul' c s := by
    refine LinearMap.ext fun x => LinearMap.ext fun t => LinearMap.ext fun y => ?_
    change inductionSourceMk φ ψ M N ((c • (show S from s)) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y) =
      c • inductionSourceMk φ ψ M N ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
    rw [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply]

lemma inductionPure_balance_left (a : A) (s : AlgebraInduction.Bimod φ) (x : M) :
    inductionPure φ ψ M N (MulOpposite.op a • s) x = inductionPure φ ψ M N s (a • x) := by
  ext t y
  have h := BalancedTensor.balance (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
    (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
    (N := ((bifunctor k A B).obj M).obj N)
    (a ⊗ₜ[k] (1 : B)) ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
  have h₁ : MulOpposite.op (a ⊗ₜ[k] (1 : B)) •
      (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from
        ((show S from s) ⊗ₜ[k] (show T from t))) = ((show S from s) * φ a) ⊗ₜ[k] (show T from t) := by
    change ((show S from s) ⊗ₜ[k] (show T from t)) * (φ a ⊗ₜ[k] ψ 1) = _
    erw [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h₂ : (a ⊗ₜ[k] (1 : B)) •
      (show ((bifunctor k A B).obj M).obj N from x ⊗ₜ[k] y) = (a • x) ⊗ₜ[k] y := by
    change (a • x) ⊗ₜ[k] ((1 : B) • y) = _
    rw [one_smul]
  rw [h₁, h₂] at h
  exact h

lemma inductionPure_balance_right (b : B) (s : AlgebraInduction.Bimod φ) (x : M)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionPure φ ψ M N s x (MulOpposite.op b • t) y =
      inductionPure φ ψ M N s x t (b • y) := by
  have h := BalancedTensor.balance (k := k) (R := A ⊗[k] B) (S := S ⊗[k] T)
    (M := AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ))
    (N := ((bifunctor k A B).obj M).obj N)
    ((1 : A) ⊗ₜ[k] b) ((show S from s) ⊗ₜ[k] (show T from t)) (x ⊗ₜ[k] y)
  have h₁ : MulOpposite.op ((1 : A) ⊗ₜ[k] b) •
      (show AlgebraInduction.Bimod (Algebra.TensorProduct.map φ ψ) from
        ((show S from s) ⊗ₜ[k] (show T from t))) = (show S from s) ⊗ₜ[k] ((show T from t) * ψ b) := by
    change ((show S from s) ⊗ₜ[k] (show T from t)) * (φ 1 ⊗ₜ[k] ψ b) = _
    erw [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have h₂ : ((1 : A) ⊗ₜ[k] b) •
      (show ((bifunctor k A B).obj M).obj N from x ⊗ₜ[k] y) = x ⊗ₜ[k] (b • y) := by
    change ((1 : A) • x) ⊗ₜ[k] (b • y) = _
    rw [one_smul]
  rw [h₁, h₂] at h
  exact h

def inductionLeftLift : BalancedTensor.T (k := k) (R := A) (S := S) (M := AlgebraInduction.Bimod φ) (N := M) →ₗ[k]
    AlgebraInduction.Bimod ψ →ₗ[k] N →ₗ[k] inductionSource φ ψ M N :=
  (BalancedTensor.liftGround (S := S) (inductionPure φ ψ M N)
    (inductionPure_balance_left φ ψ M N))

@[simp] lemma inductionLeftLift_mk (s : AlgebraInduction.Bimod φ) (x : M)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionLeftLift φ ψ M N (BalancedTensor.mk (k := k) (R := A) (S := S) s x) t y =
      inductionPure φ ψ M N s x t y := rfl

lemma inductionLeftLift_balance (z : BalancedTensor.T (k := k) (R := A) (S := S) (M := AlgebraInduction.Bimod φ) (N := M)) (b : B)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionLeftLift φ ψ M N z (MulOpposite.op b • t) y =
      inductionLeftLift φ ψ M N z t (b • y) := by
  induction z using BalancedTensor.induction_on with
  | h0 => simp
  | ha z w hz hw => simp only [map_add, LinearMap.add_apply, hz, hw]
  | ht s x => exact inductionPure_balance_right φ ψ M N b s x t y

def inductionRightLift
    (z : BalancedTensor.T (k := k) (R := A) (S := S) (M := AlgebraInduction.Bimod φ) (N := M)) :
    BalancedTensor.T (k := k) (R := B) (S := T) (M := AlgebraInduction.Bimod ψ) (N := N) →ₗ[k]
      inductionSource φ ψ M N :=
  BalancedTensor.liftGround (S := T) (inductionLeftLift φ ψ M N z)
    (inductionLeftLift_balance φ ψ M N z)

lemma inductionRightLift_add (z w : BalancedTensor.T (k := k) (R := A) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := M)) :
    inductionRightLift φ ψ M N (z+w) =
      inductionRightLift φ ψ M N z + inductionRightLift φ ψ M N w := by
  unfold inductionRightLift
  simp only [map_add]
  apply BalancedTensor.liftGround_add

lemma inductionRightLift_smul (c : k) (z : BalancedTensor.T (k := k) (R := A) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := M)) :
    inductionRightLift φ ψ M N (c • z) = c • inductionRightLift φ ψ M N z := by
  unfold inductionRightLift
  simp only [map_smul]
  apply BalancedTensor.liftGround_smul

def inductionInverseBilinear : BalancedTensor.T (k := k) (R := A) (S := S)
    (M := AlgebraInduction.Bimod φ) (N := M) →ₗ[k]
    BalancedTensor.T (k := k) (R := B) (S := T) (M := AlgebraInduction.Bimod ψ) (N := N) →ₗ[k]
      inductionSource φ ψ M N where
  toFun := inductionRightLift φ ψ M N
  map_add' := inductionRightLift_add φ ψ M N
  map_smul' := inductionRightLift_smul φ ψ M N

def inductionInverseLinear : inductionTarget φ ψ M N →ₗ[k] inductionSource φ ψ M N :=
  (TensorProduct.lift (inductionInverseBilinear φ ψ M N)).comp
    ((TensorProduct.map (AlgebraInduction.underlyingEquiv φ M).toLinearMap
      (AlgebraInduction.underlyingEquiv ψ N).toLinearMap).comp
        (underlyingEquiv ((AlgebraInduction.functor φ).obj M)
          ((AlgebraInduction.functor ψ).obj N)).toLinearMap)

@[simp] lemma inductionInverseLinear_pure (s : AlgebraInduction.Bimod φ) (x : M)
    (t : AlgebraInduction.Bimod ψ) (y : N) :
    inductionInverseLinear φ ψ M N
      (BalancedTensor.mk (k := k) (R := A) (S := S) s x ⊗ₜ[k]
        BalancedTensor.mk (k := k) (R := B) (S := T) t y) =
      inductionSourceMk φ ψ M N (s ⊗ₜ[k] t) (x ⊗ₜ[k] y) := rfl

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

namespace Nakayama

variable [Module k M] [IsScalarTower k R M]

def evaluation : BalancedTensor.T (k := k) (R := R) (S := R)
    (M := DualBimodule k R) (N := M) →ₗ[R] Nakayama k R M :=
  BalancedTensor.lift evaluationBilinear evaluation_balanced

@[simp] lemma evaluation_mk (φ : DualBimodule k R) (m : M) (f : M →ₗ[R] R) :
    evaluation (BalancedTensor.mk φ m) f = φ (f m) := rfl

omit [Module k M] [IsScalarTower k R M] in

def map (f : M →ₗ[R] N) : Nakayama k R M →ₗ[R] Nakayama k R N where
  toFun ψ :=
    { toFun := fun g => ψ (g.comp f)
      map_add' := by
        intro g h
        change ψ (g.comp f + h.comp f) = ψ (g.comp f) + ψ (h.comp f)
        exact ψ.map_add _ _
      map_smul' := by
        intro c g
        change ψ (c • g.comp f) = c • ψ (g.comp f)
        exact ψ.map_smul c _ }
  map_add' := by intro ψ φ; ext g; rfl
  map_smul' := by intro r ψ; ext g; rfl

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma map_apply (f : M →ₗ[R] N) (ψ : Nakayama k R M) (g : N →ₗ[R] R) : map f ψ g = ψ (g.comp f) := rfl

variable [Module k N] [IsScalarTower k R N]

variable [FiniteDimensional k R]
local notation "V" => BalancedTensor.T (k := k) (R := R) (S := R) (M := DualBimodule k R) (N := M)

def paired (l : Module.Dual k V) (m : M) : Module.Dual k (Module.Dual k R) where
  toFun φ := l (BalancedTensor.mk (R := R) (S := R) (M := DualBimodule k R) φ m)
  map_add' φ ψ := by
    let φ' : DualBimodule k R := φ
    let ψ' : DualBimodule k R := ψ
    change l (BalancedTensor.mk (M := DualBimodule k R) (φ' + ψ') m) =
      l (BalancedTensor.mk φ' m) + l (BalancedTensor.mk ψ' m)
    rw [map_add, LinearMap.add_apply, map_add]
  map_smul' c φ := by
    change l (BalancedTensor.mk (M := DualBimodule k R) (c • φ) m) = c • l (BalancedTensor.mk (M := DualBimodule k R) φ m)
    have h : BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R) (c • φ) m =
        c • BalancedTensor.mk (M := DualBimodule k R) φ m := by
      exact congrArg (fun a : M →ₗ[k] V => a m)
        ((BalancedTensor.mk (k := k) (R := R) (S := R) (M := DualBimodule k R)).restrictScalars k |>.map_smul c φ)
    rw [h]
    exact l.map_smul c _

def transposeFun (l : Module.Dual k V) (m : M) : R := (Module.evalEquiv k R).symm (paired l m)

omit [IsScalarTower k R M] in
@[simp] lemma transposeFun_eval (l : Module.Dual k V) (m : M) (φ : DualBimodule k R) :
    φ (transposeFun l m) = l (BalancedTensor.mk φ m) :=
  Module.apply_evalEquiv_symm_apply k R φ (paired l m)

end Nakayama
end Tachikawa



namespace Tachikawa.Nakayama
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Z] [Module R Z] [Module k Z] [IsScalarTower k R Z]

def rankOne (a : P →ₗ[R] R) (z : Z) : P →ₗ[R] Z where
  toFun p := a p • z
  map_add' p q := by simp [add_smul]
  map_smul' r p := by simp [mul_smul]

@[simp] lemma rankOne_apply (a : P →ₗ[R] R) (z : Z) (p : P) : rankOne a z p = a p • z := rfl

def coevaluation : Module.Dual k (P →ₗ[R] Z) →ₗ[k] (Z →ₗ[R] Nakayama k R P) where
  toFun ψ :=
    { toFun := fun z =>
        { toFun := fun a => ψ (rankOne a z)
          map_add' := by
            intro a b
            rw [← ψ.map_add]
            congr 1
            ext p
            simp [add_smul]
          map_smul' := by
            intro c a
            rw [← ψ.map_smul]
            congr 1
            ext p
            simp [smul_assoc] }
      map_add' := by
        intro x y
        ext a
        change ψ (rankOne a (x+y)) = ψ (rankOne a x) + ψ (rankOne a y)
        rw [← ψ.map_add]
        congr 1
        ext p
        simp [smul_add]
      map_smul' := by
        intro r z
        ext a
        change ψ (rankOne a (r • z)) = ψ (rankOne (homRight r a) z)
        congr 1
        ext p
        simp [mul_smul] }
  map_add' := by intro x y; ext z a; rfl
  map_smul' := by intro c ψ; ext z a; rfl

@[simp] lemma coevaluation_apply (ψ : Module.Dual k (P →ₗ[R] Z)) (z : Z) (a : P →ₗ[R] R) :
    coevaluation ψ z a = ψ (rankOne a z) := rfl

variable (n : ℕ) (p : P →ₗ[R] (Fin n → R)) (s : (Fin n → R) →ₗ[R] P)
  (hs : s.comp p = LinearMap.id)

include hs in
lemma rankOne_sum (f : P →ₗ[R] Z) :
    ∑ i, rankOne ((LinearMap.proj i).comp p) (f (s (Pi.single i 1))) = f := by
  ext x
  simp only [LinearMap.sum_apply, rankOne_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  simpa only [map_sum, map_smul] using congrArg f (decomposed n p s hs x)

def homPair (g : Z →ₗ[R] Nakayama k R P) : Module.Dual k (P →ₗ[R] Z) where
  toFun f := ∑ i, g (f (s (Pi.single i 1))) ((LinearMap.proj i).comp p)
  map_add' := by intro a b; simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    simp only [LinearMap.smul_apply]
    simp only [← IsScalarTower.algebraMap_smul R c, map_smul, action_apply]
    have hh (a : P →ₗ[R] R) : homRight (k := k) (algebraMap k R c) a = c • a := by
      ext x
      simp [Algebra.mul_smul_comm, Algebra.algebraMap_eq_smul_one]
    simp only [hh, map_smul, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]

include hs in
lemma homPair_coevaluation (ψ : Module.Dual k (P →ₗ[R] Z)) :
    homPair n p s (coevaluation ψ) = ψ := by
  ext f
  change (∑ i, ψ (rankOne ((LinearMap.proj i).comp p) (f (s (Pi.single i 1))))) = ψ f
  rw [← map_sum, rankOne_sum n p s hs]

include hs in
lemma coevaluation_homPair (g : Z →ₗ[R] Nakayama k R P) :
    coevaluation (homPair n p s g) = g := by
  ext z a
  change (∑ i, g (a (s (Pi.single i 1)) • z) ((LinearMap.proj i).comp p)) = g z a
  simp only [map_smul, action_apply]
  rw [← map_sum]
  congr 1
  ext x
  simp only [LinearMap.sum_apply, homRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  have hx := congrArg a (decomposed n p s hs x)
  simpa only [map_sum, map_smul, smul_eq_mul] using hx

lemma coevaluation_bijective [Module.Finite R P] [Module.Projective R P] :
    Function.Bijective (coevaluation (k := k) (R := R) (P := P) (Z := Z)) := by
  let c := finiteFreeCover (R := R) (M := P)
  obtain ⟨i, hi⟩ := Module.projective_lifting_property c.map (LinearMap.id (R := R) (M := P)) c.surjective
  exact ⟨Function.LeftInverse.injective (homPair_coevaluation c.rank i c.map hi),
    Function.RightInverse.surjective (coevaluation_homPair c.rank i c.map hi)⟩

def homDualEquiv [Module.Finite R P] [Module.Projective R P] :
    (Z →ₗ[R] Nakayama k R P) ≃ₗ[k] Module.Dual k (P →ₗ[R] Z) :=
  (LinearEquiv.ofBijective coevaluation coevaluation_bijective).symm

end Tachikawa.Nakayama



namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {P Q Z : Type} [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [AddCommGroup Z] [Module R Z]
  [Module k Z] [IsScalarTower k R Z]

@[simp] lemma homPrecomp_apply (f : P →ₗ[R] Q) (g : Q →ₗ[R] Z) :
    homPrecomp (k := k) f g = g.comp f := rfl

namespace Nakayama

@[simp] lemma coevaluation_homDualEquiv [Module.Finite R P] [Module.Projective R P]
    (g : Z →ₗ[R] Nakayama k R P) : coevaluation (homDualEquiv g) = g :=
  (LinearEquiv.ofBijective coevaluation coevaluation_bijective).apply_symm_apply g

@[simp] lemma homDualEquiv_coevaluation [Module.Finite R P] [Module.Projective R P]
    (ψ : Module.Dual k (P →ₗ[R] Z)) : homDualEquiv (coevaluation ψ) = ψ :=
  (LinearEquiv.ofBijective coevaluation coevaluation_bijective).symm_apply_apply ψ

@[simp] lemma map_id : map (k := k) (LinearMap.id : P →ₗ[R] P) = LinearMap.id := by
  ext ψ a
  rfl

@[simp] lemma map_zero : map (k := k) (0 : P →ₗ[R] Q) = 0 := by
  ext ψ a
  change ψ (a.comp 0) = 0
  simp

end Nakayama
end Tachikawa



namespace Tachikawa
namespace TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]

def Obj (k R M : Type) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module R M] := M × Nakayama k R M

instance instAddCommGroupObj : AddCommGroup (Obj k R M) := inferInstanceAs (AddCommGroup (M × Nakayama k R M))
instance instModuleObj : Module R (Obj k R M) := inferInstanceAs (Module R (M × Nakayama k R M))

def act (a : TrivialExtension k R) (x : Obj k R M) : Obj k R M :=
  (a.fst • x.1, Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2)

instance instModuleTrivialExtensionObj : Module (TrivialExtension k R) (Obj k R M) where
  smul := act
  one_smul x := by
    apply Prod.ext
    · exact one_smul _ _
    · change Nakayama.evaluationBilinear (0 : DualBimodule k R) x.1 + (1:R) • x.2 = _
      simp
  mul_smul a b x := by
    apply Prod.ext
    · exact mul_smul _ _ _
    · change Nakayama.evaluationBilinear (a.fst • b.snd + MulOpposite.op b.fst • a.snd) x.1 +
        (a.fst*b.fst) • x.2 = Nakayama.evaluationBilinear a.snd (b.fst • x.1) +
          a.fst • (Nakayama.evaluationBilinear b.snd x.1 + b.fst • x.2)
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        Nakayama.evaluation_balanced, smul_add, mul_smul]
      abel
  smul_zero a := by
    apply Prod.ext
    · exact smul_zero _
    · change Nakayama.evaluationBilinear a.snd 0 + a.fst • (0 : Nakayama k R M) = 0
      simp
  smul_add a x y := by
    apply Prod.ext
    · exact smul_add _ _ _
    · change Nakayama.evaluationBilinear a.snd (x.1+y.1) + a.fst • (x.2+y.2) = _
      simp only [map_add, smul_add]
      change _ = (Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2) +
        (Nakayama.evaluationBilinear a.snd y.1 + a.fst • y.2)
      abel
  zero_smul x := by
    apply Prod.ext
    · exact zero_smul _ _
    · change Nakayama.evaluationBilinear (0 : DualBimodule k R) x.1 + (0:R) • x.2 = 0
      simp
  add_smul a b x := by
    apply Prod.ext
    · exact add_smul _ _ _
    · change Nakayama.evaluationBilinear (a.snd+b.snd) x.1 + (a.fst+b.fst) • x.2 = _
      simp only [map_add, LinearMap.add_apply, add_smul]
      change _ = (Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2) +
        (Nakayama.evaluationBilinear b.snd x.1 + b.fst • x.2)
      abel

@[simp] lemma inl_smul (r : R) (x : Obj k R M) :
    (TrivSqZeroExt.inl r : TrivialExtension k R) • x = r • x := by
  apply Prod.ext
  · rfl
  · change Nakayama.evaluationBilinear (0 : DualBimodule k R) x.1 + r • x.2 = _
    simp only [_root_.map_zero, LinearMap.zero_apply, zero_add]
    rfl

def unit : M →ₗ[R] Obj k R M := LinearMap.inl R M (Nakayama k R M)
def first : Obj k R M →ₗ[R] M := LinearMap.fst R M (Nakayama k R M)
def second : Obj k R M →ₗ[R] Nakayama k R M := LinearMap.snd R M (Nakayama k R M)

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma unit_apply (x : M) : unit (k := k) (R := R) x = (x,0) := rfl
omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma first_apply (x : Obj k R M) : first x = x.1 := rfl
omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma second_apply (x : Obj k R M) : second x = x.2 := rfl

def map (f : M →ₗ[R] N) : Obj k R M →ₗ[TrivialExtension k R] Obj k R N where
  toFun x := (f x.1, Nakayama.map f x.2)
  map_add' x y := by
    exact Prod.ext (f.map_add x.1 y.1) ((Nakayama.map f).map_add x.2 y.2)
  map_smul' a x := by
    apply Prod.ext
    · exact f.map_smul _ _
    · change Nakayama.map f (Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2) =
        Nakayama.evaluationBilinear a.snd (f x.1) + a.fst • Nakayama.map f x.2
      rw [map_add, map_smul]
      rfl

@[simp] lemma map_apply (f : M →ₗ[R] N) (x : Obj k R M) :
    map (k := k) f x = (f x.1, Nakayama.map f x.2) := rfl

end TrivialInduction
end Tachikawa



namespace Tachikawa.TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (n : ℕ)

def coordinateHom (i : Fin n) : R →ₗ[k] ((Fin n → R) →ₗ[R] R) where
  toFun r := (rightMultiply r).comp (LinearMap.proj i)
  map_add' r s := by ext x; simp [mul_add]
  map_smul' c r := by ext x; simp [Algebra.mul_smul_comm]

@[simp] lemma coordinateHom_apply (i : Fin n) (r : R) (x : Fin n → R) :
    coordinateHom (k := k) n i r x = x i*r := rfl

variable {M : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]

lemma map_id : map (k := k) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  ext x
  apply Prod.ext
  · rfl
  · exact LinearMap.congr_fun Nakayama.map_id x.2

lemma map_comp {N O : Type} [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
    [AddCommGroup O] [Module R O] [Module k O] [IsScalarTower k R O]
    (f : M →ₗ[R] N) (g : N →ₗ[R] O) :
    map (k := k) (g.comp f) = (map g).comp (map f) := rfl

end Tachikawa.TrivialInduction



namespace Tachikawa.TrivialInduction
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N P : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup P] [Module R P] [Module k P] [IsScalarTower k R P]

def restrict (f : Obj k R M →ₗ[TrivialExtension k R] Obj k R N) : M →ₗ[R] Obj k R N where
  toFun m := f (unit m)
  map_add' m n := by rw [map_add, map_add]
  map_smul' r m := by
    rw [map_smul, ← inl_smul, map_smul, inl_smul]
    rfl

@[simp] lemma restrict_apply (f : Obj k R M →ₗ[TrivialExtension k R] Obj k R N) (m : M) :
    restrict f m = f (unit m) := rfl

def lift (u : M →ₗ[R] Obj k R N) : Obj k R M →ₗ[TrivialExtension k R] Obj k R N where
  toFun x := ((u x.1).1, (u x.1).2 + Nakayama.map (first.comp u) x.2)
  map_add' x y := by
    apply Prod.ext
    · change (u (x.1+y.1)).1 = (u x.1).1+(u y.1).1
      rw [map_add]
      rfl
    · change (u (x.1+y.1)).2 + Nakayama.map (first.comp u) (x.2+y.2) = _
      rw [map_add, map_add]
      change ((u x.1).2+(u y.1).2) + (Nakayama.map (first.comp u) x.2+Nakayama.map (first.comp u) y.2) = _
      change ((u x.1).2+(u y.1).2) + (Nakayama.map (first.comp u) x.2+Nakayama.map (first.comp u) y.2) =
        ((u x.1).2 + Nakayama.map (first.comp u) x.2) + ((u y.1).2 + Nakayama.map (first.comp u) y.2)
      abel
  map_smul' a x := by
    apply Prod.ext
    · change (u (a.fst • x.1)).1 = a.fst • (u x.1).1
      rw [map_smul]
      rfl
    · change (u (a.fst • x.1)).2 + Nakayama.map (first.comp u)
        (Nakayama.evaluationBilinear a.snd x.1 + a.fst • x.2) =
        Nakayama.evaluationBilinear a.snd (u x.1).1 + a.fst • ((u x.1).2 + Nakayama.map (first.comp u) x.2)
      rw [map_smul, map_add, map_smul, smul_add]
      have he : Nakayama.map (first.comp u) (Nakayama.evaluationBilinear a.snd x.1) =
          Nakayama.evaluationBilinear a.snd (u x.1).1 := rfl
      rw [he]
      change a.fst • (u x.1).2 + (_ + _) = _
      abel

@[simp] lemma lift_unit (u : M →ₗ[R] Obj k R N) (m : M) : lift u (unit m) = u m := by
  apply Prod.ext
  · rfl
  · change (u m).2 + Nakayama.map (first.comp u) 0 = (u m).2
    rw [_root_.map_zero, add_zero]

@[simp] lemma restrict_lift (u : M →ₗ[R] Obj k R N) : restrict (lift u) = u := by
  ext m
  exact lift_unit u m

end Tachikawa.TrivialInduction



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

namespace TrivialInflation
variable {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
instance instModuleTrivialExtension : Module (TrivialExtension k R) (TrivialInflation k R M) :=
  Module.compHom M (TrivSqZeroExt.fstHom k R (DualBimodule k R)).toRingHom

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma smul_def (a : TrivialExtension k R) (x : TrivialInflation k R M) :
    a • x = (a.fst • (show M from x) : M) := rfl

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma inl_smul (r : R) (x : TrivialInflation k R M) :
    (TrivSqZeroExt.inl r : TrivialExtension k R) • x = r • x := rfl

omit [Module k M] [IsScalarTower k R M] in
@[simp] lemma inr_smul (φ : DualBimodule k R) (x : TrivialInflation k R M) :
    (TrivSqZeroExt.inr φ : TrivialExtension k R) • x = 0 := zero_smul R x

end TrivialInflation
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Period
attribute [-instance] _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
namespace TrivialInduction

@[simp] lemma map_zero {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
    [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N] :
    map (k := k) (0 : M →ₗ[R] N) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · exact LinearMap.congr_fun Nakayama.map_zero x.2

def functor : ModuleCat R ⥤ ModuleCat (TrivialExtension k R) where
  obj M := ModuleCat.of (TrivialExtension k R) (Obj k R M)
  map f := ModuleCat.ofHom (map f.hom)
  map_id _ := ModuleCat.hom_ext map_id
  map_comp f g := ModuleCat.hom_ext (map_comp f.hom g.hom)

end TrivialInduction

namespace C
variable [CharP k 2] (q : k)
abbrev T := TrivialExtension k (C k q)

end C
end Tachikawa



namespace Tachikawa.TrivialExtension
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

def scaleDual (H : k) (hH : H ≠ 0) : TrivialExtension k R ≃ₐ[k] TrivialExtension k R where
  toFun a := ⟨a.fst, H • a.snd⟩
  invFun a := ⟨a.fst, H⁻¹ • a.snd⟩
  left_inv a := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · change H⁻¹ • (H • a.snd) = a.snd
      simp [smul_smul, hH]
  right_inv a := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · change H • (H⁻¹ • a.snd) = a.snd
      simp [smul_smul, hH]
  map_mul' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · ext r
      change H * (b.snd (r*a.fst) + a.snd (b.fst*r)) =
        H*b.snd (r*a.fst) + H*a.snd (b.fst*r)
      exact mul_add _ _ _
  map_add' a b := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · exact smul_add H a.snd b.snd
  commutes' c := by
    refine TrivSqZeroExt.ext ?_ ?_
    · rfl
    · exact smul_zero H

@[simp] lemma scaleDual_fst (H : k) (hH : H ≠ 0) (a : TrivialExtension k R) :
    (scaleDual H hH a).fst = a.fst := rfl
@[simp] lemma scaleDual_snd (H : k) (hH : H ≠ 0) (a : TrivialExtension k R) :
    (scaleDual H hH a).snd = H • a.snd := rfl
@[simp] lemma scaleDual_inl (H : k) (hH : H ≠ 0) (a : R) :
    scaleDual H hH (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl a := by
  refine TrivSqZeroExt.ext ?_ ?_
  · rfl
  · exact smul_zero H
@[simp] lemma scaleDual_inr (H : k) (hH : H ≠ 0) (a : DualBimodule k R) :
    scaleDual H hH (TrivSqZeroExt.inr a) = TrivSqZeroExt.inr (H • a) := rfl

end Tachikawa.TrivialExtension



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open scoped TensorProduct
namespace Construction
variable {k : Type*} [Field k] (q : k)

abbrev T := TrivialExtension k (C k q)
abbrev E := T q ⊗[k] T q

def characterT : T q →ₐ[k] k :=
  (C.character q).comp (TrivSqZeroExt.fstHom k (C k q) (DualBimodule k (C k q)))
def characterE : E q →ₐ[k] k :=
  Algebra.TensorProduct.productMap (characterT q) (characterT q)

instance instModuleEX : Module (E q) (X q) := Module.compHom (X q) (characterE q).toRingHom

@[simp] lemma X_smul (a : E q) (x : X q) : a • x = (characterE q a : k) • x := rfl

def sigma (H : k) (hH : H ≠ 0) : E q ≃ₐ[k] E q :=
  Algebra.TensorProduct.congr (TrivialExtension.scaleDual H hH)
    (TrivialExtension.scaleDual H hH)

@[simp] lemma characterT_scaleDual (H : k) (hH : H ≠ 0) (a : T q) :
    characterT q (TrivialExtension.scaleDual H hH a) = characterT q a := rfl

@[simp] lemma characterE_sigma (H : k) (hH : H ≠ 0) (a : E q) :
    characterE q (sigma q H hH a) = characterE q a := by
  induction a using OAI.tensorInductionOn with
  | tmul a b => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

end Construction
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_ReverseResolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

def dualCoeff (i : Fin 10) : DualBimodule k (C k q) := LinearMap.proj i

@[simp] lemma dualCoeff_apply (i : Fin 10) (a : C k q) : dualCoeff q i a = a i := rfl

end Tachikawa.C



namespace Tachikawa.C
open CategoryTheory
variable {k : Type} [Field k] (q : k)

def j : C k q := ![0,0,0,0,0,0,0,0,1,0]

end Tachikawa.C



end


end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Bimodule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra



namespace BimoduleTensorHom
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  {M : ModuleCat (Enveloping.Alg k S R)} {X : ModuleCat R} {Z : ModuleCat S}

def uncurry (f : M ⟶ HomBimodule.obj (k := k) X Z) : Enveloping.evalObj X M ⟶ Z :=
  ModuleCat.ofHom (BalancedTensor.lift (uncurryLinear f) (uncurryLinear_balanced f))

@[simp] lemma uncurry_mk (f : M ⟶ HomBimodule.obj (k := k) X Z)
    (m : Enveloping.Obj M) (x : X) :
    uncurry f (BalancedTensor.mk m x) = (show X →ₗ[k] Z from f m) x := rfl

def curryLinear (g : Enveloping.evalObj X M ⟶ Z) :
    Enveloping.Obj M →ₗ[S] HomBimodule.Base (k := k) X Z where
  toFun m := (g.hom.restrictScalars k).comp (BalancedTensor.mk m)
  map_add' m n := by
    apply LinearMap.ext
    intro x
    change g (BalancedTensor.mk (m+n) x) = g (BalancedTensor.mk m x) + g (BalancedTensor.mk n x)
    exact (congrArg g (congrArg (fun h : X →ₗ[k] Enveloping.evalType X M => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Enveloping.Obj M) (N := X)).map_add m n))).trans
      (g.hom.map_add _ _)
  map_smul' s m := by
    apply LinearMap.ext
    intro x
    change g (BalancedTensor.mk (s • m) x) = s • g (BalancedTensor.mk m x)
    exact (congrArg g (congrArg (fun h : X →ₗ[k] Enveloping.evalType X M => h x)
      ((BalancedTensor.mk (k := k) (R := R) (S := S) (M := Enveloping.Obj M) (N := X)).map_smul s m))).trans
      (g.hom.map_smul s _)

lemma curryLinear_right (g : Enveloping.evalObj X M ⟶ Z) (r : Rᵐᵒᵖ) (m : Enveloping.Obj M) :
    curryLinear g (r • m) = r • curryLinear g m := by
  apply LinearMap.ext
  intro x
  change g (BalancedTensor.mk (r • m) x) = g (BalancedTensor.mk m (r.unop • x))
  exact congrArg g (BalancedTensor.balance r.unop m x)

def curry (g : Enveloping.evalObj X M ⟶ Z) : M ⟶ HomBimodule.obj (k := k) X Z :=
  (Enveloping.reassembleIso M).inv ≫
    Enveloping.ofBimoduleHom (curryLinear g) (curryLinear_right g)

@[simp] lemma curry_apply (g : Enveloping.evalObj X M ⟶ Z) (m : M) (x : X) :
    (show X →ₗ[k] Z from curry g m) x = g (BalancedTensor.mk (show Enveloping.Obj M from m) x) := rfl

lemma uncurry_curry (g : Enveloping.evalObj X M ⟶ Z) : uncurry (curry g) = g := by
  apply ModuleCat.hom_ext
  apply BalancedTensor.hom_ext
  intro m x
  rfl

lemma curry_uncurry (f : M ⟶ HomBimodule.obj (k := k) X Z) : curry (uncurry f) = f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  rfl

end BimoduleTensorHom
end Tachikawa



namespace Tachikawa.HomBimodule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R) {Z Z' : ModuleCat S}

def postLinear (g : Z ⟶ Z') : Base (k := k) X Z →ₗ[S] Base (k := k) X Z' where
  toFun f := (g.hom.restrictScalars k).comp (show X →ₗ[k] Z from f)
  map_add' f h := by
    apply LinearMap.ext
    intro x
    exact g.hom.map_add _ _
  map_smul' s f := by
    apply LinearMap.ext
    intro x
    exact g.hom.map_smul s _

def postMap (g : Z ⟶ Z') : obj (k := k) X Z ⟶ obj (k := k) X Z' :=
  Enveloping.ofBimoduleHom (postLinear X g) (fun _ _ => rfl)

@[simp] lemma postMap_apply (g : Z ⟶ Z') (f : obj (k := k) X Z) (x : X) :
    (show X →ₗ[k] Z' from postMap X g f) x = g ((show X →ₗ[k] Z from f) x) := rfl

end Tachikawa.HomBimodule



namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

def adjunction (φ : R →ₐ[k] S) : functor φ ⊣ res φ :=
  Adjunction.mkOfHomEquiv
  { homEquiv := homEquiv φ
    homEquiv_naturality_left_symm := by
      intro X X' Y f g
      apply ModuleCat.hom_ext
      apply BalancedTensor.hom_ext
      intro s x
      rfl
    homEquiv_naturality_right := by
      intro X Y Y' f g
      ext x
      rfl }

def compositionIso (φ : R →ₐ[k] S) (ψ : S →ₐ[k] U) :
    functor φ ⋙ functor ψ ≅ functor (ψ.comp φ) := by
  let a := (adjunction φ).comp (adjunction ψ)
  let b := adjunction (ψ.comp φ)
  exact Adjunction.leftAdjointUniq a b

end Tachikawa.AlgebraInduction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_RightInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.Enveloping
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (X : ModuleCat R)

def rightEvaluation : ModuleCat Rᵐᵒᵖ ⥤ ModuleCat k where
  obj M := ModuleCat.of k (BalancedTensor.T (k := k) (R := R) (S := k) (M := M) (N := X))
  map f := ModuleCat.ofHom (BalancedTensor.mapLeft (k := k) (R := R) (S := k) (N := X)
    (f.hom.restrictScalars k) f.hom.map_smul)
  map_id M := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply BalancedTensor.hom_ext
    intro m x
    rfl

def rightObjEquiv (M : ModuleCat (Alg k S R)) :
    Obj M ≃ₗ[Rᵐᵒᵖ] (rightFunctor.obj M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rightEvaluationEquiv (M : ModuleCat (Alg k S R)) :
    evalType X M ≃ₗ[k] (rightEvaluation (k := k) X).obj (rightFunctor.obj M) := by
  let e := (rightObjEquiv (k := k) M).restrictScalars k
  let f := BalancedTensor.mapLeft (k := k) (R := R) (S := k) (N := X)
    e.toLinearMap (rightObjEquiv (k := k) M).map_smul
  let g := BalancedTensor.mapLeft (k := k) (R := R) (S := k) (N := X)
    e.symm.toLinearMap (rightObjEquiv (k := k) M).symm.map_smul
  let t : BalancedTensor.T (k := k) (R := R) (S := k) (M := Obj M) (N := X) ≃ₗ[k]
      (rightEvaluation (k := k) X).obj (rightFunctor.obj M) :=
    { f with
      invFun := g
      left_inv x := by
        change g (f x) = x
        induction x using BalancedTensor.induction_on with
        | h0 => simp only [map_zero]
        | ht m x => rfl
        | ha x y hx hy => simp only [map_add, hx, hy]
      right_inv x := by
        change f (g x) = x
        induction x using BalancedTensor.induction_on with
        | h0 => simp only [map_zero]
        | ht m x => rfl
        | ha x y hx hy => simp only [map_add, hx, hy] }
  exact BalancedTensor.restrictEquiv.trans t

@[simp] lemma rightEvaluationEquiv_mk (M : ModuleCat (Alg k S R)) (m : Obj M) (x : X) :
    rightEvaluationEquiv (k := k) X M (BalancedTensor.mk m x) =
      BalancedTensor.mk (k := k) (R := R) (S := k) (N := X)
        (show rightFunctor.obj M from m) x := rfl

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

abbrev leftIndObj (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) : ModuleCat (Alg k S U) :=
  ofBimodule (k := k) (R := S) (S := U)
    (BalancedTensor.T (k := k) (R := R) (S := S) (M := AlgebraInduction.Bimod φ) (N := Obj M))

end Tachikawa.Enveloping



namespace Tachikawa.BalancedTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U M N : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N] [Module U N]
  [IsScalarTower k R N] [IsScalarTower k U N] [SMulCommClass U R N]

def commutingAction : U →+* Module.End S (T (k := k) (R := R) (S := S) (M := M) (N := N)) where
  toFun u := mapRight ((Algebra.lsmul k R N) u)
  map_one' := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) 1) = LinearMap.id
    rw [map_one]
    exact mapRight_id
  map_mul' u v := by
    change mapRight (k := k) (S := S) (M := M) ((Algebra.lsmul k R N) (u*v)) = _
    rw [map_mul]
    exact mapRight_comp _ _
  map_zero' := by rw [map_zero]; exact mapRight_zero
  map_add' u v := by rw [map_add]; exact mapRight_add _ _

end Tachikawa.BalancedTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.HomBimodule
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] (X : ModuleCat R)

def representationLinear : R →ₗ[R] Base (k := k) X X where
  toFun a := (Algebra.lsmul k k X) a
  map_add' a b := map_add (Algebra.lsmul k k X) a b
  map_smul' a b := by
    apply LinearMap.ext
    intro x
    exact mul_smul a b x

def representation : Enveloping.regular (k := k) (R := R) ⟶ obj (k := k) X X :=
  Enveloping.ofBimoduleHom (representationLinear (k := k) X) (by
    intro a b
    apply LinearMap.ext
    intro x
    exact mul_smul b a.unop x)

@[simp] lemma representation_apply (a : Enveloping.regular (k := k) (R := R)) (x : X) :
    (show X →ₗ[k] X from representation X a) x = (show R from a) • x := rfl

end Tachikawa.HomBimodule



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Induction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S U : Type} [Field k] [Ring R] [Ring S] [Ring U]
  [Algebra k R] [Algebra k S] [Algebra k U]

abbrev leftEnvelopingMap (φ : R →ₐ[k] S) : Alg k R U →ₐ[k] Alg k S U :=
  Algebra.TensorProduct.map φ (AlgHom.id k Uᵐᵒᵖ)

def leftIndUnit (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) :
    M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj (leftIndObj φ M) :=
  ModuleCat.ofHom (X := M) (Y := (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj (leftIndObj φ M))
  { toFun := fun m => BalancedTensor.mk (k := k) (R := R) (S := S)
      (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from m)
    map_add' := by intro m n; exact (BalancedTensor.mk (k := k) (R := R) (S := S)
      (N := Obj M) (show AlgebraInduction.Bimod φ from (1:S))).map_add m n
    map_smul' a m := by
      change BalancedTensor.mk (k := k) (R := R) (S := S)
        (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from a • m) =
        (action (k := k) (R := S) (S := U)
          (BalancedTensor.T (k := k) (R := R) (S := S) (M := AlgebraInduction.Bimod φ) (N := Obj M))
          (leftEnvelopingMap φ a)) _
      induction a using OAI.tensorInductionOn with
      | tmul r u =>
        change BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from (r ⊗ₜ[k] u) • m) =
          (φ r) • (u • BalancedTensor.mk (k := k) (R := R) (S := S)
            (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from m))
        trans BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (r • u • (show Obj M from m))
        · exact congrArg (BalancedTensor.mk (k := k) (R := R) (S := S)
            (show AlgebraInduction.Bimod φ from (1:S))) (tmul_smul M r u m)
        exact (AlgebraInduction.unit φ (ModuleCat.of R (Obj M))).hom.map_smul r (u • (show Obj M from m))
      | add a b ha hb =>
        rw [map_add, map_add]
        change BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from (a+b) • m) = _
        exact (congrArg (fun x : M => BalancedTensor.mk (k := k) (R := R) (S := S)
          (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from x)) (add_smul a b m)).trans
          (((BalancedTensor.mk (k := k) (R := R) (S := S) (N := Obj M)
            (show AlgebraInduction.Bimod φ from (1:S))).map_add _ _).trans
              (congrArg₂ (fun x y => x+y) ha hb)) }

@[simp] lemma leftIndUnit_apply (φ : R →ₐ[k] S) (M : ModuleCat (Alg k R U)) (m : M) :
    leftIndUnit φ M m = BalancedTensor.mk (k := k) (R := R) (S := S)
      (show AlgebraInduction.Bimod φ from (1:S)) (show Obj M from m) := rfl




def leftIndResMap (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) :
    ModuleCat.of R (Obj M) ⟶ (AlgebraInduction.res φ).obj (ModuleCat.of S (Obj N)) :=
  ModuleCat.ofHom (X := ModuleCat.of R (Obj M))
    (Y := (AlgebraInduction.res φ).obj (ModuleCat.of S (Obj N)))
  { toFun := fun m => (show Obj N from f m)
    map_add' := f.hom.map_add
    map_smul' r m := by
      have h := f.hom.map_smul (r ⊗ₜ[k] (1:Uᵐᵒᵖ)) m
      change (show N from f ((r ⊗ₜ[k] (1:Uᵐᵒᵖ)) • (show M from m))) =
        (leftEnvelopingMap φ (r ⊗ₜ[k] (1:Uᵐᵒᵖ))) • (show N from f m) at h
      exact h }

lemma leftIndResMap_right (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) (u : Uᵐᵒᵖ) (m : Obj M) :
    (show Obj N from f (u • m)) = u • (show Obj N from f m) := by
  have h := f.hom.map_smul ((1:R) ⊗ₜ[k] u) m
  change (show N from f (((1:R) ⊗ₜ[k] u) • (show M from m))) =
    leftEnvelopingMap φ ((1:R) ⊗ₜ[k] u) • (show N from f m) at h
  change (show N from f (((1:R) ⊗ₜ[k] u) • (show M from m))) =
    ((1:S) ⊗ₜ[k] u) • (show N from f m)
  simpa only [leftEnvelopingMap, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] using h

def leftIndExtendLinear (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) :
    BalancedTensor.T (k := k) (R := R) (S := S) (M := AlgebraInduction.Bimod φ) (N := Obj M) →ₗ[S] Obj N :=
  (AlgebraInduction.extend φ (leftIndResMap φ f)).hom

lemma leftIndExtendLinear_right (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) (u : Uᵐᵒᵖ) (x) :
    leftIndExtendLinear φ f (u • x) = u • leftIndExtendLinear φ f x := by
  induction x using BalancedTensor.induction_on with
  | h0 => simp only [smul_zero, map_zero]
  | ht s m =>
    change (show S from s) • (show Obj N from f (u • m)) =
      u • ((show S from s) • (show Obj N from f m))
    rw [leftIndResMap_right φ f, smul_comm]
  | ha x y hx hy => simp only [smul_add, map_add, hx, hy]

def leftIndExtend (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N) :
    leftIndObj φ M ⟶ N :=
  ofBimoduleHom (leftIndExtendLinear φ f) (leftIndExtendLinear_right φ f) ≫ (reassembleIso N).hom

@[simp] lemma leftIndExtend_mk (φ : R →ₐ[k] S) {M : ModuleCat (Alg k R U)} {N : ModuleCat (Alg k S U)}
    (f : M ⟶ (AlgebraInduction.res (leftEnvelopingMap (U := U) φ)).obj N)
    (s : AlgebraInduction.Bimod φ) (m : Obj M) :
    leftIndExtend φ f (BalancedTensor.mk s m) = (show Obj N from (show S from s) • (show Obj N from f m)) := rfl




end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.TrivialInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

abbrev inclusion : R →ₐ[k] TrivialExtension k R :=
  TrivSqZeroExt.inlAlgHom k R (DualBimodule k R)

def tensorGenerators (M : ModuleCat.{0} R) : M ⟶
    (AlgebraInduction.res (inclusion (k := k) (R := R))).obj
      ((functor (k := k) (R := R)).obj M) :=
  ModuleCat.ofHom
    (X := M)
    (Y := (AlgebraInduction.res (inclusion (k := k) (R := R))).obj
      ((functor (k := k) (R := R)).obj M))
    { toFun := fun m => (show Obj k R M from (m,0))
      map_add' := by
        intro x y
        apply Prod.ext
        · rfl
        · exact (zero_add _).symm
      map_smul' := by
        intro r m
        change (r • m, (0 : Nakayama k R M)) =
          (TrivSqZeroExt.inl r : TrivialExtension k R) • (show Obj k R M from (m,0))
        rw [inl_smul]
        apply Prod.ext
        · rfl
        · exact (smul_zero r).symm }

def tensorComparison (M : ModuleCat.{0} R) :
    (AlgebraInduction.functor (inclusion (k := k) (R := R))).obj M ⟶
      (functor (k := k) (R := R)).obj M :=
  AlgebraInduction.extend (inclusion (k := k) (R := R)) (tensorGenerators M)

@[simp] lemma tensorComparison_mk (M : ModuleCat.{0} R)
    (a : AlgebraInduction.Bimod (inclusion (k := k) (R := R))) (m : M) :
    tensorComparison (k := k) M (BalancedTensor.mk a m) =
      (show TrivialExtension k R from a) • unit m := rfl

end Tachikawa.TrivialInduction



namespace Tachikawa.AlgebraInduction
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def resUnderlyingEquiv (φ : R →ₐ[k] S) (M : ModuleCat.{0} S) :
    (res φ).obj M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change φ (algebraMap k R c) • (show M from x) = c • (show M from x)
    rw [φ.commutes]
    rfl

instance resFinite (φ : R →ₐ[k] S) (M : ModuleCat.{0} S) [FiniteDimensional k M] :
    FiniteDimensional k ((res φ).obj M) :=
  Module.Finite.equiv (resUnderlyingEquiv φ M).symm

end Tachikawa.AlgebraInduction



namespace Tachikawa.AlgebraInduction
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (φ : R →ₐ[k] S)
variable {ι : Type} (c : ComplexShape ι)

abbrev complexInduction := (functor φ).mapHomologicalComplex c
abbrev complexRestriction := (res φ).mapHomologicalComplex c

def complexUnit (P : HomologicalComplex (ModuleCat.{0} R) c) :
    P ⟶ (complexRestriction φ c).obj ((complexInduction φ c).obj P) where
  f i := unit φ (P.X i)
  comm' i j _ := (unit_naturality φ (P.d i j)).symm

def complexExtend {P : HomologicalComplex (ModuleCat.{0} R) c}
    {Q : HomologicalComplex (ModuleCat.{0} S) c}
    (f : P ⟶ (complexRestriction φ c).obj Q) :
    (complexInduction φ c).obj P ⟶ Q where
  f i := extend φ (f.f i)
  comm' i j _ := by
    apply (homEquiv φ (P.X i) (Q.X j)).injective
    change unit φ (P.X i) ≫ (res φ).map (extend φ (f.f i) ≫ Q.d i j) =
      unit φ (P.X i) ≫ (res φ).map ((functor φ).map (P.d i j) ≫ extend φ (f.f j))
    rw [Functor.map_comp,Functor.map_comp,← Category.assoc,unit_extend,
      ← Category.assoc,← unit_naturality,Category.assoc,unit_extend]
    exact f.comm i j

lemma complexUnit_extend {P : HomologicalComplex (ModuleCat.{0} R) c}
    {Q : HomologicalComplex (ModuleCat.{0} S) c}
    (f : P ⟶ (complexRestriction φ c).obj Q) :
    complexUnit φ c P ≫ (complexRestriction φ c).map (complexExtend φ c f) = f := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact unit_extend φ (f.f i)

end Tachikawa.AlgebraInduction



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_FiniteCoinduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

structure CoindReplacement (P : CochainComplex (ModuleCat (Alg k R S)) ℤ) where
  complex : CochainComplex (ModuleCat (Alg k R S)) ℤ
  map : P ⟶ complex
  quasiIso : QuasiIso map

attribute [instance] CoindReplacement.quasiIso

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.BalancedTensor
variable {k R S M M' N : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k S M'] [IsScalarTower k Rᵐᵒᵖ M'] [SMulCommClass S Rᵐᵒᵖ M']
  [AddCommGroup N] [Module k N] [Module R N]

omit [Algebra k R] [IsScalarTower k Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M'] in
lemma restrictEquiv_mapLeft (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (x : T (k := k) (R := R) (S := S) (M := M) (N := N)) :
    restrictEquiv (mapLeft (k := k) (N := N) f hf x) =
      mapLeft (k := k) (S := k) (N := N) (f.restrictScalars k) hf (restrictEquiv x) := by
  induction x using induction_on with
  | h0 => simp
  | ht m n => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

end Tachikawa.BalancedTensor



end

end OAI
end


