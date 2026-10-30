-- Prove2me | Definitions.Def_OAIQ116Ta005
-- name    : OAIQ116Ta005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:36:04.570631+00:00
-- url     : https://prove2.me/theorems/194fb8a3-2b88-48b2-98b6-e6a88e8aabec
-- title:
--   Definitions bundle OAIQ116Ta005 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 61 declarations of OpenAI's Lean: 20 definitions, 8 instances and 33 theorems. The definitions and types are `OAI.Tachikawa.DownCone.assemble`, `OAI.Tachikawa.DownCone.cross`, `OAI.Tachikawa.DownCone.high`, `OAI.Tachikawa.DownCone.low`, `OAI.Tachikawa.DownHom.Boundary`, `OAI.Tachikawa.DownHom.actionDelta`, `OAI.Tachikawa.DownHom.cochainEquiv`, `OAI.Tachikawa.DownHom.diff`, `OAI.Tachikawa.DownHom.indexEquiv`, `OAI.Tachikawa.DownHom.mapCochain`, `OAI.Tachikawa.DownHom.ofChain`, `OAI.Tachikawa.DownHom.ofMap`, `OAI.Tachikawa.DownHom.post`, `OAI.Tachikawa.DownHom.pre`, `OAI.Tachikawa.DownHom.toChain`, `OAI.Tachikawa.TotalDualPairing.equiv`, `OAI.Tachikawa.cokerKernelEquiv`, `OAI.Tachikawa.mappedResolutionCochainIso`, `OAI.Tachikawa.mappedResolutionCochainXIso`, `OAI.Tachikawa.resolutionReflectCokerEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_CompleteResolution`, `Tachikawa_CompleteTensor`, `Tachikawa_Cone`, `Tachikawa_Counterexample`, `Tachikawa_Delta`, `Tachikawa_DownHom`, `Tachikawa_HomProfile`, `Tachikawa_Nakayama`, `Tachikawa_OuterExt`, `Tachikawa_Perfect`, `Tachikawa_Socle`, `Tachikawa_StableDuality`, `Tachikawa_StableLift`, `Tachikawa_Symmetry`, `Tachikawa_TwistHom`.
--
--   **Imports.** It imports the bundles `OAIQ116Ta000`, `OAIQ116Ta001` and `OAIQ116Ta002` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ116Ta008`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta000
import Definitions.Def_OAIQ116Ta001
import Definitions.Def_OAIQ116Ta002

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Symmetry
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section
namespace Tachikawa

namespace DualBimodule
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

instance instSMulCommClass : SMulCommClass k R (DualBimodule k R) where
  smul_comm a b φ := by ext x; simp

instance instSMulCommClassMulOpposite_1 : SMulCommClass k Rᵐᵒᵖ (DualBimodule k R) where
  smul_comm a b φ := by ext x; simp

end DualBimodule
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableDuality
attribute [-instance] _root_.OAI.Tachikawa.FiniteModule.instAddCommGroupCarrierObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {M N L : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module R M] [Module R N] [Module R L]
  [Module k M] [Module k N] [Module k L]
  [IsScalarTower k R M] [IsScalarTower k R N] [IsScalarTower k R L]

lemma id_mem_projectiveFactors_iff [Module.Finite R M] :
    LinearMap.id (R := R) (M := M) ∈ projectiveFactors (k := k) ↔ Module.Projective R M := by
  constructor
  · rintro ⟨P, -, hPp, i, p, hp⟩
    let := hPp
    exact Module.Projective.of_split i p hp
  · intro h
    exact ⟨ModuleCat.of R M, inferInstance, h, LinearMap.id, LinearMap.id, rfl⟩

lemma stable_id_ne_zero_iff [Module.Finite R M] :
    stableClass (k := k) (LinearMap.id (R := R) (M := M)) ≠ 0 ↔ ¬ Module.Projective R M := by
  rw [ne_eq, stableClass_eq_zero_iff, id_mem_projectiveFactors_iff]

instance instFiniteDimensionalStableHom [FiniteDimensional k M] [FiniteDimensional k N] :
    FiniteDimensional k (StableHom (k := k) (R := R) (M := M) (N := N)) := by
  let : FiniteDimensional k (M →ₗ[R] N) :=
    Module.Finite.of_injective (LinearMap.restrictScalarsₗ k R M N k)
      (LinearMap.restrictScalars_injective k)
  exact Module.Finite.of_surjective stableClass stableClass_surjective

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteResolution
attribute [-instance] _root_.OAI.Tachikawa.FiniteModule.instAddCommGroupCarrierObj _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]

variable (P Q : ChainComplex (ModuleCat R) ℤ)

theorem exists_complete_lift (hp : TotallyAcyclic P) (hq : ComplexExact Q)
    (pproj : ∀ j, Module.Projective R (P.X j))
    (qfin : ∀ j, Module.Finite R (Q.X j)) (qproj : ∀ j, Module.Projective R (Q.X j))
    (u : CokerAt P 0 →ₗ[R] CokerAt Q 0) :
    ∃ f : P ⟶ Q, CokerAt.map f 0 = u := by
  refine ⟨CompleteLift.chainMap P Q hp hq pproj qfin qproj u, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := CokerAt.π_surjective P 0 x
  change CokerAt.π Q 0 ((CompleteLift.square P Q hp hq pproj qfin qproj u 0).map y) = _
  have h := LinearMap.congr_fun (CompleteLift.square P Q hp hq pproj qfin qproj u 0).lower y
  exact h.trans (LinearMap.congr_fun
    (CompleteLift.cokerMap_zero P Q hp hq pproj qfin qproj u) (CokerAt.π P 0 y))

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_CompleteTensor
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
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
instance instModuleCarrierObj (M : FiniteModule k R) : Module R M := inferInstanceAs (Module R M.obj)

end FiniteModule
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_TwistHom
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesProjectiveObjects] [F.PreservesHomology]
  {X : C} (P : ProjectiveResolution X)

def mappedResolutionCochainXIso (j : ℤ) :
    (mappedResolution F P).cochainComplex.X j ≅ F.obj (P.cochainComplex.X j) := by
  by_cases h : j ≤ 0
  · let n := (-j).toNat
    have hn : -(n : ℤ) = j := by dsimp [n]; omega
    exact (mappedResolution F P).cochainComplexXIso j n hn ≪≫
      (F.mapIso (P.cochainComplexXIso j n hn)).symm
  · exact (CochainComplex.isZero_of_isStrictlyLE (mappedResolution F P).cochainComplex 0 j).isoZero ≪≫
      (F.map_isZero (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 j)).isoZero.symm

lemma mappedResolutionCochainXIso_nonpos (j : ℤ) (n : ℕ) (hn : -(n : ℤ) = j) :
    mappedResolutionCochainXIso F P j =
      (mappedResolution F P).cochainComplexXIso j n hn ≪≫
      (F.mapIso (P.cochainComplexXIso j n hn)).symm := by
  have hj : j ≤ 0 := by omega
  simp only [mappedResolutionCochainXIso,dite_eq_left hj]
  have : (-j).toNat = n := by omega
  subst n
  rfl

lemma mappedResolutionCochainXIso_comm (i j : ℤ) :
    (mappedResolution F P).cochainComplex.d i j ≫ (mappedResolutionCochainXIso F P j).hom =
      (mappedResolutionCochainXIso F P i).hom ≫ F.map (P.cochainComplex.d i j) := by
  by_cases hi : i ≤ 0
  · by_cases hj : j ≤ 0
    · obtain ⟨a,rfl⟩ := Int.exists_eq_neg_ofNat hi
      obtain ⟨b,rfl⟩ := Int.exists_eq_neg_ofNat hj
      rw [mappedResolutionCochainXIso_nonpos F P _ a rfl,
        mappedResolutionCochainXIso_nonpos F P _ b rfl,
        ProjectiveResolution.cochainComplex_d _ _ _ a b rfl rfl,
        ProjectiveResolution.cochainComplex_d _ _ _ a b rfl rfl]
      dsimp only [mappedResolution, Functor.mapProjectiveResolution,
        Functor.mapHomologicalComplex]
      simp only [Iso.trans_hom,Iso.symm_hom,Functor.mapIso_inv,Functor.map_comp,
        Category.assoc,Iso.inv_hom_id_assoc]
      rw [← F.map_comp_assoc,Iso.inv_hom_id,F.map_id,Category.id_comp]
    · exact (F.map_isZero (CochainComplex.isZero_of_isStrictlyLE P.cochainComplex 0 j)).eq_of_tgt _ _
  · exact (CochainComplex.isZero_of_isStrictlyLE (mappedResolution F P).cochainComplex 0 i).eq_of_src _ _

def mappedResolutionCochainIso : (mappedResolution F P).cochainComplex ≅
    (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (mappedResolutionCochainXIso F P)
    (fun i j _ => (mappedResolutionCochainXIso_comm F P i j).symm)

end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterExt
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa.TotalDualPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))

def equiv (n : ℕ) : (G.total (.up ℕ)).X n ≃ₗ[k] ((K.total (.down ℕ)).X n ⟶ N) :=
  (coproductPiEquiv (cochainFamily G n)).trans
    ((LinearEquiv.piCongrRight (fun t : Diag n => p t.val.1 t.val.2)).trans
      (coproductHomEquiv (k := k) (chainFamily K n) N).symm)

lemma evaluate (n i j : ℕ) (h : i+j=n) (z : (G.total (.up ℕ)).X n) :
    K.ιTotal (.down ℕ) i j n h ≫ equiv K G N p n z =
      p i j (coproductPiEquiv (cochainFamily G n) z ⟨(i,j),h⟩) := by
  exact congrFun ((coproductHomEquiv (k := k) (chainFamily K n) N).apply_symm_apply
    (fun t : Diag n => p t.val.1 t.val.2 (coproductPiEquiv (cochainFamily G n) z t))) ⟨(i,j),h⟩

lemma evaluate_ι_self (n i j : ℕ) (h : i+j=n) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) i j n h ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) = p i j x := by
  rw [evaluate]
  change p i j (coproductPiEquiv (cochainFamily G n)
    (Sigma.ι (cochainFamily G n) ⟨(i,j),h⟩ x) ⟨(i,j),h⟩) = _
  rw [coproductPiEquiv_ι_self]

lemma evaluate_ι_ne (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n)
    (hne : (a,b) ≠ (i,j)) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) a b n h' ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) = 0 := by
  rw [evaluate]
  change p a b (coproductPiEquiv (cochainFamily G n)
    (Sigma.ι (cochainFamily G n) ⟨(i,j),h⟩ x) ⟨(a,b),h'⟩) = _
  rw [coproductPiEquiv_ι_ne _ (show (⟨(i,j),h⟩ : Diag n) ≠ ⟨(a,b),h'⟩ by
    intro he; exact hne (congrArg Subtype.val he).symm), map_zero]

end Tachikawa.TotalDualPairing



namespace Tachikawa.TotalDualPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [hk : CharP k 2]

variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))

omit hk in
lemma up_d₁ (i j n : ℕ) (h : i+1+j=n) :
    G.d₁ (.up ℕ) i j n =
      (G.d i (i+1)).f j ≫ G.ιTotal (.up ℕ) (i+1) j n h := by
  rw [G.d₁_eq (.up ℕ) (show (ComplexShape.up ℕ).Rel i (i+1) from rfl) j n h]
  change (1 : ℤˣ) • _ = _
  exact one_smul _ _

lemma up_d₂ (i j n : ℕ) (h : i+(j+1)=n) :
    G.d₂ (.up ℕ) i j n =
      (G.X i).d j (j+1) ≫ G.ιTotal (.up ℕ) i (j+1) n h := by
  rw [G.d₂_eq (.up ℕ) i (show (ComplexShape.up ℕ).Rel j (j+1) from rfl) n h,
    units_smul_eq (k := k)]

lemma down_d₁ (i j n : ℕ) (h : i+j=n) :
    K.d₁ (.down ℕ) (i+1) j n =
      (K.d (i+1) i).f j ≫ K.ιTotal (.down ℕ) i j n h := by
  rw [K.d₁_eq (.down ℕ) (show (ComplexShape.down ℕ).Rel (i+1) i from rfl) j n h]
  change (1 : ℤˣ) • _ = _
  exact one_smul _ _

include hk in
lemma down_d₂ (i j n : ℕ) (h : i+j=n) :
    K.d₂ (.down ℕ) i (j+1) n =
      (K.X i).d (j+1) j ≫ K.ιTotal (.down ℕ) i j n h := by
  rw [K.d₂_eq (.down ℕ) i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl) n h,
    units_smul_eq (k := k)]

lemma down_d₁_zero (j n : ℕ) : K.d₁ (.down ℕ) 0 j n = 0 :=
  K.d₁_eq_zero (.down ℕ) 0 j n (by change ¬ _+1=0; omega)

lemma down_d₂_zero (i n : ℕ) : K.d₂ (.down ℕ) i 0 n = 0 :=
  K.d₂_eq_zero (.down ℕ) i 0 n (by change ¬ _+1=0; omega)

variable (hp₁ : ∀ i j (x : (G.X i).X j),
  p (i+1) j ((G.d i (i+1)).f j x) = (K.d (i+1) i).f j ≫ p i j x)
variable (hp₂ : ∀ i j (x : (G.X i).X j),
  p i (j+1) ((G.X i).d j (j+1) x) = (K.X i).d (j+1) j ≫ p i j x)

omit hk in
include hp₁ in
lemma horizontal (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n+1) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.d₁ (.up ℕ) i j (n+1) x) =
    K.d₁ (.down ℕ) a b n ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) := by
  rw [up_d₁ G i j (n+1) (by omega)]
  change K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.ιTotal (.up ℕ) (i+1) j (n+1) _ ((G.d i (i+1)).f j x)) = _
  cases a with
  | zero =>
    rw [down_d₁_zero, zero_comp]
    exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
      intro he
      have hc := congrArg (fun t : ℕ × ℕ => t.1) he
      dsimp at hc
      omega) _
  | succ a =>
    rw [down_d₁ K a b n (by omega), Category.assoc]
    by_cases hab : (a,b) = (i,j)
    · have ha := congrArg Prod.fst hab
      have hb := congrArg Prod.snd hab
      dsimp at ha hb
      subst a b
      rw [evaluate_ι_self, evaluate_ι_self]
      exact hp₁ i j x
    · rw [evaluate_ι_ne K G N p _ _ _ _ _ _ _ hab, comp_zero]
      exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
        intro he
        apply hab
        have h1 := congrArg (fun t : ℕ × ℕ => t.1) he
        have h2 := congrArg (fun t : ℕ × ℕ => t.2) he
        apply Prod.ext <;> dsimp at * <;> omega) _

include hp₂ in
lemma vertical (n i j a b : ℕ) (h : i+j=n) (h' : a+b=n+1) (x : (G.X i).X j) :
    K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.d₂ (.up ℕ) i j (n+1) x) =
    K.d₂ (.down ℕ) a b n ≫
      equiv K G N p n (G.ιTotal (.up ℕ) i j n h x) := by
  rw [up_d₂ G i j (n+1) (by omega)]
  change K.ιTotal (.down ℕ) a b (n+1) h' ≫
      equiv K G N p (n+1) (G.ιTotal (.up ℕ) i (j+1) (n+1) _ ((G.X i).d j (j+1) x)) = _
  cases b with
  | zero =>
    rw [down_d₂_zero, zero_comp]
    exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
      intro he
      have hc := congrArg (fun t : ℕ × ℕ => t.2) he
      dsimp at hc
      omega) _
  | succ b =>
    rw [down_d₂ (k := k) K a b n (by omega), Category.assoc]
    by_cases hab : (a,b) = (i,j)
    · have ha := congrArg Prod.fst hab
      have hb := congrArg Prod.snd hab
      dsimp at ha hb
      subst a b
      rw [evaluate_ι_self, evaluate_ι_self]
      exact hp₂ i j x
    · rw [evaluate_ι_ne K G N p _ _ _ _ _ _ _ hab, comp_zero]
      exact evaluate_ι_ne K G N p _ _ _ _ _ _ _ (by
        intro he
        apply hab
        have h1 := congrArg (fun t : ℕ × ℕ => t.1) he
        have h2 := congrArg (fun t : ℕ × ℕ => t.2) he
        apply Prod.ext <;> dsimp at * <;> omega) _

end Tachikawa.TotalDualPairing



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
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

namespace TrivialInflation
variable {M N : Type} [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
instance instFiniteDimensional [FiniteDimensional k M] : FiniteDimensional k (TrivialInflation k R M) :=
  inferInstanceAs (FiniteDimensional k M)

end TrivialInflation
end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Socle
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.downIntTensorSigns
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

instance instFiniteDimensionalX : FiniteDimensional k (X q) := inferInstanceAs (FiniteDimensional k k)

end Construction
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Perfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R S : Type} [Ring R] [Ring S]

def resolutionReflectCokerEquiv {M : ModuleCat.{0} R} (P : ProjectiveResolution M)
    (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] (n : ℕ) :
    CokerAt (reflectCochain ((F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)) n ≃ₗ[S]
      (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).X n ⧸
        LinearMap.range (((F.mapHomologicalComplex (.down ℕ)).obj P.complex).d (n+1) n).hom) := by
  let e₁ := F.mapIso (P.cochainComplexXIso (-((n:ℤ)+1)) (n+1) (by omega))
  let e₂ := F.mapIso (P.cochainComplexXIso (-(n:ℤ)) n)
  apply cokerLinearEquiv _ _ e₁.toLinearEquiv e₂.toLinearEquiv
  apply ModuleCat.hom_ext_iff.mp
  change F.map (P.cochainComplex.d _ _) ≫ F.map _ = F.map _ ≫ F.map (P.complex.d _ _)
  rw [P.cochainComplex_d (-((n:ℤ)+1)) (-(n:ℤ)) (n+1) n (by omega) rfl]
  simp only [← F.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Tachikawa



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



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B]
  [Module R C] [Module R D] [Module k B] [Module k D]
  [IsScalarTower k R B] [IsScalarTower k R D]

lemma projectiveFactors_conjugate_iff (f : A →ₗ[R] B) (e : C ≃ₗ[R] A) (v : B ≃ₗ[R] D) :
    (v.toLinearMap.comp f).comp e.toLinearMap ∈ projectiveFactors (k := k) ↔
      f ∈ projectiveFactors (k := k) := by
  constructor
  · intro h
    have hh := projectiveFactors_postcomp (projectiveFactors_precomp h e.symm.toLinearMap)
      v.symm.toLinearMap
    have he : v.symm.toLinearMap.comp (((v.toLinearMap.comp f).comp e.toLinearMap).comp e.symm.toLinearMap) = f := by
      ext x; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
    rw [he] at hh
    exact hh
  · intro h
    exact projectiveFactors_precomp (projectiveFactors_postcomp h v.toLinearMap) e.toLinearMap

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
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
variable (P : ChainComplex (ModuleCat R) ℤ) (hP : ComplexExact P)

def cokerKernelEquiv (i : ℤ) : CokerAt P (i+1) ≃ₗ[R] LinearMap.ker (CokerAt.π P i) := by
  let f := (CokerAt.δ P (i+1) i).codRestrict (LinearMap.ker (CokerAt.π P i))
    (fun x => (CokerAt.δ_π_exact P (i+1) i rfl _).mpr ⟨x,rfl⟩)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y h
    exact CokerAt.δ_injective P hP (i+1) i rfl (congrArg Subtype.val h)
  · intro y
    obtain ⟨x,hx⟩ := (CokerAt.δ_π_exact P (i+1) i rfl y).mp y.property
    exact ⟨x,Subtype.ext hx⟩

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Delta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra

lemma projective_kernel_of_surjective {R M P N : Type} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N] [Module.Projective R P] [Module.Projective R N]
    (i : M →ₗ[R] P) (q : P →ₗ[R] N)
    (hi : Function.Injective i) (hq : Function.Surjective q) (he : Function.Exact i q) :
    Module.Projective R M := by
  let h := linearShortExact i q he hi hq
  have : CategoryTheory.Projective (linearShortComplex i q he).X₃ :=
    show CategoryTheory.Projective (ModuleCat.of R N) from inferInstance
  have : Module.Projective R (linearShortComplex i q he).X₂ :=
    show Module.Projective R P from inferInstance
  let s := h.splittingOfProjective
  exact Module.Projective.of_split i s.r.hom (ModuleCat.hom_ext_iff.mp s.f_r)

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DownHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P Q : ChainComplex (ModuleCat.{0} R) ℤ)

variable {P Q}

variable (P Q) in
def ofChain {a : ℤ} (f : CompleteTranslate.complex P a ⟶ Q) : Cochain P Q a :=
  fun _i j h => (P.XIsoOfEq h).hom ≫ f.f j

def toChain {a : ℤ} (f : Cochain P Q a) (hf : Closed f) :
    CompleteTranslate.complex P a ⟶ Q where
  f j := f (j+a) j rfl
  comm' i j _ := hf (i+a) i (j+a) j rfl rfl

@[simp] lemma of_toChain {a : ℤ} (f : Cochain P Q a) (hf : Closed f) :
    ofChain P Q (toChain f hf) = f := by
  funext i j h
  subst i
  simp [ofChain,toChain]

def Boundary {a : ℤ} (f : Cochain P Q a) : Prop :=
  ∃ h : Cochain P Q (a-1), ∀ i j (he : i=j+a),
    f i j he = P.d i (i-1) ≫ h (i-1) j (by omega) +
      h i (j+1) (by omega) ≫ Q.d (j+1) j

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {P Q S : ChainComplex (ModuleCat.{0} R) ℤ}

def indexEquiv (a : ℤ) : Cochain P Q a ≃ (∀ t : Index a, P.X t.i ⟶ Q.X t.j) where
  toFun f t := f t.i t.j t.h
  invFun f i j h := f ⟨i,j,h⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance instAddCommGroupCochain (a : ℤ) : AddCommGroup (Cochain P Q a) := (indexEquiv a).addCommGroup
instance instModuleCochain (a : ℤ) : Module k (Cochain P Q a) :=
  AddEquiv.module k { toEquiv := indexEquiv a, map_add' := fun _ _ => rfl }

@[simp] lemma zero_apply {a : ℤ} (i j : ℤ) (h : i=j+a) :
    (0 : Cochain P Q a) i j h = 0 := rfl
@[simp] lemma add_apply {a : ℤ} (f g : Cochain P Q a) (i j : ℤ) (h : i=j+a) :
    (f+g) i j h = f i j h+g i j h := rfl

lemma closed_add {a : ℤ} {f g : Cochain P Q a} (hf : Closed f) (hg : Closed g) :
    Closed (f+g) := by
  intro i j l m hij hlm
  change (f i j hij+g i j hij) ≫ _ = _ ≫ (f l m hlm+g l m hlm)
  rw [add_comp,comp_add,hf,hg]

def diff {a : ℤ} (f : Cochain P Q (a-1)) : Cochain P Q a := fun i j he =>
  P.d i (i-1) ≫ f (i-1) j (by omega) + f i (j+1) (by omega) ≫ Q.d (j+1) j

def pre (u : S ⟶ P) {a : ℤ} (f : Cochain P Q a) : Cochain S Q a :=
  fun i j he => u.f i ≫ f i j he

def post {a : ℤ} (f : Cochain P Q a) (u : Q ⟶ S) : Cochain P S a :=
  fun i j he => f i j he ≫ u.f j
lemma pre_closed (u : S ⟶ P) {a : ℤ} {f : Cochain P Q a} (hf : Closed f) : Closed (pre u f) := by
  intro i j l m hij hlm
  dsimp only [pre]
  rw [Category.assoc,hf,← Category.assoc,u.comm,Category.assoc]
lemma post_closed {a : ℤ} {f : Cochain P Q a} (hf : Closed f) (u : Q ⟶ S) : Closed (post f u) := by
  intro i j l m hij hlm
  dsimp only [post]
  rw [Category.assoc,u.comm,← Category.assoc,hf,Category.assoc]
end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {P' Q' : ChainComplex (ModuleCat.{0} S) ℤ}
variable (e : ∀ i j, (P.X i ⟶ Q.X j) ≃ₗ[k] (P'.X i ⟶ Q'.X j))

def cochainEquiv (a : ℤ) : Cochain P Q a ≃ₗ[k] Cochain P' Q' a where
  toFun f i j h := e i j (f i j h)
  invFun f i j h := (e i j).symm (f i j h)
  left_inv f := by funext i j h; exact (e i j).symm_apply_apply _
  right_inv f := by funext i j h; exact (e i j).apply_symm_apply _
  map_add' f g := by funext i j h; exact (e i j).map_add _ _
  map_smul' c f := by funext i j h; exact (e i j).map_smul c _

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R]  [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {N : ModuleCat.{0} R}
  (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε = 0)

variable (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R) [F.Additive]

def mapCochain {a : ℤ} (f : Cochain P Q a) : Cochain (mapComplex F P) (mapComplex F Q) a :=
  fun i j h => F.map (f i j h)
lemma map_closed {a : ℤ} {f : Cochain P Q a} (hf : Closed f) : Closed (mapCochain F f) := by
  intro i j l m hij hlm
  change F.map (f i j hij) ≫ F.map (Q.d j m) = F.map (P.d i l) ≫ F.map (f l m hlm)
  rw [← F.map_comp,← F.map_comp,hf]

variable [F.Linear k] (X : ModuleCat.{0} R) (εP : P.X 0 ⟶ X)
  (hεP : P.d 1 0 ≫ εP = 0) (u : P ⟶ mapComplex F P) (u₀ : X ⟶ F.obj X)
  (hu : u.f 0 ≫ F.map εP = εP ≫ u₀)

def actionDelta {a : ℤ} (f g : Cochain P P a) : Cochain P (mapComplex F P) a :=
  pre u (mapCochain F f) + post g u
lemma actionDelta_closed {a : ℤ} {f g : Cochain P P a} (hf : Closed f) (hg : Closed g) :
    Closed (actionDelta F u f g) := closed_add (pre_closed u (map_closed F hf)) (post_closed hg u)

end Tachikawa.DownHom



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Cone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

def low {a : ℤ} (f : Cochain (C v) (C v) a) : Cochain A A a :=
  fun i j h => inRight v i ≫ f i j h ≫ right v j
def high {a : ℤ} (f : Cochain (C v) (C v) a) : Cochain B B a :=
  fun i j h => iL v i ≫ f (i+1) (j+1) (by omega) ≫ pL v j
def cross {a : ℤ} (f : Cochain (C v) (C v) a) : Cochain B A (a-1) :=
  fun i j h => iL v i ≫ f (i+1) j (by omega) ≫ right v j

def assemble {a : ℤ} (f : Cochain A A a) (g : Cochain B B a)
    (c : Cochain B A (a-1)) : Cochain (C v) (C v) a := fun i j h =>
  right v i ≫ f i j h ≫ inRight v j +
  left v i ≫ g (i-1) (j-1) (by omega) ≫ inLeft v j +
  left v i ≫ c (i-1) j (by omega) ≫ inRight v j

end Tachikawa.DownCone



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

@[reassoc] lemma d_right (i : ℤ) : (C v).d i (i-1) ≫ right v (i-1) =
    left v i ≫ v.f (i-1) + right v i ≫ A.d i (i-1) :=
  homotopyCofiber.d_sndX v i (i-1) (by change i-1+1=i; omega)

end Tachikawa.DownCone



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
open DownHom CompleteCone
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)

@[simp] lemma low_zero (a : ℤ) : low v (0 : Cochain (C v) (C v) a) = 0 := by
  funext i j h; simp [low]
@[simp] lemma high_zero (a : ℤ) : high v (0 : Cochain (C v) (C v) a) = 0 := by
  funext i j h; simp [high]
@[simp] lemma cross_zero (a : ℤ) : cross v (0 : Cochain (C v) (C v) a) = 0 := by
  funext i j h; simp [cross]
@[simp] lemma low_add {a : ℤ} (f g : Cochain (C v) (C v) a) :
    low v (f+g) = low v f+low v g := by funext i j h; simp [low,comp_add,add_comp]
@[simp] lemma high_add {a : ℤ} (f g : Cochain (C v) (C v) a) :
    high v (f+g) = high v f+high v g := by funext i j h; simp [high,comp_add,add_comp]
@[simp] lemma cross_add {a : ℤ} (f g : Cochain (C v) (C v) a) :
    cross v (f+g) = cross v f+cross v g := by funext i j h; simp [cross,comp_add,add_comp]

end Tachikawa.DownCone



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Counterexample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ}
def ofMap (f : P ⟶ Q) : Cochain P Q 0 := fun i j h =>
  (P.XIsoOfEq (show i=j by omega)).hom ≫ f.f j
end Tachikawa.DownHom



end

end OAI
end


