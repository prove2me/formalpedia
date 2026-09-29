-- Prove2me | solution 1 for AutomorphicForm.exists_glArch_eq_one_and_semiLocalComponent_glFin_eq_of_mem_semiLocalIntegralSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0460af8c-cb92-5265-aa1d-6ac860bcb8b9

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_glArch_eq_one_and_semiLocalComponent_glFin_eq_of_mem_semiLocalIntegralSet

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option synthInstance.maxHeartbeats 1600000

open TopologicalSpace Filter Topology
open scoped TensorProduct.RightActions

noncomputable section

namespace KappaGlue

section IntegralUnitsAlgebra

variable {A : Type*} [CommRing A]

theorem mul_mem_integralUnitsSet (B : Subring A) {g h : GL (Fin 2) A}
    (hg : g ∈ AutomorphicForm.integralUnitsSet (B : Set A)) (hh : h ∈ AutomorphicForm.integralUnitsSet (B : Set A)) :
    g * h ∈ AutomorphicForm.integralUnitsSet (B : Set A) := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg hh ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact B.sum_mem fun k _ => B.mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact B.sum_mem fun k _ => B.mul_mem (hh.2 i k) (hg.2 k j)

theorem inv_mem_integralUnitsSet (U : Set A) {g : GL (Fin 2) A}
    (hg : g ∈ AutomorphicForm.integralUnitsSet U) : g⁻¹ ∈ AutomorphicForm.integralUnitsSet U := by
  rw [AutomorphicForm.mem_integralUnitsSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem isClosed_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] {U : Set A} (hU : IsClosed U) :
    IsClosed (AutomorphicForm.integralUnitsSet (A := A) U) := by
  rw [AutomorphicForm.integralUnitsSet_eq_preimage]
  have hC : IsClosed (AutomorphicForm.integralMatrixSet (A := A) U) := by
    rw [AutomorphicForm.integralMatrixSet_eq_pi]
    exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => hU
  exact (hC.prod (MulOpposite.opHomeomorph.isClosedMap _ hC)).preimage Units.continuous_embedProduct

theorem continuous_glMap {B : Type*} [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

end IntegralUnitsAlgebra

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalHomeomorph_apply (x : L ⊗[K] v.adicCompletion K) :
    AutomorphicForm.semiLocalHomeomorph K L v x =
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x :=
  rfl

theorem semiLocalEval_apply (a : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v a =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) :=
  rfl

theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    AutomorphicForm.semiLocalHomeomorph K L v (AutomorphicForm.semiLocalEval K L v a) w = a w.1 := by
  rw [semiLocalHomeomorph_apply, semiLocalEval_apply, AlgEquiv.apply_symm_apply]
  rfl

theorem semiLocalEval_mem_semiLocalIntegers_iff (a : FiniteAdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalEval K L v a ∈ AutomorphicForm.semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), a w.1 ∈ w.1.adicCompletionIntegers L := by
  rw [AutomorphicForm.semiLocalIntegers_eq_preimage, Set.mem_preimage, AutomorphicForm.piIntegers, Set.mem_univ_pi]
  refine forall_congr' fun w => ?_
  rw [semiLocalHomeomorph_semiLocalEval, SetLike.mem_coe]

theorem semiLocalComponent_apply (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    (AutomorphicForm.semiLocalComponent K L v h : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
      AutomorphicForm.semiLocalEval K L v ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) :=
  rfl

theorem semiLocalComponent_mem_iff (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    AutomorphicForm.semiLocalComponent K L v h ∈ AutomorphicForm.semiLocalIntegralSet K L v ↔
      ∀ w : v.Extension (𝓞 L), AdelicLevel.finComponent (𝓞 L) L w.1 h ∈ AutomorphicForm.localIntegralSet L w.1 := by
  rw [AutomorphicForm.semiLocalIntegralSet, AutomorphicForm.mem_integralUnitsSet]
  simp only [← map_inv, semiLocalComponent_apply, semiLocalEval_mem_semiLocalIntegers_iff,
    AutomorphicForm.mem_localIntegralSet, AdelicLevel.finComponent_apply]
  constructor
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w⟩
  · intro hw
    exact ⟨fun i j w => (hw w).1 i j, fun i j w => (hw w).2 i j⟩

theorem continuous_semiLocalEval : Continuous (AutomorphicForm.semiLocalEval K L v) := by
  have h1 : Continuous fun a : FiniteAdeleRing (𝓞 L) L =>
      (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) :=
    continuous_pi fun w => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1
  have h2 : Continuous (AutomorphicForm.semiLocalHomeomorph K L v).symm :=
    (AutomorphicForm.semiLocalHomeomorph K L v).symm.continuous
  have key : ∀ a : FiniteAdeleRing (𝓞 L) L, AutomorphicForm.semiLocalEval K L v a =
      (AutomorphicForm.semiLocalHomeomorph K L v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) := by
    intro a
    apply (AutomorphicForm.semiLocalHomeomorph K L v).injective
    rw [Homeomorph.apply_symm_apply]
    funext w
    exact semiLocalHomeomorph_semiLocalEval K L v a w
  have heq : (fun a : FiniteAdeleRing (𝓞 L) L => AutomorphicForm.semiLocalEval K L v a) =
      fun a => (AutomorphicForm.semiLocalHomeomorph K L v).symm
        (fun w : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w.1 a) := funext key
  show Continuous fun a : FiniteAdeleRing (𝓞 L) L => AutomorphicForm.semiLocalEval K L v a
  rw [heq]
  exact h2.comp h1

theorem continuous_semiLocalComponent : Continuous (AutomorphicForm.semiLocalComponent K L v) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L (v.adicCompletion K)
  exact continuous_glMap _ (continuous_semiLocalEval K L v)

end SemiLocal

section ListProd

theorem list_prod_map_eq_of_forall_ne {α M : Type*} [Monoid M] [DecidableEq α] :
    ∀ (l : List α), l.Nodup → ∀ (x₀ : α), x₀ ∈ l → ∀ (f : α → M), (∀ x ∈ l, x ≠ x₀ → f x = 1) →
      (l.map f).prod = f x₀
  | [], _, x₀, hx, _, _ => absurd hx (by simp)
  | (a :: l), hl, x₀, hx, f, hf => by
    rw [List.map_cons, List.prod_cons]
    rw [List.nodup_cons] at hl
    by_cases ha : a = x₀
    · subst ha
      have : (l.map f).prod = 1 := List.prod_eq_one fun y hy => by
        obtain ⟨x, hxl, rfl⟩ := List.mem_map.mp hy
        exact hf x (List.mem_cons_of_mem _ hxl) fun h => hl.1 (h ▸ hxl)
      rw [this, mul_one]
    · have hx' : x₀ ∈ l := by
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm ha
        · exact h
      rw [hf a (by simp) ha, one_mul]
      exact list_prod_map_eq_of_forall_ne l hl.2 x₀ hx' f fun x hxl => hf x (List.mem_cons_of_mem _ hxl)

theorem list_prod_map_eq_one {α M : Type*} [Monoid M] (l : List α) (f : α → M) (hf : ∀ x ∈ l, f x = 1) :
    (l.map f).prod = 1 :=
  List.prod_eq_one fun y hy => by
    obtain ⟨x, hxl, rfl⟩ := List.mem_map.mp hy
    exact hf x hxl

end ListProd

section Lift

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

def coordHom (w : v.Extension (𝓞 L)) : L ⊗[K] v.adicCompletion K →+* w.1.adicCompletion L :=
  (Pi.evalRingHom (fun w : v.Extension (𝓞 L) => w.1.adicCompletion L) w).comp
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).toRingEquiv.toRingHom

theorem coordHom_apply (w : v.Extension (𝓞 L)) (x : L ⊗[K] v.adicCompletion K) :
    coordHom K L v w x = AutomorphicForm.semiLocalHomeomorph K L v x w := rfl

def coordGL (w : v.Extension (𝓞 L)) : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (w.1.adicCompletion L) :=
  Matrix.GeneralLinearGroup.map (coordHom K L v w)

theorem coordGL_apply (w : v.Extension (𝓞 L)) (k : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (i j : Fin 2) :
    ((coordGL K L v w k : GL (Fin 2) (w.1.adicCompletion L)) : Matrix (Fin 2) (Fin 2) _) i j =
      AutomorphicForm.semiLocalHomeomorph K L v ((k : Matrix (Fin 2) (Fin 2) _) i j) w := rfl

theorem exists_lift (k : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hk : k ∈ AutomorphicForm.semiLocalIntegralSet K L v) :
    ∃ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
      h ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L ∧
      AutomorphicForm.semiLocalComponent K L v h = k ∧
      ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → AutomorphicForm.semiLocalComponent K L v' h = 1 := by
  classical
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : Fintype (v.Extension (𝓞 L)) := Fintype.ofFinite _
  set LW : List (v.Extension (𝓞 L)) := (Finset.univ : Finset (v.Extension (𝓞 L))).toList with hLW
  have hLWnd : LW.Nodup := Finset.nodup_toList _
  have hLWmem : ∀ w : v.Extension (𝓞 L), w ∈ LW := fun w => Finset.mem_toList.mpr (Finset.mem_univ w)
  let h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
    (LW.map fun w : v.Extension (𝓞 L) => AdelicDock.localEmbed (𝓞 L) L w.1 (coordGL K L v w k)).prod

  have hcomp_above : ∀ w : v.Extension (𝓞 L),
      AdelicLevel.finComponent (𝓞 L) L w.1 h = coordGL K L v w k := by
    intro w
    show AdelicLevel.finComponent (𝓞 L) L w.1
      (LW.map fun w : v.Extension (𝓞 L) => AdelicDock.localEmbed (𝓞 L) L w.1 (coordGL K L v w k)).prod = _
    rw [map_list_prod, List.map_map]
    refine (list_prod_map_eq_of_forall_ne LW hLWnd w (hLWmem w) _ fun w' _ hw' => ?_).trans ?_
    · exact AdelicDock.finComponent_localEmbed_of_ne (𝓞 L) L w'.1 _ fun e => hw' (Subtype.ext e).symm
    · exact AdelicDock.finComponent_localEmbed_self (𝓞 L) L w.1 _
  have hcomp_away : ∀ w' : HeightOneSpectrum (𝓞 L), (∀ w : v.Extension (𝓞 L), w.1 ≠ w') →
      AdelicLevel.finComponent (𝓞 L) L w' h = 1 := by
    intro w' hw'
    show AdelicLevel.finComponent (𝓞 L) L w'
      (LW.map fun w : v.Extension (𝓞 L) => AdelicDock.localEmbed (𝓞 L) L w.1 (coordGL K L v w k)).prod = 1
    rw [map_list_prod, List.map_map]
    exact list_prod_map_eq_one _ _ fun w _ => AdelicDock.finComponent_localEmbed_of_ne (𝓞 L) L w.1 _ (hw' w).symm

  have hentry : ∀ (w' : HeightOneSpectrum (𝓞 L)) (i j : Fin 2),
      ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w' =
        ((AdelicLevel.finComponent (𝓞 L) L w' h : GL (Fin 2) _) : Matrix (Fin 2) (Fin 2) _) i j :=
    fun w' i j => (AdelicLevel.finComponent_apply (𝓞 L) L w' h i j).symm

  have hv : AutomorphicForm.semiLocalComponent K L v h = k := by
    refine Units.ext (Matrix.ext fun i j => (AutomorphicForm.semiLocalHomeomorph K L v).injective (funext fun w => ?_))
    rw [semiLocalComponent_apply, semiLocalHomeomorph_semiLocalEval, hentry, hcomp_above, coordGL_apply]

  have hv' : ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → AutomorphicForm.semiLocalComponent K L v' h = 1 := by
    intro v' hvv
    refine Units.ext (Matrix.ext fun i j => (AutomorphicForm.semiLocalHomeomorph K L v').injective (funext fun w => ?_))
    have hne : ∀ w₀ : v.Extension (𝓞 L), w₀.1 ≠ w.1 := fun w₀ e => hvv (by rw [← w.2, ← e, w₀.2])
    rw [semiLocalComponent_apply, semiLocalHomeomorph_semiLocalEval, hentry, hcomp_away w.1 hne,
      semiLocalHomeomorph_apply]
    rw [Units.val_one, Units.val_one]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]; rfl
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]; rfl

  have hint_above : ∀ w : v.Extension (𝓞 L),
      AdelicLevel.finComponent (𝓞 L) L w.1 h ∈ AutomorphicForm.localIntegralSet L w.1 :=
    (semiLocalComponent_mem_iff K L v h).mp (hv ▸ hk)
  have hint : h ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L := by
    rw [AdelicLevel.mem_finiteIntegralGL2_iff]
    have key : ∀ w', AdelicLevel.finComponent (𝓞 L) L w' h ∈ AutomorphicForm.localIntegralSet L w' := by
      intro w'
      by_cases hw : ∃ w : v.Extension (𝓞 L), w.1 = w'
      · obtain ⟨w, rfl⟩ := hw; exact hint_above w
      · push Not at hw
        rw [hcomp_away w' hw]
        exact AutomorphicForm.one_mem_integralUnitsSet (zero_mem _) (one_mem _)
    refine ⟨fun i j w' => ?_, fun i j w' => ?_⟩
    · have := ((AutomorphicForm.mem_localIntegralSet L w').mp (key w')).1 i j
      rwa [AdelicLevel.finComponent_apply] at this
    · have := ((AutomorphicForm.mem_localIntegralSet L w').mp (key w')).2 i j
      rwa [← map_inv, AdelicLevel.finComponent_apply] at this
  exact ⟨h, hint, hv, hv'⟩

end Lift

end KappaGlue

end

open AutomorphicForm

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (k : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hk : k ∈ semiLocalIntegralSet K L v) :
    ∃ g : AdelicGL2 (𝓞 L) L,
      NumberField.AdelicLevel.glArch (𝓞 L) L g = 1 ∧
      NumberField.AdelicLevel.glFin (𝓞 L) L g ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 L) L ∧
      semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L g) = k ∧
      ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v →
        semiLocalComponent K L v' (NumberField.AdelicLevel.glFin (𝓞 L) L g) = 1 := by
  obtain ⟨h, hint, hv, hv'⟩ := KappaGlue.exists_lift K L v k hk
  refine ⟨AdelicDock.finEmbed (𝓞 L) L h, AdelicDock.glArch_finEmbed (𝓞 L) L h, ?_, ?_, ?_⟩
  · rw [AdelicDock.glFin_finEmbed]; exact hint
  · rw [AdelicDock.glFin_finEmbed]; exact hv
  · intro v' hvv; rw [AdelicDock.glFin_finEmbed]; exact hv' v' hvv

end S_AutomorphicForm_exists_glArch_eq_one_and_semiLocalComponent_glFin_eq_of_mem_semiLocalIntegralSet
end P2MW
export P2MW.S_AutomorphicForm_exists_glArch_eq_one_and_semiLocalComponent_glFin_eq_of_mem_semiLocalIntegralSet (solution)
