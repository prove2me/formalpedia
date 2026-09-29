-- Prove2me | solution 1 for AutomorphicForm.adelicHeight_sigmaAdelicAct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/54110144-bace-5607-b75e-6a4ac622051d

import Mathlib
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_adelicHeight_sigmaAdelicAct

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.AdelicLevel NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NumberField.PlaceTransport

noncomputable section

namespace R4KitHeight

section Transport

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in

theorem mult_smul (σ : L ≃ₐ[K] L) (w : InfinitePlace L) : (σ • w).mult = w.mult := by
  unfold NumberField.InfinitePlace.mult
  by_cases hw : w.IsReal
  · rw [if_pos hw, if_pos (NumberField.InfinitePlace.isReal_smul_iff.2 hw)]
  · rw [if_neg hw, if_neg (fun h => hw (NumberField.InfinitePlace.isReal_smul_iff.1 h))]

omit [NumberField K] [NumberField L] in

theorem norm_transport_infinite (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w')
    (x : w.Completion) : ‖NumberField.InfinitePlaceTransport.transport σ h x‖ = ‖x‖ := by
  refine NumberField.InfinitePlace.Completion.induction_on _
    (p := fun x : w.Completion => ‖NumberField.InfinitePlaceTransport.transport σ h x‖ = ‖x‖) x ?_ ?_
  · exact isClosed_eq ((continuous_norm).comp (NumberField.InfinitePlaceTransport.continuous_transport σ h))
      continuous_norm
  · intro a
    rw [NumberField.InfinitePlaceTransport.transport_coe, NumberField.InfinitePlace.Completion.norm_coe,
      NumberField.InfinitePlace.Completion.norm_coe]
    exact NumberField.InfinitePlaceTransport.apply_apply_of_smul_eq h _

omit [NumberField K] in

theorem absNorm_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (σ • w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv w.asIdeal _
    (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ) rfl).toEquiv).symm

theorem toNNReal_congr {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a = b)
    (x : WithZero (Multiplicative ℤ)) :
    WithZeroMulInt.toNNReal ha x = WithZeroMulInt.toNNReal hb x := by
  subst hab; rfl

omit [NumberField K] in

theorem norm_transport_finite (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w')
    (x : w.adicCompletion L) : ‖NumberField.PlaceTransport.transport σ h x‖ = ‖x‖ := by
  have habs : Ideal.absNorm w'.asIdeal = Ideal.absNorm w.asIdeal := by rw [← h]; exact absNorm_smul σ w
  rw [NumberField.FinitePlace.norm_def w' _, NumberField.FinitePlace.norm_def w _,
    NumberField.PlaceTransport.valued_transport]
  congr 1
  refine toNNReal_congr _ _ ?_ _
  exact_mod_cast habs

end Transport

section LocalHeights

variable {A B : Type*} [NormedField A] [NormedField B]

theorem localHeight_map (φ : A →+* B) (hφ : ∀ y, ‖φ y‖ = ‖y‖) (g : GL (Fin 2) A) :
    localHeight (Matrix.GeneralLinearGroup.map φ g) = localHeight g := by
  unfold localHeight rowNormSq
  have hcoe : ((Matrix.GeneralLinearGroup.map φ g : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) =
      φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) A) := rfl
  rw [hcoe, ← RingHom.map_det, hφ]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hφ]

theorem finLocalHeight_map (φ : A →+* B) (hφ : ∀ y, ‖φ y‖ = ‖y‖) (g : GL (Fin 2) A) :
    finLocalHeight (Matrix.GeneralLinearGroup.map φ g) = finLocalHeight g := by
  unfold finLocalHeight rowMaxNorm
  have hcoe : ((Matrix.GeneralLinearGroup.map φ g : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) =
      φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) A) := rfl
  rw [hcoe, ← RingHom.map_det, hφ]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hφ]

end LocalHeights

section Genuine

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Dg (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L :=
  M4aHerbrand.GenuineDescent.genuineDescentDatum K L

omit [NumberField K] in

theorem sigmaAdelicAct_apply (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      (D.act σ : RingAut (AdeleRing (𝓞 L) L)) ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) :=
  rfl

theorem archComponent_sigmaAdelicAct (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L)
    {u u' : InfinitePlace L} (h : σ • u = u') :
    archComponent L u' (glArch (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g)) =
      Matrix.GeneralLinearGroup.map (NumberField.InfinitePlaceTransport.transport σ h).toRingHom
        (archComponent L u (glArch (𝓞 L) L g)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [archComponent_apply, glArch_apply, sigmaAdelicAct_apply]
  change _ = NumberField.InfinitePlaceTransport.transport σ h
    ((archComponent L u (glArch (𝓞 L) L g) : Matrix (Fin 2) (Fin 2) u.Completion) i j)
  rw [archComponent_apply, glArch_apply]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ h

theorem finComponent_sigmaAdelicAct (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L)
    {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w') :
    finComponent (𝓞 L) L w' (glFin (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g)) =
      Matrix.GeneralLinearGroup.map (NumberField.PlaceTransport.transport σ h).toRingHom
        (finComponent (𝓞 L) L w (glFin (𝓞 L) L g)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [finComponent_apply, glFin_apply, sigmaAdelicAct_apply]
  change _ = NumberField.PlaceTransport.transport σ h
    ((finComponent (𝓞 L) L w (glFin (𝓞 L) L g) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j)
  rw [finComponent_apply, glFin_apply]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ h

theorem archHeight_sigmaAdelicAct_genuine (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    archHeight L (glArch (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g)) = archHeight L (glArch (𝓞 L) L g) := by
  unfold archHeight

  rw [← Fintype.prod_equiv (MulAction.toPerm σ)
    (fun u => localHeight (archComponent L (σ • u) (glArch (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g))) ^
      (σ • u).mult)
    (fun u' => localHeight (archComponent L u' (glArch (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g))) ^ u'.mult)
    (fun _ => rfl)]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [archComponent_sigmaAdelicAct σ g (rfl : σ • u = σ • u), mult_smul,
    localHeight_map _ (norm_transport_infinite σ (rfl : σ • u = σ • u))]

theorem finHeight_sigmaAdelicAct_genuine (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    finHeight L (glFin (𝓞 L) L (sigmaAdelicAct K L (Dg K L) σ g)) = finHeight L (glFin (𝓞 L) L g) := by
  unfold finHeight
  symm
  refine finprod_eq_of_bijective (fun w => σ • w) (MulAction.bijective σ) fun w => ?_
  rw [finComponent_sigmaAdelicAct σ g (rfl : σ • w = σ • w),
    finLocalHeight_map _ (norm_transport_finite σ (rfl : σ • w = σ • w))]

end Genuine

end R4KitHeight

end

open R4KitHeight in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.sigmaAdelicAct K L D σ g) =
      NumberField.AdelicHeight.adelicHeight L g := by

  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = R4KitHeight.Dg K L := Subsingleton.elim _ _
  unfold NumberField.AdelicHeight.adelicHeight
  rw [archHeight_sigmaAdelicAct_genuine, finHeight_sigmaAdelicAct_genuine]

end S_AutomorphicForm_adelicHeight_sigmaAdelicAct
end P2MW
export P2MW.S_AutomorphicForm_adelicHeight_sigmaAdelicAct (solution)
