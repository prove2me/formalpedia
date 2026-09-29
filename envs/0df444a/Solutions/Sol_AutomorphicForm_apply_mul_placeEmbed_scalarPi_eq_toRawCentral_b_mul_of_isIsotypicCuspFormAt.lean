-- Prove2me | solution 1 for AutomorphicForm.apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/16f8b753-efa3-515f-b53a-c7af5c3a40e4

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm UnramifiedWhittaker

noncomputable section

namespace CentralValueSol

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

def iota : GL (Fin 2) (v.adicCompletion F) →* AdelicGL2 (𝓞 F) F :=
  (AdelicDock.finEmbed (𝓞 F) F).comp (AdelicDock.localEmbed (𝓞 F) F v)

def Kv : Subgroup (GL (Fin 2) (v.adicCompletion F)) := AdelicDock.localLevelOne (𝓞 F) F v ⊤

variable {F v}

theorem placeEmbed_eq_iota : placeEmbed (R := 𝓞 F) F v = iota F v := rfl

theorem iota_apply (κ : GL (Fin 2) (v.adicCompletion F)) :
    iota F v κ = AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v κ) := rfl

theorem coe_iota (κ : GL (Fin 2) (v.adicCompletion F)) :
    ((iota F v κ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      AdelicDock.finMat (𝓞 F) F (AdelicDock.localMat (𝓞 F) F v κ) := rfl

theorem iota_mem_finiteAdelicGL2Subgroup (κ : GL (Fin 2) (v.adicCompletion F)) :
    iota F v κ ∈ finiteAdelicGL2Subgroup F :=
  AdelicDock.glArch_finEmbed _ _ _

theorem mem_Kv_iff (κ : GL (Fin 2) (v.adicCompletion F)) :
    κ ∈ Kv F v ↔
      (∀ i j, (κ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F) ∧
      (∀ i j, ((κ⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈
        v.adicCompletionIntegers F) := by
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F),
      AdelicDock.IsLocalLevelOne (𝓞 F) F v ⊤ m ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers F := by
    intro m
    constructor
    · exact fun h => h.integral
    · intro h
      refine ⟨h, ?_, ?_⟩
      · rw [idealBound_top]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
      · rw [idealBound_top]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (sub_mem (h 1 1) (one_mem _))
  rw [Kv, AdelicDock.mem_localLevelOne_iff, key, key]

theorem localLevelOne_eq_Kv {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) (hv : ¬ v.asIdeal ∣ N) :
    AdelicDock.localLevelOne (𝓞 F) F v N = Kv F v := by
  ext κ
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F),
      AdelicDock.IsLocalLevelOne (𝓞 F) F v N m ↔ ∀ i j, m i j ∈ v.adicCompletionIntegers F := by
    intro m
    constructor
    · exact fun h => h.integral
    · intro h
      refine ⟨h, ?_, ?_⟩
      · rw [idealBound_eq_one_of_not_dvd hN hv]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (h 1 0)
      · rw [idealBound_eq_one_of_not_dvd hN hv]
        exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (sub_mem (h 1 1) (one_mem _))
  rw [AdelicDock.mem_localLevelOne_iff, key, key, mem_Kv_iff]

theorem iota_mem_level {N : Ideal (𝓞 F)} {κ : GL (Fin 2) (v.adicCompletion F)}
    (hκ : κ ∈ AdelicDock.localLevelOne (𝓞 F) F v N) :
    iota F v κ ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine ⟨?_, iota_mem_finiteAdelicGL2Subgroup κ⟩
  change iota F v κ ∈ levelOne (𝓞 F) F N
  rw [iota_apply, AdelicDock.finEmbed_mem_levelOne_iff]
  exact hκ

theorem scalar_mem_Kv {u : (v.adicCompletion F)ˣ} (hu : Valued.v (u : v.adicCompletion F) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ Kv F v := by
  have hint : ∀ (w : (v.adicCompletion F)ˣ), Valued.v (w : v.adicCompletion F) = 1 →
      ∀ i j, ((Matrix.GeneralLinearGroup.scalar (Fin 2) w : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    intro w hw i j
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    change Matrix.diagonal (fun _ => (w : v.adicCompletion F)) i j ∈ _
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hw.le
    · exact zero_mem _
  refine (mem_Kv_iff _).mpr ⟨hint u hu, ?_⟩
  rw [← map_inv]
  refine hint u⁻¹ ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

theorem coe_centralScalar_apply (z : (AdeleRing (𝓞 F) F)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
  change ((Matrix.GeneralLinearGroup.scalar (Fin 2) z : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j = _
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  change Matrix.diagonal (fun _ => (z : AdeleRing (𝓞 F) F)) i j = _
  rw [Matrix.diagonal_apply]

theorem centralScalar_localUnit (t : (v.adicCompletion F)ˣ) :
    centralScalar (𝓞 F) F (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t)) =
      iota F v (Matrix.GeneralLinearGroup.scalar (Fin 2) t) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [coe_centralScalar_apply, coe_iota]
  change _ = (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
    AdelicDock.localMat (𝓞 F) F v ((Matrix.GeneralLinearGroup.scalar (Fin 2) t :
      GL (Fin 2) (v.adicCompletion F)) : Matrix _ _ _) i j) : AdeleRing (𝓞 F) F)
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  refine Prod.ext ?_ ?_
  · by_cases h : i = j
    · subst h
      rw [if_pos rfl, Units.coe_map]
      change (finIncl (𝓞 F) F _).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i i
      rw [finIncl_apply_fst, Matrix.one_apply_eq]
    · rw [if_neg h, Matrix.one_apply_ne h]
      rfl
  · refine Subtype.ext (funext fun w => ?_)
    change (if i = j then (((Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v t) : (AdeleRing (𝓞 F) F)ˣ) :
        AdeleRing (𝓞 F) F)) else 0).2 w =
      AdelicDock.localMat (𝓞 F) F v (Matrix.scalar (Fin 2) (t : v.adicCompletion F)) i j w
    by_cases hw : w = v
    · subst hw
      rw [AdelicDock.localMat_apply_self, Matrix.scalar_apply]
      by_cases h : i = j
      · subst h
        rw [if_pos rfl, Matrix.diagonal_apply_eq, Units.coe_map]
        change (finIncl (𝓞 F) F _).2 w = _
        rw [finIncl_apply_snd, localUnit_apply_self]
      · rw [if_neg h, Matrix.diagonal_apply_ne _ h]
        rfl
    · rw [AdelicDock.localMat_apply_of_ne _ _ _ _ _ _ hw]
      by_cases h : i = j
      · subst h
        rw [if_pos rfl, Matrix.one_apply_eq, Units.coe_map]
        change (finIncl (𝓞 F) F _).2 w = _
        rw [finIncl_apply_snd, localUnit_apply_of_ne _ _ _ _ hw]
      · rw [if_neg h, Matrix.one_apply_ne h]
        rfl

theorem centralScalar_mul_comm (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    centralScalar (𝓞 F) F z * g = g * centralScalar (𝓞 F) F z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  change Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) * (g : Matrix _ _ _) =
    (g : Matrix _ _ _) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
  exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq

theorem det_diagOne {A : Type*} [CommRing A] (z : Aˣ) :
    Matrix.GeneralLinearGroup.det (AdelicLevel.diagOne z) = z := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply,
    show ((AdelicLevel.diagOne z : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
        = Matrix.diagonal ![(z : A), 1] from rfl,
    Matrix.det_diagonal]
  simp

theorem det_heckeGen :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) =
      Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* _)
        (localUnit (𝓞 F) F v (uniformizerUnit F v)) := by
  show Matrix.GeneralLinearGroup.det
      (AdelicLevel.diagOne ((Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* _))
        (localUnit (𝓞 F) F v (uniformizerUnit F v)))) = _
  rw [det_diagOne]

theorem scalarPi_eq_scalar (π : v.adicCompletion F) (hπ : π ≠ 0) :
    scalarPi π hπ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 π hπ) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  change (!![π, 0; 0, π] : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
    Matrix.diagonal (fun _ => ((Units.mk0 π hπ : (v.adicCompletion F)ˣ) : v.adicCompletion F))
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end CentralValueSol

end

open CentralValueSol in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
        (fun w => heckeGen (𝓞 F) F w) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsIsotypicCuspFormAt F
      (productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
        (fun w => heckeGen (𝓞 F) F w) B) ξ N S Φ φ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) (hvN : ¬ v.asIdeal ∣ N)
    (ϖ : v.adicCompletionIntegers F)
    (hπ : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ)) :
    (∀ g : AdelicGL2 (𝓞 F) F,
        φ (g * placeEmbed F v (scalarPi (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) =
          Φ.toRawCentral.b v * φ g) ∧
    ((∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0) →
      (((ξ.comp Subgroup.topEquiv.symm.toMonoidHom)
          (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
            (localUnit (𝓞 F) F v (Units.mk0 _ hπ))) : ℂˣ) : ℂ) = Φ.toRawCentral.b v) := by

  have hN : N ≠ ⊥ := by
    rintro rfl
    exact hvN (dvd_zero _)

  have hu : Valued.v ((((uniformizerUnit F v)⁻¹ * Units.mk0 _ hπ : (v.adicCompletion F)ˣ)) :
      v.adicCompletion F) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, valued_uniformizerUnit,
      Units.val_mk0, hϖ, inv_mul_cancel₀ WithZero.exp_ne_zero]

  have hsplit : placeEmbed F v (scalarPi (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)
      = centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) *
          iota F v (Matrix.GeneralLinearGroup.scalar (Fin 2) ((uniformizerUnit F v)⁻¹ * Units.mk0 _ hπ)) := by
    rw [det_heckeGen, centralScalar_localUnit, ← map_mul, ← map_mul, mul_inv_cancel_left,
      placeEmbed_eq_iota, scalarPi_eq_scalar]
  have hlevel : iota F v (Matrix.GeneralLinearGroup.scalar (Fin 2) ((uniformizerUnit F v)⁻¹ * Units.mk0 _ hπ)) ∈
      levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine iota_mem_level ?_
    rw [localLevelOne_eq_Kv hN hvN]
    exact scalar_mem_Kv hu

  have h1 : ∀ g : AdelicGL2 (𝓞 F) F,
      φ (g * placeEmbed F v (scalarPi (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) =
        Φ.toRawCentral.b v * φ g := fun g => by
    rw [hsplit, ← mul_assoc, hφ.level_invariant _ _ hlevel, ← centralScalar_mul_comm]
    exact hφ.central_eigen v hv g
  refine ⟨h1, fun ⟨g, hg⟩ => ?_⟩

  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  have hA : IsAutomorphicFnAt F (productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
        (fun w => heckeGen (𝓞 F) F w) B) ξ φ := hφ.smoothCusp.1.1
  have hL := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hA
  set z : (productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
        (fun w => heckeGen (𝓞 F) F w) B).Z :=
    Subgroup.topEquiv.symm.toMonoidHom
      (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
        (localUnit (𝓞 F) F v (Units.mk0 _ hπ)))
    with hz
  have hzval : ((z : (productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
        (fun w => heckeGen (𝓞 F) F w) B).Z) : (AdeleRing (𝓞 F) F)ˣ)
      = Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
          (localUnit (𝓞 F) F v (Units.mk0 _ hπ)) :=
    rfl
  have hc := hL.1.central_transform z g
  rw [hzval, centralScalar_mul_comm, centralScalar_localUnit, ← scalarPi_eq_scalar _ hπ,
    ← placeEmbed_eq_iota, h1 g] at hc
  show ((ξ z : ℂˣ) : ℂ) = Φ.toRawCentral.b v
  exact (mul_right_cancel₀ hg hc).symm

end S_AutomorphicForm_apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt
end P2MW
export P2MW.S_AutomorphicForm_apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt (solution)
