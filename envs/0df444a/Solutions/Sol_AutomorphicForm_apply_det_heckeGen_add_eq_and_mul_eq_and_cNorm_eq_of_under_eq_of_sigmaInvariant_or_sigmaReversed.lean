-- Prove2me | solution 1 for AutomorphicForm.apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3d5cc8ed-684b-5fcc-9a0d-b05e5e085dda

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_AutomorphicForm_HeckeEigensystem_cNorm_eq_of_asIdeal_eq_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped Pointwise NumberField.PlaceTransport

namespace R4TabFibSigma

section IdeleUnit

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable (v : HeightOneSpectrum R)

noncomputable def ideleAt : (v.adicCompletion K)ˣ →* (AdeleRing R K)ˣ :=
  (Units.map (finIncl R K)).comp (localUnit R K v)

variable {R K v}

theorem ideleAt_fst (t : (v.adicCompletion K)ˣ) : ((ideleAt R K v t : (AdeleRing R K)ˣ) : AdeleRing R K).1 = 1 := rfl

theorem ideleAt_snd_self (t : (v.adicCompletion K)ˣ) :
    ((ideleAt R K v t : (AdeleRing R K)ˣ) : AdeleRing R K).2 v = t :=
  localUnit_apply_self R K v t

theorem ideleAt_snd_of_ne (t : (v.adicCompletion K)ˣ) {w : HeightOneSpectrum R} (hw : w ≠ v) :
    ((ideleAt R K v t : (AdeleRing R K)ˣ) : AdeleRing R K).2 w = 1 :=
  localUnit_apply_of_ne R K v t hw

theorem det_heckeGenAt (t : (v.adicCompletion K)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt R K v t) = ideleAt R K v t := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  show (Matrix.diagonal ![((ideleAt R K v t : (AdeleRing R K)ˣ) : AdeleRing R K), 1] 0 0) *
      (Matrix.diagonal ![((ideleAt R K v t : (AdeleRing R K)ˣ) : AdeleRing R K), 1] 1 1) -
      (Matrix.diagonal ![((ideleAt R K v t : (AdeleRing R K)ˣ) : AdeleRing R K), 1] 0 1) *
      (Matrix.diagonal ![((ideleAt R K v t : (AdeleRing R K)ˣ) : AdeleRing R K), 1] 1 0) = _
  simp

theorem det_heckeGen :
    Matrix.GeneralLinearGroup.det (heckeGen R K v) = ideleAt R K v (uniformizerUnit K v) :=
  det_heckeGenAt (uniformizerUnit K v)

theorem localChar_eq {F : Type} [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (u : HeightOneSpectrum (𝓞 F)) (t : (u.adicCompletion F)ˣ) :
    NumberField.TateGlobal.localChar χ u t = χ (ideleAt (𝓞 F) F u t) := rfl

end IdeleUnit

section Transport

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem unitsAct_genuine_ideleAt (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)} (h : σ • w = w')
    (t : (w.adicCompletion L)ˣ) :
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct σ (ideleAt (𝓞 L) L w t)
      = ideleAt (𝓞 L) L w' (NumberField.PlaceTransport.transportUnits σ h t) := by
  refine Units.ext (Prod.ext ?_ ?_)
  ·
    funext u
    have hu : σ • (σ⁻¹ • u) = u := smul_inv_smul σ u
    show ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ
      ((ideleAt (𝓞 L) L w t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)).1 u =
        ((ideleAt (𝓞 L) L w' (NumberField.PlaceTransport.transportUnits σ h t) : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L).1 u
    rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ hu, ideleAt_fst,
      ideleAt_fst]
    exact map_one (NumberField.InfinitePlaceTransport.transport σ hu)
  ·
    refine Subtype.ext (funext fun u => ?_)
    show ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ
      ((ideleAt (𝓞 L) L w t : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)).2 u =
        ((ideleAt (𝓞 L) L w' (NumberField.PlaceTransport.transportUnits σ h t) : (AdeleRing (𝓞 L) L)ˣ) :
          AdeleRing (𝓞 L) L).2 u
    by_cases hu : u = w'
    · subst hu
      rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ h, ideleAt_snd_self,
        ideleAt_snd_self]
      rfl
    · have hu' : σ • (σ⁻¹ • u) = u := smul_inv_smul σ u
      have hne : σ⁻¹ • u ≠ w := by
        intro he
        apply hu
        rw [← hu', he, h]
      rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ hu', ideleAt_snd_of_ne _ hne,
        ideleAt_snd_of_ne _ hu, map_one]

omit [NumberField K] [NumberField L] in

theorem smul_eq_of_asIdeal_eq_smul (σ : L ≃ₐ[K] L) (w w' : HeightOneSpectrum (𝓞 L))
    (hw' : w'.asIdeal = σ • w.asIdeal) : σ • w = w' := by
  refine HeightOneSpectrum.ext ?_
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, hw', Ideal.pointwise_smul_def]
  rfl

omit [NumberField K] in

theorem valued_transportUnits_uniformizer_mul_inv (σ : L ≃ₐ[K] L) {w w' : HeightOneSpectrum (𝓞 L)}
    (h : σ • w = w') :
    Valued.v (((NumberField.PlaceTransport.transportUnits σ h (uniformizerUnit L w) * (uniformizerUnit L w')⁻¹ :
      (w'.adicCompletion L)ˣ)) : w'.adicCompletion L) = 1 := by
  have hT : Valued.v ((NumberField.PlaceTransport.transportUnits σ h (uniformizerUnit L w) :
      (w'.adicCompletion L)ˣ) : w'.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
    show Valued.v (NumberField.PlaceTransport.transport σ h (uniformizerUnit L w : w.adicCompletion L)) = _
    rw [NumberField.PlaceTransport.valued_transport, valued_uniformizerUnit]
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hT, valued_uniformizerUnit,
    mul_inv_cancel₀ WithZero.exp_ne_zero]

theorem apply_ideleAt_eq_one_of_isUnramifiedCharAt (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (u : HeightOneSpectrum (𝓞 L)) (hχ : NumberField.TateGlobal.IsUnramifiedCharAt χ u)
    (t : (u.adicCompletion L)ˣ) (ht : Valued.v (t : u.adicCompletion L) = 1) :
    χ (ideleAt (𝓞 L) L u t) = 1 := by
  have h1 : (t : u.adicCompletion L) ∈ u.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, ht]
  have h2 : ((t⁻¹ : (u.adicCompletion L)ˣ) : u.adicCompletion L) ∈ u.adicCompletionIntegers L := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, ht, inv_one]
  have := hχ t h1 h2
  rwa [localChar_eq] at this

theorem apply_unitsAct_genuine_det_heckeGen (σ : L ≃ₐ[K] L) (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (w w' : HeightOneSpectrum (𝓞 L)) (h : σ • w = w') (hχ : NumberField.TateGlobal.IsUnramifiedCharAt χ w') :
    χ ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).unitsAct σ
        (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w))) =
      χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) := by
  rw [det_heckeGen, det_heckeGen, unitsAct_genuine_ideleAt σ h]
  have hsplit : NumberField.PlaceTransport.transportUnits σ h (uniformizerUnit L w) =
      (NumberField.PlaceTransport.transportUnits σ h (uniformizerUnit L w) * (uniformizerUnit L w')⁻¹) *
        uniformizerUnit L w' := by
    rw [inv_mul_cancel_right]
  rw [hsplit, map_mul, map_mul,
    apply_ideleAt_eq_one_of_isUnramifiedCharAt χ w' hχ _ (valued_transportUnits_uniformizer_mul_inv σ h), one_mul]

end Transport

section Fibre

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem unif (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (w w' : HeightOneSpectrum (𝓞 L)) (h : σ • w = w')
    (hχ : NumberField.TateGlobal.IsUnramifiedCharAt χ w') :
    χ (D.unitsAct σ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w))) =
      χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  exact apply_unitsAct_genuine_det_heckeGen σ χ w w' h hχ

omit [NumberField K] [NumberField L] in

theorem smul_asIdeal (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : (σ • w).asIdeal = σ • w.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.pointwise_smul_def]
  rfl

private theorem _root_.R4TabFibSigma.under_smul [IsGalois K L] (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum.under (𝓞 K) (σ • w) = HeightOneSpectrum.under (𝓞 K) w := by
  refine HeightOneSpectrum.ext ?_
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, smul_asIdeal, Ideal.under_smul]

p2m_export "R4TabFibSigma" "under_smul"

noncomputable def val (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (u : HeightOneSpectrum (𝓞 L)) : ℂ :=
  ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L u)) : ℂˣ) : ℂ)

noncomputable def symTable (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (u : HeightOneSpectrum (𝓞 L)) : ℂ × ℂ × ℂ :=
  (val χ₁ u + val χ₂ u, val χ₁ u * val χ₂ u, AutomorphicForm.HeckeEigensystem.cNorm u)

theorem step [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hur : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      NumberField.TateGlobal.IsUnramifiedCharAt χ₁ w ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ w)
    (hrel : (∀ z : (AdeleRing (𝓞 L) L)ˣ, χ₁ (D.unitsAct σ z) = χ₁ z ∧ χ₂ (D.unitsAct σ z) = χ₂ z) ∨
      (∀ z : (AdeleRing (𝓞 L) L)ˣ, χ₁ (D.unitsAct σ z) = χ₂ z ∧ χ₂ (D.unitsAct σ z) = χ₁ z))
    (u : HeightOneSpectrum (𝓞 L)) (hu : u ∉ SL) :
    σ • u ∉ SL ∧ HeightOneSpectrum.under (𝓞 K) (σ • u) = HeightOneSpectrum.under (𝓞 K) u ∧
      symTable χ₁ χ₂ (σ • u) = symTable χ₁ χ₂ u := by
  have hunder : HeightOneSpectrum.under (𝓞 K) (σ • u) = HeightOneSpectrum.under (𝓞 K) u := under_smul σ u
  have hnot : σ • u ∉ SL := fun hmem => hu ((hSL (σ • u) u hunder).1 hmem)
  refine ⟨hnot, hunder, ?_⟩
  have h₁ := unif D σ χ₁ u (σ • u) rfl (hur _ hnot).1
  have h₂ := unif D σ χ₂ u (σ • u) rfl (hur _ hnot).2
  have hN : AutomorphicForm.HeckeEigensystem.cNorm (σ • u) = AutomorphicForm.HeckeEigensystem.cNorm u :=
    AutomorphicForm.HeckeEigensystem.cNorm_eq_of_asIdeal_eq_smul K L σ u (σ • u) (smul_asIdeal σ u)
  rcases hrel with hinv | hrev
  ·
    have e₁ : val χ₁ (σ • u) = val χ₁ u := by
      unfold val; rw [← h₁, (hinv _).1]
    have e₂ : val χ₂ (σ • u) = val χ₂ u := by
      unfold val; rw [← h₂, (hinv _).2]
    simp only [symTable, e₁, e₂, hN]
  ·
    have e₁ : val χ₁ (σ • u) = val χ₂ u := by
      unfold val; rw [← h₁, (hrev _).1]
    have e₂ : val χ₂ (σ • u) = val χ₁ u := by
      unfold val; rw [← h₂, (hrev _).2]
    simp only [symTable, e₁, e₂, hN, add_comm (val χ₂ u), mul_comm (val χ₂ u)]

theorem iterate [IsGalois K L] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hur : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      NumberField.TateGlobal.IsUnramifiedCharAt χ₁ w ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ w)
    (hrel : (∀ z : (AdeleRing (𝓞 L) L)ˣ, χ₁ (D.unitsAct σ z) = χ₁ z ∧ χ₂ (D.unitsAct σ z) = χ₂ z) ∨
      (∀ z : (AdeleRing (𝓞 L) L)ˣ, χ₁ (D.unitsAct σ z) = χ₂ z ∧ χ₂ (D.unitsAct σ z) = χ₁ z))
    (w : HeightOneSpectrum (𝓞 L)) (hw : w ∉ SL) (m : ℕ) :
    σ ^ m • w ∉ SL ∧ symTable χ₁ χ₂ (σ ^ m • w) = symTable χ₁ χ₂ w := by
  induction m with
  | zero => exact ⟨by rwa [pow_zero, one_smul], by rw [pow_zero, one_smul]⟩
  | succ m ih =>
    obtain ⟨hm, hT⟩ := ih
    obtain ⟨h1, -, h3⟩ := step D σ SL hSL χ₁ χ₂ hur hrel (σ ^ m • w) hm
    rw [pow_succ', mul_smul]
    exact ⟨h1, h3.trans hT⟩

end Fibre

end R4TabFibSigma

set_option linter.unusedVariables false in
open R4TabFibSigma in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hur : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      NumberField.TateGlobal.IsUnramifiedCharAt χ₁ w ∧ NumberField.TateGlobal.IsUnramifiedCharAt χ₂ w)
    (hrel : (∀ z : (AdeleRing (𝓞 L) L)ˣ, χ₁ (D.unitsAct σ z) = χ₁ z ∧ χ₂ (D.unitsAct σ z) = χ₂ z) ∨
      (∀ z : (AdeleRing (𝓞 L) L)ˣ, χ₁ (D.unitsAct σ z) = χ₂ z ∧ χ₂ (D.unitsAct σ z) = χ₁ z))
    (w w' : HeightOneSpectrum (𝓞 L)) (hw : w ∉ SL) (hw' : w' ∉ SL)
    (h : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') :
    ((χ₁ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) : ℂˣ) : ℂ) +
        ((χ₂ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) : ℂˣ) : ℂ) =
      ((χ₁ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) : ℂˣ) : ℂ) +
        ((χ₂ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) : ℂˣ) : ℂ) ∧
    ((χ₁ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) : ℂˣ) : ℂ) *
        ((χ₂ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) : ℂˣ) : ℂ) =
      ((χ₁ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) : ℂˣ) : ℂ) *
        ((χ₂ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w')) : ℂˣ) : ℂ) ∧
    AutomorphicForm.HeckeEigensystem.cNorm w = AutomorphicForm.HeckeEigensystem.cNorm w' := by

  have hI : w.asIdeal.under (𝓞 K) = w'.asIdeal.under (𝓞 K) := by
    have := congrArg HeightOneSpectrum.asIdeal h
    rwa [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal] at this
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 L) (L ≃ₐ[K] L) w.asIdeal w'.asIdeal hI
  obtain ⟨n, hn⟩ : ∃ n : ℕ, σ ^ n = g :=
    (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hgen g))
  have hw'eq : σ ^ n • w = w' := smul_eq_of_asIdeal_eq_smul (σ ^ n) w w' (by rw [hn]; exact hg)
  obtain ⟨-, hT⟩ := iterate D σ SL hSL χ₁ χ₂ hur hrel w hw n
  rw [hw'eq] at hT
  simp only [symTable, Prod.mk.injEq] at hT
  exact ⟨hT.1.symm, hT.2.1.symm, hT.2.2.symm⟩

end S_AutomorphicForm_apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed
end P2MW
export P2MW.S_AutomorphicForm_apply_det_heckeGen_add_eq_and_mul_eq_and_cNorm_eq_of_under_eq_of_sigmaInvariant_or_sigmaReversed (solution)
