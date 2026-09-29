-- Prove2me | solution 1 for AutomorphicForm.exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5a32e808-a880-5b5f-904c-8359fc8646a3

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_algHom
import Theorems.Thm_AutomorphicForm_exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom
import Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain

section

open NumberField IsDedekindDomain AutomorphicForm

noncomputable section

namespace LocalTestAssembly

variable (K : Type) [Field K] [NumberField K]

private theorem mul_mem_localIntegralSet (v : HeightOneSpectrum (𝓞 K))
    {x y : GL (Fin 2) (v.adicCompletion K)} (hx : x ∈ localIntegralSet K v)
    (hy : y ∈ localIntegralSet K v) : x * y ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hx hy ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hx.1 i k) (hy.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hy.2 i k) (hx.2 k j)

private theorem inv_mem_localIntegralSet (v : HeightOneSpectrum (𝓞 K))
    {x : GL (Fin 2) (v.adicCompletion K)} (hx : x ∈ localIntegralSet K v) :
    x⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hx ⊢
  refine ⟨hx.2, ?_⟩
  rw [inv_inv]
  exact hx.1

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

private def offS : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
  {h | ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v}

private theorem mul_mem_offS_iff {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hu : u ∈ unitFinSet K)
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : u * h ∈ offS K S ↔ h ∈ offS K S := by
  constructor
  · intro H v hv
    have H' := H v hv
    rw [map_mul] at H'
    have := mul_mem_localIntegralSet K v (inv_mem_localIntegralSet K v (hu v)) H'
    rwa [inv_mul_cancel_left] at this
  · intro H v hv
    rw [map_mul]
    exact mul_mem_localIntegralSet K v (hu v) (H v hv)

private theorem mem_mul_offS_iff {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hu : u ∈ unitFinSet K)
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : h * u ∈ offS K S ↔ h ∈ offS K S := by
  constructor
  · intro H v hv
    have H' := H v hv
    rw [map_mul] at H'
    have := mul_mem_localIntegralSet K v H' (inv_mem_localIntegralSet K v (hu v))
    rwa [mul_inv_cancel_right] at this
  · intro H v hv
    rw [map_mul]
    exact mul_mem_localIntegralSet K v (H v hv) (hu v)

private def finFactor (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ :=
  (offS K S).indicator fun h => ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v h)

private theorem finFactor_of_mem (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hh : h ∈ offS K S) :
    finFactor K S fS h = ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v h) :=
  Set.indicator_of_mem hh _

private theorem finFactor_of_notMem (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    {h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hh : h ∉ offS K S) : finFactor K S fS h = 0 :=
  Set.indicator_of_notMem hh _

private theorem finFactor_mul_left (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hu : u ∈ unitFinSet K)
    (hS : ∀ v ∈ S, ∀ y, fS v (AdelicLevel.finComponent (𝓞 K) K v u * y) = fS v y)
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : finFactor K S fS (u * h) = finFactor K S fS h := by
  by_cases hh : h ∈ offS K S
  · rw [finFactor_of_mem K S fS ((mul_mem_offS_iff K S hu h).2 hh), finFactor_of_mem K S fS hh]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [map_mul]
    exact hS v hv _
  · rw [finFactor_of_notMem K S fS (fun H => hh ((mul_mem_offS_iff K S hu h).1 H)),
      finFactor_of_notMem K S fS hh]

private theorem finFactor_mul_right (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hu : u ∈ unitFinSet K)
    (hS : ∀ v ∈ S, ∀ y, fS v (y * AdelicLevel.finComponent (𝓞 K) K v u) = fS v y)
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : finFactor K S fS (h * u) = finFactor K S fS h := by
  by_cases hh : h ∈ offS K S
  · rw [finFactor_of_mem K S fS ((mem_mul_offS_iff K S hu h).2 hh), finFactor_of_mem K S fS hh]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [map_mul]
    exact hS v hv _
  · rw [finFactor_of_notMem K S fS (fun H => hh ((mem_mul_offS_iff K S hu h).1 H)),
      finFactor_of_notMem K S fS hh]

private def levelIdeal (m : HeightOneSpectrum (𝓞 K) → ℕ) : Ideal (𝓞 K) := ∏ v ∈ S, v.asIdeal ^ m v

omit [NumberField K] in
private theorem levelIdeal_ne_bot (m : HeightOneSpectrum (𝓞 K) → ℕ) : levelIdeal K S m ≠ ⊥ := by
  rw [levelIdeal, ← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)

private theorem mem_of_dvd_levelIdeal (m : HeightOneSpectrum (𝓞 K) → ℕ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∣ levelIdeal K S m) : v ∈ S := by
  rw [levelIdeal] at hv
  obtain ⟨w, hw, hvw⟩ := (Prime.dvd_finsetProd_iff v.prime _).1 hv
  have h1 : v.asIdeal ∣ w.asIdeal := v.prime.dvd_of_dvd_pow hvw
  have h2 : w.asIdeal = v.asIdeal := w.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd h1)
  have h3 : w = v := HeightOneSpectrum.ext h2
  rw [← h3]
  exact hw

private theorem idealBound_levelIdeal_le (m : HeightOneSpectrum (𝓞 K) → ℕ) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∈ S) :
    AdelicLevel.idealBound (𝓞 K) (levelIdeal K S m) v ≤ WithZero.exp (-(m v : ℤ)) := by
  classical
  rw [AdelicLevel.idealBound_of_ne_bot (levelIdeal_ne_bot K S m), WithZero.exp_le_exp]
  have hdvd : v.asIdeal ^ m v ∣ levelIdeal K S m := Finset.dvd_prod_of_mem _ hv
  have h0 : Associates.mk (levelIdeal K S m) ≠ 0 :=
    Associates.mk_ne_zero.2 (by rw [Ideal.zero_eq_bot]; exact levelIdeal_ne_bot K S m)
  have hk : m v ≤ (Associates.mk v.asIdeal).count (Associates.mk (levelIdeal K S m)).factors :=
    (Associates.prime_pow_dvd_iff_le h0 (Associates.irreducible_mk.2 v.irreducible)).1
      (by rw [← Associates.mk_pow]; exact Associates.mk_le_mk_of_dvd hdvd)
  omega

private def wf : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) := AdelicLevel.glFin (𝓞 K) K (AdelicLevel.weyl (𝓞 K) K)

private theorem wf_val : (wf K : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) = !![0, 1; 1, 0] := by
  refine Matrix.ext fun i j => ?_
  rw [wf, AdelicLevel.glFin_apply]
  fin_cases i <;> fin_cases j <;> rfl

private theorem wf_mul_wf : wf K * wf K = 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, wf_val, Units.val_one, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp

private theorem wf_inv : (wf K)⁻¹ = wf K := inv_eq_of_mul_eq_one_right (wf_mul_wf K)

private theorem conj_wf_apply (p₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (i j : Fin 2) :
    ((wf K * p₀ * (wf K)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
      = (p₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (1 - i) (1 - j) := by
  rw [wf_inv, Units.val_mul, Units.val_mul, wf_val,
    Matrix.eta_fin_two (p₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)), Matrix.mul_fin_two,
    Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

private def finPrincipal (N : Ideal (𝓞 K)) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
  AdelicLevel.finiteLevelOne (𝓞 K) K N ⊓
    (AdelicLevel.finiteLevelOne (𝓞 K) K N).map (MulAut.conj (wf K)).toMonoidHom

private theorem glFin_mem_finPrincipal {N : Ideal (𝓞 K)} {u : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.principalLevel (𝓞 K) K N) : AdelicLevel.glFin (𝓞 K) K u ∈ finPrincipal K N := by
  have hu' : u ∈ AdelicLevel.levelOne (𝓞 K) K N ⊓
      (AdelicLevel.levelOne (𝓞 K) K N).map (MulAut.conj (AdelicLevel.weyl (𝓞 K) K)).toMonoidHom := hu
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hu'
  refine Subgroup.mem_inf.2 ⟨AdelicLevel.mem_levelOne_iff.1 h1, ?_⟩
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.1 h2
  refine Subgroup.mem_map.2 ⟨AdelicLevel.glFin (𝓞 K) K u₀, AdelicLevel.mem_levelOne_iff.1 hu₀, ?_⟩
  simp [wf, MulAut.conj_apply, map_mul, map_inv]

private theorem mem_unitFinSet_of_mem_finPrincipal {N : Ideal (𝓞 K)} {p : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hp : p ∈ finPrincipal K N) : p ∈ unitFinSet K := by
  obtain ⟨h1, -⟩ := Subgroup.mem_inf.1 hp
  obtain ⟨ha, hb⟩ := AdelicLevel.mem_finiteLevelOne_iff.1 h1
  rw [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe, AdelicLevel.mem_finiteIntegralGL2_iff]
  exact ⟨ha.integral, hb.integral⟩

private theorem sub_one_mem_idealBall_of_mem_finPrincipal {N : Ideal (𝓞 K)}
    {p : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hp : p ∈ finPrincipal K N) (i j : Fin 2) :
    (p : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j ∈ AdelicLevel.idealBall (𝓞 K) K N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hp
  obtain ⟨ha, -⟩ := AdelicLevel.mem_finiteLevelOne_iff.1 h1
  obtain ⟨p₀, hp₀, hp₀p⟩ := Subgroup.mem_map.1 h2
  obtain ⟨hc, -⟩ := AdelicLevel.mem_finiteLevelOne_iff.1 hp₀
  have hconj : ∀ i j : Fin 2, (p : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
      = (p₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (1 - i) (1 - j) := by
    have hp' : p = wf K * p₀ * (wf K)⁻¹ := by
      rw [← hp₀p]
      simp [MulAut.conj_apply]
    intro i j
    rw [hp']
    exact conj_wf_apply K p₀ i j
  fin_cases i <;> fin_cases j
  ·
    simpa [hconj] using hc.lowerRight
  ·
    simpa [hconj] using hc.lowerLeft
  ·
    simpa using ha.lowerLeft
  ·
    simpa using ha.lowerRight

private def IsDeep (v : HeightOneSpectrum (𝓞 K)) (m : ℕ) (x : GL (Fin 2) (v.adicCompletion K)) : Prop :=
  ∀ i j : Fin 2, Valued.v ((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(m : ℤ))

private theorem one_entry_apply (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) v
      = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem isDeep_of_mem_finPrincipal (m : HeightOneSpectrum (𝓞 K) → ℕ)
    {p : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hp : p ∈ finPrincipal K (levelIdeal K S m))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    IsDeep K v (m v) (AdelicLevel.finComponent (𝓞 K) K v p) := by
  intro i j
  rw [AdelicLevel.finComponent_apply]
  have hb := sub_one_mem_idealBall_of_mem_finPrincipal K hp i j v
  rw [AdelicLevel.coe_sub_apply, one_entry_apply] at hb
  exact le_trans hb (idealBound_levelIdeal_le K S m hv)

private theorem isOpen_finPrincipal {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) :
    IsOpen (finPrincipal K N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  have h1 := AdelicLevel.isOpen_finiteLevelOne (𝓞 K) K hN
  rw [finPrincipal, MulEquiv.toMonoidHom_eq_coe, Subgroup.map_equiv_eq_comap_symm, Subgroup.coe_inf,
    Subgroup.coe_comap]
  refine h1.inter (h1.preimage ?_)
  show Continuous fun x => (MulAut.conj (wf K)).symm x
  simp only [MulAut.conj_symm_apply]
  exact (continuous_const.mul continuous_id).mul continuous_const

private theorem isLocallyConstant_of_right_invariant {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    {P : Subgroup G} (hP : IsOpen (P : Set G)) {φ : G → ℂ} (hφ : ∀ p ∈ P, ∀ x, φ (x * p) = φ x) :
    IsLocallyConstant φ := by
  refine (IsLocallyConstant.iff_exists_open φ).2 fun x => ⟨(fun p => x * p) '' (P : Set G), ?_, ?_, ?_⟩
  · exact (Homeomorph.mulLeft x).isOpenMap _ hP
  · exact ⟨1, P.one_mem, mul_one x⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact hφ p hp x

private theorem isCompact_setOf_integral_off (B : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K))
    (hB : ∀ v ∈ S, IsCompact (B v)) :
    IsCompact {x : FiniteAdeleRing (𝓞 K) K |
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → x v ∈ v.adicCompletionIntegers K) ∧ ∀ v ∈ S, x v ∈ B v} := by
  classical
  have hO : ∀ v : HeightOneSpectrum (𝓞 K),
      (interior (v.adicCompletionIntegers K : Set (v.adicCompletion K))).Nonempty := fun v => by
    have hopen : IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
      Valued.isOpen_valuationSubring _
    rw [hopen.interior_eq]
    exact ⟨0, zero_mem _⟩
  choose t ht using fun v : S => compact_covered_by_add_left_translates (hB v.1 v.2) (hO v.1)
  let shift : (∀ v : S, (v.1).adicCompletion K) → FiniteAdeleRing (𝓞 K) K := fun c =>
    ∑ v : S, RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v.1 (c v)
  let A : Finset (FiniteAdeleRing (𝓞 K) K) := (Fintype.piFinset t).image shift
  have hshift_on : ∀ (c : ∀ v : S, (v.1).adicCompletion K) (w : HeightOneSpectrum (𝓞 K)) (hw : w ∈ S),
      shift c w = c ⟨w, hw⟩ := by
    intro c w hw
    have h1 : shift c w = ∑ v : S, (RestrictedProduct.single
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v.1 (c v)) w :=
      map_sum (AdelicLevel.finAdeleEval (𝓞 K) K w) _ _
    rw [h1, Finset.sum_eq_single (⟨w, hw⟩ : S)]
    · simp
    · intro v _ hv
      have hne : v.1 ≠ w := fun h => hv (Subtype.ext h)
      simp [hne.symm]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hshift_off : ∀ (c : ∀ v : S, (v.1).adicCompletion K) (w : HeightOneSpectrum (𝓞 K)) (hw : w ∉ S),
      shift c w = 0 := by
    intro c w hw
    have h1 : shift c w = ∑ v : S, (RestrictedProduct.single
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v.1 (c v)) w :=
      map_sum (AdelicLevel.finAdeleEval (𝓞 K) K w) _ _
    rw [h1]
    refine Finset.sum_eq_zero fun v _ => ?_
    have hne : v.1 ≠ w := fun h => hw (h ▸ v.2)
    simp [hne.symm]
  have hcover : {x : FiniteAdeleRing (𝓞 K) K |
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → x v ∈ v.adicCompletionIntegers K) ∧ ∀ v ∈ S, x v ∈ B v} ⊆
      ⋃ a ∈ A, (fun x => a + x) ⁻¹' AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rintro x ⟨hoff, hon⟩
    have hex : ∀ v : S, ∃ g ∈ t v, g + x v.1 ∈ (v.1).adicCompletionIntegers K := fun v => by
      obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 (ht v (hon v.1 v.2))
      exact ⟨g, hg, hgx⟩
    choose c hc hc' using hex
    refine Set.mem_iUnion₂.2 ⟨shift c, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.2 hc), ?_⟩
    refine fun w => ?_
    show (shift c + x) w ∈ w.adicCompletionIntegers K
    rw [AdelicLevel.coe_add_apply]
    by_cases hw : w ∈ S
    · rw [hshift_on c w hw]
      exact hc' ⟨w, hw⟩
    · rw [hshift_off c w hw, zero_add]
      exact hoff w hw
  have hclosed : IsClosed {x : FiniteAdeleRing (𝓞 K) K |
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → x v ∈ v.adicCompletionIntegers K) ∧ ∀ v ∈ S, x v ∈ B v} := by
    have heq : {x : FiniteAdeleRing (𝓞 K) K |
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → x v ∈ v.adicCompletionIntegers K) ∧ ∀ v ∈ S, x v ∈ B v} =
        (⋂ v : HeightOneSpectrum (𝓞 K), ⋂ (_ : v ∉ S),
            AdelicLevel.finAdeleEval (𝓞 K) K v ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K))) ∩
          ⋂ v : HeightOneSpectrum (𝓞 K), ⋂ (_ : v ∈ S), AdelicLevel.finAdeleEval (𝓞 K) K v ⁻¹' B v := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe,
        AdelicLevel.finAdeleEval_apply]
    rw [heq]
    refine IsClosed.inter (isClosed_iInter fun v => isClosed_iInter fun _ => ?_)
      (isClosed_iInter fun v => isClosed_iInter fun hv => ?_)
    · exact (AdelicLevel.isClosed_adicCompletionIntegers v).preimage (AdelicLevel.continuous_finAdeleEval (𝓞 K) K v)
    · exact (hB v hv).isClosed.preimage (AdelicLevel.continuous_finAdeleEval (𝓞 K) K v)
  refine IsCompact.of_isClosed_subset ?_ hclosed hcover
  refine A.isCompact_biUnion fun a _ => ?_
  exact (Homeomorph.addLeft a).isCompact_preimage.2 (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)

private def entryBall (v : HeightOneSpectrum (𝓞 K)) (C : Set (GL (Fin 2) (v.adicCompletion K))) :
    Set (v.adicCompletion K) :=
  ⋃ i : Fin 2, ⋃ j : Fin 2,
    ((fun x : GL (Fin 2) (v.adicCompletion K) => (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) '' C ∪
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) '' C)

private theorem isCompact_entryBall (v : HeightOneSpectrum (𝓞 K)) {C : Set (GL (Fin 2) (v.adicCompletion K))}
    (hC : IsCompact C) : IsCompact (entryBall K v C) := by
  refine isCompact_iUnion fun i => isCompact_iUnion fun j => IsCompact.union ?_ ?_
  · exact hC.image (Units.continuous_val.matrix_elem i j)
  · exact hC.image (Units.continuous_coe_inv.matrix_elem i j)

private theorem entry_mem_entryBall (v : HeightOneSpectrum (𝓞 K)) {C : Set (GL (Fin 2) (v.adicCompletion K))}
    {x : GL (Fin 2) (v.adicCompletion K)} (hx : x ∈ C) (i j : Fin 2) :
    (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ entryBall K v C :=
  Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Or.inl ⟨x, hx, rfl⟩⟩⟩

private theorem inv_entry_mem_entryBall (v : HeightOneSpectrum (𝓞 K)) {C : Set (GL (Fin 2) (v.adicCompletion K))}
    {x : GL (Fin 2) (v.adicCompletion K)} (hx : x ∈ C) (i j : Fin 2) :
    ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      ∈ entryBall K v C :=
  Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Or.inr ⟨x, hx, rfl⟩⟩⟩

private theorem hasCompactSupport_finFactor
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfS : ∀ v ∈ S, IsLocalTestFn K v (fS v)) : HasCompactSupport (finFactor K S fS) := by
  have hEc : IsCompact {x : FiniteAdeleRing (𝓞 K) K |
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → x v ∈ v.adicCompletionIntegers K) ∧
        ∀ v ∈ S, x v ∈ entryBall K v (tsupport (fS v))} :=
    isCompact_setOf_integral_off K S (fun v => entryBall K v (tsupport (fS v)))
      fun v hv => isCompact_entryBall K v (hfS v hv).2
  refine HasCompactSupport.intro (isCompact_integralUnitsSet hEc) fun h hh => ?_
  by_contra hne
  apply hh
  have hoff : h ∈ offS K S := by
    by_contra hoff
    exact hne (finFactor_of_notMem K S fS hoff)
  rw [finFactor_of_mem K S fS hoff] at hne
  have hsupp : ∀ v ∈ S, AdelicLevel.finComponent (𝓞 K) K v h ∈ tsupport (fS v) := fun v hv =>
    subset_tsupport _ (Finset.prod_ne_zero_iff.1 hne v hv)
  rw [mem_integralUnitsSet]
  refine ⟨fun i j => ⟨fun v hv => ?_, fun v hv => ?_⟩, fun i j => ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
  · exact ((mem_localIntegralSet K v).1 (hoff v hv)).1 i j
  · exact entry_mem_entryBall K v (hsupp v hv) i j
  · have := ((mem_localIntegralSet K v).1 (hoff v hv)).2 i j
    rwa [← map_inv] at this
  · have := inv_entry_mem_entryBall K v (hsupp v hv) i j
    rwa [← map_inv] at this

private def glob (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ) :
    GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ :=
  fun g => fa (AdelicLevel.glArch (𝓞 K) K g) * finFactor K S fS (AdelicLevel.glFin (𝓞 K) K g)

private theorem finFactor_biInvariant (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (m : HeightOneSpectrum (𝓞 K) → ℕ)
    (hm : ∀ v ∈ S, ∀ x : GL (Fin 2) (v.adicCompletion K), IsDeep K v (m v) x →
      ∀ y, fS v (x * y) = fS v y ∧ fS v (y * x) = fS v y)
    {p : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (hp : p ∈ finPrincipal K (levelIdeal K S m))
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    finFactor K S fS (p * h) = finFactor K S fS h ∧ finFactor K S fS (h * p) = finFactor K S fS h := by
  have hu := mem_unitFinSet_of_mem_finPrincipal K hp
  constructor
  · exact finFactor_mul_left K S fS hu
      (fun v hv y => (hm v hv _ (isDeep_of_mem_finPrincipal K S m hp hv) y).1) h
  · exact finFactor_mul_right K S fS hu
      (fun v hv y => (hm v hv _ (isDeep_of_mem_finPrincipal K S m hp hv) y).2) h

private theorem isFinTestFactor_finFactor
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfS : ∀ v ∈ S, IsLocalTestFn K v (fS v)) (m : HeightOneSpectrum (𝓞 K) → ℕ)
    (hm : ∀ v ∈ S, ∀ x : GL (Fin 2) (v.adicCompletion K), IsDeep K v (m v) x →
      ∀ y, fS v (x * y) = fS v y ∧ fS v (y * x) = fS v y) :
    IsFinTestFactor K (finFactor K S fS) :=
  ⟨isLocallyConstant_of_right_invariant (isOpen_finPrincipal K (levelIdeal_ne_bot K S m))
      fun _ hp h => (finFactor_biInvariant K S fS m hm hp h).2,
    hasCompactSupport_finFactor K S fS hfS⟩

private theorem isUnitFactorization_glob (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : IsArchTestFactor K fa)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfS : ∀ v ∈ S, IsLocalTestFn K v (fS v)) (m : HeightOneSpectrum (𝓞 K) → ℕ)
    (hm : ∀ v ∈ S, ∀ x : GL (Fin 2) (v.adicCompletion K), IsDeep K v (m v) x →
      ∀ y, fS v (x * y) = fS v y ∧ fS v (y * x) = fS v y) :
    IsUnitFactorization K S (glob K S fa fS) fa (finFactor K S fS) fS :=
  ⟨hfa, isFinTestFactor_finFactor K S fS hfS m hm, hfS,
    fun h hh => finFactor_of_mem K S fS hh,
    fun h hh => finFactor_of_notMem K S fS fun H => by
      obtain ⟨v, hv, hv'⟩ := hh
      exact hv' (H v hv),
    fun _ => rfl⟩

private theorem isBiInvariantUnder_glob (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (m : HeightOneSpectrum (𝓞 K) → ℕ)
    (hm : ∀ v ∈ S, ∀ x : GL (Fin 2) (v.adicCompletion K), IsDeep K v (m v) x →
      ∀ y, fS v (x * y) = fS v y ∧ fS v (y * x) = fS v y) :
    IsBiInvariantUnder K (AdelicLevel.principalLevel (𝓞 K) K (levelIdeal K S m) ⊓ finiteAdelicGL2Subgroup K)
      (glob K S fa fS) := by
  intro u hu g
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
  have harch : AdelicLevel.glArch (𝓞 K) K u = 1 := (mem_finiteAdelicGL2Subgroup_iff K u).1 hu2
  have hp := glFin_mem_finPrincipal K hu1
  obtain ⟨hl, hr⟩ := finFactor_biInvariant K S fS m hm hp (AdelicLevel.glFin (𝓞 K) K g)
  constructor
  · simp only [glob, map_mul, harch, one_mul, hl]
  · simp only [glob, map_mul, harch, mul_one, hr]

private theorem exists_assembly (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : IsArchTestFactor K fa)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfS : ∀ v ∈ S, IsLocalTestFn K v (fS v)) (m : HeightOneSpectrum (𝓞 K) → ℕ)
    (hm : ∀ v ∈ S, ∀ x : GL (Fin 2) (v.adicCompletion K), IsDeep K v (m v) x →
      ∀ y, fS v (x * y) = fS v y ∧ fS v (y * x) = fS v y) :
    ∃ (N' : Ideal (𝓞 K)) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
      (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      N' ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ S) ∧
      IsUnitFactorization K S f fa ff fS ∧
      IsUnitFactorizableAt K (AdelicLevel.principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) S f :=
  ⟨levelIdeal K S m, glob K S fa fS, finFactor K S fS, levelIdeal_ne_bot K S m,
    fun _ hv => mem_of_dvd_levelIdeal K S m hv, isUnitFactorization_glob K S fa hfa fS hfS m hm,
    (isUnitFactorizableAt_iff K S _ _).2 ⟨isBiInvariantUnder_glob K S fa fS m hm, fa, finFactor K S fS, fS,
      isUnitFactorization_glob K S fa hfa fS hfS m hm⟩⟩

end LocalTestAssembly

end

end

section

open NumberField IsDedekindDomain AutomorphicForm Filter Topology

namespace LocalSupply

private theorem exists_mem_nhds_one_forall_mul_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {f : G → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x ∈ W, ∀ y, f (x * y) = f y ∧ f (y * x) = f y := by
  have hL : IsOpen {z : G × G | f (z.1 * z.2) = f z.2} := by
    have h1 : IsLocallyConstant fun z : G × G => f (z.1 * z.2) := hf.comp_continuous continuous_mul
    have h2 : IsLocallyConstant fun z : G × G => f z.2 := hf.comp_continuous continuous_snd
    exact (h1.prodMk h2) {p : ℂ × ℂ | p.1 = p.2}
  have hR : IsOpen {z : G × G | f (z.2 * z.1) = f z.2} := by
    have h1 : IsLocallyConstant fun z : G × G => f (z.2 * z.1) :=
      hf.comp_continuous (continuous_snd.mul continuous_fst)
    have h2 : IsLocallyConstant fun z : G × G => f z.2 := hf.comp_continuous continuous_snd
    exact (h1.prodMk h2) {p : ℂ × ℂ | p.1 = p.2}
  have hLe : ∀ᶠ x in 𝓝 (1 : G), ∀ y ∈ tsupport f, f (x * y) = f y :=
    IsCompact.eventually_forall_of_forall_eventually (x₀ := (1 : G))
      (P := fun x y => f (x * y) = f y) (hc : IsCompact (tsupport f))
      fun y _ => hL.mem_nhds (by simp)
  have hRe : ∀ᶠ x in 𝓝 (1 : G), ∀ y ∈ tsupport f, f (y * x) = f y :=
    IsCompact.eventually_forall_of_forall_eventually (x₀ := (1 : G))
      (P := fun x y => f (y * x) = f y) (hc : IsCompact (tsupport f))
      fun y _ => hR.mem_nhds (by simp)
  have hinv : Tendsto (fun x : G => x⁻¹) (𝓝 (1 : G)) (𝓝 (1 : G)) := by
    simpa only [inv_one] using continuous_inv.tendsto (1 : G)
  have hLi : ∀ᶠ x in 𝓝 (1 : G), ∀ y ∈ tsupport f, f (x⁻¹ * y) = f y := hinv.eventually hLe
  have hRi : ∀ᶠ x in 𝓝 (1 : G), ∀ y ∈ tsupport f, f (y * x⁻¹) = f y := hinv.eventually hRe
  obtain ⟨W, hW, hWall⟩ := (hLe.and (hRe.and (hLi.and hRi))).exists_mem
  refine ⟨W, hW, fun x hx y => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hWall x hx
  constructor
  · by_cases hy : y ∈ tsupport f
    · exact h1 y hy
    · by_cases hxy : x * y ∈ tsupport f
      · have h := h3 (x * y) hxy
        rw [inv_mul_cancel_left] at h
        exact h.symm
      · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hxy]
  · by_cases hy : y ∈ tsupport f
    · exact h2 y hy
    · by_cases hxy : y * x ∈ tsupport f
      · have h := h4 (y * x) hxy
        rw [mul_inv_cancel_right] at h
        exact h.symm
      · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hxy]

private theorem exists_nat_forall_valued_sub_le_imp_mem {R : Type*} [Ring R]
    [Valued R (WithZero (Multiplicative ℤ))] {a : R} {s : Set R} (hs : s ∈ 𝓝 a) :
    ∃ n : ℕ, ∀ y : R, Valued.v (y - a) ≤ WithZero.exp (-(n : ℤ)) → y ∈ s := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
  obtain ⟨e, he, hlt⟩ : ∃ e : WithZero (Multiplicative ℤ), e ≠ 0 ∧
      ∀ z : R, Valued.v z < e →
        (Valued.v : Valuation R (WithZero (Multiplicative ℤ))).restrict z < γ.1 := by
    refine ⟨_, ?_, fun z hz =>
      (Valuation.restrict_lt_iff_lt_embedding
        (Valued.v : Valuation R (WithZero (Multiplicative ℤ)))).mpr hz⟩
    exact (map_ne_zero _).mpr γ.ne_zero
  obtain ⟨n, hn⟩ := WithZero.exists_exp_neg_natCast_lt he
  exact ⟨n, fun y hy => hγ (hlt _ (lt_of_le_of_lt hy hn))⟩

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private def depthSet (m : ℕ) : Set (GL (Fin 2) (v.adicCompletion K)) :=
  {x | ∀ i j, Valued.v ((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(m : ℤ))}

private theorem depthSet_antitone : Antitone (depthSet K v) := by
  intro m n hmn x hx
  simp only [depthSet, Set.mem_setOf_eq] at hx ⊢
  intro i j
  refine (hx i j).trans ?_
  rw [WithZero.exp_le_exp]
  omega

private def depthFilter : Filter (GL (Fin 2) (v.adicCompletion K)) := ⨅ m : ℕ, 𝓟 (depthSet K v m)

private theorem depthSet_mem_depthFilter (m : ℕ) : depthSet K v m ∈ depthFilter K v :=
  mem_iInf_of_mem m (mem_principal_self _)

private theorem tendsto_val_depthFilter :
    Tendsto (fun x : GL (Fin 2) (v.adicCompletion K) =>
        (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
      (depthFilter K v) (𝓝 (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := by
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  rw [tendsto_def]
  intro s hs
  obtain ⟨n, hn⟩ := exists_nat_forall_valued_sub_le_imp_mem hs
  exact mem_of_superset (depthSet_mem_depthFilter K v n) fun x hx => hn _ (hx i j)

private theorem depthFilter_le_nhds_one : depthFilter K v ≤ 𝓝 (1 : GL (Fin 2) (v.adicCompletion K)) := by
  have hval := tendsto_val_depthFilter K v

  have hdet : ContinuousAt (Ring.inverse : v.adicCompletion K → v.adicCompletion K)
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det := by
    rw [Matrix.det_one, Ring.inverse_eq_inv']
    exact continuousAt_inv₀ one_ne_zero
  have hinvmat : ContinuousAt (Inv.inv : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) → _) 1 :=
    continuousAt_matrix_inv _ hdet
  have hone : ((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))⁻¹) = 1 := by
    have h := Matrix.coe_units_inv (1 : GL (Fin 2) (v.adicCompletion K))
    rw [inv_one, Units.val_one] at h
    exact h.symm
  have hinv : Tendsto (fun x : GL (Fin 2) (v.adicCompletion K) =>
      ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
      (depthFilter K v) (𝓝 (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := by
    have h := hinvmat.tendsto.comp hval
    rw [hone] at h
    refine h.congr fun x => ?_
    simp only [Function.comp_apply, Matrix.coe_units_inv]

  have key : Tendsto (id : GL (Fin 2) (v.adicCompletion K) → GL (Fin 2) (v.adicCompletion K))
      (depthFilter K v)
      (𝓝 (1 : GL (Fin 2) (v.adicCompletion K))) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    have h2 : Tendsto (fun x : GL (Fin 2) (v.adicCompletion K) =>
        MulOpposite.op
          ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
        (depthFilter K v) (𝓝 (MulOpposite.op (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) :=
      (MulOpposite.continuous_op.tendsto _).comp hinv
    have h := hval.prodMk_nhds h2
    simpa only [Function.comp_def, id_eq, Units.embedProduct_apply, inv_one, Units.val_one] using h
  exact tendsto_id'.mp key

private theorem localDepth (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : IsLocalTestFn K v fv) :
    ∃ m : ℕ, ∀ x : GL (Fin 2) (v.adicCompletion K),
      (∀ i j, Valued.v ((x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
          - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      ∀ y, fv (x * y) = fv y ∧ fv (y * x) = fv y := by
  obtain ⟨W, hW, hWall⟩ := exists_mem_nhds_one_forall_mul_eq hfv.1 hfv.2
  have hWF : W ∈ depthFilter K v := depthFilter_le_nhds_one K v hW
  have hanti : Antitone fun m : ℕ => 𝓟 (depthSet K v m) :=
    fun m n hmn => principal_mono.mpr (depthSet_antitone K v hmn)
  obtain ⟨m, hm⟩ := (mem_iInf_of_directed hanti.directed_ge W).mp hWF
  exact ⟨m, fun x hx y => hWall x (mem_principal.mp hm (show x ∈ depthSet K v m from hx)) y⟩

end LocalSupply

end

section

open NumberField IsDedekindDomain AutomorphicForm

namespace LocalSupply

variable (L : Type) [Field L] [NumberField L]

noncomputable section

private def adelicFinGLIncl : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) →* AdelicGL2 (𝓞 L) L :=
  (Units.mapEquiv (adelicMatrixProdEquiv L).symm.toMulEquiv).toMonoidHom.comp <|
    (MulEquiv.prodUnits.symm : _ ≃* (_ × _)ˣ).toMonoidHom.comp <|
      MonoidHom.prod (1 : _ →* GL (Fin 2) (InfiniteAdeleRing L)) (MonoidHom.id _)

private theorem glArch_adelicFinGLIncl (y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    AdelicLevel.glArch (𝓞 L) L (adelicFinGLIncl L y) = 1 := by
  ext i j
  rfl

private theorem glFin_adelicFinGLIncl (y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    AdelicLevel.glFin (𝓞 L) L (adelicFinGLIncl L y) = y := by
  ext i j
  rfl

end

private theorem ext_of_glArch_of_glFin {a b : AdelicGL2 (𝓞 L) L}
    (h1 : AdelicLevel.glArch (𝓞 L) L a = AdelicLevel.glArch (𝓞 L) L b)
    (h2 : AdelicLevel.glFin (𝓞 L) L a = AdelicLevel.glFin (𝓞 L) L b) : a = b := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have e1 : ((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1
      = ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 :=
    congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing L) =>
      (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j) h1
  have e2 : ((a : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2
      = ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 :=
    congrArg (fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) =>
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) h2
  exact Prod.ext e1 e2

private theorem commute_adelicFinGLIncl_rowIsometryInclAt₀ (y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (w : InfinitePlace L) (k : rowIsometrySubgroup₀ w.Completion) :
    Commute (adelicFinGLIncl L y) (rowIsometryInclAt₀ L w k) := by
  show adelicFinGLIncl L y * rowIsometryInclAt₀ L w k
    = rowIsometryInclAt₀ L w k * adelicFinGLIncl L y
  refine ext_of_glArch_of_glFin L ?_ ?_
  · rw [map_mul, map_mul, glArch_adelicFinGLIncl, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_adelicFinGLIncl, glFin_rowIsometryInclAt₀, one_mul, mul_one]

private theorem transport_typeSubmodule {w : InfinitePlace L} {W : Type*} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) W} {Φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hΦ : Φ ∈ typeSubmodule (rowIsometryInclAt₀ L w) ρ) (g₀ : AdelicGL2 (𝓞 L) L)
    (hg₀ : ∀ k, Commute g₀ (rowIsometryInclAt₀ L w k)) (c : ℂ) :
    (fun x : GL (Fin 2) (InfiniteAdeleRing L) => Φ (adelicArchGLIncl L x * g₀) * c) ∈
      typeSubmodule (archRowIsometryInclAt₀ L w) ρ :=
  comp_mul_mem_typeSubmodule_of_hom (ι := archRowIsometryInclAt₀ L w) (ι' := rowIsometryInclAt₀ L w)
    (adelicArchGLIncl L) (fun _ => rfl) (m := fun _ => c) (fun _ _ => rfl)
    (comp_mul_mem_typeSubmodule_of_commute hΦ g₀ hg₀)

private theorem isArchFactorBiFinite_of_isArchBiFinite {tys : ArchTypeFamily L} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    {φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    (hφ : IsArchBiFinite L tys φ)
    (hfac : ∀ g, φ g = φa (AdelicLevel.glArch (𝓞 L) L g) * φf (AdelicLevel.glFin (𝓞 L) L g))
    {y₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hy₀ : φf y₀ ≠ 0) :
    IsArchFactorBiFinite L tys φa := by
  have hA : ∀ x : GL (Fin 2) (InfiniteAdeleRing L),
      φ (adelicArchGLIncl L x * adelicFinGLIncl L y₀) * (φf y₀)⁻¹ = φa x := by
    intro x
    rw [hfac, map_mul, map_mul, glArch_adelicArchGLIncl, glArch_adelicFinGLIncl, mul_one,
      glFin_adelicArchGLIncl, glFin_adelicFinGLIncl, one_mul, mul_inv_cancel_right₀ hy₀]
  have hB : ∀ x : GL (Fin 2) (InfiniteAdeleRing L),
      φ (adelicArchGLIncl L x * adelicFinGLIncl L y₀⁻¹)⁻¹ * (φf y₀)⁻¹ = φa x⁻¹ := by
    intro x
    rw [mul_inv_rev, ← map_inv, ← map_inv, inv_inv, hfac, map_mul, map_mul, glArch_adelicFinGLIncl,
      glArch_adelicArchGLIncl, one_mul, glFin_adelicFinGLIncl, glFin_adelicArchGLIncl, mul_one,
      mul_inv_cancel_right₀ hy₀]
  have h1 : (fun x => φ x⁻¹) ∈ ⨅ w : InfinitePlace L, ⨆ i : Fin (tys.card w),
      archTypeSubmoduleAt L w (tys.rep w i) := hφ.1
  have h2 : φ ∈ ⨅ w : InfinitePlace L, ⨆ i : Fin (tys.card w),
      archDualTypeSubmoduleAt L w (tys.rep w i) := hφ.2
  refine ⟨?_, ?_⟩
  · show (fun x => φa x⁻¹) ∈ ⨅ w : InfinitePlace L, ⨆ i : Fin (tys.card w),
      archFactorTypeSubmoduleAt L w (tys.rep w i)
    refine (Submodule.mem_iInf _).mpr fun w => ?_
    have key : (fun x : GL (Fin 2) (InfiniteAdeleRing L) =>
        φ (adelicArchGLIncl L x * adelicFinGLIncl L y₀⁻¹)⁻¹ * (φf y₀)⁻¹) ∈
          ⨆ i : Fin (tys.card w), archFactorTypeSubmoduleAt L w (tys.rep w i) :=
      comp_mul_mem_iSup_of_forall (fun x => adelicArchGLIncl L x * adelicFinGLIncl L y₀⁻¹)
        (fun _ => (φf y₀)⁻¹) (fun i => archTypeSubmoduleAt L w (tys.rep w i))
        (fun i => archFactorTypeSubmoduleAt L w (tys.rep w i))
        (fun _ Φ hΦ => transport_typeSubmodule L hΦ _
          (commute_adelicFinGLIncl_rowIsometryInclAt₀ L y₀⁻¹ w) _)
        ((Submodule.mem_iInf _).mp h1 w)
    have e : (fun x : GL (Fin 2) (InfiniteAdeleRing L) => φa x⁻¹) = fun x =>
        φ (adelicArchGLIncl L x * adelicFinGLIncl L y₀⁻¹)⁻¹ * (φf y₀)⁻¹ :=
      funext fun x => (hB x).symm
    rw [e]
    exact key
  · show φa ∈ ⨅ w : InfinitePlace L, ⨆ i : Fin (tys.card w),
      archFactorDualTypeSubmoduleAt L w (tys.rep w i)
    refine (Submodule.mem_iInf _).mpr fun w => ?_
    have key : (fun x : GL (Fin 2) (InfiniteAdeleRing L) =>
        φ (adelicArchGLIncl L x * adelicFinGLIncl L y₀) * (φf y₀)⁻¹) ∈
          ⨆ i : Fin (tys.card w), archFactorDualTypeSubmoduleAt L w (tys.rep w i) :=
      comp_mul_mem_iSup_of_forall (fun x => adelicArchGLIncl L x * adelicFinGLIncl L y₀)
        (fun _ => (φf y₀)⁻¹) (fun i => archDualTypeSubmoduleAt L w (tys.rep w i))
        (fun i => archFactorDualTypeSubmoduleAt L w (tys.rep w i))
        (fun _ Φ hΦ => transport_typeSubmodule L hΦ _
          (commute_adelicFinGLIncl_rowIsometryInclAt₀ L y₀ w) _)
        ((Submodule.mem_iInf _).mp h2 w)
    have e : φa = fun x : GL (Fin 2) (InfiniteAdeleRing L) =>
        φ (adelicArchGLIncl L x * adelicFinGLIncl L y₀) * (φf y₀)⁻¹ :=
      funext fun x => (hA x).symm
    rw [e]
    exact key

end LocalSupply

end

section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open scoped TensorProduct

noncomputable section

namespace PrincipalLevelReduction

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem reduction
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ) :
    ∃ (N' : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ),
      N' ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK) ∧
      Continuous f ∧ HasCompactSupport f ∧
      IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f ∧
      AreMatchingAt K L σ SK φ f := by
  have hprime : (Module.finrank K L).Prime :=
    hdeg.elim (fun h => by rw [h]; exact Nat.prime_two) (fun h => by rw [h]; exact Nat.prime_three)
  obtain ⟨⟨-, φa, φf, φS, hF⟩, hbf⟩ := hφt
  obtain ⟨hφa, hφf, hφS, hF4, hF5, hF6⟩ := hF
  by_cases hz : ∃ y₀, φf y₀ ≠ 0
  ·
    obtain ⟨y₀, hy₀⟩ := hz
    have hφaT : IsArchFactorBiFinite L tysL φa := LocalSupply.isArchFactorBiFinite_of_isArchBiFinite L hbf hF6 hy₀

    obtain ⟨tysK, fa, hfa, hfaT, harch⟩ :
        ∃ (tysK : ArchTypeFamily K) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
          IsArchTestFactor K fa ∧ IsArchFactorBiFinite K tysK fa ∧ AreMatchingArch K L σ φa fa := by
      by_cases hι : Nonempty (L →ₐ[K] InfiniteAdeleRing K)
      · exact AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_algHom
          K L hprime σ hσ hι.some tysL φa hφa hφaT
      · exact AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_areMatchingArch_of_isEmpty_algHom
          K L hdeg σ hσ (not_nonempty_iff.1 hι) tysL φa hφa hφaT

    have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ,
        v ∈ SK → IsLocalTestFn K v fv ∧ AreMatchingLocal K L v σ (φS v) fv := by
      intro v
      by_cases hv : v ∈ SK
      · by_cases hι : Nonempty (L →ₐ[K] v.adicCompletion K)
        · obtain ⟨fv, h⟩ := AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_algHom
            K L hprime σ hσ v hι.some (φS v) (hφS v hv)
          exact ⟨fv, fun _ => h⟩
        · obtain ⟨fv, h⟩ := AutomorphicForm.exists_isLocalTestFn_areMatchingLocal_of_isEmpty_algHom
            K L hdeg σ hσ v (not_nonempty_iff.1 hι) (φS v) (hφS v hv)
          exact ⟨fv, fun _ => h⟩
      · exact ⟨fun _ => 0, fun h => absurd h hv⟩
    choose fS hfS using hloc

    have hdep : ∀ v : HeightOneSpectrum (𝓞 K), ∃ m : ℕ, v ∈ SK →
        ∀ x : GL (Fin 2) (v.adicCompletion K), LocalTestAssembly.IsDeep K v m x →
          ∀ y, fS v (x * y) = fS v y ∧ fS v (y * x) = fS v y := by
      intro v
      by_cases hv : v ∈ SK
      · obtain ⟨m, hm⟩ := LocalSupply.localDepth K v (fS v) (hfS v hv).1
        exact ⟨m, fun _ => hm⟩
      · exact ⟨0, fun h => absurd h hv⟩
    choose m hm using hdep

    obtain ⟨N', f, ff, hN', hdiv, hUF, hUFA⟩ :=
      LocalTestAssembly.exists_assembly K SK fa hfa fS (fun v hv => (hfS v hv).1) m hm
    obtain ⟨hcont, hcpt⟩ :=
      continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hUFA.isFactorizableTestFn
    refine ⟨N', tysK, f, hN', hdiv, hcont, hcpt, ?_, ?_⟩
    · exact hUFA.isUnitFactorizableOfTypeAt_of_factorization hUF.2.2.2.2.2 hfaT
    · exact ⟨φa, φf, φS, fa, ff, fS, ⟨hφa, hφf, hφS, hF4, hF5, hF6⟩, hUF, harch, fun v hv => (hfS v hv).2⟩
  ·
    simp only [not_exists, ne_eq, not_not] at hz
    have hSK : SK.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have h1 := hF4 1 fun v _ => by rw [map_one]; exact one_mem_semiLocalIntegralSet K L v
      rw [hempty, Finset.prod_empty, hz] at h1
      exact zero_ne_one h1
    obtain rfl : φ = fun _ => 0 := funext fun g => by rw [hF6, hz, mul_zero]
    refine ⟨⊤, ⟨fun _ => 0, fun _ => Fin.elim0⟩, fun _ => 0, top_ne_bot, ?_, continuous_const, ?_, ?_, ?_⟩
    · intro v hv
      exact absurd (top_le_iff.1 (Ideal.le_of_dvd hv)) v.isPrime.ne_top
    · exact (continuous_and_hasCompactSupport_of_isFactorizableTestFn K _
        (isUnitFactorizableAt_zero K ⊥ SK).isFactorizableTestFn).2
    · exact isUnitFactorizableOfTypeAt_zero K _ _ SK
    · exact areMatchingAt_zero K L σ SK hSK

end PrincipalLevelReduction

end

end

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2 ∨ Module.finrank K L = 3) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ) :
    ∃ (N' : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ),
      N' ≠ ⊥ ∧ (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK) ∧
      Continuous f ∧ HasCompactSupport f ∧
      IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) SK f ∧
      AreMatchingAt K L σ SK φ f :=
  PrincipalLevelReduction.reduction K L hdeg σ hσ SK N tysL φ hφt

end S_AutomorphicForm_exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three
end P2MW
export P2MW.S_AutomorphicForm_exists_principalLevel_areMatchingAt_of_isUnitFactorizableAboveOfType_of_finrank_two_or_three (solution)
