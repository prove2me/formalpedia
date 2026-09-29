-- Prove2me | solution 1 for AutomorphicForm.sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6a22a532-5d07-5a24-85b3-45d9bc410d16

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace PlaceIdempotentTransport

open AdelicDock Filter Topology

variable (L : Type) [Field L] [NumberField L]

private def atPlace (w : HeightOneSpectrum (𝓞 L)) (t : w.adicCompletion L) : AdeleRing (𝓞 L) L :=
  ((0 : InfiniteAdeleRing L), splice (𝓞 L) L w 0 t)

variable {L}

private theorem atPlace_fst (w : HeightOneSpectrum (𝓞 L)) (t : w.adicCompletion L) : (atPlace L w t).1 = 0 := rfl

private theorem atPlace_snd_self (w : HeightOneSpectrum (𝓞 L)) (t : w.adicCompletion L) :
    (atPlace L w t).2 w = t :=
  splice_apply_self (𝓞 L) L w 0 t

private theorem atPlace_snd_of_ne (w : HeightOneSpectrum (𝓞 L)) (t : w.adicCompletion L)
    {v : HeightOneSpectrum (𝓞 L)} (hv : v ≠ w) : (atPlace L w t).2 v = 0 :=
  splice_apply_of_ne (𝓞 L) L w 0 t hv

private theorem mul_atPlace_one (a : AdeleRing (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L)) :
    a * atPlace L w 1 = atPlace L w (a.2 w) := by
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext L fun v => ?_)
  change a.2 v * (atPlace L w 1).2 v = (atPlace L w (a.2 w)).2 v
  by_cases hv : v = w
  · subst hv
    rw [atPlace_snd_self, atPlace_snd_self, mul_one]
  · rw [atPlace_snd_of_ne w _ hv, atPlace_snd_of_ne w _ hv, mul_zero]

private theorem atPlace_mul (w : HeightOneSpectrum (𝓞 L)) (s t : w.adicCompletion L) :
    atPlace L w s * atPlace L w t = atPlace L w (s * t) := by
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext L fun v => ?_)
  change (atPlace L w s).2 v * (atPlace L w t).2 v = (atPlace L w (s * t)).2 v
  by_cases hv : v = w
  · subst hv
    rw [atPlace_snd_self, atPlace_snd_self, atPlace_snd_self]
  · rw [atPlace_snd_of_ne w _ hv, atPlace_snd_of_ne w _ hv, atPlace_snd_of_ne w _ hv, mul_zero]

private theorem atPlace_add (w : HeightOneSpectrum (𝓞 L)) (s t : w.adicCompletion L) :
    atPlace L w s + atPlace L w t = atPlace L w (s + t) := by
  refine Prod.ext (add_zero _) (FiniteAdeleRing.ext L fun v => ?_)
  change (atPlace L w s).2 v + (atPlace L w t).2 v = (atPlace L w (s + t)).2 v
  by_cases hv : v = w
  · subst hv
    rw [atPlace_snd_self, atPlace_snd_self, atPlace_snd_self]
  · rw [atPlace_snd_of_ne w _ hv, atPlace_snd_of_ne w _ hv, atPlace_snd_of_ne w _ hv, add_zero]

private theorem atPlace_zero (w : HeightOneSpectrum (𝓞 L)) : atPlace L w 0 = 0 := by
  refine Prod.ext rfl (FiniteAdeleRing.ext L fun v => ?_)
  change (atPlace L w 0).2 v = 0
  by_cases hv : v = w
  · subst hv; exact atPlace_snd_self _ _
  · exact atPlace_snd_of_ne w _ hv

private theorem atPlace_injective (w : HeightOneSpectrum (𝓞 L)) : Function.Injective (atPlace L w) := by
  intro s t h
  have := congrArg (fun a : AdeleRing (𝓞 L) L => a.2 w) h
  simpa only [atPlace_snd_self] using this

private theorem atPlace_one_ne_zero (w : HeightOneSpectrum (𝓞 L)) : atPlace L w 1 ≠ 0 := fun h =>
  one_ne_zero (atPlace_injective w (h.trans (atPlace_zero w).symm))

private theorem isIdempotentElem_atPlace_one (w : HeightOneSpectrum (𝓞 L)) : IsIdempotentElem (atPlace L w 1) := by
  show atPlace L w 1 * atPlace L w 1 = atPlace L w 1
  rw [atPlace_mul, mul_one]

private theorem exists_map_atPlace_one_eq (ψ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (w : HeightOneSpectrum (𝓞 L))
    (hf : (ψ (atPlace L w 1)).2 ≠ 0) :
    ∃ w₁ : HeightOneSpectrum (𝓞 L), ψ (atPlace L w 1) = atPlace L w₁ 1 := by
  set f := ψ (atPlace L w 1) with hf_def
  have hfi : f * f = f := by
    rw [hf_def, ← map_mul, (isIdempotentElem_atPlace_one w).eq]
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : HeightOneSpectrum (𝓞 L), f.2 w₁ ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (FiniteAdeleRing.ext L fun v => h v)
  have hf1 : f.2 w₁ = 1 := by
    have h2 : f.2 w₁ * f.2 w₁ = f.2 w₁ := congrArg (fun a : AdeleRing (𝓞 L) L => a.2 w₁) hfi
    rcases (IsIdempotentElem.iff_eq_zero_or_one (p := f.2 w₁)).mp h2 with h0 | h1
    · exact absurd h0 hw₁
    · exact h1

  have hg : atPlace L w₁ 1 * f = atPlace L w₁ 1 := by
    rw [mul_comm, mul_atPlace_one, hf1]

  set h := ψ.symm (atPlace L w₁ 1) with hh_def
  have hh : h * atPlace L w 1 = h := by
    have := congrArg ψ.symm hg
    rw [map_mul, hf_def, RingEquiv.symm_apply_apply] at this
    exact this
  have hx : h = atPlace L w (h.2 w) := by
    rw [← mul_atPlace_one, hh]
  have hxi : h.2 w * h.2 w = h.2 w := by
    have hhi : h * h = h := by
      rw [hh_def, ← map_mul, (isIdempotentElem_atPlace_one w₁).eq]
    exact congrArg (fun a : AdeleRing (𝓞 L) L => a.2 w) hhi
  rcases (IsIdempotentElem.iff_eq_zero_or_one (p := h.2 w)).mp hxi with h0 | h1
  · exfalso
    have hz : h = 0 := by rw [hx, h0, atPlace_zero]
    have : atPlace L w₁ 1 = 0 := by
      have := congrArg ψ hz
      rw [hh_def, RingEquiv.apply_symm_apply, map_zero] at this
      exact this
    exact atPlace_one_ne_zero w₁ this
  · refine ⟨w₁, ?_⟩
    rw [h1] at hx
    have := congrArg ψ hx
    rw [hh_def, RingEquiv.apply_symm_apply] at this
    rw [← hf_def] at this
    exact this.symm

private def localMap (ψ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (w w₁ : HeightOneSpectrum (𝓞 L))
    (t : w.adicCompletion L) : w₁.adicCompletion L :=
  (ψ (atPlace L w t)).2 w₁

private theorem map_atPlace (ψ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) {w w₁ : HeightOneSpectrum (𝓞 L)}
    (hψ : ψ (atPlace L w 1) = atPlace L w₁ 1) (t : w.adicCompletion L) :
    ψ (atPlace L w t) = atPlace L w₁ (localMap ψ w w₁ t) := by
  have h1 : atPlace L w t = atPlace L w t * atPlace L w 1 := by rw [atPlace_mul, mul_one]
  rw [h1, map_mul, hψ, mul_atPlace_one]
  rfl

private def localRingHom (ψ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) {w w₁ : HeightOneSpectrum (𝓞 L)}
    (hψ : ψ (atPlace L w 1) = atPlace L w₁ 1) : w.adicCompletion L →+* w₁.adicCompletion L where
  toFun := localMap ψ w w₁
  map_one' := by
    show (ψ (atPlace L w 1)).2 w₁ = 1
    rw [hψ, atPlace_snd_self]
  map_mul' s t := by
    show localMap ψ w w₁ (s * t) = localMap ψ w w₁ s * localMap ψ w w₁ t
    apply atPlace_injective w₁
    rw [← map_atPlace ψ hψ, ← atPlace_mul, map_mul, map_atPlace ψ hψ, map_atPlace ψ hψ, atPlace_mul]
  map_zero' := by
    show (ψ (atPlace L w 0)).2 w₁ = 0
    have h : ψ (atPlace L w 0) = 0 := by rw [atPlace_zero, map_zero]
    exact (congrArg (fun a : AdeleRing (𝓞 L) L => a.2 w₁) h).trans rfl
  map_add' s t := by
    show localMap ψ w w₁ (s + t) = localMap ψ w w₁ s + localMap ψ w w₁ t
    apply atPlace_injective w₁
    rw [← map_atPlace ψ hψ, ← atPlace_add, map_add, map_atPlace ψ hψ, map_atPlace ψ hψ, atPlace_add]

private theorem localRingHom_apply (ψ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) {w w₁ : HeightOneSpectrum (𝓞 L)}
    (hψ : ψ (atPlace L w 1) = atPlace L w₁ 1) (t : w.adicCompletion L) :
    localRingHom ψ hψ t = (ψ (atPlace L w t)).2 w₁ := rfl

private theorem snd_map_apply (ψ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) {w w₁ : HeightOneSpectrum (𝓞 L)}
    (hψ : ψ (atPlace L w 1) = atPlace L w₁ 1) (a : AdeleRing (𝓞 L) L) :
    (ψ a).2 w₁ = localRingHom ψ hψ (a.2 w) := by
  have h1 : (ψ a).2 w₁ = (ψ a * atPlace L w₁ 1).2 w₁ := by
    rw [mul_atPlace_one, atPlace_snd_self]
  rw [localRingHom_apply, h1, ← hψ, ← map_mul, mul_atPlace_one]

section ArchimedeanExclusion

private def sm (z : Π v : HeightOneSpectrum (𝓞 L), v.adicCompletionIntegers L) : FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
    (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite z

private theorem continuous_sm : Continuous (sm (L := L)) :=
  (RestrictedProduct.isEmbedding_structureMap).continuous

private theorem sm_zero : sm (L := L) 0 = 0 := FiniteAdeleRing.ext L fun _ => rfl

open scoped Classical in

private theorem atPlace_eq_sm (w : HeightOneSpectrum (𝓞 L)) (t : w.adicCompletionIntegers L) :
    atPlace L w t = ((0 : InfiniteAdeleRing L), sm (Pi.single w t)) := by
  refine Prod.ext rfl (FiniteAdeleRing.ext L fun v => ?_)
  change (atPlace L w (t : w.adicCompletion L)).2 v = ((Pi.single w t : Π v, v.adicCompletionIntegers L) v :
    v.adicCompletion L)
  by_cases hv : v = w
  · subst hv
    rw [atPlace_snd_self, Pi.single_eq_same]
  · rw [atPlace_snd_of_ne w _ hv, Pi.single_eq_of_ne hv]
    exact (ZeroMemClass.coe_zero _).symm

open scoped Classical in

private theorem tendsto_atPlace_pow (w : HeightOneSpectrum (𝓞 L)) (c : w.adicCompletion L) (hc : Valued.v c < 1) :
    Tendsto (fun n : ℕ => atPlace L w (c ^ n)) atTop (𝓝 0) := by
  set ci : w.adicCompletionIntegers L := ⟨c, hc.le⟩ with hci
  have h1 : ∀ n : ℕ, atPlace L w (c ^ n) = ((0 : InfiniteAdeleRing L), sm (Pi.single w (ci ^ n))) := by
    intro n
    have h := atPlace_eq_sm w (ci ^ n)
    rwa [SubmonoidClass.coe_pow] at h
  simp_rw [h1]
  have hpow : Tendsto (fun n : ℕ => ci ^ n) atTop (𝓝 0) := by
    rw [tendsto_subtype_rng]
    simp only [SubmonoidClass.coe_pow, ZeroMemClass.coe_zero]
    exact Valued.tendsto_zero_pow_of_v_lt_one hc
  have hpi : Tendsto (fun n : ℕ => (Pi.single w (ci ^ n) : Π v, v.adicCompletionIntegers L)) atTop (𝓝 0) := by
    have hcs := continuous_single (A := fun v : HeightOneSpectrum (𝓞 L) => ↥(v.adicCompletionIntegers L)) w
    simpa only [Function.comp_def, Pi.single_zero] using (hcs.tendsto 0).comp hpow
  have hsm : Tendsto (fun n : ℕ => sm (Pi.single w (ci ^ n))) atTop (𝓝 (0 : FiniteAdeleRing (𝓞 L) L)) := by
    rw [← sm_zero]
    exact (continuous_sm.tendsto 0).comp hpi
  exact tendsto_const_nhds.prodMk_nhds hsm

private theorem norm_algebraMap_natCast_fst (u : InfinitePlace L) (n : ℕ) :
    ‖(algebraMap L (AdeleRing (𝓞 L) L) (n : L)).1 u‖ = n := by
  change ‖algebraMap L (InfiniteAdeleRing L) (n : L) u‖ = n
  simp only [InfiniteAdeleRing.algebraMap_apply, NumberField.InfinitePlace.Completion.norm_ofCompletion,
    UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]
  exact u.map_natCast n

private theorem snd_map_atPlace_one_ne_zero (ψ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (hψ : Continuous ψ)
    (hnat : ∀ n : ℕ, ψ (algebraMap L (AdeleRing (𝓞 L) L) (n : L)) = algebraMap L (AdeleRing (𝓞 L) L) (n : L))
    (w : HeightOneSpectrum (𝓞 L)) : (ψ (atPlace L w 1)).2 ≠ 0 := by
  intro hf2
  set f := ψ (atPlace L w 1) with hf_def
  have hf0 : f ≠ 0 := fun h => atPlace_one_ne_zero w (ψ.injective (h.trans (map_zero ψ).symm))
  have hf1 : f.1 ≠ 0 := fun h => hf0 (Prod.ext h hf2)
  obtain ⟨u, hu⟩ : ∃ u : InfinitePlace L, f.1 u ≠ 0 := by
    by_contra h
    push Not at h
    exact hf1 (funext h)
  have hfi : f * f = f := by
    rw [hf_def, ← map_mul, (isIdempotentElem_atPlace_one w).eq]
  have hu1 : f.1 u = 1 := by
    have h2 : f.1 u * f.1 u = f.1 u := congrArg (fun a : AdeleRing (𝓞 L) L => a.1 u) hfi
    rcases (IsIdempotentElem.iff_eq_zero_or_one (p := f.1 u)).mp h2 with h0 | h1
    · exact absurd h0 hu
    · exact h1

  set m : ℕ := Ideal.absNorm w.asIdeal with hm_def
  have hm0 : m ≠ 0 := by
    rw [hm_def, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hmem : ((m : ℕ) : 𝓞 L) ∈ w.asIdeal := Ideal.absNorm_mem w.asIdeal
  set a0 : AdeleRing (𝓞 L) L := algebraMap L (AdeleRing (𝓞 L) L) (m : L) with ha0

  have hc : Valued.v (a0.2 w) < 1 := by
    change Valued.v (((m : L) : w.adicCompletion L)) < 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_natCast (algebraMap (𝓞 L) L) m,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hmem

  have hseq : ∀ n : ℕ, ψ (atPlace L w ((a0.2 w) ^ n)) = a0 ^ n * f := by
    intro n
    have h1 : atPlace L w ((a0.2 w) ^ n) = a0 ^ n * atPlace L w 1 := by
      rw [mul_atPlace_one]
      show atPlace L w (a0.2 w ^ n) = atPlace L w ((a0.2 ^ n) w)
      rw [← finAdeleEval_apply (𝓞 L) L w (a0.2 ^ n), map_pow, finAdeleEval_apply]
    have h2 : ψ (a0 ^ n) = a0 ^ n := by
      rw [ha0, ← map_pow, ← Nat.cast_pow, hnat]
    rw [h1, map_mul, h2]
  have hlim := (hψ.tendsto 0).comp (tendsto_atPlace_pow w (a0.2 w) hc)
  rw [map_zero] at hlim
  have hlim2 : Tendsto (fun n : ℕ => a0 ^ n * f) atTop (𝓝 0) := by
    refine hlim.congr fun n => ?_
    exact hseq n
  have hcu : Continuous (fun a : AdeleRing (𝓞 L) L => a.1 u) := (continuous_apply u).comp continuous_fst
  have hlim3 := (hcu.tendsto 0).comp hlim2
  have hfst : ∀ n : ℕ, (a0 ^ n * f).1 u = a0.1 u ^ n := fun n => by
    show a0.1 u ^ n * f.1 u = a0.1 u ^ n
    rw [hu1, mul_one]
  have hlim4 : Tendsto (fun n : ℕ => a0.1 u ^ n) atTop (𝓝 0) := hlim3.congr hfst
  have hnorm : ‖a0.1 u‖ < 1 := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hlim4
  rw [ha0, norm_algebraMap_natCast_fst] at hnorm
  have : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hm0)
  exact absurd hnorm (not_lt.mpr this)

end ArchimedeanExclusion

section ValuationTransport

private theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with h0 | h0
  · rw [h0]
    exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    exact WithZero.exp_le_exp.mpr (by omega)

private theorem exp_neg_one_lt_one : WithZero.exp (-1 : ℤ) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

private theorem v_lt_one_iff_tendsto_pow {w : HeightOneSpectrum (𝓞 L)} (x : w.adicCompletion L) :
    Valued.v x < 1 ↔ Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) :=
  (Valued.toNormedField.norm_lt_one_iff (x := x)).symm.trans
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one (x := x)).symm

private theorem continuous_snd_apply (w₁ : HeightOneSpectrum (𝓞 L)) :
    Continuous (fun a : AdeleRing (𝓞 L) L => a.2 w₁) :=
  (RestrictedProduct.continuous_eval w₁ : Continuous (fun b : FiniteAdeleRing (𝓞 L) L => b w₁)).comp
    continuous_snd

private theorem v_localRingHom_lt_one (ψ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L) (hcont : Continuous ψ)
    {w w₁ : HeightOneSpectrum (𝓞 L)} (hψ : ψ (atPlace L w 1) = atPlace L w₁ 1) {c : w.adicCompletion L}
    (hc : Valued.v c < 1) : Valued.v (localRingHom ψ hψ c) < 1 := by
  rw [v_lt_one_iff_tendsto_pow]
  have h1 := (hcont.tendsto 0).comp (tendsto_atPlace_pow w c hc)
  rw [map_zero] at h1
  have h2 := ((continuous_snd_apply w₁).tendsto 0).comp h1
  have h3 : ∀ n : ℕ, (ψ (atPlace L w (c ^ n))).2 w₁ = localRingHom ψ hψ c ^ n := fun n => by
    rw [← localRingHom_apply ψ hψ, map_pow]
  exact h2.congr h3

variable {K : Type} [Field K] [Algebra K L]

open scoped Pointwise in

private theorem eq_of_act_atPlace_one_eq (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {w w' w₁ : HeightOneSpectrum (𝓞 L)} (hw' : w'.asIdeal = σ • w.asIdeal)
    (hψ : D.act σ (atPlace L w 1) = atPlace L w₁ 1) : w₁ = w' := by
  have hle : w'.asIdeal ≤ w₁.asIdeal := by
    intro z hz
    rw [hw', Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hz
    have h1 : Valued.v ((algebraMap (𝓞 L) L (σ⁻¹ • z) : L) : w.adicCompletion L) < 1 := by
      rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hz
    have h2 := v_localRingHom_lt_one (D.act σ) (D.continuous_act σ) hψ h1
    have h3 : localRingHom (D.act σ) hψ ((algebraMap (𝓞 L) L (σ⁻¹ • z) : L) : w.adicCompletion L)
        = ((algebraMap (𝓞 L) L z : L) : w₁.adicCompletion L) := by
      have h := snd_map_apply (D.act σ) hψ
        (algebraMap L (AdeleRing (𝓞 L) L) (algebraMap (𝓞 L) L (σ⁻¹ • z)))
      rw [D.compat] at h
      have h4 : σ (algebraMap (𝓞 L) L (σ⁻¹ • z)) = algebraMap (𝓞 L) L z := by
        have h5 : algebraMap (𝓞 L) L (σ • σ⁻¹ • z) = σ (algebraMap (𝓞 L) L (σ⁻¹ • z)) := rfl
        rw [← h5, smul_inv_smul]
      rw [h4] at h
      exact h.symm
    rw [h3, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_lt_one_iff_mem] at h2
    exact h2
  exact (HeightOneSpectrum.ext ((Ring.DimensionLeOne.prime_le_prime_iff_eq w'.ne_bot).mp hle)).symm

open scoped Pointwise in

private theorem exists_localRingHom (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {w w' : HeightOneSpectrum (𝓞 L)} (hw' : w'.asIdeal = σ • w.asIdeal) :
    ∃ e : w.adicCompletion L →+* w'.adicCompletion L,
      (∀ t, D.act σ (atPlace L w t) = atPlace L w' (e t)) ∧
        ∀ c : w.adicCompletion L, Valued.v c < 1 → Valued.v (e c) < 1 := by
  have hnat : ∀ n : ℕ, D.act σ (algebraMap L (AdeleRing (𝓞 L) L) (n : L)) = algebraMap L (AdeleRing (𝓞 L) L) (n : L) :=
    fun n => by rw [D.compat, map_natCast]
  obtain ⟨w₁, hψ⟩ := exists_map_atPlace_one_eq (D.act σ) w
    (snd_map_atPlace_one_ne_zero (D.act σ) (D.continuous_act σ) hnat w)
  obtain rfl := eq_of_act_atPlace_one_eq D σ hw' hψ
  exact ⟨localRingHom (D.act σ) hψ, map_atPlace (D.act σ) hψ,
    fun _ hc => v_localRingHom_lt_one (D.act σ) (D.continuous_act σ) hψ hc⟩

omit [NumberField L] in
open scoped Pointwise in
private theorem asIdeal_eq_inv_smul {σ : L ≃ₐ[K] L} {w w' : HeightOneSpectrum (𝓞 L)}
    (hw' : w'.asIdeal = σ • w.asIdeal) :
    w.asIdeal = σ⁻¹ • w'.asIdeal := by
  rw [hw', inv_smul_smul]

private theorem act_inv_act (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    D.act σ⁻¹ (D.act σ a) = a := by
  rw [← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, RingAut.one_apply]

private theorem act_act_inv (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (a : AdeleRing (𝓞 L) L) :
    D.act σ (D.act σ⁻¹ a) = a := by
  rw [← RingAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, RingAut.one_apply]

open scoped Pointwise in

private theorem exists_localRingHom_pair (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {w w' : HeightOneSpectrum (𝓞 L)} (hw' : w'.asIdeal = σ • w.asIdeal) :
    ∃ (e : w.adicCompletion L →+* w'.adicCompletion L) (e' : w'.adicCompletion L →+* w.adicCompletion L),
      (∀ t, D.act σ (atPlace L w t) = atPlace L w' (e t)) ∧
      (∀ s, D.act σ⁻¹ (atPlace L w' s) = atPlace L w (e' s)) ∧
      (∀ t, e' (e t) = t) ∧ (∀ s, e (e' s) = s) ∧
      (∀ c : w.adicCompletion L, Valued.v c < 1 → Valued.v (e c) < 1) ∧
      ∀ c : w'.adicCompletion L, Valued.v c < 1 → Valued.v (e' c) < 1 := by
  obtain ⟨e, he, hev⟩ := exists_localRingHom D σ hw'
  obtain ⟨e', he', hev'⟩ := exists_localRingHom D σ⁻¹ (asIdeal_eq_inv_smul hw')
  refine ⟨e, e', he, he', fun t => ?_, fun s => ?_, hev, hev'⟩
  · apply atPlace_injective w
    rw [← he', ← he, act_inv_act]
  · apply atPlace_injective w'
    rw [← he, ← he', act_act_inv]

private theorem v_map_le_one_of_pair {w w' : HeightOneSpectrum (𝓞 L)} {e : w.adicCompletion L →+* w'.adicCompletion L}
    {e' : w'.adicCompletion L →+* w.adicCompletion L} (hee : ∀ t, e' (e t) = t)
    (hev' : ∀ c : w'.adicCompletion L, Valued.v c < 1 → Valued.v (e' c) < 1) {c : w.adicCompletion L}
    (hc : Valued.v c ≤ 1) : Valued.v (e c) ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at h
    exact absurd h (not_lt.mpr zero_le')
  have h1 : Valued.v (e c)⁻¹ < 1 := (Valuation.one_lt_val_iff Valued.v ((map_ne_zero e).mpr hc0)).mp h
  rw [← map_inv₀] at h1
  have h2 := hev' _ h1
  rw [hee] at h2
  exact absurd ((Valuation.one_lt_val_iff Valued.v hc0).mpr h2) (not_lt.mpr hc)

private theorem v_map_eq_exp_neg_one_of_pair {w w' : HeightOneSpectrum (𝓞 L)}
    {e : w.adicCompletion L →+* w'.adicCompletion L} {e' : w'.adicCompletion L →+* w.adicCompletion L}
    (hee' : ∀ s, e (e' s) = s)
    (hle : ∀ c : w.adicCompletion L, Valued.v c ≤ 1 → Valued.v (e c) ≤ 1)
    (hev : ∀ c : w.adicCompletion L, Valued.v c < 1 → Valued.v (e c) < 1)
    (hev' : ∀ c : w'.adicCompletion L, Valued.v c < 1 → Valued.v (e' c) < 1)
    {a : w.adicCompletion L} (ha : Valued.v a = WithZero.exp (-1 : ℤ)) {b : w'.adicCompletion L}
    (hb : Valued.v b = WithZero.exp (-1 : ℤ)) : Valued.v (e a) = WithZero.exp (-1 : ℤ) := by
  have ha1 : Valued.v a < 1 := by
    rw [ha]
    exact exp_neg_one_lt_one
  have hb1 : Valued.v b < 1 := by
    rw [hb]
    exact exp_neg_one_lt_one
  have hva0 : Valued.v a ≠ 0 := by
    rw [ha]
    exact WithZero.exp_ne_zero
  have ha0 : a ≠ 0 := fun h => hva0 (by rw [h, map_zero])
  have hea0 : Valued.v (e a) ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr ((map_ne_zero e).mpr ha0)
  apply le_antisymm
  · exact le_exp_neg_one_of_lt_one (hev a ha1)
  · have hx : Valued.v (e' b) ≤ Valued.v a := by
      rw [ha]
      exact le_exp_neg_one_of_lt_one (hev' b hb1)
    have hq : Valued.v (e' b * a⁻¹) ≤ 1 := by
      rw [map_mul, map_inv₀, ← mul_inv_cancel₀ hva0]
      exact mul_le_mul' hx le_rfl
    have hq' := hle _ hq
    rw [map_mul, map_inv₀, hee', map_mul, map_inv₀] at hq'
    rw [← hb]
    calc Valued.v b = Valued.v b * (Valued.v (e a))⁻¹ * Valued.v (e a) := (inv_mul_cancel_right₀ hea0 _).symm
      _ ≤ 1 * Valued.v (e a) := mul_le_mul' hq' le_rfl
      _ = Valued.v (e a) := one_mul _

end ValuationTransport

section EmbeddedMatrices

variable {K : Type} [Field K] [Algebra K L]

private theorem coe_finEmbed_localEmbed_apply (w : HeightOneSpectrum (𝓞 L)) (g : GL (Fin 2) (w.adicCompletion L))
    (i j : Fin 2) :
    ((finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w g) : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
      = (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
          + atPlace L w ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j
              - (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j) := by
  rw [coe_finEmbed, coe_localEmbed]
  refine Prod.ext ?_ (FiniteAdeleRing.ext L fun v => ?_)
  · show (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j
        = ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 + 0
    rw [add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · show localMat (𝓞 L) L w (g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j v
        = ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 v
          + (atPlace L w ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j
              - (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j)).2 v
    have h1 : ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 v
        = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    by_cases hv : v = w
    · subst hv
      rw [localMat_apply_self, atPlace_snd_self, h1, add_sub_cancel]
    · rw [localMat_apply_of_ne (𝓞 L) L w _ i j hv, atPlace_snd_of_ne w _ hv, add_zero, h1]

private theorem sigmaAdelicAct_finEmbed_localEmbed (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {w w' : HeightOneSpectrum (𝓞 L)} (e : w.adicCompletion L →+* w'.adicCompletion L)
    (he : ∀ t, D.act σ (atPlace L w t) = atPlace L w' (e t)) (g : GL (Fin 2) (w.adicCompletion L)) :
    AutomorphicForm.sigmaAdelicAct K L D σ (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w g))
      = finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w' (Matrix.GeneralLinearGroup.map e g)) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show D.act σ (((finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w g) : GL (Fin 2) (AdeleRing (𝓞 L) L)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) = _
  rw [coe_finEmbed_localEmbed_apply, map_add, he, coe_finEmbed_localEmbed_apply]
  have h1 : D.act σ ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j)
      = (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j := by
    rw [Matrix.one_apply]
    split_ifs
    · exact map_one _
    · exact map_zero _
  have h2 : ((Matrix.GeneralLinearGroup.map e g : GL (Fin 2) (w'.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (w'.adicCompletion L)) i j = e ((g : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j) :=
    rfl
  have h3 : e ((1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j)
      = (1 : Matrix (Fin 2) (Fin 2) (w'.adicCompletion L)) i j := by
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one e
    · exact map_zero e
  rw [h1, h2, map_sub, h3]

private theorem heckeGenAt_eq_finEmbed_localEmbed (w : HeightOneSpectrum (𝓞 L)) (t : (w.adicCompletion L)ˣ) :
    heckeGenAt (𝓞 L) L w t = finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w (diagOne t)) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [coe_finEmbed_localEmbed_apply]
  refine Prod.ext ?_ (FiniteAdeleRing.ext L fun v => ?_)
  · rw [heckeGenAt_fst]
    show _ = ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1 + (0 : InfiniteAdeleRing L)
    rw [add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> rfl
  · show _ = ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 v
        + (atPlace L w ((diagOne t : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j
            - (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j)).2 v
    have h1 : ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).2 v
        = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion L)) i j := by
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> rfl
    by_cases hv : v = w
    · subst hv
      rw [heckeGenAt_snd_apply_self, atPlace_snd_self, h1, diagOne_coe_apply, add_sub_cancel]
    · rw [heckeGenAt_snd_apply_of_ne t hv, atPlace_snd_of_ne w _ hv, add_zero, h1]

private theorem map_diagOne {w w' : HeightOneSpectrum (𝓞 L)} (e : w.adicCompletion L →+* w'.adicCompletion L)
    (t : (w.adicCompletion L)ˣ) :
    Matrix.GeneralLinearGroup.map e (diagOne t)
      = diagOne (Units.map (e : w.adicCompletion L →* w'.adicCompletion L) t) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show e ((diagOne t : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j) = _
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp

private theorem isLocalLevelOne_top_map {w w' : HeightOneSpectrum (𝓞 L)}
    (e : w.adicCompletion L →+* w'.adicCompletion L)
    (hle : ∀ c : w.adicCompletion L, Valued.v c ≤ 1 → Valued.v (e c) ≤ 1)
    {m : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)} (hm : IsLocalLevelOne (𝓞 L) L w ⊤ m) :
    IsLocalLevelOne (𝓞 L) L w' ⊤ (m.map e) where
  integral i j := hle _ (hm.integral i j)
  lowerLeft := by
    rw [idealBound_top]
    have h := hm.lowerLeft
    rw [idealBound_top] at h
    exact hle _ h
  lowerRight := by
    rw [idealBound_top]
    have h := hm.lowerRight
    rw [idealBound_top] at h
    show Valued.v (e (m 1 1) - 1) ≤ 1
    rw [← map_one e, ← map_sub]
    exact hle _ h

private theorem map_mem_localLevelOne_top {w w' : HeightOneSpectrum (𝓞 L)}
    (e : w.adicCompletion L →+* w'.adicCompletion L)
    (hle : ∀ c : w.adicCompletion L, Valued.v c ≤ 1 → Valued.v (e c) ≤ 1) {g : GL (Fin 2) (w.adicCompletion L)}
    (hg : g ∈ localLevelOne (𝓞 L) L w ⊤) :
    Matrix.GeneralLinearGroup.map e g ∈ localLevelOne (𝓞 L) L w' ⊤ := by
  rw [mem_localLevelOne_iff] at hg ⊢
  refine ⟨isLocalLevelOne_top_map e hle hg.1, ?_⟩
  rw [← map_inv]
  exact isLocalLevelOne_top_map e hle hg.2

private theorem isLocalLevelOne_top_diagOne {w : HeightOneSpectrum (𝓞 L)} (a : (w.adicCompletion L)ˣ)
    (ha : Valued.v (a : w.adicCompletion L) ≤ 1) :
    IsLocalLevelOne (𝓞 L) L w ⊤ (diagOne a : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) where
  integral i j := by
    rw [diagOne_coe_apply]
    fin_cases i <;> fin_cases j <;> simp [HeightOneSpectrum.mem_adicCompletionIntegers, ha]
  lowerLeft := by
    rw [idealBound_top, diagOne_coe_apply]
    simp
  lowerRight := by
    rw [idealBound_top, diagOne_coe_apply]
    simp

private theorem diagOne_mem_localLevelOne_top {w : HeightOneSpectrum (𝓞 L)} (a : (w.adicCompletion L)ˣ)
    (ha : Valued.v (a : w.adicCompletion L) = 1) : diagOne a ∈ localLevelOne (𝓞 L) L w ⊤ := by
  rw [mem_localLevelOne_iff]
  refine ⟨isLocalLevelOne_top_diagOne a ha.le, ?_⟩
  rw [← map_inv]
  refine isLocalLevelOne_top_diagOne a⁻¹ ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, ha, inv_one]

end EmbeddedMatrices

end PlaceIdempotentTransport

open AutomorphicForm PlaceIdempotentTransport in
theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (w w' : HeightOneSpectrum (𝓞 L)) (hw' : w'.asIdeal = σ • w.asIdeal) :
    ((AdelicDock.localEmbed (𝓞 L) L w).range.map (AdelicDock.finEmbed (𝓞 L) L)).map (sigmaAdelicAct K L D σ)
        = (AdelicDock.localEmbed (𝓞 L) L w').range.map (AdelicDock.finEmbed (𝓞 L) L) ∧
      (∃ u ∈ AdelicDock.localLevelOne (𝓞 L) L w' ⊤,
        sigmaAdelicAct K L D σ (heckeGen (𝓞 L) L w)
          = heckeGen (𝓞 L) L w' * AdelicDock.finEmbed (𝓞 L) L (AdelicDock.localEmbed (𝓞 L) L w' u)) ∧
      (((AdelicDock.localLevelOne (𝓞 L) L w ⊤).map (AdelicDock.localEmbed (𝓞 L) L w)).map
            (AdelicDock.finEmbed (𝓞 L) L)).map (sigmaAdelicAct K L D σ)
        = ((AdelicDock.localLevelOne (𝓞 L) L w' ⊤).map (AdelicDock.localEmbed (𝓞 L) L w')).map
            (AdelicDock.finEmbed (𝓞 L) L) := by
  obtain ⟨e, e', he, he', hee, hee', hev, hev'⟩ := exists_localRingHom_pair D σ hw'
  have hle : ∀ c : w.adicCompletion L, Valued.v c ≤ 1 → Valued.v (e c) ≤ 1 :=
    fun _ hc => v_map_le_one_of_pair hee hev' hc
  have hle' : ∀ c : w'.adicCompletion L, Valued.v c ≤ 1 → Valued.v (e' c) ≤ 1 :=
    fun _ hc => v_map_le_one_of_pair hee' hev hc
  have hmap : ∀ h : GL (Fin 2) (w'.adicCompletion L),
      Matrix.GeneralLinearGroup.map e (Matrix.GeneralLinearGroup.map e' h) = h :=
    fun h => Matrix.GeneralLinearGroup.ext fun i j => hee' _
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · rintro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hz
      rw [sigmaAdelicAct_finEmbed_localEmbed D σ e he g]
      exact Subgroup.mem_map.mpr ⟨_, MonoidHom.mem_range.mpr ⟨_, rfl⟩, rfl⟩
    · rintro x hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hz
      refine Subgroup.mem_map.mpr
        ⟨AdelicDock.finEmbed (𝓞 L) L (AdelicDock.localEmbed (𝓞 L) L w (Matrix.GeneralLinearGroup.map e' h)),
          Subgroup.mem_map.mpr ⟨_, MonoidHom.mem_range.mpr ⟨_, rfl⟩, rfl⟩, ?_⟩
      rw [sigmaAdelicAct_finEmbed_localEmbed D σ e he, hmap]
  · refine ⟨diagOne ((uniformizerUnit L w')⁻¹ *
      Units.map (e : w.adicCompletion L →* w'.adicCompletion L) (uniformizerUnit L w)),
      diagOne_mem_localLevelOne_top _ ?_, ?_⟩
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map]
      show Valued.v ((uniformizerUnit L w' : w'.adicCompletion L)⁻¹ * e (uniformizerUnit L w : w.adicCompletion L)) = 1
      rw [map_mul, map_inv₀, valued_uniformizerUnit,
        v_map_eq_exp_neg_one_of_pair hee' hle hev hev' (valued_uniformizerUnit L w) (valued_uniformizerUnit L w'),
        inv_mul_cancel₀ WithZero.exp_ne_zero]
    · rw [heckeGen, heckeGen, heckeGenAt_eq_finEmbed_localEmbed, heckeGenAt_eq_finEmbed_localEmbed,
        sigmaAdelicAct_finEmbed_localEmbed D σ e he, map_diagOne, ← map_mul, ← map_mul, ← map_mul,
        mul_inv_cancel_left]
  · apply le_antisymm
    · rintro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hz
      rw [sigmaAdelicAct_finEmbed_localEmbed D σ e he g]
      exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨_, map_mem_localLevelOne_top e hle hg, rfl⟩, rfl⟩
    · rintro x hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hz
      refine Subgroup.mem_map.mpr
        ⟨AdelicDock.finEmbed (𝓞 L) L (AdelicDock.localEmbed (𝓞 L) L w (Matrix.GeneralLinearGroup.map e' h)),
          Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨_, map_mem_localLevelOne_top e' hle' hh, rfl⟩, rfl⟩, ?_⟩
      rw [sigmaAdelicAct_finEmbed_localEmbed D σ e he, hmap]

end

end S_AutomorphicForm_sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_sigmaAdelicAct_localEmbed_range_and_heckeGen_of_asIdeal_eq_smul (solution)
