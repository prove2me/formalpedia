-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PoleParts
-- name    : dusart_psi_433_20261014_PoleParts
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:20:26.730557+00:00
-- url     : https://prove2.me/theorems/e4d9f1d6-46a5-4d02-b4a8-f29fb39eabbd
-- title:
--   Dusart smoothing: Pole Parts
-- statement:
--   This module gives the complete pole parts component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_PrincipalParts
/- Copyright (c) 2026 Anthropic, PBC. Released under Apache 2.0.
The regularized-pole proof is extracted from the weighted argument principle. -/
noncomputable section
namespace DusartSmoothing.Contour
open Complex _root_.Set Topology Filter Asymptotics Real

lemma weighted_logDeriv_pole_principal_part {f g : ℂ → ℂ} {q c : ℂ} {m : ℕ}
    (hnearF : ∀ᶠ s in 𝓝[≠] q, AnalyticAt ℂ f s)
    (hc : c ≠ 0) (hT : Tendsto (fun s => (s - q)^m * f s) (𝓝[≠] q) (𝓝 c))
    (hga : AnalyticAt ℂ g q) :
    ((fun s => g s * logDeriv f s) - fun s => -((m : ℂ) * g q) / (s - q))
      =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
  let A : ℂ → ℂ := fun _ => -((m : ℂ) * g q)
  have hA : A q = -((m : ℂ) * g q) := rfl
  change ((fun s => g s * logDeriv f s) - fun s => A q / (s - q))
    =O[𝓝[≠] q] (1 : ℂ → ℂ)
  -- the regularisation G := (s − q)^m · f, extended by c at q: analytic at q, G q ≠ 0
  set F : ℂ → ℂ := fun s => (s - q) ^ m * f s with hF
  set G : ℂ → ℂ := Function.update F q c with hG
  have hGq : G q = c := Function.update_self _ _ _
  have hGF : ∀ s, s ≠ q → G s = F s := fun s hs => Function.update_of_ne hs _ _
  have hnear : ∀ᶠ s in 𝓝[≠] q, s ≠ q ∧ AnalyticAt ℂ f s := by
    filter_upwards [self_mem_nhdsWithin, hnearF] with s hs ha
    exact ⟨by simpa using hs, ha⟩
  have hGdiff : ∀ᶠ s in 𝓝[≠] q, DifferentiableAt ℂ G s := by
    filter_upwards [hnear] with s ⟨hsq, hsRP⟩
    have hFs : DifferentiableAt ℂ F s :=
      ((differentiableAt_id.sub_const q).pow _).mul hsRP.differentiableAt
    refine hFs.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
    exact hGF x hx
  have hGcont : ContinuousAt G q := by
    rw [hG, continuousAt_update_same]
    exact hT
  have hGan : AnalyticAt ℂ G q :=
    analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hGdiff hGcont
  have hG0 : G q ≠ 0 := by rwa [hGq]
  have hFne : ∀ᶠ s in 𝓝[≠] q, F s ≠ 0 := hT.eventually_ne hc
  have hGan' : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ G s := hGan.eventually_analyticAt
  have hexp : ∀ᶠ s in 𝓝[≠] q,
      g s * logDeriv G s - (m : ℂ) * ((g s - g q) / (s - q))
        = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
    filter_upwards [hnear, hFne, mem_nhdsWithin_of_mem_nhds hGan'] with s ⟨hsq, hsRP⟩ hFs hGs
    have hsq' : s - q ≠ 0 := sub_ne_zero.mpr hsq
    have hfs : f s ≠ 0 := fun h => hFs (by simp [hF, h])
    have hfd : DifferentiableAt ℂ f s := hsRP.differentiableAt
    have hldF : logDeriv F s = (m : ℂ) / (s - q) + logDeriv f s := by
      rw [hF, logDeriv_mul (f := fun s : ℂ => (s - q) ^ m) (g := f) s
        (pow_ne_zero _ hsq') hfs (by fun_prop) hfd]
      have e2 : logDeriv (fun s : ℂ => (s - q) ^ m) s = (m : ℂ) / (s - q) := by
        rw [show (fun s : ℂ => (s - q) ^ m) = (fun x : ℂ => x ^ m) ∘ (fun s => s - q)
            from rfl, logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
        simp
      rw [e2]
    have hGFs : G =ᶠ[𝓝 s] F := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
      exact hGF x hx
    have hldG : logDeriv G s = logDeriv F s := by
      simp only [logDeriv_apply, hGFs.deriv_eq, hGFs.self_of_nhds]
    simp only [Pi.sub_apply, hA, hldG, hldF]
    ring
  have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
    have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
    simpa only [slope_fun_def_field] using this
  have hcont : Tendsto (fun s => g s * logDeriv G s) (𝓝[≠] q)
      (𝓝 (g q * logDeriv G q)) := by
    have : ContinuousAt (fun s => g s * logDeriv G s) q := by
      show ContinuousAt (fun s => g s * (deriv G s / G s)) q
      exact hga.continuousAt.mul (hGan.deriv.continuousAt.div hGan.continuousAt hG0)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hO : (fun s => g s * logDeriv G s - (m : ℂ) * ((g s - g q) / (s - q)))
      =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
    (hcont.sub (hslope.const_mul (m : ℂ))).isBigO_one ℂ
  exact hO.congr' hexp EventuallyEq.rfl

lemma analytic_div_principal_part {A : ℂ → ℂ} {q : ℂ} (hA : AnalyticAt ℂ A q) :
    ((fun s => A s / (s - q)) - fun s => A q / (s - q))
      =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
  have h := hasDerivAt_iff_tendsto_slope.mp hA.differentiableAt.hasDerivAt
  have hs : Tendsto (fun s => (A s - A q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv A q)) := by
    simpa only [slope_fun_def_field] using h
  refine (hs.isBigO_one ℂ).congr' ?_ EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun s => by simp only [Pi.sub_apply]; ring)

end DusartSmoothing.Contour


