-- Prove2me | Definitions.Def_dusart_psi_433_20261014_PrincipalParts
-- name    : dusart_psi_433_20261014_PrincipalParts
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-14T09:19:29.561897+00:00
-- url     : https://prove2.me/theorems/d798e54f-198c-4b96-8c55-fbc4803328be
-- title:
--   Dusart smoothing: Principal Parts
-- statement:
--   This module gives the complete principal parts component of Gaussian resampling for Chebyshev’s psi function. It is part of the direct formal proof of the parameter-dependent explicit prime-number-theorem error estimate. Its supporting analytic and numerical results are included with their proofs.
--
--   Formalization Note: The imported components are complete proof modules; no open theorem is assumed.
-- source:
--   Pierre Dusart, Estimates of Some Functions Over Primes without R.H., https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf, Theorem 45 and Lemmas 47–55, printed pp. 38–46; supporting analytic and numerical formalization.

import Definitions.Def_dusart_psi_433_20261014_ArgumentPrinciple
/- Copyright (c) 2026 Anthropic, PBC. Released under Apache 2.0.
The local principal-part proof is extracted from the weighted argument principle. -/
noncomputable section
namespace DusartSmoothing.Contour
open Complex _root_.Set Topology Filter Asymptotics Real

lemma weighted_logDeriv_principal_part {f g : ℂ → ℂ} {q : ℂ}
    (hfa : AnalyticAt ℂ f q) (hga : AnalyticAt ℂ g q) :
    ((fun s => g s * logDeriv f s) -
      fun s => ((analyticOrderNatAt f q : ℂ) * g q) / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
  let A : ℂ → ℂ := fun p => (analyticOrderNatAt f p : ℂ) * g p
  have hA : A q = (analyticOrderNatAt f q : ℂ) * g q := rfl
  change ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ)
  by_cases htop : analyticOrderAt f q = ⊤
  · -- f vanishes identically near q: everything is 0
    have h0 : ∀ᶠ s in 𝓝 q, f s = 0 := analyticOrderAt_eq_top.mp htop
    have hO : (fun _ : ℂ => (0 : ℂ)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := isBigO_zero _ _
    refine hO.congr' ?_ EventuallyEq.rfl
    filter_upwards [mem_nhdsWithin_of_mem_nhds (h0.eventually_nhds)] with s hs
    have hs' : f =ᶠ[𝓝 s] fun _ => (0 : ℂ) := hs
    have hds : deriv f s = 0 := by
      rw [hs'.deriv_eq]; simp
    simp [hA, logDeriv_apply, hds, analyticOrderNatAt, htop]
  obtain ⟨h, hh, hh0, hfh⟩ := hfa.analyticOrderAt_ne_top.mp htop
  have hh_ne : ∀ᶠ s in 𝓝 q, h s ≠ 0 := hh.continuousAt.eventually_ne hh0
  have h2 : ∀ᶠ s in 𝓝 q, f =ᶠ[𝓝 s] (fun s => (s - q) ^ analyticOrderNatAt f q • h s) :=
    hfh.eventually_nhds
  have h3 : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ h s := hh.eventually_analyticAt
  have hexp : ∀ᶠ s in 𝓝[≠] q,
      (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q)) + g s * logDeriv h s
        = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h2,
      mem_nhdsWithin_of_mem_nhds hh_ne, mem_nhdsWithin_of_mem_nhds h3]
      with s hs hfs hhs hhas
    have hsq : s - q ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
    have hld : logDeriv f s = (analyticOrderNatAt f q : ℂ) / (s - q) + logDeriv h s := by
      have e1 : logDeriv f s
          = logDeriv (fun s => (s - q) ^ analyticOrderNatAt f q * h s) s := by
        simp only [logDeriv_apply, hfs.deriv_eq, hfs.self_of_nhds, smul_eq_mul]
      rw [e1, logDeriv_mul (f := fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) (g := h) s
        (pow_ne_zero _ hsq) hhs (by fun_prop) hhas.differentiableAt]
      have e2 : logDeriv (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) s
          = (analyticOrderNatAt f q : ℂ) / (s - q) := by
        rw [show (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q)
            = (fun x : ℂ => x ^ analyticOrderNatAt f q) ∘ (fun s => s - q) from rfl,
          logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
        simp
      rw [e2]
    simp only [Pi.sub_apply, hld, hA]
    ring
  have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
    have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
    simpa only [slope_fun_def_field] using this
  have hcont : Tendsto (fun s => g s * logDeriv h s) (𝓝[≠] q)
      (𝓝 (g q * logDeriv h q)) := by
    have : ContinuousAt (fun s => g s * logDeriv h s) q := by
      show ContinuousAt (fun s => g s * (deriv h s / h s)) q
      exact hga.continuousAt.mul (hh.deriv.continuousAt.div hh.continuousAt hh0)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hO : (fun s => (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q))
      + g s * logDeriv h s) =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
    ((hslope.const_mul (analyticOrderNatAt f q : ℂ)).add hcont).isBigO_one ℂ
  exact hO.congr' hexp EventuallyEq.rfl

end DusartSmoothing.Contour


