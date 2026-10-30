-- Prove2me | Definitions.Def_FreeSamples_FullRevenue_DeterministicIntegral
-- name    : FreeSamples_FullRevenue_DeterministicIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:52:31.652389+00:00
-- url     : https://prove2.me/theorems/86c508ce-c412-4061-ad6d-73877d65d2d6
-- title:
--   Deterministic Wiener integral for the physical posterior SDE
-- statement:
--   For a deterministic continuously differentiable function $f$ and a Brownian path $B$, the Wiener integral has the integration-by-parts representation
--   $$\int_0^t f(s)\,dB_s=f(t)B_t-f(0)B_0-\int_0^t f'(s)B_s\,ds.$$
--   This definition supplies that representation for the particular smooth coefficient $f(s)=v_s/\sqrt n$ in Lemma 1. On continuous paths it also equals the limit of left-endpoint stochastic sums; no arbitrary stochastic integral operator or SDE solution is assumed. The SDE theorem includes integrability of the ordinary integral terms on every finite interval.
-- source:
--   Drakopoulos & Makhdoumi, Providing Data Samples for Free, SSRN 3611003, pinned local PDF snapshot (creation metadata 2021-08-30; SHA-256 2e29ad6e37639d93e587e9999f63959d3eb52c66a1fe2ac7e78f3d33976e44c0), p.14, opening SDE of Lemma 1; p.29, proof using the smooth posterior coefficient

import Mathlib

open MeasureTheory
open scoped NNReal

namespace FreeSamples.FullRevenue

/-- Wiener/Itô integral for a deterministic continuously differentiable integrand,
in its integration-by-parts representation. Used with f(s)=v_s/√n only.
On a continuous path this equals the limit of left endpoint stochastic sums. -/
noncomputable def deterministicWienerIntegral {Ω : Type*} (f : ℝ → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  f t * B t ω - f 0 * B 0 ω -
    ∫ s in (0 : ℝ)..(t : ℝ), deriv f s * B s.toNNReal ω

end FreeSamples.FullRevenue


