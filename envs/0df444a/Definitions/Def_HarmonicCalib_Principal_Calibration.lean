-- Prove2me | Definitions.Def_HarmonicCalib_Principal_Calibration
-- name    : HarmonicCalib_Principal_Calibration
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:05:51.327528+00:00
-- url     : https://prove2.me/theorems/e04579cf-d0ea-4da5-92cd-709b6adeeb65
-- title:
--   Calibration error $\mathrm{Cal}_{L,T}$, the general algorithm (5), and Algorithm 1 (harmonic averaging and replay)
-- statement:
--   A finite distribution over forecasts is a finitely supported weight function $\mu : \mathbb R^d \to \mathbb R$; forecasts with equal point values are the same point, so their masses add.
--
--   * **Calibration error.** For announced distributions $\mu_0,\dots,\mu_{T-1}$ and outcomes $y_0,\dots,y_{T-1}$,
--   $$\mathrm{Cal}_{L,T} = \sum_{p} \Bigl\| \sum_{t=0}^{T-1} \mu_t(p)\,(y_t - p) \Bigr\|_L,$$
--   the sum over the distinct forecast points $p$ (in the supports of the $\mu_t$) with positive total weight $\sum_t \mu_t(p) > 0$, and $\|\cdot\|_L$ the gauge of $L$.
--   * **General algorithm (5)** for $H \in \widehat{\mathcal H}_T$: $H = Q - P^{\mathsf T}$ with $P$ lower triangular and $Q$ strictly lower triangular, so the stored forecasts are $p_s = \sum_{t \le s} (-H_{ts})\,y_t$ and the announced distributions are $\mu_0 = \delta_{p_{\mathrm{init}}}$ and $\mu_t = \sum_{s < t} H_{ts}\,\delta_{p_s}$ for $t \ge 1$.
--   * **Algorithm 1** (anytime; outcomes $y_0, y_1, \dots$): stored forecasts $p_t = \sum_{s=0}^{t} \dfrac{y_s}{h_{t+1}\,(2(t-s)+1)}$ (so $p_0 = y_0$), announced distributions $\mu_0 = \delta_{p_{\mathrm{init}}}$ and $\mu_t = \sum_{s=0}^{t-1} \dfrac{\delta_{p_s}}{h_t\,(2(t-s)-1)}$ for $t \ge 1$, with $h_t = \sum_{j<t} 1/(2j+1)$. Thus $\mu_t$ depends only on $y_0,\dots,y_{t-1}$; this is algorithm (5) with $H = \widehat K_T$.
--   * $\mathrm{Cal}_{L,T}$ of Algorithm 1 with initial forecast $p_{\mathrm{init}}$ on outcomes $y$ is `alg1Cal L T p_init y`.
-- source:
--   Fishelson and Mohri (2026), High-Dimensional Online Calibration from Harmonic Weights, arXiv:2610.07740 (version dated October 29, 2026; PDF SHA256 62ac31a3…), p. 3 (Cal), (5) p. 8, Algorithm 1 p. 10

import Mathlib
import Definitions.Def_HarmonicCalib_Principal_Geometry
import Definitions.Def_HarmonicCalib_Principal_Hilbert

namespace HarmonicCalib.Principal

/-! # Calibration error, the general algorithm (5) and Algorithm 1
(Fishelson–Mohri 2026, p. 3, (5) p. 8, Algorithm 1 p. 10)

A finite distribution over forecasts is a finitely supported function `E →₀ ℝ`: two forecasts
with the same point value are the same key, so their masses are aggregated automatically. -/

/-- The `L`-calibration error after `T` rounds (p. 3):
`Cal_{L,T} = ∑_p ‖∑_t μ_t(p) (y_t - p)‖_L`, the sum over the distinct forecast points `p` that
receive positive total weight `∑_t μ_t(p) > 0`, with `‖·‖_L = gauge L`. Rounds are
`t = 0, …, T-1`. -/
noncomputable def calError {d : ℕ} (L : Set (EuclideanSpace ℝ (Fin d))) (T : ℕ)
    (μ : Fin T → (EuclideanSpace ℝ (Fin d) →₀ ℝ)) (y : Fin T → EuclideanSpace ℝ (Fin d)) : ℝ := by
  classical
  exact ∑ p ∈ (Finset.univ.biUnion fun t => (μ t).support).filter (fun p => 0 < ∑ t, μ t p),
    gauge L (∑ t, μ t p • (y t - p))

/-- Stored forecasts of the general algorithm (5) for `H ∈ Ĥ_T` (p. 8). From `H = Q - Pᵀ` with
`P` lower triangular and `Q` strictly lower triangular, `P_{st} = -H_{ts}` for `t ≤ s`, so
`p_s = ∑_{t ≤ s} P_{st} y_t = ∑_{t ≤ s} (-H_{ts}) y_t`. -/
noncomputable def genStored {d T : ℕ} (H : Matrix (Fin T) (Fin T) ℝ)
    (y : Fin T → EuclideanSpace ℝ (Fin d)) (s : Fin T) : EuclideanSpace ℝ (Fin d) :=
  ∑ t, if t ≤ s then (-H t s) • y t else 0

/-- Announced distributions of the general algorithm (5) (p. 8): `μ_0 = δ_{p_init}` and, for
`t ≥ 1`, `μ_t = ∑_{s<t} Q_{ts} δ_{p_s} = ∑_{s<t} H_{ts} δ_{p_s}` (masses of equal points
aggregated). -/
noncomputable def genMu {d T : ℕ} (H : Matrix (Fin T) (Fin T) ℝ)
    (pinit : EuclideanSpace ℝ (Fin d)) (y : Fin T → EuclideanSpace ℝ (Fin d)) (t : Fin T) :
    EuclideanSpace ℝ (Fin d) →₀ ℝ :=
  if (t : ℕ) = 0 then Finsupp.single pinit 1
  else ∑ s, if s < t then Finsupp.single (genStored H y s) (H t s) else 0

/-- Algorithm 1, stored forecasts (line 7, p. 10):
`p_t = ∑_{s=0}^{t} y_s / [h_{t+1} (2(t-s)+1)]`; in particular `p_0 = y_0`. The outcome sequence is
indexed by all rounds `t ∈ ℕ` (the algorithm is anytime); `p_t` uses only `y_0, …, y_t`. -/
noncomputable def alg1Stored {d : ℕ} (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ s ∈ Finset.range (t + 1), (1 / (harm (t + 1) * (2 * ((t : ℝ) - (s : ℝ)) + 1))) • y s

/-- Algorithm 1, announced distributions (lines 1 and 4, p. 10): `μ_0 = δ_{p_init}` and, for
`t ≥ 1`, `μ_t = ∑_{s=0}^{t-1} δ_{p_s} / [h_t (2(t-s)-1)]`, masses of equal point values
aggregated. `μ_t` depends only on `y_0, …, y_{t-1}`. -/
noncomputable def alg1Mu {d : ℕ} (pinit : EuclideanSpace ℝ (Fin d))
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) : EuclideanSpace ℝ (Fin d) →₀ ℝ :=
  if t = 0 then Finsupp.single pinit 1
  else ∑ s ∈ Finset.range t,
    Finsupp.single (alg1Stored y s) (1 / (harm t * (2 * ((t : ℝ) - (s : ℝ)) - 1)))

/-- `Cal_{L,T}` of Algorithm 1 with initial forecast `p_init` on the outcomes `y_0, …, y_{T-1}`. -/
noncomputable def alg1Cal {d : ℕ} (L : Set (EuclideanSpace ℝ (Fin d))) (T : ℕ)
    (pinit : EuclideanSpace ℝ (Fin d)) (y : ℕ → EuclideanSpace ℝ (Fin d)) : ℝ :=
  calError L T (fun t => alg1Mu pinit y t) (fun t => y t)

end HarmonicCalib.Principal


