-- Prove2me | Definitions.Def_LeiBR_Rand_Constants
-- name    : LeiBR_Rand_Constants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:05:26.829143+00:00
-- url     : https://prove2.me/theorems/ad2ebc20-5efa-4c1a-9754-bd9e65b6a808
-- title:
--   Lemma 5, (B.1), (B.3), (36) — the constants $p_{\min}, p_{\max}, \tilde a, \tilde\eta, \tilde\eta_0, \tilde c, D, \tilde C, \tilde D$
-- statement:
--   Let $p_1,\dots,p_N \in (0,1]$ be the update probabilities of the players, $a = \|\Gamma\|$, $\eta \in (0,1)$, $C \ge 0$ and $\tilde q \in (0,1)$. The randomized scheme's rate and complexity statements use
--
--   1. $p_{\min} = \min_i p_i$ and $p_{\max} = \max_i p_i$;
--   2. $\tilde a = \big(1 - p_{\min}(1 - a^2)\big)^{1/2}$, from (B.1);
--   3. $\tilde\eta = \big(1 - p_{\min}(1 - \eta^2)\big)^{1/2}$, from (B.3);
--   4. $\tilde\eta_0$, defined by $\tilde\eta_0^{-2} = p_{\max}(\eta^{-2} - 1) + 1$, from (36);
--   5. $\tilde c = \max\{\tilde a, \tilde\eta\}$;
--   6. $D = 1/\ln\big((\tilde q/\tilde c)^e\big) = 1/\big(e\ln(\tilde q/\tilde c)\big)$;
--   7. $\tilde C = C\big(\sum_{i=1}^N N^{-1}p_i^{-1}\big)^{1/2}$ and $\tilde D = D\eta\tilde\eta^{-1}$.
--
--   The factor $\tilde a$ is the contraction factor of the exact randomized step in the weighted norm, $\tilde\eta$ and $\tilde\eta_0$ control the moments of the random inexactness $\eta^{\beta_{i,k}+1}$, and $\tilde c$ is the resulting linear rate.
--
--   **Formalization Note** $p_{\min}$ and $p_{\max}$ are `⨅ i, p i` and `⨆ i, p i`; they are the minimum and maximum when $N \ge 1$, which every theorem using them assumes. $D$ reads the paper's $\ln((q/c)^e)$ as $e\ln(q/c)$, as the proof of Lemma 2 does.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 15, Lemma 5 and Remark 6; p. 16, (36); p. 32, (B.1), (B.3)

import Mathlib

namespace LeiBR.Rand

variable {N : ℕ}

/-- `p_min = min_i p_i` (App. B, p. 32). -/
noncomputable def pmin (p : Fin N → ℝ) : ℝ := ⨅ i, p i

/-- `p_max = max_i p_i` (Remark 6, p. 15). -/
noncomputable def pmax (p : Fin N → ℝ) : ℝ := ⨆ i, p i

/-- `ã = (1 − p_min(1 − a²))^{1/2}`, (B.1). -/
noncomputable def atil (p : Fin N → ℝ) (a : ℝ) : ℝ := Real.sqrt (1 - pmin p * (1 - a ^ 2))

/-- `η̃ = (1 − p_min(1 − η²))^{1/2}`, (B.3). -/
noncomputable def etatil (p : Fin N → ℝ) (η : ℝ) : ℝ := Real.sqrt (1 - pmin p * (1 - η ^ 2))

/-- `η̃₀`, defined through `η̃₀^{-2} = p_max(η^{-2} − 1) + 1`, (36). -/
noncomputable def etatil0 (p : Fin N → ℝ) (η : ℝ) : ℝ :=
  1 / Real.sqrt (pmax p * ((η ^ 2)⁻¹ - 1) + 1)

/-- `c̃ = max{ã, η̃}` (Lemma 5). -/
noncomputable def ctil (p : Fin N → ℝ) (a η : ℝ) : ℝ := max (atil p a) (etatil p η)

/-- `D = 1/ln((q/c)^e) = 1/(e · ln(q/c))` (Lemma 2, Lemma 5). -/
noncomputable def Dconst (q c : ℝ) : ℝ := 1 / (Real.exp 1 * Real.log (q / c))

/-- `C̃ = C (∑_i N^{-1} p_i^{-1})^{1/2}` (Lemma 5). -/
noncomputable def Ctil (p : Fin N → ℝ) (C : ℝ) : ℝ :=
  C * Real.sqrt (∑ i, ((N : ℝ)⁻¹ * (p i)⁻¹))

/-- `D̃ = D η η̃^{-1}` with `D = 1/ln((q̃/c̃)^e)` (Lemma 5). -/
noncomputable def Dtil (p : Fin N → ℝ) (a η q : ℝ) : ℝ :=
  Dconst q (ctil p a η) * η / etatil p η

end LeiBR.Rand


