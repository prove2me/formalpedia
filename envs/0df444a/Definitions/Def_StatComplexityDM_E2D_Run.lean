-- Prove2me | Definitions.Def_StatComplexityDM_E2D_Run
-- name    : StatComplexityDM_E2D_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:21:41.295131+00:00
-- url     : https://prove2.me/theorems/547bdf23-7320-4376-893c-ccc519f0be3a
-- title:
--   Algorithm 1 (Option II), p. 18, and Assumption D.1, p. 96 — a realized E2D run with Hellinger confidence sets, the event E, and the radius ε_t of (35)
-- statement:
--   This module describes a realized run of the **Estimation-to-Decisions (E2D)** meta-algorithm with **Option II** (Algorithm 1, lines 6–8), the high-probability event of Assumption D.1, and the localization radius of Theorem 4.1.
--
--   Fix a model class $\mathcal M$, an exploration parameter $\gamma$, a horizon $T$ and a squared confidence radius $R^2$. For a reference model $\widehat M$, a distribution $p \in \Delta(\Pi)$ and a model $M$, write
--   $$
--   \mathcal V^{\widehat M}_\gamma(p, M) = \mathbb E_{\pi\sim p}\big[f^M(\pi_M) - f^M(\pi) - \gamma\, D^2_{\mathrm H}(M(\pi), \widehat M(\pi))\big] \qquad (20),
--   $$
--   where $D^2_{\mathrm H}(P,Q) = \sum_y (\sqrt{P(y)} - \sqrt{Q(y)})^2$ is the squared Hellinger distance. A run consists of estimates $\widehat M^{(t)}$, distributions $p^{(t)}$ and confidence sets $\mathcal M^{(t)}$, $t = 1, \dots, T$, such that:
--
--   1. (line 7) $\mathcal M^{(0)} := \mathcal M$ and
--   $$
--   \mathcal M^{(t)} = \Big\{ M \in \mathcal M^{(t-1)} : \sum_{i=1}^{t-1} \mathbb E_{\pi\sim p^{(i)}}\big[D^2_{\mathrm H}(M(\pi), \widehat M^{(i)}(\pi))\big] \le R^2 \Big\};
--   $$
--   2. (line 8) $p^{(t)} \in \Delta(\Pi)$ and $\mathcal V^{\widehat M^{(t)}}_\gamma(p^{(t)}, M) \le \mathrm{dec}_\gamma(\mathcal M^{(t)}, \widehat M^{(t)})$ for every $M \in \mathcal M^{(t)}$, where $\mathrm{dec}_\gamma(\mathcal M', \widehat M) = \inf_{p\in\Delta(\Pi)} \sup_{M \in \mathcal M'} \mathcal V^{\widehat M}_\gamma(p, M)$;
--   3. the estimate lies in the convex hull of the confidence set, $\widehat M^{(t)} \in \mathrm{co}(\mathcal M^{(t)})$.
--
--   The **event $\mathcal E$** of Assumption D.1, (136), for a true model $M^\star$ and a known bound $\widetilde{\mathrm{Est}}_{\mathrm H}(T,\delta)$, is
--   $$
--   \sum_{t=1}^T \mathbb E_{\pi\sim p^{(t)}}\big[D^2_{\mathrm H}(M^\star(\pi), \widehat M^{(t)}(\pi))\big]\,\mathbb I\{M^\star \in \mathcal M^{(t)}\} \le \widetilde{\mathrm{Est}}_{\mathrm H}(T,\delta).
--   $$
--   The **radius** of (35) at round $t \ge 1$ is
--   $$
--   \varepsilon_t := 6\frac{\gamma}{t}\,\widetilde{\mathrm{Est}}_{\mathrm H}(T,\delta) + \sup_{\bar M \in \mathrm{co}(\mathcal M)} \mathrm{dec}_\gamma(\mathcal M, \bar M) + (2\gamma)^{-1}.
--   $$
--
--   These are the objects the localized regret bound of Theorem 4.1 is about.
--
--   **Formalization Note** Rounds are 0-based: the Lean round `t : Fin T` is the paper's round $t+1$, so the radius `epsT γ R2 t D` is always evaluated at `(t : ℕ) + 1`. Line 8's "arg min" is relaxed to "certifies the minimax value from above" (Remark 4.1, p. 24, which says the theorems continue to hold); an exact minimizer satisfies it. The probability statement is replaced by the pathwise event: the theorems assume `EventD1` on the run, which holds with probability at least $1-\delta$ by Assumption D.1. The radius takes the value $D = \sup_{\bar M\in\mathrm{co}(\mathcal M)}\mathrm{dec}_\gamma(\mathcal M,\bar M)$ as an argument; the theorems pass the published `dec`.
-- source:
--   arXiv:2112.13487v3, Algorithm 1 (lines 6–8) and (20), pp. 17–18; Remark 4.1, p. 24; Assumption D.1, (136), p. 96; Theorem 4.1 (35), p. 24

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_StatComplexityDM_LowerBound_Core

namespace StatComplexityDM.E2D

open FoundationsRL.GeneralDM

/-- A realized run of `T` rounds of E2D with Option II (Algorithm 1, lines 6–8, arXiv:2112.13487v3,
p. 18), with exploration parameter `γ` and squared confidence radius `R2 = R²`. Rounds are 0-based:
the Lean round `t : Fin T` is the paper's round `t + 1`. The run records the oracle's estimates
`Mhat t = M̂^{(t+1)}`, the decision distributions `p t = p^{(t+1)}` and the confidence sets
`Mt t = M^{(t+1)}`, and requires:

1. line 7, `M^{(t)} = {M ∈ M^{(t−1)} | Σ_{i<t} E_{π∼p^{(i)}}[D²_H(M(π), M̂^{(i)}(π))] ≤ R²}`, with
   `M^{(0)} := M`;
2. line 8, `p^{(t)}` is a distribution on `Π` attaining (or certifying an upper bound on) the minimax
   value `dec_γ(M^{(t)}, M̂^{(t)})`: its payoff `V^{M̂^{(t)}}_γ(p^{(t)}, M)` of (20) against every
   `M ∈ M^{(t)}` is at most that value (Remark 4.1, p. 24);
3. the oracle's estimate lies in the convex hull of the confidence set, `M̂^{(t)} ∈ co(M^{(t)})`
   (Assumption D.1, p. 96; Theorem 4.1, p. 24). -/
def IsOptionIIRun {S Y : Type*} [Fintype S] [Fintype Y] (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ)
    (piStar : (S → Y → ℝ) → S) (γ R2 : ℝ) (T : ℕ) (Mhat : Fin T → S → Y → ℝ)
    (p : Fin T → S → ℝ) (Mt : Fin T → Set (S → Y → ℝ)) : Prop :=
  (∀ t : Fin T, Mt t =
      {m | m ∈ (if (t : ℕ) = 0 then 𝓜
                else Mt ⟨(t : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩) ∧
        ∑ i : Fin T with i < t, ∑ π, p i π * hellingerSq (m π) (Mhat i π) ≤ R2}) ∧
  (∀ t : Fin T, StatComplexityDM.LowerBound.IsDist (p t)) ∧
  (∀ t : Fin T, ∀ m ∈ Mt t,
      ∑ π, p t π * (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (Mhat t π))
        ≤ decGf (Mt t) rew piStar γ (Mhat t)) ∧
  (∀ t : Fin T, Mhat t ∈ convexHull ℝ (Mt t))

open Classical in
/-- The high-probability event `E` of Assumption D.1, (136), p. 96, on a realized run: the Hellinger
estimation error of the rounds whose confidence set still contains the true model `M⋆` is at most
the known bound `Ẽst_H(T, δ) = R2`,
`Σ_t E_{π∼p^{(t)}}[D²_H(M⋆(π), M̂^{(t)}(π))] · 𝕀{M⋆ ∈ M^{(t)}} ≤ Ẽst_H(T, δ)`. -/
noncomputable def EventD1 {S Y : Type*} [Fintype S] [Fintype Y] {T : ℕ} (Mstar : S → Y → ℝ)
    (Mhat : Fin T → S → Y → ℝ) (p : Fin T → S → ℝ) (Mt : Fin T → Set (S → Y → ℝ))
    (R2 : ℝ) : Prop :=
  ∑ t : Fin T, (if Mstar ∈ Mt t then ∑ π, p t π * hellingerSq (Mstar π) (Mhat t π) else 0) ≤ R2

/-- The localization radius of Theorem 4.1, (35), p. 24 (and (137), p. 96), at the paper's round
`t ≥ 1`: `ε_t := 6 (γ/t) Ẽst_H(T, δ) + sup_{M̄∈co(M)} dec_γ(M, M̄) + (2γ)^{-1}`, with
`R2 = Ẽst_H(T, δ)` and `D = sup_{M̄∈co(M)} dec_γ(M, M̄)` passed as arguments. -/
noncomputable def epsT (γ R2 : ℝ) (t : ℕ) (D : ℝ) : ℝ :=
  6 * (γ / t) * R2 + D + (2 * γ)⁻¹

end StatComplexityDM.E2D


