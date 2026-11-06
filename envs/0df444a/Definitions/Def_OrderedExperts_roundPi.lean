-- Prove2me | Definitions.Def_OrderedExperts_roundPi
-- name    : OrderedExperts_roundPi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:59.617015+00:00
-- url     : https://prove2.me/theorems/bd0a5fe6-2c99-4b05-86ea-acdcba91a582
-- title:
--   Smoothed intended distribution $\pi_t$ of Algorithm 2
-- statement:
--   In Algorithm 2 (learning rate $\eta>0$, horizon $T$), with cumulative estimates $L_{t-1}(f)$ and $L_0=0$, the expert mixture of round $t$ is
--   $$
--   u_t(f)=\frac{\exp(-\eta L_{t-1}(f))}{\sum_{f'}\exp(-\eta L_{t-1}(f'))},
--   $$
--   its induced distribution on active ranks is $p_t(j)=\sum_{f:\,j_t(f)=j}u_t(f)$, and the learner intends to play
--   $$
--   \pi_t=\Bigl(1-\frac1T\Bigr)p_t+\frac1T\,\mathrm{Unif}(X_t),
--   $$
--   that is, $\pi_t(j)=(1-1/T)p_t(j)+1/(Tm_t)$ on the active ranks $j=1,\dots,m_t$ (and $0$ elsewhere). It satisfies the floor with $\xi=1/T$.
--
--   **Formalization Note** Rounds are $0$-based; $u_t$ is the published exponential-weights distribution `UnderstandingML.wmWeights` applied to the past estimate vectors.
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Algorithm 2, p.11; Sec. 4.1, p.10

import Definitions.Def_OrderedExperts_chainSize
import Definitions.Def_OrderedExperts_rank
import Definitions.Def_UnderstandingML_Online

namespace OrderedExperts

/-- **The smoothed intended distribution `πt` of
Algorithm 2.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Algorithm 2, p.11: "Set `ut(f) ∝ exp(−ηLt−1(f))`,
`pt(j) = Σ_{f: jt(f)=j} ut(f)`, and `πt = (1 − 1/T)pt + (1/T) Unif(Xt)`", with "Set `L0(f) = 0`" and
"Set `Lt(f) = Lt−1(f) + ℓ̂↑t(jt(f)) + ℓ̂↓t(jt(f))`".

Given the past estimate vectors `v s : Fin n → ℝ` (`s < t`), `ut = wmWeights η v t` is the
exponential-weights distribution with `Lt−1 = Σ_{s<t} v s`, and `roundPi η T rec v t j` is
`(1 − 1/T) pt(j) + (1/T)(1/mt)` on the active ranks `j ∈ {1, …, mt}`, and `0` elsewhere.

**Formalization Note.** Rounds are 0-based (`t = 0, …, T−1` for the paper's `1, …, T`); the
exponential weights are the published `UnderstandingML.wmWeights`, whose cumulative loss
`Σ_{s ∈ range t} v s` builds in `L0 = 0`. -/
noncomputable def roundPi {A : Type*} [LinearOrder A] {n : ℕ} (η : ℝ) (T : ℕ)
    (rec : ℕ → Fin n → A) (v : ℕ → Fin n → ℝ) (t j : ℕ) : ℝ :=
  if j ∈ Finset.Icc 1 (chainSize rec t) then
    (1 - 1 / (T : ℝ)) * (∑ f ∈ Finset.univ.filter (fun f => rank rec t f = j),
        UnderstandingML.wmWeights η v t f) +
      1 / (T : ℝ) * (1 / (chainSize rec t : ℝ))
  else 0

end OrderedExperts


