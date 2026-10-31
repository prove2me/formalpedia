-- Prove2me | Definitions.Def_ReviewProvision_ratingStat
-- name    : ReviewProvision_ratingStat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:52:27.545039+00:00
-- url     : https://prove2.me/theorems/e1bbdcb5-ef7c-47cd-a1b6-a5cee288ba99
-- title:
--   Rating precision $w_n$ and rating statistic $y_n$
-- statement:
--   If $k_n\ge0$ customers buy in cluster $n$ in the first period, a fraction $\theta$ rate the product, so the average rating $r_n$ satisfies $r_n\mid(q,t_n)\sim N(q+t_n,1/w_n)$ with precision
--
--   $$
--   w_n:=k_n\theta\zeta.
--   $$
--
--   The **rating statistic** of cluster $n$ is
--
--   $$
--   y_n:=w_n(q+t_n)+\sqrt{w_n}\,\varepsilon_n .
--   $$
--
--   **Formalization Note** For $w_n>0$ one has $y_n=w_nr_n$ with $r_n=q+t_n+\varepsilon_n/\sqrt{w_n}$, so $y_n$ and $r_n$ carry the same information, and $S_1\bar r=\sum_l y_l$. For $w_n=0$ the statistic is $0$: nobody bought, so no rating exists. The rating itself is not usable in Lean, where $1/\sqrt0=0$ would make $r_n$ the perfect signal $q+t_n$ at $k_n=0$, the opposite of the model.
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), §3.3, p.11

import Mathlib
import Definitions.Def_ReviewProvision_prior

open MeasureTheory ProbabilityTheory

namespace ReviewProvision

/-- The **precision of the average rating** of cluster `n`: `w_n := k_n θ ζ`.
SSRN 3403322 (manuscript of 2021-05-24), §3.3, p.11 (PDF 11). -/
def weight {N : ℕ} (p : Params) (k : Fin N → ℝ) (n : Fin N) : ℝ := k n * p.theta * p.zeta

/-- The **rating statistic** of cluster `n`:
`y_n = w_n (q + t_n) + √w_n ε_n`. SSRN 3403322 (manuscript of 2021-05-24), §3.3, p.11 (PDF 11), which
has `r_n | (q, t_n) ∼ N(q + t_n, 1/w_n)`.

**Formalization Note.** For `w_n > 0`, `y_n = w_n r_n` with `r_n = q + t_n + ε_n/√w_n`, so `y_n` and
`r_n` generate the same σ-algebra, and `S_1 r̄ = Σ_l y_l`. For `w_n = 0`, `y_n = 0`: nobody bought, so
no rating exists and the statistic carries no information. The rating itself cannot be used: in
Lean `1/√0 = 0`, so `r_n` at `w_n = 0` would be the perfect signal `q + t_n`, the opposite of the
model. -/
noncomputable def ratingStat {N : ℕ} (p : Params) (k : Fin N → ℝ) (n : Fin N) (ω : Sample N) : ℝ :=
  weight p k n * (quality ω + taste ω n) + √(weight p k n) * noise ω n

lemma measurable_quality {N : ℕ} : Measurable (quality : Sample N → ℝ) := measurable_fst

lemma measurable_taste {N : ℕ} (n : Fin N) : Measurable (fun ω : Sample N => taste ω n) :=
  (measurable_pi_apply n).comp (measurable_fst.comp measurable_snd)

lemma measurable_noise {N : ℕ} (n : Fin N) : Measurable (fun ω : Sample N => noise ω n) :=
  (measurable_pi_apply n).comp (measurable_snd.comp measurable_snd)

lemma measurable_ratingStat {N : ℕ} (p : Params) (k : Fin N → ℝ) (n : Fin N) :
    Measurable (ratingStat p k n) :=
  ((measurable_quality.add (measurable_taste n)).const_mul _).add
    ((measurable_noise n).const_mul _)

end ReviewProvision


