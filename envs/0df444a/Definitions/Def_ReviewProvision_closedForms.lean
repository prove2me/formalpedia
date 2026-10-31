-- Prove2me | Definitions.Def_ReviewProvision_closedForms
-- name    : ReviewProvision_closedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:51:32.806636+00:00
-- url     : https://prove2.me/theorems/b22c2f2a-d36b-4cd1-9380-8160d1e228c3
-- title:
--   Closed-form variances $\sigma^2_{\psi n}$ and their derivatives
-- statement:
--   With $S_1=\sum_lw_l$, $S_2=\sum_lw_l^2$, $S_1'=S_1-w_n$, $S_2'=S_2-w_n^2$ and $T=\sum_l\eta w_l/(\eta+w_l)$, the closed forms of the paper are
--
--   $$
--   \sigma^2_{An}=\frac{(\tau+\eta)^2w_n}{\tau\eta[\tau\eta+(\tau+\eta)w_n]},\qquad
--   \sigma^2_{Gn}=\frac{(\tau w_n+\eta S_1)^2}{\tau\eta(\tau\eta S_1+\tau S_2+\eta S_1^2)},
--   $$
--
--   $$
--   \sigma^2_{Fn}=\frac{w_n(\tau+T)[\tau(\eta+w_n)+\eta w_n]+2\eta^2w_n(\tau+T)+\eta^3T}{\tau\eta(\eta+w_n)^2(\tau+T)},
--   $$
--
--   $$
--   \sigma^2_{Jn}=\frac{\eta^3S_1'^2+(\tau+\eta)w_n[\eta S_1'(\tau+\eta+S_1')+(\tau+\eta)S_2']}{\tau\eta\{[\tau(\eta+w_n)+\eta w_n](\eta S_1'+S_2')+\eta(\eta+w_n)S_1'^2\}}.
--   $$
--
--   The same module holds the right sides of (25)–(26), the symmetric variance $\sigma^2(w)$ with $w=k\theta\zeta$ of p.45, and the display below (29). They are used in milestones only: neither the profit nor the goal mentions them.
--
--   **Formalization Note** $\sigma^2_{Gn}$ is $0/0$ at $S_1=0$ and $\sigma^2_{Jn}$ at $S_1'=0$, so every use carries that guard.
-- source:
--   Xiao, Chen, Tang, Customer Review Provision Policies with Heterogeneous Cluster Preferences, SSRN 3403322 (manuscript of 2021-05-24), Lemma 1, p.15; (12), p.23; (13), p.24; (25)–(26), (29), p.45

import Mathlib
import Definitions.Def_ReviewProvision_Params

namespace ReviewProvision

/-- `S_1 := Σ_l w_l`, (2), p.12 (PDF 12). -/
def S1 {N : ℕ} (w : Fin N → ℝ) : ℝ := ∑ l, w l

/-- `S_2 := Σ_l w_l²`, (2), p.12 (PDF 12). -/
def S2 {N : ℕ} (w : Fin N → ℝ) : ℝ := ∑ l, w l ^ 2

/-- `S′_1 := (Σ_l w_l) − w_n`, p.24 (PDF 24). -/
def S1' {N : ℕ} (w : Fin N → ℝ) (n : Fin N) : ℝ := S1 w - w n

/-- `S′_2 := (Σ_l w_l²) − w_n²`, p.24 (PDF 24). -/
def S2' {N : ℕ} (w : Fin N → ℝ) (n : Fin N) : ℝ := S2 w - w n ^ 2

/-- `T := Σ_l η w_l/(η + w_l)`, p.23 (PDF 23). -/
noncomputable def T {N : ℕ} (p : Params) (w : Fin N → ℝ) : ℝ :=
  ∑ l, p.eta * w l / (p.eta + w l)

/-- `σ²_{An} = (τ+η)² w_n / (τη[τη + (τ+η) w_n])`, Lemma 1, p.15 (PDF 15). A closed form, used in
milestones only. -/
noncomputable def sigmaSqA {N : ℕ} (p : Params) (w : Fin N → ℝ) (n : Fin N) : ℝ :=
  (p.tau + p.eta) ^ 2 * w n /
    (p.tau * p.eta * (p.tau * p.eta + (p.tau + p.eta) * w n))

/-- `σ²_{Gn} = (τ w_n + η S_1)² / (τη(τη S_1 + τ S_2 + η S_1²))`, Lemma 1, p.15 (PDF 15). A closed form,
used in milestones only; it is `0/0` at `S_1 = 0`, so every use is guarded by `0 < S1 w`. -/
noncomputable def sigmaSqG {N : ℕ} (p : Params) (w : Fin N → ℝ) (n : Fin N) : ℝ :=
  (p.tau * w n + p.eta * S1 w) ^ 2 /
    (p.tau * p.eta * (p.tau * p.eta * S1 w + p.tau * S2 w + p.eta * S1 w ^ 2))

/-- `σ²_{Fn}`, (12), p.23 (PDF 23). A closed form, used in milestones only. -/
noncomputable def sigmaSqF {N : ℕ} (p : Params) (w : Fin N → ℝ) (n : Fin N) : ℝ :=
  (w n * (p.tau + T p w) * (p.tau * (p.eta + w n) + p.eta * w n) +
      2 * p.eta ^ 2 * w n * (p.tau + T p w) + p.eta ^ 3 * T p w) /
    (p.tau * p.eta * (p.eta + w n) ^ 2 * (p.tau + T p w))

/-- `σ²_{Jn}`, (13), p.24 (PDF 24). A closed form, used in milestones only; it is `0/0` at
`S′_1 = 0`, so every use is guarded by `0 < S1' w n`. -/
noncomputable def sigmaSqJ {N : ℕ} (p : Params) (w : Fin N → ℝ) (n : Fin N) : ℝ :=
  (p.eta ^ 3 * S1' w n ^ 2 +
      (p.tau + p.eta) * w n *
        (p.eta * S1' w n * (p.tau + p.eta + S1' w n) + (p.tau + p.eta) * S2' w n)) /
    (p.tau * p.eta *
      ((p.tau * (p.eta + w n) + p.eta * w n) * (p.eta * S1' w n + S2' w n) +
        p.eta * (p.eta + w n) * S1' w n ^ 2))

/-- The partial derivative `∂σ²_{Fl}/∂w_n`: the right side of (25) for `l ≠ n`, of (26) for `l = n`,
p.45 (PDF 45). `eq_25_26` proves that it is the derivative. -/
noncomputable def dSigmaSqF {N : ℕ} (p : Params) (w : Fin N → ℝ) (l n : Fin N) : ℝ :=
  if l = n then
    ((p.tau + T p w) * (p.eta + w n) + p.eta ^ 2) ^ 2 /
      ((p.tau + T p w) ^ 2 * (p.eta + w n) ^ 4)
  else
    p.eta ^ 4 / ((p.tau + T p w) ^ 2 * (p.eta + w n) ^ 2 * (p.eta + w l) ^ 2)

/-- The common variance at symmetric sales, with `w = k θ ζ`:
`w[Nη³ + (τ+η)(τ+Nη)w + τη(τ+2η)] / (τη(η+w)[τη + (τ+Nη)w])`, proof of Proposition 4, p.45 (PDF 45). -/
noncomputable def sigmaSqSym (p : Params) (N : ℕ) (w : ℝ) : ℝ :=
  w * (N * p.eta ^ 3 + (p.tau + p.eta) * (p.tau + N * p.eta) * w +
      p.tau * p.eta * (p.tau + 2 * p.eta)) /
    (p.tau * p.eta * (p.eta + w) * (p.tau * p.eta + (p.tau + N * p.eta) * w))

/-- `∂σ²_F/∂w_F`, the display below (29), p.45 (PDF 45). The final `2` of the printed denominator is
an exponent. -/
noncomputable def dSigmaSqSym (p : Params) (N : ℕ) (w : ℝ) : ℝ :=
  (N * p.eta ^ 2 * (N * w ^ 2 + p.eta * (2 * w + p.eta)) +
      2 * p.tau * p.eta * (w + p.eta) * (N * w + p.eta) + p.tau ^ 2 * (w + p.eta) ^ 2) /
    ((w + p.eta) ^ 2 * (N * w * p.eta + (w + p.eta) * p.tau) ^ 2)

end ReviewProvision


