-- Prove2me | Definitions.Def_FreemiumActions_Threshold_Data
-- name    : FreemiumActions_Threshold_Data
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:57:34.511649+00:00
-- url     : https://prove2.me/theorems/eb5fab25-5983-44cc-b4b9-79ab336e279e
-- title:
--   Freemium model data and Assumptions 1–7
-- statement:
--   The state set is $E=\{0,\ldots,N\}$ with a separate absorbing quit state. Controls are offer ($1$) and remove ($0$); a policy is any stationary map from $E$ to these controls. The data are six real state arrays $p_M,p_I,p_Q,q_M,q_Q,\alpha$, constant progression probabilities $\tau_M,\tau_I$, and revenues $\mu_M,\mu_I$.
--
--   The standing conditions place all probabilities and $\alpha$ in $[0,1]$, normalize the choice probabilities, and require $\mu_I\ge0$. Assumption 1 redistributes $p_I$ between monetization and quitting in proportions $\alpha$ and $1-\alpha$. Assumption 3 requires $p_M,q_M,\alpha$ nondecreasing, $p_Q,q_Q,p_I$ nonincreasing, strictly positive quitting and $\tau_M>\tau_I$. Assumption 4 is $\mu_I<\mu_M$. Assumption 5 is $\alpha(N)=1$. Assumption 6 is $\alpha(f)-\alpha(e)>q_M(f)-q_M(e)$ for adjacent levels $f=e+1$. Assumption 7 is
--   $$1-\alpha(e+1)\le(1-\alpha(e))\frac{p_M(e+1)\tau_M+p_I(e+1)\tau_I}{p_Q(e+1)+p_M(e+1)\tau_M+p_I(e+1)\tau_I},\qquad 1\le e<N.$$
--   The predicates for Assumptions 1–4, 1–6 and 1–7 combine these conditions. Assumption 2 is implemented by the dynamics definition, rather than an unproved field. The weak monotonicity and nonnegative-revenue conventions are explicit; the printed lower endpoint of Assumption 7 is unchanged.
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, §§3–5, pp. 7–11 and 19–20 (PDF pp. 7–11 and 19–20), Assumptions 1–7; catalog DOI 10.1287/msom.2020.0925.

import Mathlib

namespace FreemiumActions.Threshold

abbrev Level (N : ℕ) := Fin (N + 1)
abbrev State (N : ℕ) := Option (Level N)
abbrev Policy (N : ℕ) := Level N → Bool

structure Data (N : ℕ) where
  pM : Level N → ℝ
  pI : Level N → ℝ
  pQ : Level N → ℝ
  qM : Level N → ℝ
  qQ : Level N → ℝ
  alpha : Level N → ℝ
  tauM : ℝ
  tauI : ℝ
  muM : ℝ
  muI : ℝ

def Standing {N : ℕ} (d : Data N) : Prop :=
  (∀ e, d.pM e ∈ Set.Icc 0 1 ∧ d.pI e ∈ Set.Icc 0 1 ∧
    d.pQ e ∈ Set.Icc 0 1 ∧ d.qM e ∈ Set.Icc 0 1 ∧
    d.qQ e ∈ Set.Icc 0 1 ∧ d.alpha e ∈ Set.Icc 0 1 ∧
    d.pM e + d.pI e + d.pQ e = 1 ∧ d.qM e + d.qQ e = 1) ∧
  d.tauM ∈ Set.Icc 0 1 ∧ d.tauI ∈ Set.Icc 0 1 ∧ 0 ≤ d.muI

def A1 {N : ℕ} (d : Data N) : Prop :=
  ∀ e, d.qM e = d.pM e + d.alpha e * d.pI e ∧
    d.qQ e = d.pQ e + (1 - d.alpha e) * d.pI e

def A3 {N : ℕ} (d : Data N) : Prop :=
  Monotone d.pM ∧ Monotone d.qM ∧ Antitone d.pQ ∧ Antitone d.qQ ∧
  (∀ e, 0 < d.pQ e ∧ 0 < d.qQ e) ∧ Antitone d.pI ∧
  d.tauI < d.tauM ∧ Monotone d.alpha

def A4 {N : ℕ} (d : Data N) : Prop := d.muI < d.muM

def A5 {N : ℕ} (d : Data N) : Prop := d.alpha (Fin.last N) = 1

def A6 {N : ℕ} (d : Data N) : Prop :=
  ∀ e f : Level N, f.val = e.val + 1 →
    d.qM f - d.qM e < d.alpha f - d.alpha e

def A7 {N : ℕ} (d : Data N) : Prop :=
  ∀ e f : Level N, 1 ≤ e.val → f.val = e.val + 1 →
    1 - d.alpha f ≤ (1 - d.alpha e) *
      (d.pM f * d.tauM + d.pI f * d.tauI) /
      (d.pQ f + d.pM f * d.tauM + d.pI f * d.tauI)

def Assumptions14 {N : ℕ} (d : Data N) : Prop :=
  Standing d ∧ A1 d ∧ A3 d ∧ A4 d

def Assumptions16 {N : ℕ} (d : Data N) : Prop :=
  Assumptions14 d ∧ A5 d ∧ A6 d

def Assumptions17 {N : ℕ} (d : Data N) : Prop :=
  Assumptions16 d ∧ A7 d

end FreemiumActions.Threshold


