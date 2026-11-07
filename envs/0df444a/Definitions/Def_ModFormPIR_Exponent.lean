-- Prove2me | Definitions.Def_ModFormPIR_Exponent
-- name    : ModFormPIR_Exponent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:47.799709+00:00
-- url     : https://prove2.me/theorems/a20f29bb-9e67-4f7b-a55f-91bb1ad02f8b
-- title:
--   The Track 3 exponent $\eta_{q,s}(\vartheta,\nu)$ and $\eta_{q,s}$
-- statement:
--   Let $q$ be an odd prime and $s\in[2,q]$. The **cost** and its generating function are
--   $$w_{q,\vartheta}(j)=\min_{k\in\mathbb Z,\ k\equiv j\ (q)}\big(k(k-1)+2\vartheta k\big),\qquad M_\vartheta(t)=\sum_{j\in\mathbb Z_q}t^{w_{q,\vartheta}(j)}.$$
--   A pair $(\vartheta,\nu)$ is **feasible** if $0\le\vartheta\le\min\{1,\frac{q+1}{6s}\}$ and $0\le\nu\le\frac{q^2-1}{8s}$, with budget
--   $$\gamma(\vartheta,\nu)=\frac{q-1}2\vartheta+\Big(1-\frac{6s}{q+1}\vartheta\Big)\Big(\frac{q^2-1}{4s}-2\nu\Big).$$
--   Then
--   $$E^{\mathrm{sq}}_q(\nu)=\frac1{\ln q}\inf_{0<t\le1}\big(\ln M_{1/2}(t)-\nu\ln t\big),\quad E^{\mathrm{edge}}_{q,s}(\vartheta,\nu)=\frac1{\ln q}\inf_{0<t\le1}\big(\ln M_\vartheta(t)-\gamma(\vartheta,\nu)\ln t\big),$$
--   $$\eta_{q,s}(\vartheta,\nu)=\max\big(E^{\mathrm{sq}}_q(\nu),E^{\mathrm{edge}}_{q,s}(\vartheta,\nu)\big),\qquad \eta_{q,s}=\inf\{\eta_{q,s}(\vartheta,\nu):(\vartheta,\nu)\text{ feasible}\}.$$
--   These are Chernoff bounds on the number of frequency vectors of small total cost; they are the exponents of the goal theorem.
--
--   **Formalization Note** Minima and infima are real `sInf`. On the source's domain each is over a nonempty set bounded below.
-- source:
--   Henzinger, Ragavan, Doubly-Efficient Private Information Retrieval from Modular Forms, STOC 2027 submission (manuscript sha256 2442f3db…), Definition 5.4 with (14), pp.21–22

import Mathlib

open scoped BigOperators

set_option autoImplicit false

namespace ModFormPIR

/-!
# The Track 3 exponent

Henzinger, Ragavan, *Doubly-Efficient Private Information Retrieval from Modular Forms*, STOC 2027
submission (manuscript sha256 2442f3db…), Definition 5.4 with (14), pp.21–22.

**Formalization Note.** The minima over `k ≡ j` and the infima over `t ∈ (0,1]` and over feasible pairs are
real `sInf`s. They are never junk on the source's domain: `k(k-1)+2ϑk` is bounded below and tends to
`+∞`; for a feasible pair `ln M(t) ≥ 0` and the budgets are nonnegative, so each infimum is over a nonempty
set bounded below by `0`. The sanity file proves this.
-/

/-- `w_{q,ϑ}(j) = min_{k ∈ ℤ, k ≡ j (mod q)} (k(k-1) + 2ϑk)`. -/
noncomputable def cost (q : ℕ) (ϑ : ℝ) (j : ZMod q) : ℝ :=
  sInf {r : ℝ | ∃ k : ℤ, (k : ZMod q) = j ∧ r = (k : ℝ) * ((k : ℝ) - 1) + 2 * ϑ * (k : ℝ)}

/-- `M_ϑ(t) = ∑_{j ∈ ℤ_q} t^{w_{q,ϑ}(j)}`. -/
noncomputable def genM (q : ℕ) [NeZero q] (ϑ t : ℝ) : ℝ := ∑ j : ZMod q, t ^ cost q ϑ j

/-- `(ϑ, ν)` is feasible for `q, s`: `0 ≤ ϑ ≤ min{1, (q+1)/(6s)}` and `0 ≤ ν ≤ (q²-1)/(8s)`. -/
def Feasible (q s : ℕ) (ϑ ν : ℝ) : Prop :=
  0 ≤ ϑ ∧ ϑ ≤ min 1 (((q : ℝ) + 1) / (6 * (s : ℝ))) ∧
    0 ≤ ν ∧ ν ≤ ((q : ℝ) ^ 2 - 1) / (8 * (s : ℝ))

/-- `γ(ϑ,ν) = ((q-1)/2) ϑ + (1 - (6s/(q+1)) ϑ) ((q²-1)/(4s) - 2ν)`. -/
noncomputable def budget (q s : ℕ) (ϑ ν : ℝ) : ℝ :=
  (((q : ℝ) - 1) / 2) * ϑ +
    (1 - (6 * (s : ℝ) / ((q : ℝ) + 1)) * ϑ) * (((q : ℝ) ^ 2 - 1) / (4 * (s : ℝ)) - 2 * ν)

/-- `(1/ln q) inf_{0<t≤1} (ln M_ϑ(t) - c ln t)`, the Chernoff exponent at budget `c`. -/
noncomputable def chernoff (q : ℕ) [NeZero q] (ϑ c : ℝ) : ℝ :=
  (1 / Real.log q) *
    sInf ((fun t : ℝ => Real.log (genM q ϑ t) - c * Real.log t) '' Set.Ioc 0 1)

/-- `E^sq_q(ν)`. -/
noncomputable def Esq (q : ℕ) [NeZero q] (ν : ℝ) : ℝ := chernoff q (1 / 2) ν

/-- `E^edge_{q,s}(ϑ,ν)`. -/
noncomputable def Eedge (q s : ℕ) [NeZero q] (ϑ ν : ℝ) : ℝ := chernoff q ϑ (budget q s ϑ ν)

/-- `η_{q,s}(ϑ,ν) = max(E^sq_q(ν), E^edge_{q,s}(ϑ,ν))`. -/
noncomputable def eta (q s : ℕ) [NeZero q] (ϑ ν : ℝ) : ℝ := max (Esq q ν) (Eedge q s ϑ ν)

/-- `η_{q,s} = inf{η_{q,s}(ϑ,ν) : (ϑ,ν) feasible}`, display (14). -/
noncomputable def etaInf (q s : ℕ) [NeZero q] : ℝ :=
  sInf {x : ℝ | ∃ ϑ ν : ℝ, Feasible q s ϑ ν ∧ x = eta q s ϑ ν}

end ModFormPIR


