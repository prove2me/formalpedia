-- Prove2me | Definitions.Def_ScheduledQueue_Stability_Reversed
-- name    : ScheduledQueue_Stability_Reversed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:12.654711+00:00
-- url     : https://prove2.me/theorems/2d5e9e67-4b32-4c33-b121-3a3d61a611fa
-- title:
--   Proof of Theorem 1, pp. 5–6 — reversed arrivals, Λ(s), M(t), β₁, β₂, Γ₁, Γ₂, Y_n, Ỹ_n
-- statement:
--   These are the auxiliary quantities of the proof of Theorem 1 of Araman and Glynn, built from the scheduled-traffic data $h$, $(\xi_j)_{j\in\mathbb Z}$ and $U$ of the setting.
--
--   The **time-reversed arrival time** of customer $j$ is $R_j = jh + Uh - \xi_j$. For $s\ge0$ let
--   $$\Lambda(s) = h\cdot\#\{j\in\mathbb Z : R_j\in(0,s]\},\qquad M(t)=\sup_{0\le s\le t}\big(\Lambda(s)-s\big).$$
--   With $k(s)=\lfloor s/h\rfloor$, the proof uses the counts (all valued in $\{0,1,2,\dots\}\cup\{\infty\}$)
--   $$\beta_1(s)=\sum_{j\ge1} I\big(R_{-j}\in(0,s]\big),\qquad \beta_2(s)=\sum_{j\ge k(s)+1} I\big(R_j\in(0,s]\big),$$
--   $$\Gamma_1=\sum_{j\ge1} I\big(-\xi_{-j}>(j-1)h\big),\qquad \Gamma_2=\sum_{j\ge1} I\big(\xi_j\ge(j-1)h\big),$$
--   and, for $n=0,1,2,\dots$,
--   $$Y_n=\sum_{j\ge1} I\big(-\xi_{n+1-j}>(j-2)h\big),\qquad \tilde Y_n=\sum_{j\ge1} I\big(\xi^+_{n+j}\ge(j+2)h\big),$$
--   where $\xi^+=\max(\xi,0)$.
--
--   $\Lambda$ and $M$ are the reversed arrival process and its running maximum, whose law equals that of the workload by Loynes' lemma. $\beta_1,\beta_2,\Gamma_1$ control $M$ from above (customers arriving early in reversed time, and late customers), while $Y_n,\tilde Y_n,\Gamma_2$ control it from below.
--
--   **Formalization Note.** The reversed count is `revCount` (`Set.encard`, valued in `ℕ∞`), and every proof count is `Set.encard` too, so that "$\Gamma_1<\infty$ a.s." is a real statement rather than true by a junk value. `Lam` converts the count with `ENat.toNat` (value $0$ at $\infty$); the count is finite for all $s$ simultaneously on a full-measure event, so this junk value only occurs on a null event, and `revMax` is a real supremum over $[0,t]$ that is bounded on that event. Corrections to the page: the printed $Y_{k(s)}=\sum_{j\ge1} I(\xi_{k(s)-j}>(j-2)h)$ has the wrong sign (the next sentence, "Since $\mathbb E\xi_0^-<\infty$, $Y_0<\infty$", requires $-\xi$) and omits $\xi_{k(s)}$; the definition here is the corrected one. $\beta_3,\beta_4$ are not defined, because the printed identity $\Lambda(s)-h\lfloor s/h\rfloor=\beta_1+\beta_2-\beta_3-\beta_4$ is false as printed (it omits $j=0$ and $\beta_4$ is infinite); the milestones state the two one-sided inequalities the proof actually uses.
-- source:
--   Araman and Glynn, Stability of a Queue Fed by Scheduled Traffic at Critical Loading, arXiv:2212.04164v1, pp. 5–6, proof of Theorem 1 (displays defining M(t), Λ(s), β₁, β₂, Γ₁, Y_{k(s)}, Ỹ_{k(s)}, Γ₂)

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting

namespace ScheduledQueue.Stability

open Set

variable {Ω : Type*}

/-- Time-reversed arrival time of customer `j` (proof of Theorem 1, p. 5): `jh + Uh − ξ_j`. -/
def revArrival (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (j : ℤ) (ω : Ω) : ℝ :=
  j * h + U ω * h - ξ j ω

/-- Number of reversed arrivals in `(0, s]`, valued in `ℕ∞`. -/
noncomputable def revCount (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (s : ℝ) (ω : Ω) : ℕ∞ :=
  {j : ℤ | revArrival h ξ U j ω ∈ Ioc 0 s}.encard

/-- `Λ(s) = h · #{j : jh + Uh − ξ_j ∈ (0, s]}`. -/
noncomputable def Lam (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  h * (revCount h ξ U s ω).toNat

/-- `M(t) = sup_{0 ≤ s ≤ t} (Λ(s) − s)`, the running maximum of the time-reversed process. -/
noncomputable def revMax (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ⨆ s : Icc 0 t, (Lam h ξ U s ω - s)

/-- `β₁(s) = Σ_{j ≥ 1} I(Uh − jh − ξ_{−j} ∈ (0, s])`. -/
noncomputable def beta1 (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (s : ℝ) (ω : Ω) : ℕ∞ :=
  {j : ℤ | 1 ≤ j ∧ revArrival h ξ U (-j) ω ∈ Ioc 0 s}.encard

/-- `β₂(s) = Σ_{j ≥ ⌊s/h⌋ + 1} I(Uh + jh − ξ_j ∈ (0, s])`. -/
noncomputable def beta2 (h : ℝ) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) (s : ℝ) (ω : Ω) : ℕ∞ :=
  {j : ℤ | (⌊s / h⌋₊ : ℤ) + 1 ≤ j ∧ revArrival h ξ U j ω ∈ Ioc 0 s}.encard

/-- `Γ₁ = Σ_{j ≥ 1} I(−ξ_{−j} > (j − 1)h)`. -/
noncomputable def gamma1 (h : ℝ) (ξ : ℤ → Ω → ℝ) (ω : Ω) : ℕ∞ :=
  {j : ℤ | 1 ≤ j ∧ (j - 1) * h < -ξ (-j) ω}.encard

/-- `Γ₂ = Σ_{j ≥ 1} I(ξ_j ≥ (j − 1)h)`. -/
noncomputable def gamma2 (h : ℝ) (ξ : ℤ → Ω → ℝ) (ω : Ω) : ℕ∞ :=
  {j : ℤ | 1 ≤ j ∧ (j - 1) * h ≤ ξ j ω}.encard

/-- `Y_n = Σ_{j ≥ 1} I(−ξ_{n+1−j} > (j − 2)h)` (corrected from the printed
`Σ_{j ≥ 1} I(ξ_{n−j} > (j − 2)h)`, p. 6). -/
noncomputable def Y (h : ℝ) (ξ : ℤ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ∞ :=
  {j : ℤ | 1 ≤ j ∧ (j - 2) * h < -ξ ((n : ℤ) + 1 - j) ω}.encard

/-- `Ỹ_n = Σ_{j ≥ 1} I(ξ⁺_{n+j} ≥ (j + 2)h)` (p. 6). -/
noncomputable def tildeY (h : ℝ) (ξ : ℤ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℕ∞ :=
  {j : ℤ | 1 ≤ j ∧ (j + 2) * h ≤ max (ξ ((n : ℤ) + j) ω) 0}.encard

end ScheduledQueue.Stability


