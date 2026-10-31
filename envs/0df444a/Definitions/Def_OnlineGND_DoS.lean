-- Prove2me | Definitions.Def_OnlineGND_DoS
-- name    : OnlineGND_DoS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:59.238988+00:00
-- url     : https://prove2.me/theorems/99ef6879-e868-4e5f-9481-5962f6d77af1
-- title:
--   (1), (3) — (dis)economies-of-scale costs $f_e$, thresholds $q_e$, $\max\{q,1\}$ and $h_e$
-- statement:
--   Each resource $e$ has parameters $\sigma_e\ge0$, $\xi_e>0$, $\alpha_e\ge1$.
--
--   1. **(D)oS cost (1), p.2.**
--   $$f_e(x)=\begin{cases}0 & x=0,\\ \sigma_e+\xi_e x^{\alpha_e} & x>0.\end{cases}$$
--   2. **Threshold load, p.3.** $q_e=(\sigma_e/\xi_e)^{1/\alpha_e}$, the load at which $\sigma_e$ and $\xi_e x^{\alpha_e}$ are equal; $\max\{q,1\}$ with $q=\max_e q_e$.
--   3. **Convex surrogate (3), p.6.** $h_e(x)=\xi_e q_e^{\alpha_e-1}x+\xi_e x^{\alpha_e}$ for $x\ge0$.
--
--   The start-up cost $\sigma_e$ is paid only on a resource that carries load. Lemma 1 sandwiches $f_e$ between multiples of $h_e$.
--
--   **Formalization Note** Powers are `Real.rpow`, so $0^0=1$; this only arises in $q_e^{\alpha_e-1}$ when $q_e=0$ and $\alpha_e=1$, where the paper's value is $1$ as well. $\max\{q,1\}$ is computed as $\max(1,\max_e q_e)$, which is $1$ for $E=\emptyset$.
-- source:
--   Nagarajan & Wang, Online Generalized Network Design Under (Dis)Economies of Scale, arXiv:2007.07721v1, (1) p.2; q_e, q p.3; (3) p.6; max{q,1} (26)–(27) p.14

import Mathlib

namespace OnlineGND

/-! # (Dis)economies-of-scale cost functions (Nagarajan & Wang, arXiv:2007.07721v1, (1) p.2, p.3, (3) p.6)

The (D)oS cost `fₑ`, the threshold loads `qₑ`, `max{q, 1}` and the convex surrogate `hₑ` of §2.

**Formalization Note.** Powers `x^{αₑ}` are `Real.rpow`, so `0^0 = 1`; this only matters in
`qₑ^{αₑ−1}` when `qₑ = 0` and `αₑ = 1`, where the paper's value is also `1`. Parameters are
functions `σ ξ α : E → ℝ`; the theorems assume `σₑ ≥ 0`, `ξₑ > 0`, `αₑ ≥ 1`. -/

variable {E : Type*} [Fintype E]

/-- The (D)oS cost function (1) (arXiv:2007.07721v1, p.2): `fₑ(x) = 0` if `x = 0` and
`fₑ(x) = σₑ + ξₑ · x^{αₑ}` if `x > 0`.

**Formalization Note.** The function is defined on all of `ℝ` by the `x ≠ 0` branch; it is only
evaluated at loads, which are `≥ 0`. The start-up cost `σₑ` is charged only on a used resource. -/
noncomputable def dosCost (σ ξ α : E → ℝ) (e : E) (x : ℝ) : ℝ :=
  if x = 0 then 0 else σ e + ξ e * x ^ α e

/-- The threshold load `qₑ := (σₑ/ξₑ)^{1/αₑ}` (arXiv:2007.07721v1, p.3), the load at which `σₑ` and
`ξₑ x^{αₑ}` are equal.

**Formalization Note.** Defined with Lean's total division; every theorem assumes `ξₑ > 0`, so the
quotient is the paper's. -/
noncomputable def qPar (σ ξ α : E → ℝ) (e : E) : ℝ :=
  (σ e / ξ e) ^ (1 / α e)

/-- `max{q, 1}` with `q := max_{e∈E} qₑ` (arXiv:2007.07721v1, p.3 and (26)–(27), p.14), computed as
`max(1, maxₑ qₑ)`.

**Formalization Note.** For `E = ∅` it is `1`; otherwise it is the paper's `max{q, 1}`. -/
noncomputable def qMax1 (σ ξ α : E → ℝ) : ℝ :=
  Finset.univ.fold max 1 (qPar σ ξ α)

/-- The convex surrogate (3) (arXiv:2007.07721v1, p.6):
`hₑ(x) := ξₑ qₑ^{αₑ−1} · x + ξₑ · x^{αₑ}` for `x ≥ 0`. -/
noncomputable def hFun (σ ξ α : E → ℝ) (e : E) (x : ℝ) : ℝ :=
  ξ e * qPar σ ξ α e ^ (α e - 1) * x + ξ e * x ^ α e

end OnlineGND


