-- Prove2me | Definitions.Def_RestartPD_Fixed_Algorithms
-- name    : RestartPD_Fixed_Algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:37.328568+00:00
-- url     : https://prove2.me/theorems/ae3d3987-0512-49e8-a8b6-4749f698c3c9
-- title:
--   §2, §4, pp. 6–16 — the generic algorithm (6), Properties 1–3, Algorithm 1 with fixed-frequency restarts (29)
-- statement:
--   Fix problem (1) on $Z = X \times Y$, a semi-norm $\|\cdot\|$, and the objects of the Problem definition.
--
--   **Property 3** (pp. 9–10). An abstract primal-dual algorithm is described by the set of its admissible output sequences $\{\bar z^t\}_{t \ge 1}$ from each start $z^0$. It satisfies Property 3 with constants $q, C > 0$ if for every $z^0 \in Z$, every such output sequence and every $t \ge 1$, $\bar z^t \in Z$ and
--   $$\text{i. } \rho_{\|\bar z^t - z^0\|}(\bar z^t) \le \frac{2C \|\bar z^t - z^0\|}{t}, \qquad \text{ii. } \|\bar z^t - z^0\| \le (q + 2) \operatorname{dist}(z^0, Z^\star).$$
--
--   **Algorithm 1 with fixed-frequency restarts** (pp. 15–16, rule (29)). Given $t^\star \in \mathbb N$, a run consists of outer iterates $z^{n,0}$ ($n \ge 0$) and inner outputs $\bar z^{n,t}$: for each $n$, $\{\bar z^{n,t}\}_t$ is an output sequence of the base algorithm started at $z^{n,0}$, and the next outer iterate is $z^{n+1,0} = \bar z^{n,t^\star}$. In the paper $t^\star = \lceil 2C(q+2)/(\alpha\beta) \rceil$.
--
--   **The generic algorithm (6)** (p. 6) produces iterates $z^t$ ($t \ge 0$) and target solutions $\hat z^t$ ($t \ge 1$), both in $Z$, with average $\bar z^t = \frac1t \sum_{i=1}^t \hat z^i$. It satisfies
--   1. **Property 1** (p. 7, (12)) with $C > 0$ if for every $t \ge 0$ and $z = (x, y) \in Z$,
--   $$L(\hat x^{t+1}, y) - L(x, \hat y^{t+1}) \le \frac C2 \|z - z^t\|^2 - \frac C2 \|z - z^{t+1}\|^2;$$
--   2. **Property 2** (p. 9) with $q > 0$ if for every $t \ge 1$, $\|\hat z^t - z^t\| \le q \operatorname{dist}(z^t, Z^\star)$ or $\|\hat z^t - z^{t-1}\| \le q \operatorname{dist}(z^t, Z^\star)$.
--
--   The set of averaged output sequences of all such runs from $z^0$ is the base algorithm of Proposition 4.
--
--   **Formalization Note** The base algorithm is a map from starts to sets of sequences (`Runs`), because a primal-dual step is in general an argmin and need not be single-valued; Property 3 quantifies over every start in $Z$ and every admissible run, with $q$ and $C$ fixed first. The fixed-frequency run has $\tau^n = t^\star$ for every $n$: the inner loop of Algorithm 1 starts at $t = 0$, takes at least one step, and (29) first holds at $t = t^\star$. Property 1 is required for every $t \ge 0$, although the page's $\mathbb N$ starts at one: the proof of Proposition 2 (ii) telescopes from $z^0$. "The algorithm stays in $Z$" is implicit on the page and stated here.
-- source:
--   Applegate, Hinder, Lu & Lubin, Faster First-Order Primal-Dual Methods for Linear Programming using Restarts and Sharpness, arXiv:2105.12715v4, pp. 6–10, 15–16, (6), Property 1 (12), Property 2, Property 3, Algorithm 1, (29)

import Mathlib
import Definitions.Def_RestartPD_Fixed_Problem

namespace RestartPD.Fixed

variable {n m : ℕ}

/-- Property 3 (pp. 9–10) of a primal-dual algorithm with constants `q, C > 0`. `Runs z0` is the set
of admissible output sequences `{z̄ᵗ}` started at `z⁰` (only `t ≥ 1` is used): for every `z⁰ ∈ Z`,
every run and every `t ≥ 1`, `z̄ᵗ ∈ Z`, (i) `ρ_{‖z̄ᵗ − z⁰‖}(z̄ᵗ) ≤ 2C‖z̄ᵗ − z⁰‖/t` and
(ii) `‖z̄ᵗ − z⁰‖ ≤ (q + 2) dist(z⁰, Z⋆)`. -/
def Property3 (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (Runs : E n m → Set (ℕ → E n m)) (q C : ℝ) : Prop :=
  0 < q ∧ 0 < C ∧
    ∀ z0 ∈ X ×ˢ Y, ∀ zb ∈ Runs z0, ∀ t : ℕ, 1 ≤ t →
      zb t ∈ X ×ˢ Y ∧
      rho L X Y p (p (zb t - z0)) (zb t) ≤ ((2 * C * p (zb t - z0) / t : ℝ) : EReal) ∧
      p (zb t - z0) ≤ (q + 2) * distZ L X Y p z0

/-- Algorithm 1 with the fixed-frequency restart rule (29): restart every `tstar` inner steps.
`z n = z^{n,0}`, `zb n t = z̄^{n,t}`; each inner loop is a run of the base algorithm from `z^{n,0}`,
and `z^{n+1,0} = z̄^{n,t⋆}` (line 10, with `τⁿ = t⋆`). -/
def IsFixedRestartRun (Runs : E n m → Set (ℕ → E n m)) (tstar : ℕ) (z : ℕ → E n m)
    (zb : ℕ → ℕ → E n m) : Prop :=
  ∀ k : ℕ, zb k ∈ Runs (z k) ∧ z (k + 1) = zb k tstar

/-- The average target solution `z̄ᵗ = (1/t) Σ_{i=1}^t ẑⁱ` of the generic algorithm (6). -/
noncomputable def zbar (zh : ℕ → E n m) (t : ℕ) : E n m :=
  ((t : ℝ)⁻¹) • ∑ i ∈ Finset.Icc 1 t, zh i

/-- The iterates `zᵗ` (`t ≥ 0`) and targets `ẑᵗ` (`t ≥ 1`) of (6) stay in `Z`. -/
def StaysIn (X : Set (Primal n)) (Y : Set (Dual m)) (zs zh : ℕ → E n m) : Prop :=
  (∀ t : ℕ, zs t ∈ X ×ˢ Y) ∧ ∀ t : ℕ, 1 ≤ t → zh t ∈ X ×ˢ Y

/-- Property 1 (p. 7), (12), with constant `C > 0`, for every `t ≥ 0` and `z ∈ Z`:
`L(x̂^{t+1}, y) − L(x, ŷ^{t+1}) ≤ (C/2)‖z − zᵗ‖² − (C/2)‖z − z^{t+1}‖²`. -/
def IsProperty1 (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (zs zh : ℕ → E n m) (C : ℝ) : Prop :=
  0 < C ∧
    ∀ t : ℕ, ∀ z ∈ X ×ˢ Y,
      L (zh (t + 1)).1 z.2 - L z.1 (zh (t + 1)).2 ≤
        C / 2 * p (z - zs t) ^ 2 - C / 2 * p (z - zs (t + 1)) ^ 2

/-- Property 2 (p. 9) with constant `q > 0`, for every `t ≥ 1`: `‖ẑᵗ − zᵗ‖ ≤ q dist(zᵗ, Z⋆)` or
`‖ẑᵗ − z^{t−1}‖ ≤ q dist(zᵗ, Z⋆)`. -/
def IsProperty2 (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (zs zh : ℕ → E n m) (q : ℝ) : Prop :=
  0 < q ∧
    ∀ t : ℕ, 1 ≤ t →
      p (zh t - zs t) ≤ q * distZ L X Y p (zs t) ∨
        p (zh t - zs (t - 1)) ≤ q * distZ L X Y p (zs t)

/-- The averaged output sequences `{z̄ᵗ}` of every run of a generic primal-dual algorithm (6) from
`z⁰` that stays in `Z` and satisfies Property 1 with `C` and Property 2 with `q`. -/
def PDRuns (L : Primal n → Dual m → ℝ) (X : Set (Primal n)) (Y : Set (Dual m))
    (p : Seminorm ℝ (E n m)) (C q : ℝ) (z0 : E n m) : Set (ℕ → E n m) :=
  {zb | ∃ zs zh : ℕ → E n m, zs 0 = z0 ∧ StaysIn X Y zs zh ∧ IsProperty1 L X Y p zs zh C ∧
    IsProperty2 L X Y p zs zh q ∧ zb = zbar zh}

end RestartPD.Fixed


