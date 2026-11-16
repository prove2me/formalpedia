-- Prove2me | Definitions.Def_PerturbedWF_Supplement_Matching
-- name    : PerturbedWF_Supplement_Matching
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:06:01.061208+00:00
-- url     : https://prove2.me/theorems/6e0939c9-74b2-425b-b7a1-622b904d5b51
-- title:
--   Metric bipartite matching with requests at the server locations: work function and the algorithm of §7.1
-- statement:
--   In the reduced model of §7 the points $[n]$ are the initial server locations: the initial configuration $X_0\in\mathcal C=\{x\in\mathbb Z^n_{\ge0}:\sum_i x_i=k\}$ has $X_{0,i}\ge1$ for every $i$. Exactly $k$ requests $r_1,\ldots,r_k\in[n]$ arrive; $R_t=\sum_{i\le t}e_{r_i}$ counts the requests received so far. The **work function** is
--   $$W_t(x)=\begin{cases}\|X_0-x\| & \text{if } x\ge R_t,\\ \infty & \text{otherwise,}\end{cases}$$
--   and $\mathrm{OPT}=\min_{x\in\mathcal C}W_k(x)$ is the minimum matching cost.
--
--   The **algorithm of §7.1** takes vectors $A_i\in\mathbb R^m$, samples $q$ uniformly from $[-1,1]^m$, sets $v=Aq$, and at each $t\in[k]$ computes
--   $$X_t\in\arg\max_{x\in\mathcal C}\big\{\langle v,x\rangle-W_t(x)\big\}\qquad(7.2)$$
--   with $X_t=X_{t-1}-e_{i_t}+e_{r_t}$ for some $i_t\in[n]$, and matches $r_t$ to a server at $i_t$, at cost $d(i_t,r_t)$.
--
--   **Formalization Note** $W_t$ takes values in the extended reals, with $\infty$ as $\top$. OPT is the real minimum of $\|X_0-x\|$ over the finite nonempty set $\{x\in\mathcal C: x\ge R_k\}$. A run (`IsMatchRun`) records $X_t$ and $i_t$ for every $q$ in the cube and allows every such selection.
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §7 'Reduction' (after Lemma 7.1), 'Configurations', 'Work function', pp.18–19 (PDF pp.19–20); §7.1 'Algorithm', eq. (7.2), p.19 (PDF p.20)

import Mathlib
import Definitions.Def_PerturbedWF_Algorithm

namespace PerturbedWF.Supplement

/-!
# Metric bipartite matching with requests at the server locations (§7)

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), §7, pp.18–19 (PDF pp.19–20): the reduced model after
Lemma 7.1, "Configurations", "Work function", and §7.1 "Algorithm", eq. (7.2).

The points `[n]` are the initial server locations, so the initial configuration `X₀ ∈ kConfig ι k`
has `X₀,i ≥ 1` for every `i`; exactly `k` requests `r_1, …, r_k ∈ [n]` arrive.
`R_t = ∑_{i ≤ t} e_{r_i}`. The work function is `W_t(x) = ‖X₀ − x‖` if `x ≥ R_t` and `∞` otherwise.
At each `t ∈ [k]` the algorithm computes `X_t ∈ argmax_{x ∈ C} {⟨v, x⟩ − W_t(x)}` (7.2) with
`X_t = X_{t−1} − e_{i_t} + e_{r_t}` and matches `r_t` to the server at `i_t`, at cost `d(i_t, r_t)`.

**Formalization Note.**
* `reqCount r t` is `R_t`; `r : ℕ → ι` is used at times `1, …, k` (index `0` unused).
* `mbWork` takes values in `EReal` (`⊤` is the paper's `∞`); `mbOPT = min_{x ∈ C} W_k(x)` is the
  real infimum of `‖X₀ − x‖` over the finite nonempty set `{x ∈ C : x ≥ R_k}` (where `W_k` is
  finite; `R_k` itself belongs to it).
* `IsMatchRun d k X₀ r A X I`: `X_0 = X₀`, and for `1 ≤ t ≤ k` and every `q` in the cube,
  `X_t(q) ∈ C` maximizes `⟨Aq, x⟩ − W_t(x)` over `C` (in `EReal`) and
  `X_t(q) = X_{t−1}(q) − e_{I_t(q)} + e_{r_t}`; `I_t(q)` is the matched server location `i_t`.
  Every such selection is allowed (no tie-breaking, no measurability).
-/

/-- `R_t = ∑_{i=1}^t e_{r_i}`, the multiset of requests received up to time `t`. -/
def reqCount {ι : Type} [DecidableEq ι] (r : ℕ → ι) (t : ℕ) : ι → ℝ :=
  ∑ i ∈ Finset.Icc 1 t, Pi.single (r i) (1 : ℝ)

/-- The matching work function: `W_t(x) = ‖X₀ − x‖` if `x ≥ R_t`, `∞` otherwise. -/
noncomputable def mbWork {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (X₀ : ι → ℝ) (r : ℕ → ι) (t : ℕ) (x : ι → ℝ) : EReal :=
  if ∀ i, reqCount r t i ≤ x i then ((transNorm d (X₀ - x) : ℝ) : EReal) else ⊤

/-- The optimal matching cost `OPT = min_{x ∈ C} W_k(x)`. -/
noncomputable def mbOPT {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (k : ℕ)
    (X₀ : ι → ℝ) (r : ℕ → ι) : ℝ :=
  ⨅ x : {x : ι → ℝ // x ∈ kConfig ι k ∧ ∀ i, reqCount r k i ≤ x i}, transNorm d (X₀ - x)

/-- `(X, I)` is a run of the matching algorithm of §7.1 with vectors `A`. -/
def IsMatchRun {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} (d : ι → ι → ℝ) (k : ℕ)
    (X₀ : ι → ℝ) (r : ℕ → ι) (A : ι → Fin m → ℝ) (X : ℕ → (Fin m → ℝ) → (ι → ℝ))
    (I : ℕ → (Fin m → ℝ) → ι) : Prop :=
  (∀ q, X 0 q = X₀) ∧
    ∀ t ∈ Finset.Icc 1 k, ∀ q ∈ Set.Icc (-1 : Fin m → ℝ) 1,
      X t q ∈ kConfig ι k ∧
      (∀ y ∈ kConfig ι k, ((dot (matVec A q) y : ℝ) : EReal) - mbWork d X₀ r t y ≤
        ((dot (matVec A q) (X t q) : ℝ) : EReal) - mbWork d X₀ r t (X t q)) ∧
      X t q = X (t - 1) q - Pi.single (I t q) (1 : ℝ) + Pi.single (r t) (1 : ℝ)

end PerturbedWF.Supplement


