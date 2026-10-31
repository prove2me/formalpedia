-- Prove2me | Definitions.Def_PersuasionNetworks_StepPayoff
-- name    : PersuasionNetworks_StepPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:18.229991+00:00
-- url     : https://prove2.me/theorems/04416593-cb61-4c5e-86e5-c46d43f7fe06
-- title:
--   Assumption 1: the increasing step payoff $\nu$
-- statement:
--   This item formalizes Assumption 1. There are an index set $\{1,\dots,K\}$ with $K\ge1$, cutoffs $(b_k)_{k=0}^{K}$ and values $(r_k)_{k=1}^{K}$ such that:
--
--   1. $b_k\in\mathbb R$ for $k=1,\dots,K-1$;
--   2. $r_k\ge r_\ell$ and $b_k>b_\ell$ whenever $\ell>k$;
--   3. $b_K=\inf\mathcal T$ and $b_1<b_0=\sup\mathcal T$, as extended reals.
--
--   The designer's payoff at posterior mean $x$ is
--   $$
--   \nu(x)=r_k\quad\text{for }x\in[b_k,b_{k-1}),\qquad \nu(b_0)=r_1 .
--   $$
--
--   Ties among the $r_k$ are allowed (footnote 13), and the $r_k$ may be negative. This step structure is what the paper's network game produces, the steps being the cores of the network, and it is the class of payoffs for which the main results hold.
--
--   **Formalization Note** Outside $\mathcal T$, where Assumption 1 leaves $\nu$ undefined, the definition returns the junk value $0$. Posterior means lie in $\mathcal T$ almost surely, so this value plays no role.
-- source:
--   Candogan, Persuasion in Networks: Public Signals and Cores, SSRN 3346144 (preprint), https://ssrn.com/abstract=3346144, Assumption 1 and footnotes 13, 14, p.14

import Mathlib

namespace PersuasionNetworks

/-- `x ∈ [b_k, b_{k-1})`, the band of level `k`, with the end points compared in `EReal`.
Candogan, SSRN 3346144 (preprint), Assumption 1, p.14.

**Formalization Note.** Only comparisons are used; `b_K = -∞` and `b_0 = +∞` are allowed. The index
`k` is `1`-based, so `k - 1` is an honest predecessor wherever this is used (`k ∈ Finset.Icc 1 K`). -/
def InBand (b : ℕ → EReal) (k : ℕ) (x : ℝ) : Prop :=
  b k ≤ (x : EReal) ∧ (x : EReal) < b (k - 1)

open scoped Classical in
/-- The **designer's payoff function** `ν`: `ν(x) = r_k` for `x ∈ [b_k, b_{k-1})`, and `ν(b_0) = r_1`
(footnote 14). Candogan, SSRN 3346144 (preprint), Assumption 1(2) and footnote 14, p.14.

**Formalization Note.** On `x < b_K` and `x > b_0`, outside `𝒯`, Assumption 1 leaves `ν` undefined,
and the sum below takes the junk value `0`. Posterior means lie in `𝒯` almost surely, so this value
is never seen. The sum has at most one nonzero term, because the bands are pairwise disjoint under
`IsStepPayoff`. -/
noncomputable def nu (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ) (x : ℝ) : ℝ :=
  if (x : EReal) = b 0 then r 1
  else ∑ k ∈ Finset.Icc 1 K, if InBand b k x then r k else 0

/-- **Assumption 1**, part 1: the parameters `(b_k)` and `(r_k)` of an increasing step function on
the state space `𝒯`. Candogan, SSRN 3346144 (preprint), Assumption 1, p.14.

* `K ≥ 1`, and the index set is `{1, …, K}`;
* `b_k` is a real number for `k = 1, …, K - 1` (the `r_k` are real by type);
* `r_k ≥ r_ℓ` and `b_k > b_ℓ` for `ℓ > k` in `{1, …, K}`: ties among the `r_k` are allowed
  (footnote 13);
* `b_K = inf 𝒯` and `b_1 < b_0 = sup 𝒯`, in `EReal`.

**Formalization Note.** `b` and `r` are functions on `ℕ`, of which only `{0, …, K}` and `{1, …, K}`
are used. `r` may be negative and `K = 1` is allowed. -/
structure IsStepPayoff (𝒯 : Set ℝ) (K : ℕ) (b : ℕ → EReal) (r : ℕ → ℝ) : Prop where
  one_le : 1 ≤ K
  b_ne_bot : ∀ k, 1 ≤ k → k < K → b k ≠ ⊥
  b_ne_top : ∀ k, 1 ≤ k → k < K → b k ≠ ⊤
  r_antitone : ∀ k ∈ Finset.Icc 1 K, ∀ ℓ ∈ Finset.Icc 1 K, k < ℓ → r ℓ ≤ r k
  b_strictAnti : ∀ k ∈ Finset.Icc 1 K, ∀ ℓ ∈ Finset.Icc 1 K, k < ℓ → b ℓ < b k
  b_last : b K = sInf ((fun t : ℝ => (t : EReal)) '' 𝒯)
  b_zero : b 0 = sSup ((fun t : ℝ => (t : EReal)) '' 𝒯)
  b_one_lt : b 1 < b 0

end PersuasionNetworks


