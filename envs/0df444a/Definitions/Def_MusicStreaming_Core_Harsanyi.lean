-- Prove2me | Definitions.Def_MusicStreaming_Core_Harsanyi
-- name    : MusicStreaming_Core_Harsanyi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:06:44.366363+00:00
-- url     : https://prove2.me/theorems/9be2fd51-cbb1-458e-8949-3c02ae57f06d
-- title:
--   Appendix, p. 22 — Harsanyi dividends $\Delta_v(R)$, sharing systems and the Harsanyi set $H(N,v)$
-- statement:
--   Let $N=\{1,\dots,n\}$ and let $v:2^N\to\mathbb R$ be a set function on coalitions.
--
--   1. The **Harsanyi dividend** of a coalition $R\subseteq N$ is
--   $$\Delta_v(R)=\sum_{S\subseteq R}(-1)^{|R|-|S|}\,v(S).$$
--   2. A **sharing system** is a family $p=(p^R)_{\emptyset\neq R\subseteq N}$ of vectors $p^R\in\mathbb R^N$ with $p^R_i\ge 0$ for $i\in R$, $p^R_i=0$ for $i\in N\setminus R$, and $\sum_{i\in N}p^R_i=1$: each $p^R$ is a way of splitting one unit among the members of $R$.
--   3. A sharing system $p$ induces the allocation
--   $$y^p_i=\sum_{\emptyset\neq R\subseteq N,\ i\in R}\Delta_v(R)\,p^R_i\qquad(i\in N),$$
--   which distributes the dividend of every coalition among its members according to $p$.
--   4. The **Harsanyi set** of $v$ (Vasil'ev 1978, 1981) is $H(N,v)=\{y^p: p\text{ is a sharing system}\}$.
--
--   These are the general game-theoretic objects through which the paper proves Theorem 2.
--
--   **Formalization Note** The paper defines the dividends as the unique weights $\Delta_v(R)$ with $v=\sum_{\emptyset\neq R\subseteq N}\Delta_v(R)\,u_R$ (Harsanyi 1959); the Lean definition is their explicit Möbius-inversion formula above, and the milestone *Harsanyi (1959)* states that this formula gives exactly those unique weights. The exponent $|R|-|S|$ is a natural-number subtraction, exact because $S\subseteq R$. A sharing system is a function `p : Finset (Fin n) → Fin n → ℝ` constrained only at nonempty coalitions; its value at $\emptyset$ is never used. The allocation sums over all nonempty $R$; the terms with $i\notin R$ vanish for a sharing system, so this is the paper's sum over $R\ni i$ (the page writes "$p_i=0$" for $p^R_i=0$).
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 22, Appendix, proof of Theorem 2 (dividends, sharing system, y^p, H(N, v)); Harsanyi (1959); Vasil'ev (1978, 1981)

import Mathlib

namespace MusicStreaming.Core

variable {n : ℕ}

/-- The Harsanyi dividend `Δ_v(R) = ∑_{S ⊆ R} (-1)^{|R| - |S|} v(S)` of a coalition `R` in the
game `v` (Harsanyi 1959; cited on p. 22). The paper defines the dividends as the unique weights
with `v = ∑_{∅ ≠ R ⊆ N} Δ_v(R) u_R`; this is their explicit (Möbius inversion) formula. The
exponent `R.card - S.card` is a natural-number subtraction, exact because `S ⊆ R`. -/
def dividend (v : Finset (Fin n) → ℝ) (R : Finset (Fin n)) : ℝ :=
  ∑ S ∈ R.powerset, (-1) ^ (R.card - S.card) * v S

/-- A sharing system (p. 22): for every nonempty coalition `R`, `p R` is a nonnegative vector,
zero outside `R`, with total `1`. The value `p ∅` is unconstrained and never used. -/
def IsSharingSystem (p : Finset (Fin n) → Fin n → ℝ) : Prop :=
  ∀ R : Finset (Fin n), R.Nonempty →
    (∀ i ∈ R, 0 ≤ p R i) ∧ (∀ i, i ∉ R → p R i = 0) ∧ ∑ i, p R i = 1

/-- The allocation `y^p_i = ∑_{R ∋ i} Δ_v(R) p^R_i` induced by a sharing system `p` (p. 22). The sum
runs over all nonempty `R`; the terms with `i ∉ R` vanish for a sharing system. -/
def sharingAlloc (v : Finset (Fin n) → ℝ) (p : Finset (Fin n) → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ R ∈ Finset.univ.powerset.filter (fun R => R.Nonempty), dividend v R * p R i

/-- The Harsanyi set `H(N, v) = {y^p : p is a sharing system}` (Vasil'ev 1978, 1981; p. 22). -/
def harsanyiSet (v : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {y | ∃ p : Finset (Fin n) → Fin n → ℝ, IsSharingSystem p ∧ y = sharingAlloc v p}

end MusicStreaming.Core


