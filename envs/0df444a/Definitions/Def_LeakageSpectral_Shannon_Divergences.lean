-- Prove2me | Definitions.Def_LeakageSpectral_Shannon_Divergences
-- name    : LeakageSpectral_Shannon_Divergences
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:38.468087+00:00
-- url     : https://prove2.me/theorems/66fade39-4a81-4152-b943-0f361fa0bb69
-- title:
--   Definition 2 and Lemma 3 — $\chi^2$-divergence, KL divergence in bits, Rényi entropy, collision probability
-- statement:
--   These are the quantities attached to discrete distributions. Let $p,q$ be mass functions on a discrete set $\mathcal X$. The **chi-square divergence** and the **Kullback–Leibler divergence in bits** are
--
--   $$
--   \chi^2(p\|q)=\sum_{x\in\mathcal X}\frac{(p(x)-q(x))^2}{q(x)},\qquad D_{\mathrm{KL}}(p\|q)=\sum_{x\in\mathcal X}p(x)\log_2\frac{p(x)}{q(x)} .
--   $$
--
--   For a mass function $q$ on a finite set, the **Rényi entropy of order $\alpha$** is
--
--   $$
--   H_\alpha(q)=\frac{1}{1-\alpha}\log_2\sum_w q(w)^\alpha\quad(\alpha\neq1),\qquad H_1(q)=-\sum_w q(w)\log_2 q(w).
--   $$
--
--   For mass functions $q_0,\dots,q_{n-1}$ on a finite set, the **collision probability** $\Pr[W_0=\dots=W_{n-1}]$ of independent $W_i\sim q_i$ is the total product mass $\prod_i q_i(W_i)$ of the tuples whose entries are all equal.
--
--   The first two compare a posterior with a prior throughout the mission. The last two express the spectral alignment factor of Theorem 1.
--
--   **Formalization Note** Mass functions are real-valued functions. A point with $q(x)=0=p(x)$ contributes $0$ to both sums, by Lean's conventions for $x/0$ and $\log 0$, which is the right value. Sums over $\mathcal X$ are `tsum`, so a non-summable family would give $0$; in every use the family is finite or the terms are bounded by a summable family.
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Definition 2, p. 7; Lemma 3 and its proof, p. 26; Theorem 1, p. 8

import Mathlib

namespace LeakageSpectral.Shannon

/-- **χ²-divergence** of discrete distributions `p`, `q` on `X`, given by their mass functions
(Ueno, STOC 2027 submission #326, Definition 2, p. 7):
`χ²(p ∥ q) = ∑ₓ (p x - q x)² / q x`.
A point with `q x = 0 = p x` contributes `0`, as it should. -/
noncomputable def chiSquareDiv {X : Type*} (p q : X → ℝ) : ℝ :=
  ∑' x, (p x - q x) ^ 2 / q x

/-- **Kullback–Leibler divergence in bits** of discrete distributions `p`, `q` on `X`, given by their
mass functions (Lemma 3 and its proof, p. 26): `D_KL(p ∥ q) = ∑ₓ p x · log₂ (p x / q x)`.
A point with `p x = 0` contributes `0`. -/
noncomputable def discreteKLBits {X : Type*} (p q : X → ℝ) : ℝ :=
  ∑' x, p x * Real.logb 2 (p x / q x)

/-- **Rényi entropy of order `α`, in bits**, of a mass function `q` on a finite type
(Theorem 1, p. 8): `H_α(q) = (1 / (1 - α)) log₂ ∑_w q(w)^α` for `α ≠ 1`, and the Shannon entropy
`-∑_w q(w) log₂ q(w)` at `α = 1`. -/
noncomputable def renyiEntropy {ι : Type*} [Fintype ι] (α : ℝ) (q : ι → ℝ) : ℝ :=
  open Classical in
  if α = 1 then -∑ w, q w * Real.logb 2 (q w)
  else (1 / (1 - α)) * Real.logb 2 (∑ w, q w ^ α)

/-- **Collision probability** `Pr[W₀ = W₁ = ⋯ = W_{n-1}]` of independent `W_i ∼ Q i` on a finite type
(Theorem 1, p. 8): the total product mass `∏ᵢ Q i (W i)` of the tuples `W` whose entries are all equal. -/
noncomputable def collisionProb {ι : Type*} [Fintype ι] {n : ℕ} (Q : Fin n → ι → ℝ) : ℝ :=
  open Classical in
  ∑ W ∈ Finset.univ.filter (fun W : Fin n → ι => ∀ i j, W i = W j), ∏ i, Q i (W i)

end LeakageSpectral.Shannon


