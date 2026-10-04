-- Prove2me | Definitions.Def_BartlettNN_Margin_Covering
-- name    : BartlettNN_Margin_Covering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:27:40.093607+00:00
-- url     : https://prove2.me/theorems/8e7b9c0e-8f3c-47f9-984a-c8c9cbf030ec
-- title:
--   Sample ℓ∞ pseudometric, covering numbers N∞(F, ε, m) (Definition 3) and packing numbers M∞(F, α, m)
-- statement:
--   For a sample $x=(x_1,\dots,x_m)\in X^m$, the pseudometric $d_{\ell_\infty(x)}$ on real functions on $X$ is
--   $$
--   d_{\ell_\infty(x)}(f,g)=\max_i |f(x_i)-g(x_i)| .
--   $$
--   **Definition 3.** In a pseudometric space $(S,\rho)$, a set $T\subseteq S$ is an **$\epsilon$-cover** of $A\subseteq S$ if for every $a\in A$ there is $t\in T$ with $\rho(t,a)<\epsilon$; $\mathcal N(A,\epsilon,\rho)$ is the size of the smallest $\epsilon$-cover of $A$. Here $S$ is the set of all real functions on $X$, and
--   $$
--   \mathcal N_\infty(A,\epsilon,m)=\max_{x\in X^m}\mathcal N(A,\epsilon,d_{\ell_\infty(x)}).
--   $$
--   The **packing number** $\mathcal M_\infty(F,\alpha,m)$ is the maximum over all $x\in X^m$ of the size of the largest subset of $F$ all of whose pairs of elements are $\alpha$-separated with respect to $d_{\ell_\infty(x)}$.
--
--   Covering numbers of the squashed class control the margin bound of Lemma 4; packing numbers relate covering numbers at two scales.
--
--   **Formalization Note** Covers are external (the centres are arbitrary real functions on $X$, not necessarily in $A$) and finite, the inequality is strict, and $\mathcal N$ is valued in `ℕ∞`, equal to $\infty$ (`⊤`) when no finite cover exists. $\mathcal N_\infty$ and $\mathcal M_\infty$ are suprema over all samples `Fin m → X` (repetitions allowed). The paper does not define "$\alpha$-separated"; it is read as $d_{\ell_\infty(x)}(f,g)\ge\alpha$ for distinct $f,g$. For $m=0$ the maximum over the empty index set is $0$.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), p. 527, Definition 3 and d_{ℓ∞(x)}; p. 528, proof of Theorem 2 (M∞)

import Mathlib

namespace BartlettNN.Margin

/-- The sample pseudometric `d_{ℓ∞(x)}(f, g) = max_i |f(x_i) − g(x_i)|` for a sample
`x ∈ X^m` (p. 527). For the empty sample (`m = 0`) its value is `0`. -/
noncomputable def dInf {X : Type*} {m : ℕ} (x : Fin m → X) (f g : X → ℝ) : ℝ :=
  ⨆ i, |f (x i) - g (x i)|

/-- The covering number `N(A, ε, ρ)` of Definition 3 (p. 527): the least size of a finite
`T ⊆ S` with `ρ(t, a) < ε` for some `t ∈ T`, for every `a ∈ A`. Here `S` is the space of all
real functions on `X`, so the cover need not lie in `A` (external cover), and the inequality is
strict. The value is `⊤` when no finite cover exists. -/
noncomputable def coverNum {X : Type*} (d : (X → ℝ) → (X → ℝ) → ℝ) (F : Set (X → ℝ)) (ε : ℝ) :
    ℕ∞ :=
  ⨅ (T : Finset (X → ℝ)) (_ : ∀ f ∈ F, ∃ g ∈ T, d g f < ε), (T.card : ℕ∞)

/-- `N∞(F, ε, m) = max_{x ∈ X^m} N(F, ε, d_{ℓ∞(x)})` (p. 527), the maximum over all samples of
length `m` (repetitions allowed), taken in `ℕ∞`. -/
noncomputable def Ninf {X : Type*} (F : Set (X → ℝ)) (ε : ℝ) (m : ℕ) : ℕ∞ :=
  ⨆ x : Fin m → X, coverNum (dInf x) F ε

/-- The packing number `M∞(F, α, m)` (proof of Theorem 2, p. 528): the maximum over all
`x ∈ X^m` of the size of the largest subset of `F` all of whose pairs of distinct elements are
`α`-separated with respect to `d_{ℓ∞(x)}`, read as `α ≤ d_{ℓ∞(x)}(f, g)`. Valued in `ℕ∞`. -/
noncomputable def Minf {X : Type*} (F : Set (X → ℝ)) (α : ℝ) (m : ℕ) : ℕ∞ :=
  ⨆ (x : Fin m → X) (S : Finset (X → ℝ)) (_ : (S : Set (X → ℝ)) ⊆ F)
    (_ : ∀ f ∈ S, ∀ g ∈ S, f ≠ g → α ≤ dInf x f g), (S.card : ℕ∞)

end BartlettNN.Margin


