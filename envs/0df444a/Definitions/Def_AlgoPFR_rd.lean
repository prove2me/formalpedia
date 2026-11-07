-- Prove2me | Definitions.Def_AlgoPFR_rd
-- name    : AlgoPFR_rd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:40:54.081325+00:00
-- url     : https://prove2.me/theorems/5a19d559-29dd-49cb-9d48-4a7234635aab
-- title:
--   The entropic Ruzsa distance $d[X;Y]$ on $\mathbb F_2^n$
-- statement:
--   We work in $\mathbb F_2^n$, modelled as functions $\mathrm{Fin}\,n\to\mathbb Z/2$, and write laws as probability mass functions. Logarithms are base 2.
--
--   1. The **entropy** of a law $p$ on a finite type is $H[p]=\sum_x p(x)\log\frac1{p(x)}$, with $0\log\frac10=0$.
--   2. The **independent pair** law $p\otimes q$ and the **sum** law $p\oplus q$ are the laws of $(X,Y)$ and of $X+Y$ for independent $X\sim p$, $Y\sim q$.
--   3. The **entropic Ruzsa distance** is
--   $$d[X;Y]=H[X'+Y']-\tfrac12H[X']-\tfrac12H[Y'],$$
--   where $X',Y'$ are independent copies of $X,Y$. It depends only on the two laws.
--   4. $U_A$ is the uniform law on a nonempty finite set $A$, and $U_V$ the uniform law on a linear subspace $V$.
--
--   The distance $d$ is the quantity the whole mission decreases: it vanishes exactly on uniform laws of cosets, and small $d[X;U_H]$ says that $X$ is close to a subspace in the additive sense.
--
--   **Formalization Note** The space $\mathbb F_2^0$ is a single point. The uniform law on a subspace needs no nonemptiness hypothesis because a subspace contains $0$.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), §3, pp.13–15, Eqs. (1), (5)

import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace AlgoPFR

noncomputable section

/-- The ambient space `F₂ⁿ` of Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial
time*, arXiv:2609.20771 (sha256 60e45066…), §3, p.13: "All the random variables in this paper will
take values in F₂ⁿ".

**Formalization Note.** Vectors are functions `Fin n → ZMod 2`, so `n = 0` is the one-point space;
every statement of the mission is required to stay true there. -/
abbrev Vec (n : ℕ) := Fin n → ZMod 2

/-- Shannon entropy in **bits**, Eq. (1), p.13 of arXiv:2609.20771 (sha256 60e45066…):
`H[X] = ∑ₓ p_X(x) log (1 / p_X(x))`, with `log` base 2 ("All logarithms (denoted by log) are base
2", p.13).

**Formalization Note.** A law is a `PMF` on a finite type and its mass is read with `toReal`. The
convention `0 log (1/0) = 0` holds because `Real.logb 2 0 = 0`. -/
def entropy {α : Type} [Fintype α] (p : PMF α) : ℝ :=
  ∑ x, -(p x).toReal * Real.logb 2 (p x).toReal

/-- The law of the pair `(X, Y)` of **independent** random variables with laws `p` and `q`. -/
def pairLaw {α β : Type} (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind fun x => q.map fun y => (x, y)

/-- The law of `X + Y` for independent `X ∼ p`, `Y ∼ q` (written `p_{X+Y}` in arXiv:2609.20771,
sha256 60e45066…, Lemma 4.4, p.20): the convolution of `p` and `q`. -/
def sumLaw {n : ℕ} (p q : PMF (Vec n)) : PMF (Vec n) :=
  p.bind fun x => q.map fun y => x + y

/-- The **entropic Ruzsa distance**, Eq. (5), p.14 of arXiv:2609.20771 (sha256 60e45066…):
`d[X;Y] = H[X′ + Y′] − ½ H[X′] − ½ H[Y′]` for independent copies `X′, Y′` of `X, Y`. It depends only
on the two laws. -/
def rd {n : ℕ} (p q : PMF (Vec n)) : ℝ :=
  entropy (sumLaw p q) - entropy p / 2 - entropy q / 2

/-- The uniform law `U_A` on a nonempty finite set `A ⊆ F₂ⁿ` (arXiv:2609.20771, sha256 60e45066…,
§3, p.13). -/
def uniformLaw {n : ℕ} (A : Finset (Vec n)) (hA : A.Nonempty) : PMF (Vec n) :=
  PMF.uniformOfFinset A hA

/-- The uniform law `U_V` on a linear subspace `V ≤ F₂ⁿ` (arXiv:2609.20771, sha256 60e45066…, §3,
p.15). The carrier always contains `0`, so no nonemptiness hypothesis is needed. -/
def subspaceLaw {n : ℕ} (V : Submodule (ZMod 2) (Vec n)) : PMF (Vec n) :=
  PMF.uniformOfFinset (Set.toFinite (V : Set (Vec n))).toFinset ⟨0, by simp⟩

end

end AlgoPFR


