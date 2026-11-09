-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_BlockMaps
-- name    : RamseyDisambig_Spherical_BlockMaps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:21:49.765549+00:00
-- url     : https://prove2.me/theorems/2ccf3935-2a2e-4008-be01-00dcf8c6b8ff
-- title:
--   Group block maps and the dense block property
-- statement:
--   Let a group $G$ act on a set $X$. A $G$-block map $\varphi:X^m\to X^n$ of block size $k$ has pairwise disjoint coordinate blocks $I_j\subseteq\{0,\ldots,n-1\}$ of size $k$, group labels $\gamma_\ell$ on active coordinates and fixed letters $z_\ell$ on inactive coordinates, with
--   $$\varphi(x)_\ell=\gamma_\ell\cdot x_j\quad(\ell\in I_j),\qquad\varphi(x)_\ell=z_\ell\quad(\ell\notin\bigcup_j I_j).$$
--   The dense block property says that for all positive integers $r,m$ and $0<\eta<1$ there are positive integers $n,k$ with
--   $$mk\ge(1-\eta)n$$
--   such that every coloring $c:X^n\to\{0,\ldots,r-1\}$ admits such a block map satisfying
--   $$[\forall j,\ \exists g_j\in G,\ y_j=g_j\cdot x_j]\ \Longrightarrow\ c(\varphi(x))=c(\varphi(y)).$$
--   The integers $n,k$ are chosen before the coloring. This is the conclusion required by the cited Dense Block theorem.
--
--   **Formalization Note** Positive integers implement the recorded non-vacuous reading of the paper's $\mathbb N$. Fixed letters are indexed only by inactive coordinates, so empty finite action sets remain admissible. Group labels are total on coordinates, which adds no restriction since a group has an identity. The property itself is defined for arbitrary actions; Theorem 11 supplies the finite and solvable assumptions.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), §2.2, p. 11 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Mathlib

set_option autoImplicit false

namespace RamseyDisambig.Spherical

/-- A block map with disjoint equal-sized blocks (p. 11). Fixed letters exist only
on inactive coordinates, so this definition also accommodates empty action sets. -/
def IsBlockMap (G X : Type*) [Group G] [MulAction G X] (m n k : ℕ)
    (φ : (Fin m → X) → (Fin n → X)) : Prop :=
  ∃ I : Fin m → Finset (Fin n),
    (∀ i j, i ≠ j → Disjoint (I i) (I j)) ∧
    (∀ i, (I i).card = k) ∧
    ∃ (γ : Fin n → G) (z : {ℓ : Fin n // ∀ j, ℓ ∉ I j} → X),
      (∀ x j ℓ, ℓ ∈ I j → φ x ℓ = γ ℓ • x j) ∧
      (∀ x ℓ (h : ∀ j, ℓ ∉ I j), φ x ℓ = z ⟨ℓ, h⟩)

/-- Dense blocks and coordinatewise orbit dependence; n,k are uniform over colorings.
Positive integers implement the non-vacuous reading recorded for this paper. -/
def DenseBlockProperty (G X : Type*) [Group G] [MulAction G X] : Prop :=
  ∀ (r m : ℕ), 1 ≤ r → 1 ≤ m → ∀ η : ℝ, 0 < η → η < 1 →
    ∃ (n k : ℕ), 1 ≤ n ∧ 1 ≤ k ∧
      (1 - η) * (n : ℝ) ≤ (m : ℝ) * (k : ℝ) ∧
      ∀ c : (Fin n → X) → Fin r,
        ∃ φ : (Fin m → X) → (Fin n → X), IsBlockMap G X m n k φ ∧
          ∀ x y, (∀ j, ∃ g : G, y j = g • x j) → c (φ x) = c (φ y)

end RamseyDisambig.Spherical


