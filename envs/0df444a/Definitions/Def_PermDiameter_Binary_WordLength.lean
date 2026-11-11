-- Prove2me | Definitions.Def_PermDiameter_Binary_WordLength
-- name    : PermDiameter_Binary_WordLength
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:09:44.915297+00:00
-- url     : https://prove2.me/theorems/f45b4bdc-9433-4667-ba59-07a81c2e2dc5
-- title:
--   Word length $\ell(g,\Sigma)$, diameter $\operatorname{diam}(G,\Sigma)$, left and right transversals (Definition 2.1)
-- statement:
--   Let $M$ be a group (or monoid) and $\Sigma\subseteq M$. A **word** over $\Sigma$ is a finite sequence $w=a_1\cdots a_n$ of letters $a_i\in\Sigma$; its length is $|w|=n$ and it **represents** the product $a_1 a_2\cdots a_n$ (the empty word represents $1$). Only the elements of $\Sigma$ are letters: inverses of generators are not added. The **length** of $g$ and the **diameter** of a set $G$ with respect to $\Sigma$ are
--   $$\ell(g,\Sigma)=\min\{n\in\mathbb N: g=a_1\cdots a_n,\ a_i\in\Sigma\},\qquad \operatorname{diam}(G,\Sigma)=\max\{\ell(g,\Sigma): g\in G\}.$$
--   Both are valued in $\mathbb N\cup\{\infty\}$: $\ell(g,\Sigma)=\infty$ when no word over $\Sigma$ represents $g$ (in particular when $g\notin\langle\Sigma\rangle$), and the maximum is a supremum. For a finite group $G=\langle\Sigma\rangle$ these are the paper's length and diameter, i.e. distances from the identity and the diameter of the directed Cayley graph.
--
--   For subgroups $H\le K$, a **left transversal** of $H$ in $K$ is a set $T\subseteq K$ containing exactly one element of each left coset $gH$ ($g\in K$); a **right transversal** contains exactly one element of each right coset $Hg$.
--
--   These notions are used by every statement of the mission: the decision problems Binary Length and Binary Diameter, and the word-length estimates of the reduction in Section 3.
--
--   **Formalization Note.** `wordLength S g : ℕ∞` is the infimum of the lengths of lists of elements of `S` with product `g` (`⊤` when there is none), and `diamOn G S : ℕ∞` is `⨆ g ∈ G, wordLength S g`. `IsLeftTransversal T H K` says `T ⊆ K` and every `g ∈ K` has a unique `t ∈ T` with `t⁻¹ g ∈ H`; `IsRightTransversal` uses `g t⁻¹ ∈ H`.
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 9, Definition 2.1 and the paragraphs on cosets and generating sets

import Mathlib

namespace PermDiameter.Binary

/-!
# Length, diameter and transversals (Lohrey–Thumm, §2.2, p. 9, Definition 2.1)

A word `w = a₁ ⋯ aₙ` over a subset `S` of a monoid is a list of elements of `S`; it represents
its value `a₁ * ⋯ * aₙ` (`List.prod`, the empty word represents `1`). Only the elements of `S`
themselves are letters: inverses are not added.
-/

/-- The **length** `ℓ(g, S)` of `g` with respect to `S` (Definition 2.1): the least length of a
word over `S` whose value is `g`. It is `⊤` when no word over `S` represents `g` (for instance
when `g ∉ ⟨S⟩`), so no junk value occurs. -/
noncomputable def wordLength {M : Type} [Monoid M] (S : Set M) (g : M) : ℕ∞ :=
  ⨅ (w : List M) (_ : (∀ a ∈ w, a ∈ S) ∧ w.prod = g), (w.length : ℕ∞)

/-- The **diameter** `diam(G, S) = max {ℓ(g, S) : g ∈ G}` of a set `G` with respect to `S`
(Definition 2.1), as a supremum in `ℕ∞`. For a subgroup `G = ⟨S⟩` of a finite group this is
the paper's diameter. -/
noncomputable def diamOn {M : Type} [Monoid M] (G S : Set M) : ℕ∞ :=
  ⨆ g ∈ G, wordLength S g

/-- `T` is a **left transversal** of the subgroup `H` in the subgroup `K` (§2.2, p. 9): `T ⊆ K`
and every `g ∈ K` lies in exactly one left coset `tH` with `t ∈ T` (`g ∈ tH ↔ t⁻¹ * g ∈ H`).
Used with `H ≤ K`. -/
def IsLeftTransversal {G : Type} [Group G] (T : Set G) (H K : Subgroup G) : Prop :=
  T ⊆ K ∧ ∀ g ∈ K, ∃! t, t ∈ T ∧ t⁻¹ * g ∈ H

/-- `T` is a **right transversal** of `H` in `K`: `T ⊆ K` and every `g ∈ K` lies in exactly one
right coset `Ht` with `t ∈ T` (`g ∈ Ht ↔ g * t⁻¹ ∈ H`). Used with `H ≤ K`. -/
def IsRightTransversal {G : Type} [Group G] (T : Set G) (H K : Subgroup G) : Prop :=
  T ⊆ K ∧ ∀ g ∈ K, ∃! t, t ∈ T ∧ g * t⁻¹ ∈ H

end PermDiameter.Binary


