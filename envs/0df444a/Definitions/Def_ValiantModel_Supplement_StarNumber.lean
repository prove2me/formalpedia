-- Prove2me | Definitions.Def_ValiantModel_Supplement_StarNumber
-- name    : ValiantModel_Supplement_StarNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:35.239377+00:00
-- url     : https://prove2.me/theorems/e8ee7777-cf37-4bbf-99dd-0b372815a58f
-- title:
--   Definitions 10 and 11 — star number $s_h(H)$, 1-centered star number $s_1(H)$, star sets
-- statement:
--   Let $H\subseteq\{0,1\}^X$ and let $h:X\to\{0,1\}$ be any function, not necessarily in $H$. A set $T\subseteq X$ is a **star set centered at $h$** for $H$ if
--
--   1. some $h_0\in H$ agrees with $h$ on every point of $T$, and
--   2. for every $x\in T$ some $h_x\in H$ disagrees with $h$ at $x$ and agrees with $h$ on $T\setminus\{x\}$.
--
--   The **star number** $s_h(H)$ is the largest size of such a set, and $s_h(H)=\infty$ if there is no largest. For the constant-one function $\mathbf 1$, a star set centered at $\mathbf 1$ is a **1-star**, and $s_1(H):=s_{\mathbf 1}(H)$ is the **1-centered star number**. "$X$ is a 1-star for $H$" means: $\mathbf 1\in H$, and for every $x\in X$ the function equal to $0$ exactly at $x$ belongs to $H$.
--
--   The 1-centered star number controls positive-only learnability, and Theorem 5.2 relates it to Valiant's model over a general domain.
--
--   **Formalization Note** Values are in $\mathbb N\cup\{\infty\}$: the supremum of the cardinalities of all star sets. Points of a star set with at least two points are necessarily distinct, so a set loses nothing against the page's list $x_1,\dots,x_k$. For $H=\emptyset$ there is no star set and the value is $0$; the page's "largest $k$" is then undefined.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), Definitions 10 and 11, p.16 (PDF p.18); 1-star usage pp.31–36 (PDF pp.33–38)

import Mathlib

namespace ValiantModel.Supplement

/-- A **star set** centered at `h` for `H` (Definition 10, Hanneke, Mehrotra, Velegkas, Zampetakis,
arXiv:2605.13840, version held, sha256 f793f255…, p.16, PDF p.18): some `h₀ ∈ H` agrees with `h` on
`T`, and for each `x ∈ T` some `hₓ ∈ H` disagrees with `h` at `x` and agrees with it on `T ∖ {x}`. With
`h` the constant-one function this is a **1-star** (1-centered star set, pp.31–36); "`X` is a 1-star
for `H`" (Theorem 5.2(2)) is `IsStarSet H (fun _ => true) Set.univ`. `h` need not be in `H`. -/
def IsStarSet {X : Type} (H : Set (X → Bool)) (h : X → Bool) (T : Set X) : Prop :=
  (∃ h₀ ∈ H, ∀ x ∈ T, h₀ x = h x) ∧
    ∀ x ∈ T, ∃ hx ∈ H, hx x = !h x ∧ ∀ y ∈ T, y ≠ x → hx y = h y

/-- **Definition 10 (Star Number)**, arXiv:2605.13840 (version held), p.16 (PDF p.18): `s_h(H)`, the
largest size of a star set centered at `h`, and `∞` if there is no largest.

**Formalization Note.** Valued in `ℕ∞` as a supremum of `encard` over all star sets. Subsets of a star
set are star sets, so an infinite star set gives `⊤`, as do arbitrarily large finite ones, which is
the page's "`∞` if no such finite `k` exists". The points of a star set of size `≥ 2` are necessarily
distinct, so sets lose nothing against the page's lists `x₁, …, x_k`. For `H = ∅` there is no star set
and the value is `0`. -/
noncomputable def starNumber {X : Type} (H : Set (X → Bool)) (h : X → Bool) : ℕ∞ :=
  ⨆ T : {T : Set X // IsStarSet H h T}, T.1.encard

/-- **Definition 11 (1-Centered Star Number)**, arXiv:2605.13840 (version held), p.16 (PDF p.18):
`s₁(H) = s_𝟙(H)` for the constant-one function `𝟙`. -/
noncomputable def oneStarNumber {X : Type} (H : Set (X → Bool)) : ℕ∞ :=
  starNumber H (fun _ => true)

end ValiantModel.Supplement


