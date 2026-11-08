-- Prove2me | Definitions.Def_AsymSpecConn_IsAGood
-- name    : AsymSpecConn_IsAGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:00.050958+00:00
-- url     : https://prove2.me/theorems/ce16b880-a728-4225-ad05-34b557b43dfd
-- title:
--   $\mathcal A$-good function
-- statement:
--   Let $\mathcal A\subseteq\mathcal S\setminus\{0\}$ be multiplicatively closed and contain every positive integer. A function $w:\mathcal A\to\mathbb R_{\ge0}$ is **$\mathcal A$-good** if:
--
--   1. $w(ab)=w(a)w(b)$ for all $a,b\in\mathcal A$;
--   2. $w(m)=m$ for every positive integer $m$;
--   3. for every $q\in\mathbb N$ and all $a,a_1,\dots,a_q\in\mathcal A$, if $a\le\sum_{j=1}^q a_j$ then $w(a)\le\sum_{j=1}^q w(a_j)$.
--
--   These are the conditions under which $w$ extends to a spectral point.
--
--   **Formalization Note** The source states this for $w:\mathcal A\to\mathbb R_{\ge0}$ and also applies it to functions on $\mathcal S$ through their restriction to $\mathcal A$ (p.14). Here $w:\mathcal S\to\mathbb R_{\ge0}$ and only its values on $\mathcal A$ are read. The standing assumptions on $\mathcal A$ are hypotheses of the theorems that use the predicate.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Definition 2.2, p.13

import Mathlib

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

/-- **A-good function** (Definition 2.2, p.13 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)).

`w` is A-good if
(a) `w(ab) = w(a) w(b)` for all `a, b ∈ A`;
(b) `w(m) = m` for every positive integer `m`;
(c) for every `q ∈ ℕ` and all `a, a₁, …, a_q ∈ A`, if `a ≤ a₁ + ⋯ + a_q` then
    `w(a) ≤ w(a₁) + ⋯ + w(a_q)`.

**Formalization Note** The paper states this for `w : A → ℝ≥0` and also applies it to functions
`S → ℝ≥0` through their restriction to `A` (p.14). Here `w : S → ℝ≥0` and only its values on
`A` are used; every `w : A → ℝ≥0` extends to `S`. The paper's standing assumptions on `A`
(`A ⊆ S \ {0}`, multiplicatively closed, containing the positive integers) are hypotheses of
the theorems that use this predicate. -/
def IsAGood {S : Type*} [CommSemiring S] (P : Preorder S) (A : Set S) (w : S → ℝ≥0) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, w (a * b) = w a * w b) ∧
  (∀ m : ℕ, 1 ≤ m → w (m : S) = (m : ℝ≥0)) ∧
  (∀ (q : ℕ) (a : S) (b : Fin q → S), a ∈ A → (∀ j, b j ∈ A) → P.le a (∑ j, b j) →
    w a ≤ ∑ j, w (b j))

end AsymSpecConn


