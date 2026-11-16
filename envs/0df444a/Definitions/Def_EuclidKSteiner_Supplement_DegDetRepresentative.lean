-- Prove2me | Definitions.Def_EuclidKSteiner_Supplement_DegDetRepresentative
-- name    : EuclidKSteiner_Supplement_DegDetRepresentative
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:57:09.305944+00:00
-- url     : https://prove2.me/theorems/b51595f6-d2af-49d4-9ab6-30ae7660addc
-- title:
--   Representative subfamilies for $\Psi(C)=\deg\det X_C$ with $\deg 0=-\infty$ (Definition 2.1 for polynomial matrices)
-- statement:
--   Let $X$ be an $r\times n$ matrix over $\mathbb Q[t]$ whose columns are indexed by $U=\{0,\dots,n-1\}$. For an $r$-element set $C\subseteq U$, let $X_C$ be the $r\times r$ submatrix of the columns in $C$, in increasing order, and set
--   $$\Psi(C)=\deg\det X_C,\qquad \deg 0=-\infty.$$
--
--   Let $\mathcal A$ be a weighted family of $p$-element subsets of $U$ with rational costs. A subfamily $\widehat{\mathcal A}\subseteq\mathcal A$ is **representative for $\Psi$** if for every $B\subseteq U$ with $|B|=r-p$,
--   $$\max_{(A,w)\in\widehat{\mathcal A},\,A\cap B=\emptyset}\bigl(\Psi(A\cup B)-w\bigr)=\max_{(A,w)\in\mathcal A,\,A\cap B=\emptyset}\bigl(\Psi(A\cup B)-w\bigr),$$
--   where an empty maximum is $-\infty$ and $-\infty-w=-\infty$. Equivalently: whenever $(A,w)\in\mathcal A$, $A\cap B=\emptyset$ and $\det X_{A\cup B}\neq0$, some $(A',w')\in\widehat{\mathcal A}$ has $A'\cap B=\emptyset$, $\det X_{A'\cup B}\ne0$ and $\deg\det X_{A\cup B}-w\le\deg\det X_{A'\cup B}-w'$.
--
--   This is the notion of Theorem 6.7, the general algebraic construction behind Theorem 3.9.
--
--   **Formalization Note** The published `EuclidKSteiner.Representative` takes a real-valued $\Psi$ and cannot express $-\infty$; this definition states (2.2) in the equivalent "every finite score is matched" form. The column order does not affect the degree (a reordering changes the determinant by a sign). `colDet` returns $0$ for sets of size other than $r$, a value never used.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Definition 2.1, (2.2), p.5 (PDF p.7); §6.2, p.27 (PDF p.29); Theorem 6.7, p.30 (PDF p.32)

import Mathlib

set_option autoImplicit false

namespace EuclidKSteiner

namespace Supplement

open Classical

/-!
# Determinant-degree values Ψ(C) = deg det X_C and representative subfamilies for them

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), Definition 2.1, (2.2), p.5 (PDF p.7):
"A subfamily Â ⊆ 𝒜 is representative for Ψ if, for every B ⊆ U with |B| = r − p,
max_{(A,w)∈Â, A∩B=∅} (Ψ(A ∪ B) − w) = max_{(A,w)∈𝒜, A∩B=∅} (Ψ(A ∪ B) − w). An empty maximum is −∞,
and −∞ − w = −∞." §6.2, p.27 (PDF p.29): "For A ⊆ U, write X_A for its columns in a fixed
ground-set order. For |A| = r, define Ψ(A) = deg det X_A. Thus Ψ(A) = −∞ when those columns are
dependent." Theorem 6.7, p.30 (PDF p.32).

**Formalization Note**
* The ground set is `U = Fin n`, ordered as `0 < 1 < … < n − 1`; `X_C` takes the columns of `C` in
  that order (`Finset.orderEmbOfFin`). Reordering changes the determinant only by a sign, so the
  degree does not depend on the order.
* `Ψ(C) = deg det X_C` takes the value `−∞` when `det X_C = 0`. The published real-valued
  `EuclidKSteiner.Representative` cannot express `−∞`, so this module states (2.2) directly: a
  completion `B` of a pair `(A, w)` contributes a finite score `natDegree (det X_{A∪B}) − w` exactly
  when `A ∩ B = ∅` and `det X_{A∪B} ≠ 0`; otherwise its score is `−∞`. Given `Â ⊆ 𝒜`, the left maximum
  of (2.2) is at most the right one, so (2.2) says: every finite score of `𝒜` is matched or beaten by
  a finite score of `Â`. Costs are rational.
-/

/-- `det X_C` for an `r`-element column set `C` (columns in increasing order), and `0` for a set of
another size (a value never used: every use has `|C| = r`). -/
noncomputable def colDet {R : Type*} [CommRing R] {r n : ℕ} (X : Matrix (Fin r) (Fin n) R)
    (C : Finset (Fin n)) : R :=
  if h : C.card = r then (X.submatrix id (fun i => C.orderEmbOfFin h i)).det else 0

/-- **Definition 2.1 for `Ψ(C) = deg det X_C`** (with `deg 0 = −∞`). `Â` is a representative
subfamily of the weighted family `𝒜` of `p`-element subsets of `U = Fin n` with rational costs, for
completed size `r`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, Definition 2.1, (2.2), p.5 (PDF p.7); Theorem 6.7, p.30
(PDF p.32). -/
def DegDetRepresentative {r n : ℕ} (X : Matrix (Fin r) (Fin n) (Polynomial ℚ)) (p : ℕ)
    (𝒜 Â : Set (Finset (Fin n) × ℚ)) : Prop :=
  Â ⊆ 𝒜 ∧ ∀ B : Finset (Fin n), B.card = r - p → ∀ x ∈ 𝒜, Disjoint x.1 B →
    colDet X (x.1 ∪ B) ≠ 0 →
    ∃ y ∈ Â, Disjoint y.1 B ∧ colDet X (y.1 ∪ B) ≠ 0 ∧
      ((colDet X (x.1 ∪ B)).natDegree : ℚ) - x.2 ≤ ((colDet X (y.1 ∪ B)).natDegree : ℚ) - y.2

/-- The weighted family listed by `fam` (rational costs): the pairs `(A, w)` with `A` the set of
listed elements. -/
def famSetQ {n : ℕ} (fam : List (List (Fin n) × ℚ)) : Set (Finset (Fin n) × ℚ) :=
  {x | ∃ a ∈ fam, x = (a.1.toFinset, a.2)}

end Supplement

end EuclidKSteiner


