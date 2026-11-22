-- Prove2me | Definitions.Def_SelfSelReg_Supplement_ObservableFamily
-- name    : SelfSelReg_Supplement_ObservableFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:14:43.781505+00:00
-- url     : https://prove2.me/theorems/43a8e280-8c85-4ac2-b555-be233dc6bc32
-- title:
--   Definition 6.4 — $\varepsilon_{\mathrm{fam}}$-approximate observable-operator family
-- statement:
--   Let $J$ be a finite index set with $p=|J|$ elements and let $(a_i)_{i\in J}$ be vectors of $\mathbb R^n$. Symmetric matrices $\widehat D_1,\dots,\widehat D_n\in\mathbb R^{p\times p}$ form an $\varepsilon_{\mathrm{fam}}$-approximate observable-operator family for $(a_i)_{i\in J}$ if there is an orthonormal basis $(z_i)_{i\in J}$ of $\mathbb R^{p}$ such that, for every $b\in\mathbb R^n$,
--
--   $$
--   \Bigl\|\sum_{\ell=1}^n b_\ell\widehat D_\ell-\sum_{i\in J}\langle b,a_i\rangle\,z_iz_i^\top\Bigr\|_F\le\varepsilon_{\mathrm{fam}}\,\|b\|_2 .
--   $$
--
--   The basis is chosen once and serves every $b$: every contraction $\sum_\ell b_\ell\widehat D_\ell$ is then close to a matrix with the same eigenvectors $z_i$ and eigenvalues $\langle b,a_i\rangle$, which is what lets an eigendecomposition read off the vectors $a_i$ coordinate by coordinate (Theorem 6.6).
--
--   **Formalization Note** $J$ is a finite subset of the index set $[k]$ of a family $a_1,\dots,a_k$. The conditions $J\ne\emptyset$ and $\varepsilon_{\mathrm{fam}}\ge0$ are stated by the theorems that use the definition.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Definition 6.4, Eq. (41), p.30 (PDF p.33)

import Mathlib
import Definitions.Def_SelfSelReg_Tensor

namespace SelfSelReg

namespace Supplement

/-- **Definition 6.4** (Approximate Observable-Operator Family).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Definition 6.4, p.30 (PDF p.33): "Fix a non-empty set J and vectors
(a_i)_{i∈J} in ℝⁿ. For ε_fam ≥ 0, we call symmetric matrices D̂_1, …, D̂_n ∈ ℝ^{|J|×|J|} an
ε_fam-approximate observable-operator family for (a_i)_{i∈J} if there is an orthonormal basis
(z_i)_{i∈J} of ℝ^{|J|} such that, for every b ∈ ℝⁿ,
‖Σ_ℓ b_ℓ D̂_ℓ − Σ_{i∈J} ⟨b, a_i⟩ z_i z_iᵀ‖_F ≤ ε_fam ‖b‖₂ (41)."

**Formalization Note.** `J` is a finite subset of the index type of the family `a`, with `|J| = p`.
The basis is an orthonormal family `z` indexed by the elements of `J`; having `|J| = p` members in
`ℝᵖ`, it is a basis. It is chosen once, before `b`. Symmetry of the `D̂_ℓ` is a clause of the
predicate; `J ≠ ∅` and `ε_fam ≥ 0` are left to the theorems. -/
def IsApproxObservableFamily {n k p : ℕ} (a : Fin k → EuclideanSpace ℝ (Fin n))
    (J : Finset (Fin k)) (_hcard : J.card = p)
    (D : Fin n → Matrix (Fin p) (Fin p) ℝ) (εfam : ℝ) : Prop :=
  (∀ l, (D l).IsHermitian) ∧
    ∃ z : {i : Fin k // i ∈ J} → EuclideanSpace ℝ (Fin p),
      (∀ i j, inner ℝ (z i) (z j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ b : EuclideanSpace ℝ (Fin n),
        matFrobNorm ((∑ l, b l • D l) -
          ∑ i : {i : Fin k // i ∈ J}, inner ℝ b (a i) • Matrix.vecMulVec (z i) (z i)) ≤ εfam * ‖b‖

end Supplement

end SelfSelReg


