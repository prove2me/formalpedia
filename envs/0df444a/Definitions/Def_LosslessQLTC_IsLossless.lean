-- Prove2me | Definitions.Def_LosslessQLTC_IsLossless
-- name    : LosslessQLTC_IsLossless
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:19:45.263022+00:00
-- url     : https://prove2.me/theorems/5adec17a-3b98-45b1-8e7f-e66a85b0cf82
-- title:
--   Lossless complexes, the imbalance (4.25), and the constant $c$ of (4.26)
-- statement:
--   A square complex is **lossless** with parameters $(D_i,D'_i,c_i,\varepsilon_i)_{i=1}^k$ if, for every $I\subseteq[k]$ and $i\notin I$, the graph between $V_I$ and $V_{I\cup\{i\}}$ is one-sided $(c_i,\varepsilon_i)$-lossless from $V_I$ to $V_{I\cup\{i\}}$. It is **two-sided lossless** if $X^{\mathrm{rev}}$ is also lossless, with the same $c_i,\varepsilon_i$. Write $\varepsilon_\star=\sum_{j=1}^k\varepsilon_j$. The complex is **imbalanced** if
--
--   $$\max_{1\le s<t\le k}\varepsilon_tD'_s\le\varepsilon_\star,\qquad(4.25)$$
--
--   and the small-set range is governed by
--
--   $$c=\frac{\min_jc_j}{2^kk!\,D'_{[k]}D_{[k]}}.\qquad(4.26)$$
--
--   **Formalization Note.** $c$ is a function of the degrees and of $c_1,\dots,c_k$. Its value at $k=0$ is $0$; no statement uses it there.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Definition 2.18, p.19; eqs. (4.25), (4.26), p.37

import Mathlib
import Definitions.Def_LosslessQLTC_Bigraph
import Definitions.Def_LosslessQLTC_rev

namespace LosslessQLTC

variable {k : ℕ}

/-- The block `V_I` (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.14). -/
def Block (X : SquareComplex k) (I : Finset (Fin k)) : Type :=
  {v : X.Vtx // X.type v = I}

instance (X : SquareComplex k) (I : Finset (Fin k)) : Fintype (Block X I) :=
  inferInstanceAs (Fintype {v : X.Vtx // X.type v = I})

instance (X : SquareComplex k) (I : Finset (Fin k)) : DecidableEq (Block X I) :=
  inferInstanceAs (DecidableEq {v : X.Vtx // X.type v = I})

/-- The directional graph `X_{I,i}` between `V_I` and `V_{I ∪ {i}}` (p.17). -/
def dirEdge (X : SquareComplex k) (I : Finset (Fin k)) (i : Fin k)
    (x : Block X I) (y : Block X (insert i I)) : Prop :=
  X.up x.1 y.1

instance (X : SquareComplex k) (I : Finset (Fin k)) (i : Fin k) :
    DecidableRel (dirEdge X I i) :=
  fun x y => X.decUp x.1 y.1

/-- Definition 2.18 (p.19): `X` is lossless with parameters `(D_i, D′_i, c_i, ε_i)` if, for every
`I ⊆ [k]` and `i ∉ I`, the directional graph `X_{I,i}` is one-sided `(c_i, ε_i)`-lossless from
`V_I` to `V_{I ∪ {i}}`. -/
def IsLossless (X : SquareComplex k) (c ε : Fin k → ℝ) : Prop :=
  ∀ (I : Finset (Fin k)) (i : Fin k), i ∉ I →
    IsOneSidedLossless (dirEdge X I i) (X.D i) (c i) (ε i)

/-- Definition 2.18 (p.19): two-sided lossless: `X^rev` is also lossless, with `D_i, D′_i`
interchanged (which `rev` does) and the same `c_i, ε_i`. -/
def IsTwoSidedLossless (X : SquareComplex k) (c ε : Fin k → ℝ) : Prop :=
  IsLossless X c ε ∧ IsLossless (rev X) c ε

/-- `ε⋆ = Σ_{j=1}^k ε_j` (eq. (4.25), p.37). -/
def epsStar (ε : Fin k → ℝ) : ℝ := ∑ j, ε j

/-- The imbalance assumption (4.25) (p.37): `max_{1 ≤ s < t ≤ k} ε_t D′_s ≤ ε⋆`. -/
def IsImbalanced (X : SquareComplex k) (ε : Fin k → ℝ) : Prop :=
  ∀ s t : Fin k, s < t → ε t * (X.D' s : ℝ) ≤ epsStar ε

/-- `min_j c_j`; the value at `k = 0`, where `[k]` is empty, is `0` and no result uses it. -/
noncomputable def minC (c : Fin k → ℝ) : ℝ :=
  if h : (Finset.univ : Finset (Fin k)).Nonempty then Finset.univ.inf' h c else 0

/-- The constant `c = min_j c_j / (2^k k! D′_{[k]} D_{[k]})` of eq. (4.26) (p.37), as a function
of the degrees and of `c_1, …, c_k`. -/
noncomputable def cConst (D D' : Fin k → ℕ) (c : Fin k → ℝ) : ℝ :=
  minC c / (2 ^ k * (k.factorial : ℝ) * (prodD D' Finset.univ : ℝ) * (prodD D Finset.univ : ℝ))

end LosslessQLTC


