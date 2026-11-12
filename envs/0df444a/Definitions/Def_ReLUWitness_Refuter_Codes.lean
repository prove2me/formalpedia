-- Prove2me | Definitions.Def_ReLUWitness_Refuter_Codes
-- name    : ReLUWitness_Refuter_Codes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:50:33.343195+00:00
-- url     : https://prove2.me/theorems/d3eaae82-28fb-43d7-b447-662c062839e6
-- title:
--   Codes of §2.1-2.2: unary strings, exact tuples, canonical signed integers, rational pairs, cross-product order, rational vectors
-- statement:
--   Read in an arbitrary two-sorted structure:
--
--   * $\mathrm{Un}(r)$ is the string whose bits are exactly those below $r$.
--   * An **exact tuple of length $r$** is a string all of whose present bits are $\langle a,i\rangle$ with $1\le a\le r$; its entry $a$ is its row $X[a]$ (row zero is empty and there are no other bits).
--   * A **canonical signed integer** has its sign at bit $0$ (present exactly for negative values) and magnitude bit $i$ at position $i+1$. A present sign bit requires a nonzero magnitude, so zero is the empty string. A canonical positive integer is canonical, nonnegative and nonzero.
--   * Signed products, sums, differences, $\max(0,\cdot)$, fixed powers and the signed order are computed from the magnitudes with the primitive binary operations and the sign rules of p. 15.
--   * A **valid rational pair** is an exact tuple $(a,b)$ of length two, with $a$ canonical signed and $b$ canonical positive. It denotes $a/b$, and no coprimality is required. Equality and order are the cross-product tests
--     $$(a,b)=_{\mathbb Q}(c,e)\iff ae=cb,\qquad (a,b)\le_{\mathbb Q}(c,e)\iff ae\le cb.$$
--   * A **valid rational $n$-vector** is an exact tuple of $n$ valid rational pairs.
--   * $\mathrm{MAX}_n(x)$ is represented by the **first maximal coordinate**: the least $a\in[1,n]$ with $x_b\le_{\mathbb Q}x_a$ for all $b\in[1,n]$ (the parallel selection convention of p. 47).
-- source:
--   Myrisiotis, A Witnessing Duality for ReLU Network Depth, arXiv:2610.38281v1, pp. 13-16, §2.1-2.2; p. 19 (Un(r)); p. 47 (selection of a maximum)

import Mathlib
import Definitions.Def_ReLUWitness_Refuter_TwoSorted

open scoped Classical

namespace ReLUWitness.Refuter

/-! Codes of §2.1-§2.2 (Myrisiotis, arXiv:2610.38281v1, pp. 13-16), read in an arbitrary
two-sorted structure: unary strings, exact tuples, canonical signed integers, rational
pairs with cross-product equality and order, valid rational vectors and the first
maximizing coordinate. -/

noncomputable section

namespace Structure

variable (M : Structure)

/-- `X = Un(r)`: exactly the bits below `r`. -/
def IsUn (X : M.S) (r : M.N) : Prop := ∀ z, M.mem z X ↔ M.lt z r

/-- Exact tuple of length `r`: every present bit is `⟨a,i⟩` with `1 ≤ a ≤ r`
(so row zero is empty and there are no other bits); entry `a` is row `a`. -/
def IsTuple (X : M.S) (r : M.N) : Prop :=
  ∀ z, M.mem z X → ∃ a i, M.le M.one a ∧ M.le a r ∧ z = M.pair a i

/-- Sign bit (bit zero) of a signed code. -/
def Neg (u : M.S) : Prop := M.mem M.zero u

/-- Nonzero: some bit present. -/
def NonEmpty (u : M.S) : Prop := ∃ i, M.mem i u

/-- Canonical signed integer: a present sign bit needs a present magnitude bit (zero has the
unique empty code; leading zeros are absent because a string has no bits beyond its length). -/
def CanInt (u : M.S) : Prop := M.Neg u → ∃ i, M.mem i u ∧ i ≠ M.zero

/-- Canonical positive integer. -/
def CanPos (u : M.S) : Prop := M.CanInt u ∧ ¬ M.Neg u ∧ M.NonEmpty u

/-- Signed code with sign `neg` and magnitude `X`. -/
def mkS (neg : Prop) (X : M.S) : M.S := M.sgnd (if neg then M.one else M.zero) X

/-- Canonical integer one. -/
def ione : M.S := M.mkS False (M.imul M.zero M.zero M.empt)

/-- Signed product. -/
def smul (a b : M.S) : M.S := M.mkS (¬ (M.Neg a ↔ M.Neg b)) (M.bmul (M.mag a) (M.mag b))

/-- Signed difference `X - Y` of two magnitudes. -/
def ssubU (X Y : M.S) : M.S :=
  if M.BLe Y X then M.mkS False (M.bsub X Y) else M.mkS True (M.bsub Y X)

/-- Signed sum: same signs add magnitudes; opposite signs subtract the smaller magnitude
from the larger and keep the sign of the larger. -/
def sadd (a b : M.S) : M.S :=
  if (M.Neg a ↔ M.Neg b) then M.mkS (M.Neg a) (M.badd (M.mag a) (M.mag b))
  else if M.BLe (M.mag b) (M.mag a) then M.mkS (M.Neg a) (M.bsub (M.mag a) (M.mag b))
  else M.mkS (M.Neg b) (M.bsub (M.mag b) (M.mag a))

/-- Signed order. -/
def sle (a b : M.S) : Prop :=
  (M.Neg a ∧ ¬ M.Neg b) ∨ (¬ M.Neg a ∧ ¬ M.Neg b ∧ M.BLe (M.mag a) (M.mag b)) ∨
  (M.Neg a ∧ M.Neg b ∧ M.BLe (M.mag b) (M.mag a))

/-- `max(0, a)`. -/
def smax0 (a : M.S) : M.S := if M.Neg a then M.empt else a

/-- Fixed power `a^e` of a signed code, `e` external (`a^0` is integer one). -/
def spow (a : M.S) : ℕ → M.S
  | 0 => M.ione
  | e + 1 => M.smul (spow a e) a

/-- Numerator and denominator of a rational pair `(a,b)` (tuple rows one and two). -/
def qnum (P : M.S) : M.S := M.row M.one P
def qden (P : M.S) : M.S := M.row (M.numeral 2) P

/-- Valid rational pair: exact tuple `(a,b)`, `a` canonical signed, `b` canonical positive;
no coprimality. -/
def ValidPair (P : M.S) : Prop :=
  M.IsTuple P (M.numeral 2) ∧ M.CanInt (M.qnum P) ∧ M.CanPos (M.qden P)

/-- Cross-product equality `(a,b) =_Q (c,e) ↔ ae = cb`. -/
def qeq (P R : M.S) : Prop :=
  M.smul (M.qnum P) (M.qden R) = M.smul (M.qnum R) (M.qden P)

/-- Cross-product order `(a,b) ≤_Q (c,e) ↔ ae ≤ cb`. -/
def qle (P R : M.S) : Prop :=
  M.sle (M.smul (M.qnum P) (M.qden R)) (M.smul (M.qnum R) (M.qden P))

/-- Valid rational `n`-vector: exact tuple of `n` valid rational pairs. -/
def ValidVec (x : M.S) (n : M.N) : Prop :=
  M.IsTuple x n ∧ ∀ a, M.le M.one a → M.le a n → M.ValidPair (M.row a x)

/-- `a` is the first index of a maximal coordinate of `x` (cross-product order): the
selected coordinate representing `MAX_n(x)`. -/
def IsFirstMax (x : M.S) (n a : M.N) : Prop :=
  M.le M.one a ∧ M.le a n ∧
  (∀ b, M.le M.one b → M.le b n → M.qle (M.row b x) (M.row a x)) ∧
  ∀ c, M.le M.one c → M.lt c a →
    ¬ ∀ b, M.le M.one b → M.le b n → M.qle (M.row b x) (M.row c x)

end Structure

end

end ReLUWitness.Refuter


