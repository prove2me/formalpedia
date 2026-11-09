-- Prove2me | Definitions.Def_SignRankMargin_OREquality_Composition
-- name    : SignRankMargin_OREquality_Composition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:41:08.14154+00:00
-- url     : https://prove2.me/theorems/211567c0-bd4d-48a8-ad3b-aa80a5fbf428
-- title:
--   Equality on bit strings and unrestricted OR composition
-- statement:
--   An $n$-bit string is relabelled by an element of the alphabet $[2^n]$. The equality matrix and the OR composition of any Boolean matrix $B:X\times Y\to\{0,1\}$ are
--
--   $$
--   \operatorname{equalityMatrix}(n)(a,b)=\mathbf1[a=b],\qquad
--   \operatorname{orComposition}(k,B)(x,y)=\mathbf1[\exists i\in[k]:B(x_i,y_i)=1].
--   $$
--
--   Rows and columns of the composition range over all tuples $x\in X^k$, $y\in Y^k$. The matrix $\operatorname{orEquality}(k,n)$ is this same composition applied to $\operatorname{equalityMatrix}(n)$; its order is $2^{nk}$. There is no promise on the input pairs.
--
--   These constructions relate the general sparse-row upper bound to the goal's equality matrices.
--
--   **Formalization Note** Coordinates use `Fin k` and the alphabet is `Fin (2^n)`. Thus $n$ is bit length, not alphabet cardinality. At $k=0$ the existential condition is false; source results require $k\ge1$.
-- source:
--   Gabriel Hart, Kaave Hosseini, STOC 2027 submission #728 (October 2026), Section 1, p. 1; Section 2, p. 7; Section 3, p. 8

import Mathlib

namespace SignRankMargin.OREquality

/-- Equality on n-bit strings, relabelled by the alphabet Fin (2^n) (§2, p.7). -/
def equalityMatrix (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) Bool :=
  fun x y => decide (x = y)

/-- The unrestricted OR composition: an entry is true iff any coordinate succeeds (§3, p.8). -/
noncomputable def orComposition {X Y : Type*} (k : ℕ) (B : Matrix X Y Bool) :
    Matrix (Fin k → X) (Fin k → Y) Bool := by
  classical
  exact fun x y => decide (∃ i : Fin k, B (x i) (y i) = true)

/-- The actual OR of k equality tests; no restriction or promise on input pairs. -/
noncomputable def orEquality (k n : ℕ) :
    Matrix (Fin k → Fin (2 ^ n)) (Fin k → Fin (2 ^ n)) Bool :=
  orComposition k (equalityMatrix n)

end SignRankMargin.OREquality


