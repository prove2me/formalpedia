-- Prove2me | Definitions.Def_IntractableCoding_Weights_Reductions
-- name    : IntractableCoding_Weights_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:27:07.642922+00:00
-- url     : https://prove2.me/theorems/903c4a2b-e3f4-408f-9b86-c5bb62419d54
-- title:
--   The incidence matrix of a set of triples and the two reductions from THREE-DIMENSIONAL MATCHING (Section III, p. 385)
-- statement:
--   Let a THREE-DIMENSIONAL MATCHING instance be given by $T=\{0,\dots,n-1\}$ and a set $U\subseteq T\times T\times T$ of $t=|U|$ triples, listed in lexicographic order.
--
--   1. The **triple incidence matrix** $B$ is the $t\times 3n$ binary matrix whose row for the triple $(a,b,c)$ has weight three: a $1$ in column $a$, in column $n+b$ and in column $2n+c$ (three blocks of $n$ columns, one per coordinate), and $0$ elsewhere.
--   2. The **COSET WEIGHTS instance** of the reduction is $(A,y,w)=(B,\ 11\cdots1,\ n)$.
--   3. The **SUBSPACE WEIGHTS matrix** is the $(3nt+3n+t)\times(3nt+3n)$ matrix
--   $$A=\begin{pmatrix}[\,B\mid I_t\mid I_t\mid\cdots\mid I_t\,]\\[2pt] I_{3n(t+1)}\end{pmatrix},$$
--   whose top $t$ rows are $B$ followed by $3n$ copies of the $t\times t$ identity matrix, and whose lower $3nt+3n$ rows form the identity matrix of that size. The **SUBSPACE WEIGHTS instance** of the reduction is $(A,\ w)$ with $w=3n^2+4n$.
--   4. For a vector $x$ of length $3nt+3n+t$, $x_0$ is the vector formed by its first $t$ components and $x_1$ the vector formed by its last $3n(t+1)$ components.
--
--   Two structural identities record that the number of rows $t+3n(t+1)$ and of columns $3n(t+1)$ are the paper's $3nt+3n+t$ and $3nt+3n$.
--
--   **Formalization Note** The 3DM instance is the published `PricingWithTips.ThreeDMInstance` $\langle n,\mathrm{edge}\rangle$ with $U=\{(a,b,c)\mid \mathrm{edge}\,a\,b\,c\}$. The $k$-th copy of $I_t$ ($0\le k<3n$) occupies columns $3n+kt,\dots,3n+kt+t-1$.
-- source:
--   Berlekamp, McEliece & van Tilborg, On the Inherent Intractability of Certain Coding Problems, IEEE Trans. Inform. Theory IT-24(3), 1978, https://doi.org/10.1109/TIT.1978.1055873, p. 385, Section III (incidence matrix, the COSET reduction, the SUBSPACE construction)

import Mathlib
import Definitions.Def_IntractableCoding_Weights_Problems
import Definitions.Def_PricingWithTips_ThreeDM

namespace IntractableCoding.Weights

open PricingWithTips

/-- The triples of a 3DM instance `I = ⟨n, edge⟩` (with `T = Fin n`): the set
`U = {(a, b, c) | edge a b c = true}`, listed in lexicographic order. -/
def triples (I : ThreeDMInstance) : List (Fin I.1 × Fin I.1 × Fin I.1) :=
  ((List.finRange I.1).flatMap fun a => (List.finRange I.1).flatMap fun b =>
    (List.finRange I.1).map fun c => (a, b, c)).filter fun abc => I.2 abc.1 abc.2.1 abc.2.2

/-- `t = |U|`, the number of triples. -/
def tCount (I : ThreeDMInstance) : ℕ := (triples I).length

/-- The `|U| × 3|T|` triple incidence matrix `B` (p. 385): row `r` corresponds to the `r`-th
triple `(a, b, c)` of `triples I` and has weight three, with a `1` in column `a` (first block of
`n` columns), in column `n + b` (second block) and in column `2n + c` (third block). -/
def incidence (I : ThreeDMInstance) : Matrix (Fin (tCount I)) (Fin (3 * I.1)) (ZMod 2) :=
  fun r j =>
    let abc := (triples I).get r
    if j.val = abc.1.val ∨ j.val = I.1 + abc.2.1.val ∨ j.val = 2 * I.1 + abc.2.2.val then 1
    else 0

/-- The COSET WEIGHTS instance of the reduction (p. 385): `A = B`, `y = (11⋯1)`, `w = |T|`. -/
def cosetOf3DM (I : ThreeDMInstance) : CosetInstance :=
  ⟨tCount I, 3 * I.1, incidence I, fun _ => 1, I.1⟩

/-- The top `t` rows of the SUBSPACE WEIGHTS matrix (p. 385): `B` (the first `3n` columns)
followed by `3n` copies of the `t × t` identity matrix; column `3n + k t + i` (`0 ≤ k < 3n`,
`0 ≤ i < t`) is the `i`-th column of the `k`-th copy. -/
def subspaceTop (I : ThreeDMInstance) :
    Matrix (Fin (tCount I)) (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2) :=
  fun r j =>
    if hj : j.val < 3 * I.1 then incidence I r ⟨j.val, hj⟩
    else if (j.val - 3 * I.1) % tCount I = r.val then 1 else 0

/-- The `(3nt + 3n + t) × (3nt + 3n)` matrix `A` of the SUBSPACE WEIGHTS reduction (p. 385):
the top `t` rows are `subspaceTop I` = `[B | I_t | ⋯ | I_t]`, the lower `3n(t + 1)` rows form
the identity matrix `I_{3n(t+1)}`. -/
def subspaceMatrix (I : ThreeDMInstance) :
    Matrix (Fin (tCount I + 3 * I.1 * (tCount I + 1))) (Fin (3 * I.1 * (tCount I + 1)))
      (ZMod 2) :=
  Matrix.of (Fin.append (subspaceTop I) (1 : Matrix (Fin (3 * I.1 * (tCount I + 1)))
    (Fin (3 * I.1 * (tCount I + 1))) (ZMod 2)))

/-- The number of rows of `subspaceMatrix I` is the paper's `3nt + 3n + t`. -/
theorem subspaceMatrix_rows (I : ThreeDMInstance) :
    tCount I + 3 * I.1 * (tCount I + 1) = 3 * I.1 * tCount I + 3 * I.1 + tCount I := by ring

/-- The number of columns of `subspaceMatrix I` is the paper's `3nt + 3n`. -/
theorem subspaceMatrix_cols (I : ThreeDMInstance) :
    3 * I.1 * (tCount I + 1) = 3 * I.1 * tCount I + 3 * I.1 := by ring

/-- The SUBSPACE WEIGHTS instance of the reduction (pp. 385–386): the matrix `A` above and
`w = 3n² + 4n` with `n = |T|`. -/
def subspaceOf3DM (I : ThreeDMInstance) : SubspaceInstance :=
  ⟨tCount I + 3 * I.1 * (tCount I + 1), 3 * I.1 * (tCount I + 1), subspaceMatrix I,
    3 * I.1 ^ 2 + 4 * I.1⟩

/-- `x₀`: the vector of length `t` formed from the first `t` components of `x`. -/
def firstPart (I : ThreeDMInstance)
    (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2) : Fin (tCount I) → ZMod 2 :=
  fun i => x (Fin.castAdd (3 * I.1 * (tCount I + 1)) i)

/-- `x₁`: the vector formed from the last `3n(t + 1)` components of `x`. -/
def lastPart (I : ThreeDMInstance)
    (x : Fin (tCount I + 3 * I.1 * (tCount I + 1)) → ZMod 2) :
    Fin (3 * I.1 * (tCount I + 1)) → ZMod 2 :=
  fun i => x (Fin.natAdd (tCount I) i)

end IntractableCoding.Weights


