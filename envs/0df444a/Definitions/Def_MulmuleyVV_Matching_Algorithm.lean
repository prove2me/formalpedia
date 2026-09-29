-- Prove2me | Definitions.Def_MulmuleyVV_Matching_Algorithm
-- name    : MulmuleyVV_Matching_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:33:58.184452+00:00
-- url     : https://prove2.me/theorems/7d5ea499-e5e3-4268-902d-feee6d1d5d76
-- title:
--   Perfect matchings as edge sets, the matrix $B$ with $2^{w_{ij}}$ substituted into the Tutte matrix, and the output of Steps 1–3
-- statement:
--   Let $G$ be a simple graph on the vertices $v_1, \dots, v_n$, identified with $\{0, \dots, n-1\}$ in their natural order, with edge set $E$, and let $w : E \to \mathbb{N}$ assign a weight $w_{ij}$ to each edge $(v_i, v_j)$.
--
--   1. A **perfect matching** of $G$ is a set $M \subseteq E$ such that every vertex lies in exactly one edge of $M$. The perfect matchings form a family of subsets of $E$, so $(E, \{\text{perfect matchings}\})$ is a set system in the sense of §3.
--   2. The **Tutte matrix** of $G$ is the skew-symmetric $n\times n$ matrix with an indeterminate $x_{ij}$ above the diagonal and $-x_{ij}$ below it at every edge, and $0$ elsewhere. Substituting $x_{ij} = 2^{w_{ij}}$ gives the integer matrix $B$:
--   $$
--   b_{ij} = \begin{cases} 2^{w_{ij}} & (v_i, v_j) \in E,\ i < j,\\ -2^{w_{ij}} & (v_i, v_j) \in E,\ i > j,\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   3. For an integer $x$ and $k \in \mathbb{N}$, "$x / 2^k$ is odd" means that $2^k$ divides $x$ and the integer $x/2^k$ is odd.
--   4. **Step 1** computes $|B|$ and obtains $w$, the exponent for which $2^{2w}$ is the highest power of $2$ dividing $|B|$: here $w = \lfloor \nu_2(|B|)/2 \rfloor$, with $\nu_2$ the $2$-adic valuation.
--   5. **Steps 2–3** output the set of edges $(v_i, v_j)$, $i < j$, for which
--   $$
--   \frac{|B_{ij}|\, 2^{w_{ij}}}{2^{2w}}
--   $$
--   is odd, where the minor $|B_{ij}|$ is read from the $(j,i)$ entry of $\operatorname{adj}(B)$.
--
--   These are the data of the matching algorithm of §4: the output of Steps 1–3 is computed from $B$, its determinant and its adjugate by parity tests only.
--
--   **Formalization Note** Vertices are `Fin n` and edges are elements of `G.edgeSet`; weights are `w : G.edgeSet → ℕ` and perfect matchings are `Finset G.edgeSet` (`IsPerfectMatchingEdges`, `perfectMatchings`). The matrix is `weightedTutteMatrix G w`. Mathlib's `adjugate B j i` is the signed cofactor $(-1)^{i+j}|B_{ij}|$ rather than the unsigned minor $|B_{ij}|$; divisibility by $2^k$ and oddness of the quotient do not depend on the sign. Step 1's $w$ is `step1Weight G w = padicValInt 2 |B| / 2`; when $|B| = 0$ this is $0$, a junk value that only arises when the minimum weight perfect matching is not unique. The output is `mvvOutput G w`.
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), pp. 107–109, §4 (problem statement p. 107; Notation, Definition of the Tutte matrix and of B, p. 108; Steps 1–3, p. 109)

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_SetSystem

namespace MulmuleyVV.Matching

/-- `M`, a set of edges of `G`, is a perfect matching: every vertex lies in exactly one edge of
`M` (MVV 1987, §4, p. 107). -/
def IsPerfectMatchingEdges {n : ℕ} (G : SimpleGraph (Fin n)) (M : Finset G.edgeSet) : Prop :=
  ∀ v : Fin n, ∃! e, e ∈ M ∧ v ∈ (e : Sym2 (Fin n))

/-- The family of all perfect matchings of `G`, viewed as a set system on the edge set `E`
(MVV 1987, §4, p. 107). -/
noncomputable def perfectMatchings {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Finset G.edgeSet) := by
  classical
  exact Finset.univ.filter (fun M => IsPerfectMatchingEdges G M)

/-- The integer matrix `B` of MVV 1987 (§4, p. 108): the Tutte matrix of `G` (vertices
`v_1, …, v_n` = `Fin n`) with `x_ij := 2^{w_ij}` substituted.  Entry `(i, j)` is `2^{w_ij}` if
`(v_i, v_j) ∈ E` and `i < j`, `-2^{w_ij}` if `(v_i, v_j) ∈ E` and `j < i`, and `0` otherwise. -/
def weightedTutteMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : G.edgeSet → ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if h : G.Adj i j then
      (if i < j then (2 : ℤ) ^ w ⟨s(i, j), G.mem_edgeSet.mpr h⟩
        else -((2 : ℤ) ^ w ⟨s(i, j), G.mem_edgeSet.mpr h⟩))
    else 0

/-- "`x / 2^k` is odd", read as an odd integer: `2^k` divides `x` and the quotient is odd. -/
def OddQuot (x : ℤ) (k : ℕ) : Prop :=
  (2 : ℤ) ^ k ∣ x ∧ Odd (x / (2 : ℤ) ^ k)

/-- Step 1 of the MVV algorithm (p. 109): compute `|B|` and obtain `w`, the exponent with
`2^{2w}` the highest power of 2 dividing `|B|`, i.e. half the 2-adic valuation of `|B|`. -/
noncomputable def step1Weight {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : G.edgeSet → ℕ) : ℕ :=
  padicValInt 2 (weightedTutteMatrix G w).det / 2

/-- The output of Steps 1–3 of the MVV algorithm (p. 109): the set of edges `(v_i, v_j)`,
`i < j`, for which `|B_ij| 2^{w_ij} / 2^{2w}` is odd, where `w = step1Weight G w` and the
minor `|B_ij|` is read (up to sign) from the `(j, i)` entry of `adj(B)`. -/
noncomputable def mvvOutput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : G.edgeSet → ℕ) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter (fun e : G.edgeSet =>
    ∃ i j : Fin n, i < j ∧ (e : Sym2 (Fin n)) = s(i, j) ∧
      OddQuot ((weightedTutteMatrix G w).adjugate j i * (2 : ℤ) ^ w e) (2 * step1Weight G w))

end MulmuleyVV.Matching


