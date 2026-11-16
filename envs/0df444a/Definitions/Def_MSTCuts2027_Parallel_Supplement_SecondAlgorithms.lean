-- Prove2me | Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondAlgorithms
-- name    : MSTCuts2027_Parallel_Supplement_SecondAlgorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:37:04.820772+00:00
-- url     : https://prove2.me/theorems/a913c369-46fc-4642-849c-548c8ca80d71
-- title:
--   Algorithm 5 (EliminateTriangle in $G_2$), the table $M_2$ and the output of all-pairs second mincuts
-- statement:
--   This file extends the published machine model of the mission (a fork-join CREW machine whose programs are finite syntax trees, with an external single-pair procedure) and its memory layout (the table $M(u,v)$ of mincut pointers, the real cells holding $\lambda_1(u,v)$, and the store of Boolean cut arrays).
--
--   1. **Memory.** New regions above the published layout: the table $M_2(u,v)$ of pointers to second mincuts (Appendix D.2), a store of second-mincut arrays, and real cells for $\lambda_2(u,v)$.
--   2. **Algorithm 5.** `EliminateTriangle`$(u,v,x,C^1_{u,v},C^2_{u,v})$ takes pointers to a $(u,v)$-mincut $C^1_{u,v}$ and a second $(u,v)$-mincut $C^2_{u,v}$ and the real cells holding $\lambda_1(u,v)$ and $\lambda_1(x,u)$. If $\lambda_1(u,v)>\lambda_1(x,u)$ (Type 1) it tests $C^1_{u,v}$, otherwise (Type 2) $C^2_{u,v}$. It returns the edge $(x,v)$ when the tested cut keeps $x$ on the side of $u$, and $(x,u)$ otherwise, by writing the vertex $v$ or $u$ to an output cell.
--   3. **Second-mincut procedure.** A procedure $Q$ is correct when, for all distinct $u,v$, it reports a second $(u,v)$-mincut and its value.
--   4. **Tables.** $M_2(u,v)$ is correct when it points to a second $(u,v)$-mincut in the second-mincut store. The stored second-mincut cover of a set $S$ is the set of cuts that $M_2$ points to for pairs of $S$.
--   5. **Proxy edge for second mincuts.** $(x,a)$ with $a\in B$ is a proxy edge from $x$ to $B$ for a set of cuts $\mathcal C$ when, for every $v\in B$, either $\mathcal C$ contains a second $(x,v)$-mincut or every second $(x,a)$-mincut is a second $(x,v)$-mincut, and $\lambda_2(x,v)\le\lambda_2(x,a)$ for every $v\in B$.
--   6. **Output of all-pairs second mincuts.** For every ordered pair of distinct vertices, $M_2(u,v)$ points to a Boolean array that is a second $(u,v)$-mincut, and the real cell of the pair holds $\lambda_2(u,v)$.
--
--   These are the operational objects of Lemmas 9, 10 and 15 and Theorem 4.
--
--   **Formalization Note** The side test of Algorithm 5 compares the memberships of $x$ and $u$, because a stored cut need not contain $u$; on a cut containing $u$ it is the paper's test $x\in C$. The printed Algorithm 5 returns $(x,u)$ when $x\in C$; with the paper's orientation ($u\in C$) that is the wrong edge, and the corrected rule above is the one Lemmas 7, 8, 9 and 15 support (see the items of those lemmas for a counterexample). When $\lambda_1(u,v)<\lambda_1(x,u)$, a case excluded by the premise of every lemma about the algorithm and where the printed algorithm returns nothing, the program takes the Type 2 branch.
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Algorithm 5 (printed p. 13, PDF p. 15); Lemma 10 (printed p. 13, PDF p. 15); Theorem 4 (printed p. 4, PDF p. 6); array M2, Appendix D.2 (printed p. 23, PDF p. 25)

import Mathlib
import Definitions.Def_MSTCuts2027_Parallel_CutModel
import Definitions.Def_MSTCuts2027_Parallel_Machine
import Definitions.Def_MSTCuts2027_Parallel_Algorithms
import Definitions.Def_MSTCuts2027_Parallel_Supplement_SecondCutModel

/-!
# Algorithm 5, the array `M₂` and second-mincut tables in the published machine

Baswana–Roy, *Using MSTs to Compute All-Pairs Mincuts and Beyond ...*, STOC 2027 submission #21:
Algorithm 5 (printed p. 13, PDF p. 15), Lemma 10 (printed p. 13, PDF p. 15), Theorem 4 (printed
p. 4, PDF p. 6) and the array `M₂` of Appendix D.2 (printed p. 23, PDF p. 25). Built on the published
machine `MSTCuts2027.Parallel.Machine` and the published layout of `MSTCuts2027.Parallel.Algorithms`
(the mincut table `M` at `tableAddr`, its `λ₁` values at `lamAddr`, the cut store from `cutBase`).

New regions, all above the published layout (`roundsBase n + n²` is past its last cell): the table
`M₂(u, v)` of second-mincut pointers, a store of second-mincut arrays, and real cells for `λ₂(u, v)`
placed after the `n²` real cells of `λ₁`.
-/

namespace MSTCuts2027.Parallel.Supplement

open MSTCuts2027.Parallel

/-! ## Addresses -/

/-- The first word cell of the table `M₂`. -/
def table2Base (n : ℕ) : ℕ := roundsBase n + n * n

/-- The word cell of `M₂(u, v)`, the pointer to a second `(u, v)`-mincut. -/
def table2Addr (n u v : ℕ) : ℕ := table2Base n + u * n + v

/-- The first word cell of the store of second-mincut arrays. -/
def cut2Base (n : ℕ) : ℕ := table2Base n + n * n

/-- The cut slot of the pair `(x, y)` in the second-mincut store: Boolean array of `n` cells. -/
def cut2Addr (n x y : ℕ) : ℕ := cut2Base n + (x * n + y) * n

/-- The first word cell after the second-mincut store. -/
def cut2End (n : ℕ) : ℕ := cut2Base n + n * n * n

/-- The real cell holding `λ₂(u, v)`, after the `n²` real cells `lamAddr` of `λ₁`. -/
def lam2Addr (n u v : ℕ) : ℕ := n * n + u * n + v

/-! ## Algorithm 5 -/

/-- One branch of Algorithm 5 on the cut at the pointer `p`: write to `dest` (register `7`) the
vertex `v` (register `2`) when the cut keeps `x` (register `0`) on the side of `u` (register `1`),
else `u`. The written vertex `a` names the edge `(x, a)` that is returned. The side test compares
the memberships of `x` and `u`, since a stored cut need not contain `u`. -/
def elim2Branch (p : Expr) : Stmt :=
  .ite (.eq (.eq (.read (.add p (.var 0))) (.const 0)) (.eq (.read (.add p (.var 1))) (.const 0)))
    (.write (.var 7) (.var 2))
    (.write (.var 7) (.var 1))

/-- `EliminateTriangle(u, v, x, C¹ᵤᵥ, C²ᵤᵥ)` (Algorithm 5), arguments
`x, u, v, p₁, p₂, r_uv, r_xu, dest`: `p₁` points to a `(u, v)`-mincut, `p₂` to a second
`(u, v)`-mincut, and the real cells `r_uv`, `r_xu` hold `λ₁(u, v)` and `λ₁(x, u)`. If
`λ₁(u, v) > λ₁(x, u)` (Type 1) the test is made on `C¹ᵤᵥ`, otherwise (Type 2 under the premise
`λ₁(u, v) ≥ λ₁(x, u)`) on `C²ᵤᵥ`. In both cases the returned edge is `(x, v)` when the tested cut
keeps `x` on the side of `u`, and `(x, u)` otherwise: the edge to the endpoint that the cut separates
from `x`. -/
def elim2Body : Stmt :=
  .ite (.rle (.var 5) (.var 6)) (elim2Branch (.var 4)) (elim2Branch (.var 3))

/-- The program consisting of Algorithm 5 alone, as procedure `0`. -/
def elim2Program : Program := [elim2Body]

/-! ## Second-mincut procedure, tables and outputs -/

/-- `Q` is a correct single-pair second-mincut procedure for `F`: for all distinct `u, v` the
reported cut is a second `(u, v)`-mincut and the reported value is its `F`-value. -/
def IsSecondMincutOracle {n : ℕ} (F : Finset (Fin n) → ℝ) (Q : Oracle ℝ n) : Prop :=
  ∀ u v : Fin n, u ≠ v → IsSecondMincut F u v (Q u v).cut ∧ (Q u v).value = F (Q u v).cut

/-- `M₂(u, v)` holds a pointer `p` into the second-mincut store, and the array at `p` is a second
`(u, v)`-mincut. -/
def Entry2OK {n : ℕ} (F : Finset (Fin n) → ℝ) (σ : Store ℝ) (u v : Fin n) : Prop :=
  ∃ p : ℕ, σ.mem (table2Addr n u v) = p ∧ cut2Base n ≤ p ∧ p + n ≤ cut2End n ∧
    IsSecondMincut F u v (cutAt n σ.mem p)

/-- For all ordered pairs of distinct vertices of `S`, `M₂` points to a second mincut. -/
def Table2OK {n : ℕ} (F : Finset (Fin n) → ℝ) (σ : Store ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → Entry2OK F σ u v

/-- The second-mincut cover stored for the pairs of `S`: the cuts that `M₂` points to. -/
def storedCover2 {n : ℕ} (σ : Store ℝ) (S : Finset (Fin n)) : Set (Finset (Fin n)) :=
  {C | ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ∃ p : ℕ, σ.mem (table2Addr n u v) = p ∧ C = cutAt n σ.mem p}

/-- The real cells `lamAddr n x v` hold `λ₁(x, v)` for every `v ∈ S`. -/
def LamRowOK {n : ℕ} (F : Finset (Fin n) → ℝ) (σ : Store ℝ) (x : Fin n) (S : Finset (Fin n)) :
    Prop :=
  ∀ v ∈ S, σ.rmem (lamAddr n x v) = lam F x v

/-- The two properties of Lemma 10: `(x, a)` is a proxy edge for second mincuts from `x` to `B`
for the cover `C`. -/
def IsProxyEdge2 {n : ℕ} (F : Finset (Fin n) → ℝ) (x : Fin n) (B : Finset (Fin n))
    (C : Set (Finset (Fin n))) (a : Fin n) : Prop :=
  a ∈ B ∧
  (∀ v ∈ B, (∃ D ∈ C, IsSecondMincut F x v D) ∨
      ∀ D, IsSecondMincut F x a D → IsSecondMincut F x v D) ∧
  (∀ v ∈ B, lam2 F x v ≤ lam2 F x a)

/-- The final output of Theorem 4, read from the memory `σ`: for every ordered pair of distinct
vertices, `M₂(u, v)` points to a Boolean array that is a second `(u, v)`-mincut, and the real cell
of the pair holds `λ₂(u, v)`. -/
def AllPairsSecondOutput {n : ℕ} (F : Finset (Fin n) → ℝ) (σ : Store ℝ) : Prop :=
  ∀ u v : Fin n, u ≠ v → ∃ p : ℕ, σ.mem (table2Addr n u v) = p ∧
    IsSecondMincut F u v (cutAt n σ.mem p) ∧ σ.rmem (lam2Addr n u v) = lam2 F u v

end MSTCuts2027.Parallel.Supplement


