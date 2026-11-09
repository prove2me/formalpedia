-- Prove2me | Definitions.Def_LinMatroidSecretary_Online_Algorithm
-- name    : LinMatroidSecretary_Online_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:49.963209+00:00
-- url     : https://prove2.me/theorems/4c88c509-de39-4ec3-af8a-9fa288b58c60
-- title:
--   Algorithms 1–2 — the Linear Matroid Secretary policy with the label-free table (µ_Y, p_Y)
-- statement:
--   Algorithm 1 (Linear Matroid Secretary) with its subroutine UpdateDistributions (Algorithm 2), for a sample size $k$.
--
--   1. **The table.** For every set $Y$ of observed elements the algorithm stores $(\mu_Y,p_Y)$. If $|Y|\le k$, $\mu_Y$ is the point mass at the zero subspace and $p_Y=0$. If $|Y|>k$, the distributions $\mu_{Y-f}$, $f\in Y$, are computed first (recursively, by increasing size); then $p_Y$ is the solution of $\mathrm{LP}(Y)$ selected by a rule fixed a priori: a rational feasible solution whenever one exists, otherwise any feasible solution (and $0$ if $\mathrm{LP}(Y)$ were infeasible); finally $\mu_Y$ is computed from $p_Y$ and the $\mu_{Y-f}$ by (2).
--
--   2. **Label-free computation.** As the paper requires, $(\mu_Y,p_Y)$ depends only on the data revealed for the elements of $Y$ — their vectors and their relative value order — and not on their labels or on the order in which they arrived. It is therefore computed from the vectors of $Y$ listed in increasing value order, and the variables $p_Y(e,W)$ are indexed by the rank of $e$ in $Y$. For a labelled set $Y\subseteq R$, $\mu_Y$ and $p_Y(e,W)$ are read off from this list ($p_Y(e,W)$ at the rank of $e$).
--
--   3. **The policy.** At each arrival, with $X$ the set observed so far (including the arriving element $e$): if $|X|\le k$, $e$ is rejected (the sample); otherwise $e$ is accepted with probability $p_X(e,\langle\mathrm{ALG}\rangle)$, where $\langle\mathrm{ALG}\rangle$ is the span of the vectors accepted so far. The policy reads only the observed vectors, their relative order and its own past decisions.
--
--   This is the algorithm analysed in Lemma 3 and, with $k=\lfloor n/e\rfloor$ for $n\ge3$, the algorithm behind Theorem 1.
--
--   **Formalization Note** The rule "rational if possible" is a classical choice among feasible points. Feasible points are represented by functions vanishing outside the variables of $\mathrm{LP}(Y)$ (pairs with $W\notin\operatorname{supp}\mu_{Y-f}$), which changes no LP. The removal of the element of rank $j$ is the list with position $j$ deleted, which is again sorted. The rank of an observed element is read from the comparison pattern.
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), §2.2, Algorithm 1 and Algorithm 2, and the fixed choice rule (PDF pp. 10–11, printed pp. 8–9); the conventions for |Y| ≤ k in §2.1 (PDF p. 7, printed p. 5)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting
import Definitions.Def_LinMatroidSecretary_Online_DimensionLP

/-!
# Algorithm 1 (Linear Matroid Secretary) with UpdateDistributions (Algorithm 2)

Bérczi, Dughmi, Livanos, Soto, Verdugo, *The Strong Secretary Conjecture is True for Linear
Matroids*, STOC 2027 submission #608, §2.1–§2.2 (PDF pp. 7–11), for a sample size `k`.

**Label-free table.** The pair `(µ_Y, p_Y)` "depends only on `Y` and the data revealed for its
elements, and not on the order in which the elements of `Y` arrived" (PDF p. 10/8). It is
therefore computed from the vectors of `Y` listed in increasing value order,
`l : Fin m → (Fin d → F)` (position `j` holds the `(j+1)`-st smallest element of `Y`), and the
LP variables are indexed by positions. The subset `Y − f` of the `j`-th element is the list
`l ∘ j.succAbove`, which is again sorted.

**Fixed choice rule** (PDF p. 10/8). Among the feasible solutions of `LP(Y)` (variables
`p(e, W)` for `W ∈ supp µ_{Y−e}` only, represented by a function vanishing off those supports)
a rational one is chosen whenever one exists, otherwise any feasible one; the value `0` is
returned only if `LP(Y)` is infeasible.
-/

namespace LinMatroidSecretary.Online

open Finset

noncomputable section

variable {F : Type*} [Field F] {d : ℕ}

/-- A table entry for a set of `m` elements: `µ_Y` and `p_Y` (indexed by positions). -/
structure Entry (F : Type*) [Field F] (d m : ℕ) where
  μ : Dist F d
  p : Fin m → Submodule F (Fin d → F) → ℝ

/-- The fixed choice rule applied to `LP(Y)` for the sorted vector list `l` of `Y` (all of
`Fin m`), sample size `k`, and children `μ j = µ_{Y − (j-th element)}`. -/
def chooseP (k m : ℕ) (l : Fin m → Fin d → F) (μ : Fin m → Dist F d) :
    Fin m → Submodule F (Fin d → F) → ℝ := by
  classical
  exact
    let feas : (Fin m → Submodule F (Fin d → F) → ℝ) → Prop := fun p =>
      LPFeasible l Finset.univ k μ p ∧ ∀ j W, W ∉ (μ j).support → p j W = 0
    if h : ∃ p, feas p ∧ ∀ j W, ∃ q : ℚ, p j W = (q : ℝ) then Classical.choose h
    else if h' : ∃ p, feas p then Classical.choose h' else 0

/-- `UpdateDistributions` as a recursion on the size of `Y` (PDF pp. 9–11): for `|Y| ≤ k`,
`µ_Y` is the point mass at `{0}` and `p_Y = 0`; for `|Y| > k`, `p_Y` is the fixed choice of a
solution of `LP(Y)` built from the children `µ_{Y−f}`, and `µ_Y` is given by (2). -/
def tbl (k : ℕ) : (m : ℕ) → (Fin m → Fin d → F) → Entry F d m
  | 0, _ => ⟨Finsupp.single ⊥ 1, 0⟩
  | m + 1, l =>
    if m + 1 ≤ k then ⟨Finsupp.single ⊥ 1, 0⟩
    else
      let μ : Fin (m + 1) → Dist F d := fun j => (tbl k m (l ∘ j.succAbove)).μ
      let p := chooseP k (m + 1) l μ
      ⟨muY l Finset.univ μ p, p⟩

variable {R : Type*} [Fintype R] [LinearOrder R]

/-- The vectors of a set `Y ⊆ R` listed in increasing value order. -/
def sortedVecs (v : R → Fin d → F) (Y : Finset R) : Fin Y.card → Fin d → F :=
  fun j => v (Y.orderEmbOfFin rfl j)

/-- The table entry `(µ_Y, p_Y)` of a labelled set `Y ⊆ R`. -/
def tblSet (v : R → Fin d → F) (k : ℕ) (Y : Finset R) : Entry F d Y.card :=
  tbl k Y.card (sortedVecs v Y)

/-- `µ_Y` for a labelled set `Y ⊆ R`. -/
def muSet (v : R → Fin d → F) (k : ℕ) (Y : Finset R) : Dist F d := (tblSet v k Y).μ

/-- `p_Y(e, W)` for a labelled set `Y ⊆ R` (read at the rank of `e` in `Y`; `0` if `e ∉ Y`). -/
def pSet (v : R → Fin d → F) (k : ℕ) (Y : Finset R) (e : R) (W : Submodule F (Fin d → F)) : ℝ :=
  if h : e ∈ Y then (tblSet v k Y).p ((Y.orderIsoOfFin rfl).symm ⟨e, h⟩) W else 0

/-- The rank of the `j`-th observed element among the observed elements (number of observed
elements ranked below it), read from the comparison pattern. -/
def rankObs {t : ℕ} (cmp : Fin (t + 1) → Fin (t + 1) → Bool) (j : Fin (t + 1)) : Fin (t + 1) :=
  ⟨(univ.filter fun j' => cmp j' j = true).card % (t + 1), Nat.mod_lt _ (Nat.succ_pos t)⟩

/-- The observed vectors listed in increasing value order, read from the comparison pattern. -/
def sortedObs {t : ℕ} (vs : Fin (t + 1) → Fin d → F) (cmp : Fin (t + 1) → Fin (t + 1) → Bool) :
    Fin (t + 1) → Fin d → F := by
  classical
  exact fun r => if h : ∃ j, rankObs cmp j = r then vs (Classical.choose h) else 0

/-- Algorithm 1 with sample size `k` (PDF p. 10/8), as an ordinal online policy: at step `t`
the observed set `X` has `t + 1` elements; if `|X| ≤ k` the arriving element is rejected,
otherwise it is accepted with probability `p_X(e, ⟨ALG⟩)`, where `e` is the arriving element
(read at its rank in `X`) and `⟨ALG⟩` is the span of the vectors accepted so far. -/
def alg1 {n : ℕ} (k : ℕ) : Policy n d F where
  accept t vs cmp b :=
    if t + 1 ≤ k then 0
    else (tbl k (t + 1) (sortedObs vs cmp)).p (rankObs cmp (Fin.last t))
      (Submodule.span F (Set.range fun j : {j : Fin t // b j = true} => vs j.1.castSucc))

end

end LinMatroidSecretary.Online


