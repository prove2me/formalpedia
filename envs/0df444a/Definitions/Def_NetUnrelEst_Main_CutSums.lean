-- Prove2me | Definitions.Def_NetUnrelEst_Main_CutSums
-- name    : NetUnrelEst_Main_CutSums
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:13:56.770492+00:00
-- url     : https://prove2.me/theorems/dcaee864-019e-4748-884b-1e646cadeaf9
-- title:
--   Cut-failure products a_C, the cut sums z, z_θ, the ordered pair sum x, and the reduced input
-- statement:
--   The network is a multigraph on the vertices $\{0,\dots,n-1\}$ with $m$ labelled edges; edge $e$ fails independently with probability $p_e\in[0,1]$ (the published model `NetUnrelDesign_Main_Model`). A **cut** $C$ is a nontrivial bipartition $\{S,V\setminus S\}$ with the two shores identified, and an edge crosses $C$ when its endpoints lie on different shores.
--
--   - For an edge set $B$, $a_B=\prod_{e\in B}p_e$. For a cut, $a_C=\prod_{e\text{ crosses }C}p_e$ is the probability that every edge of $C$ fails, and $a_{C\cup C'}$ is the product over the edges crossing $C$ or $C'$, the probability that both cuts fail.
--   - The cut sums are
--   $$z=\sum_C a_C,\qquad z_\theta=\sum_C a_C^{\theta},\qquad x=\sum_{C\neq C'}a_{C\cup C'},\qquad \sum_{C\neq C'}a_{C\cup C'}^{\theta},$$
--   where the pair sums run over **ordered** pairs of distinct cuts.
--   - The number of failed cuts of a failure set $F$ is the number of cuts all of whose edges lie in $F$.
--   - The weights (capacities) are $w_e=-\log p_e$, and $\lambda=\min_C\sum_{e\text{ crosses }C}w_e$ is the minimum cut.
--   - The **reduced input** of §2.1 is a connected graph with $n\ge2$ vertices, no self-loops, no two edges with the same endpoints, and $0<p_e<1$ for every edge.
--
--   These are the quantities of the paper's cut-intersection theorem (Theorem 2.3) and of its hypercontractive pair bound (Lemma 3.1).
--
--   **Formalization Note.** $a_C$ is a product of the $p_e$, not $e^{-w(C)}$, so it is correct when some $p_e\in\{0,1\}$. Real powers $a^\theta$ are `Real.rpow`. A cut is the unordered pair `s(S, Sᶜ)` of the reused model, so each bipartition appears once; ordered pairs of distinct cuts are enumerated as $C$ and then $C'\neq C$.
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), p. 8, §2.1; p. 10, §2.3; p. 14, §3.1

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model

open scoped BigOperators Classical

noncomputable section

namespace NetUnrelEst.Main

open NetUnrelDesign.Main

/-!
# Cut-failure products, the cut sums `z`, `z_θ` and the ordered pair sum `x`

Mu-Xia Sun, *Near-Linear Estimation of Network Unreliability* (STOC 2027 submission),
doi:10.5281/zenodo.23913531, §2.1 (p. 8), §2.3 (p. 10), §3.1 (p. 14).

The network is the published `NetUnrelDesign.Main` model: a multigraph `ends : Ends n m`, edge
`e` failing independently with probability `p e`, cuts `s(S, Sᶜ)` with shores identified.

* `crossSet ends C` is the set of edges crossing the cut `C`.
* `failProd p B = a_B = ∏_{e ∈ B} p_e`; `cutFail ends p C = a_C = ∏_{e crosses C} p_e`, the
  probability that every edge of `C` fails (a product, valid also when some `p_e ∈ {0, 1}`).
* `pairFail ends p C C' = a_{C ∪ C'}`, the product over the union of the two crossing sets.
* `zSum = z = Σ_C a_C`; `zTheta θ = z_θ = Σ_C a_C^θ` (real power).
* `xSum = x = Σ_{C ≠ C'} a_{C ∪ C'}` over **ordered** pairs of distinct cuts;
  `xTheta θ = Σ_{C ≠ C'} a_{C ∪ C'}^θ`.
* `numFailedCuts ends F` is the number of cuts all of whose edges lie in the failure set `F`.
* `wOf p = (−log p_e)_e` are the weights (capacities) and `lam ends p = λ = min_C w(C)`.
* `IsReduced ends p`: the reduced input of §2.1 (p. 8): a connected graph with `n ≥ 2` vertices,
  no self-loops, no two edges with the same endpoints, and `0 < p_e < 1` for every edge.
-/

/-- The edges crossing the cut `C`. -/
def crossSet {n m : ℕ} (ends : Ends n m) (C : Cut n) : Finset (Fin m) :=
  Finset.univ.filter fun e => Crosses ends C e

/-- `a_B = ∏_{e ∈ B} p_e`. -/
def failProd {m : ℕ} (p : Fin m → ℝ) (B : Finset (Fin m)) : ℝ := ∏ e ∈ B, p e

/-- `a_C = ∏_{e crosses C} p_e`. -/
def cutFail {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) (C : Cut n) : ℝ :=
  failProd p (crossSet ends C)

/-- `a_{C ∪ C'}`: the product over the edges crossing `C` or `C'`. -/
def pairFail {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) (C C' : Cut n) : ℝ :=
  failProd p (crossSet ends C ∪ crossSet ends C')

/-- `z = Σ_C a_C`. -/
def zSum {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) : ℝ :=
  ∑ C ∈ cuts n, cutFail ends p C

/-- `z_θ = Σ_C a_C^θ`. -/
def zTheta {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) (θ : ℝ) : ℝ :=
  ∑ C ∈ cuts n, cutFail ends p C ^ θ

/-- `x = Σ_{C ≠ C'} a_{C ∪ C'}`, over ordered pairs of distinct cuts. -/
def xSum {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) : ℝ :=
  ∑ C ∈ cuts n, ∑ C' ∈ (cuts n).erase C, pairFail ends p C C'

/-- `Σ_{C ≠ C'} a_{C ∪ C'}^θ`, over ordered pairs of distinct cuts. -/
def xTheta {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) (θ : ℝ) : ℝ :=
  ∑ C ∈ cuts n, ∑ C' ∈ (cuts n).erase C, pairFail ends p C C' ^ θ

/-- The number of cuts that fail in the failure set `F` (all their edges lie in `F`). -/
def numFailedCuts {n m : ℕ} (ends : Ends n m) (F : Finset (Fin m)) : ℕ :=
  ((cuts n).filter fun C => crossSet ends C ⊆ F).card

/-- Weights (capacities) `w_e = −log p_e`. -/
def wOf {m : ℕ} (p : Fin m → ℝ) : Fin m → ℝ := fun e => -Real.log (p e)

/-- `λ`: the minimum cut capacity in the weights `w_e = −log p_e`. -/
def lam {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) : ℝ := minCut ends (wOf p)

/-- The reduced input of §2.1: connected, `n ≥ 2`, no loops, no parallel edges, `0 < p_e < 1`. -/
def IsReduced {n m : ℕ} (ends : Ends n m) (p : Fin m → ℝ) : Prop :=
  2 ≤ n ∧ IsConnectedGraph ends ∧ (∀ e, (ends e).1 ≠ (ends e).2) ∧
    (∀ e e', e ≠ e' → Sym2.mk (ends e) ≠ Sym2.mk (ends e')) ∧ ∀ e, 0 < p e ∧ p e < 1

end NetUnrelEst.Main


