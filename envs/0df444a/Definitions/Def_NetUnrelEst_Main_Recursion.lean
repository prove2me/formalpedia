-- Prove2me | Definitions.Def_NetUnrelEst_Main_Recursion
-- name    : NetUnrelEst_Main_Recursion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:15:26.175517+00:00
-- url     : https://prove2.me/theorems/c506db9d-a3c1-442d-ac35-3be13ec64709
-- title:
--   Algorithm 2.1 (recursion on the remaining event) with an arbitrary cut rule, and its extended random path
-- statement:
--   **Setting.** Edges fail independently with probabilities $q_e\in[0,1]$ (the initial product law $\mu$). Contraction times $0=t_0<t_1<\dots<t_h=1$ are fixed in advance. At time $\tau=t_j$ the current graph $J$ is described by the set $S$ of arrived edges: an arrived edge works, and an unarrived edge fails by time one with conditional probability $q_e^{1-\tau}$. Contracting from $\tau$ to $\tau'$ adds each unarrived edge independently with probability $1-q_e^{\tau'-\tau}$. $D$ is disconnection; for a set $A$ of stored cuts, $A$ also denotes the event that some stored cut has all its edges failed.
--
--   A **cut rule** maps the level $j$, the arrived set and the stored cuts to a law on cuts (its fresh randomness); it is valid when it returns a cut of $J$ (a cut of $G$ crossed by no arrived edge) whenever $J$ has at least two vertices. A cut is a **minimum cut of the current graph** for capacities $c_e$ when it minimizes $\sum_{e\text{ crosses }C}c_e$ among the cuts of $J$.
--
--   **Algorithm 2.1.** A call at level $j$ with arrived set $S$ and stored cuts $A$ returns $R$:
--   1. if $J$ has one vertex, $R=0$; at time one, $R=\mathbf 1_{D\setminus A}$ of the final state;
--   2. if the edges of $J$ that may still work do not connect $J$, sample the remaining states and return $\mathbf 1_{D\setminus A}$;
--   3. draw a cut $C$ from the rule, put $a=\mu(A_C)$, sample a state $X$ with the edges of $C$ failing and the others by the current law, and set $M=a\,\mathbf 1\{X\notin A\}$;
--   4. contract twice independently through $t_{j+1}$, call the recursion on both graphs with stored cuts $A\cup\{C\}$, and return
--   $$R=M+\frac{R_1+R_2}{2}.$$
--
--   $W$ is the return of the call at time zero with $A=\emptyset$ and a given initial arrived set ($\emptyset$ in Lemma 2.2).
--
--   **Extended random path.** Follow a uniformly random root path of the full binary tree, continuing the edge observations below terminated calls. At depth $j$, $U_j$ is the conditional unreliability of the current graph and $r_j$ its conditional probability of disconnection outside the stored union before the cut at depth $j$ is chosen, with $r_j=0$ once the path's call has terminated.
--
--   **Formalization Note.** Every law is a finite `PMF`; means are integrals against `PMF.toMeasure`. Since the two children of a call have the same conditional law, the path is one trajectory: at each level a cut is added if the call is alive and does not terminate, and the contraction is applied in either case. The law of $W$ at level $h-k$ is defined by recursion on $k$.
-- source:
--   Sun, Near-Linear Estimation of Network Unreliability, STOC 2027 submission, doi:10.5281/zenodo.23913531 (PDF sha256 eee2585a…), pp. 8–10, §2.1–§2.3 (Algorithm 2.1); p. 20, §3.4

import Mathlib
import Definitions.Def_NetUnrelDesign_Main_Model
import Definitions.Def_NetUnrelEst_Main_CutSums

open scoped BigOperators Classical

noncomputable section

namespace NetUnrelEst.Main

open NetUnrelDesign.Main

/-!
# Algorithm 2.1 (recursion on the remaining event) and its extended random path

Mu-Xia Sun, *Near-Linear Estimation of Network Unreliability* (STOC 2027 submission),
doi:10.5281/zenodo.23913531, §2.1–§2.3 (pp. 8–10), §3.4 (p. 20).

All laws are finite and written as `PMF`s; `pmfMean P = ∫ x ∂P` for a law `P` on `ℝ`.

* `bern p`: a Bernoulli bit, `true` with probability `p` (clamped to `[0, 1]`). `indepSet q`: the
  random set of indices `e` drawn independently with probability `q e`; its law at `F` is
  `configProb q F`.
* **Product law and contraction.** The initial product law has failure probabilities `q`. Fixed
  times `0 = t 0 < t 1 < ⋯ < t h = 1` (`TimeSeq h t`). A call at time `τ = t j` knows the set
  `S` of edges that have arrived (are connected); an edge `e ∉ S` fails by time one with
  conditional probability `q_e^{1−τ}` (`condFail q τ S`), an arrived edge works. Contracting from
  `τ` to `τ'` adds each `e ∉ S` independently with probability `1 − q_e^{τ'−τ}` (`contract`).
* `InUnion ends A F`: the failure set `F` lies in the stored union `A = ⋃_{C ∈ A} A_C` (some stored
  cut has all its edges in `F`); `remInd ends A F = 1_{D ∖ A}(F)`.
* `OneVertex ends S`: the arrived edges connect every vertex (the current graph `J` has one
  vertex). `CannotConnect ends q τ S`: the edges of `J` that may still work (conditional failure
  probability `< 1`) do not connect `J`.
* A **cut rule** maps the level `j`, the arrived set `S` and the stored union `A` to a law on
  cuts (its fresh randomness); `ValidRule` asks that, whenever `J` has at least two vertices, it
  returns cuts of `J`: cuts of `G` crossed by no arrived edge. `IsMinCurrentCut ends c S C`: `C` is
  a minimum cut of the current graph `J` for edge capacities `c` (among the cuts of `J`).
* `ret … k S A` is the law of the return `R` of Algorithm 2.1 at level `j = h − k` with arrived set
  `S` and stored union `A`:
  1. if `J` has one vertex return `0`; at time one (`k = 0`) return `1_{D∖A}` of the final state
     (unarrived edges fail);
  2. if the edges that may still work do not connect `J`, sample the remaining edge states and
     return `1_{D∖A}`;
  3. draw a cut `C` from the rule; `a = µ(A_C)` (product of the conditional failure probabilities
     over `C`); sample `X` with the edges of `C` failing and the others failing by the current law;
     `M = a·1{X ∉ A}`;
  4. contract twice independently through `t (j+1)`, recurse on both with stored union `A ∪ {C}`
     and return `M + (R₁ + R₂)/2`.
  `retLaw … S₀ = ret … h S₀ ∅` starts at time zero with arrived set `S₀` and `A = ∅`.
* **Extended random path.** `pathLaw … j` is the law of `(S_j, A_j, alive_j)` along a uniformly
  random root path of the full binary tree, with observations continued below terminated calls:
  at level `j`, if the call is alive and does not terminate, a cut is drawn and added to the stored
  union; otherwise the path is no longer alive; then the next contraction is applied in either
  case. (Both children of a call have the same conditional law, so one trajectory suffices.)
  `pathU = U_j`, the conditional unreliability of the current graph; `pathR = r_j`, its
  conditional probability of disconnection outside the stored union, `0` once the path's call has
  terminated. `pathMoment … j = E(U_j r_j)`.
-/

/-- The mean of a law on `ℝ`. -/
def pmfMean (P : PMF ℝ) : ℝ := ∫ x, x ∂P.toMeasure

/-- The second moment of a law on `ℝ`. -/
def pmfSecondMoment (P : PMF ℝ) : ℝ := ∫ x, x ^ 2 ∂P.toMeasure

/-- A Bernoulli bit, `true` with probability `p` (clamped to `[0, 1]`). -/
def bern (p : ℝ) : PMF Bool := PMF.bernoulli (min (Real.toNNReal p) 1) (min_le_right _ _)

/-- Independent bits with probabilities `q`. -/
def indepBits : (m : ℕ) → (Fin m → ℝ) → PMF (Fin m → Bool)
  | 0, _ => PMF.pure fun i => i.elim0
  | m + 1, q => (bern (q 0)).bind fun b =>
      (indepBits m fun i => q i.succ).map fun r => (Fin.cons b r : Fin (m + 1) → Bool)

/-- The random set of indices `e`, each included independently with probability `q e`. -/
def indepSet {m : ℕ} (q : Fin m → ℝ) : PMF (Finset (Fin m)) :=
  (indepBits m q).map fun r => Finset.univ.filter fun e => r e = true

/-- `0 = t 0 < t 1 < ⋯ < t h = 1`. -/
def TimeSeq (h : ℕ) (t : ℕ → ℝ) : Prop :=
  t 0 = 0 ∧ t h = 1 ∧ ∀ j < h, t j < t (j + 1)

/-- Conditional failure probabilities at time `τ` with arrived set `S`. -/
def condFail {m : ℕ} (q : Fin m → ℝ) (τ : ℝ) (S : Finset (Fin m)) : Fin m → ℝ :=
  fun e => if e ∈ S then 0 else q e ^ (1 - τ)

/-- Contraction from `τ` to `τ'`: each unarrived edge arrives with probability `1 − q_e^{τ'−τ}`. -/
def contract {m : ℕ} (q : Fin m → ℝ) (τ τ' : ℝ) (S : Finset (Fin m)) : PMF (Finset (Fin m)) :=
  (indepSet fun e => if e ∈ S then 0 else 1 - q e ^ (τ' - τ)).map fun N => S ∪ N

/-- The failure set `F` lies in the union of the stored cut-failure events. -/
def InUnion {n m : ℕ} (ends : Ends n m) (A : Finset (Cut n)) (F : Finset (Fin m)) : Prop :=
  ∃ C ∈ A, crossSet ends C ⊆ F

/-- `1_{D ∖ A}(F)`. -/
def remInd {n m : ℕ} (ends : Ends n m) (A : Finset (Cut n)) (F : Finset (Fin m)) : ℝ :=
  if Disconnected ends F ∧ ¬ InUnion ends A F then 1 else 0

/-- The current graph has one vertex: the arrived edges connect every vertex. -/
def OneVertex {n m : ℕ} (ends : Ends n m) (S : Finset (Fin m)) : Prop :=
  (workingGraph ends (Finset.univ \ S)).Connected

/-- The edges of the current graph that may still work do not connect it. -/
def CannotConnect {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) (τ : ℝ) (S : Finset (Fin m)) :
    Prop :=
  ¬ (workingGraph ends (Finset.univ.filter fun e => 1 ≤ condFail q τ S e)).Connected

/-- A cut rule: a law on cuts from the level, the arrived set and the stored union. -/
abbrev CutRule (n m : ℕ) := ℕ → Finset (Fin m) → Finset (Cut n) → PMF (Cut n)

/-- The rule returns a cut of the current graph whenever it has at least two vertices. -/
def ValidRule {n m : ℕ} (ends : Ends n m) (rule : CutRule n m) : Prop :=
  ∀ j S A, ¬ OneVertex ends S → ∀ C ∈ (rule j S A).support,
    C ∈ cuts n ∧ Disjoint (crossSet ends C) S

/-- `C` is a minimum cut of the current graph (arrived set `S`) for edge capacities `c`. -/
def IsMinCurrentCut {n m : ℕ} (ends : Ends n m) (c : Fin m → ℝ) (S : Finset (Fin m)) (C : Cut n) :
    Prop :=
  C ∈ cuts n ∧ Disjoint (crossSet ends C) S ∧
    ∀ C' ∈ cuts n, Disjoint (crossSet ends C') S →
      ∑ e ∈ crossSet ends C, c e ≤ ∑ e ∈ crossSet ends C', c e

/-- The law of the return of Algorithm 2.1 at level `h − k`, arrived set `S`, stored union `A`. -/
def ret {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) (h : ℕ) (t : ℕ → ℝ) (rule : CutRule n m) :
    ℕ → Finset (Fin m) → Finset (Cut n) → PMF ℝ
  | 0, S, A =>
      if OneVertex ends S then PMF.pure 0 else PMF.pure (remInd ends A (Finset.univ \ S))
  | k + 1, S, A =>
      if OneVertex ends S then PMF.pure 0
      else if CannotConnect ends q (t (h - (k + 1))) S then
        (indepSet (condFail q (t (h - (k + 1))) S)).map fun X => remInd ends A X
      else
        (rule (h - (k + 1)) S A).bind fun C =>
        (indepSet fun e => if Crosses ends C e then 1 else condFail q (t (h - (k + 1))) S e).bind
          fun X =>
        (contract q (t (h - (k + 1))) (t (h - (k + 1) + 1)) S).bind fun S₁ =>
        (contract q (t (h - (k + 1))) (t (h - (k + 1) + 1)) S).bind fun S₂ =>
        (ret ends q h t rule k S₁ (insert C A)).bind fun R₁ =>
        (ret ends q h t rule k S₂ (insert C A)).map fun R₂ =>
          cutFail ends (condFail q (t (h - (k + 1))) S) C * (if InUnion ends A X then 0 else 1) +
            (R₁ + R₂) / 2

/-- The law of the return `W` of Algorithm 2.1 started at time zero with arrived set `S₀` and
`A = ∅`. -/
def retLaw {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) (h : ℕ) (t : ℕ → ℝ) (rule : CutRule n m)
    (S₀ : Finset (Fin m)) : PMF ℝ :=
  ret ends q h t rule h S₀ ∅

/-- The law of `(S_j, A_j, alive_j)` along the extended random path. -/
def pathLaw {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) (t : ℕ → ℝ) (rule : CutRule n m)
    (S₀ : Finset (Fin m)) : ℕ → PMF (Finset (Fin m) × Finset (Cut n) × Bool)
  | 0 => PMF.pure (S₀, ∅, true)
  | j + 1 => (pathLaw ends q t rule S₀ j).bind fun st =>
      (if st.2.2 = true ∧ ¬ OneVertex ends st.1 ∧ ¬ CannotConnect ends q (t j) st.1 then
          (rule j st.1 st.2.1).map fun C => (insert C st.2.1, true)
        else PMF.pure (st.2.1, false)).bind fun Aa =>
      (contract q (t j) (t (j + 1)) st.1).map fun S' => (S', Aa.1, Aa.2)

/-- `U_j`: the conditional unreliability of the current graph at level `j`. -/
def pathU {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) (t : ℕ → ℝ) (j : ℕ)
    (st : Finset (Fin m) × Finset (Cut n) × Bool) : ℝ :=
  unrel ends (condFail q (t j) st.1)

/-- `r_j`: the conditional probability of disconnection outside the stored union, `0` once the
call on the path has terminated. -/
def pathR {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) (t : ℕ → ℝ) (j : ℕ)
    (st : Finset (Fin m) × Finset (Cut n) × Bool) : ℝ :=
  if st.2.2 = true then
    prob (condFail q (t j) st.1) fun F => Disconnected ends F ∧ ¬ InUnion ends st.2.1 F
  else 0

/-- `E(U_j r_j)` along the extended random path. -/
def pathMoment {n m : ℕ} (ends : Ends n m) (q : Fin m → ℝ) (t : ℕ → ℝ) (rule : CutRule n m)
    (S₀ : Finset (Fin m)) (j : ℕ) : ℝ :=
  pmfMean ((pathLaw ends q t rule S₀ j).map fun st =>
    pathU ends q t j st * pathR ends q t j st)

end NetUnrelEst.Main


