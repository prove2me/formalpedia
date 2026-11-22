-- Prove2me | Definitions.Def_SamplingLLL_Supplement_r2Data
-- name    : SamplingLLL_Supplement_r2Data
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:47:43.241438+00:00
-- url     : https://prove2.me/theorems/e0f1b628-d946-4908-a265-c323b2ff6693
-- title:
--   The radius-two sampler and FPRAS of Appendix H
-- statement:
--   The explicit procedures of the proof of Theorem 2.4, for a product-space CSP with exact one-event access. They run the packet circuit and scalar factory of Appendix A (the base mission's `Circuit` and `Factory`) with the following data, at the endpoint $p=1/(8Q)$.
--
--   1. **Search.** For the task of inserting $c$ into a family $S$: start with $T=\{c\}$ and repeatedly query the least unqueried event of the task family outside $N_H[T]$ at $H$-distance two from a member of $T$, adding it on a yes answer. $F_T$ is the set of unqueried $H$-neighbours of $T$, $D_T=(T\setminus\{c\})\cup\{\text{queried no}\}\cup F_T$, and $W_T=\mathrm{vbl}(T\cup F_T)$.
--   2. **Budget.** $B=4p=1/(2Q)$ and $s=1-B$.
--   3. **Proposal (E4).** With $R_2=Q-1$: a plane Galton–Watson tree with offspring law $P(K=j)=\tfrac35(\tfrac25)^j$, each non-root vertex mapped to a uniform slot among $R_2$ padded $H^2$-neighbour slots of its parent; padding, repetitions, images outside the task family, non-independent images and non-canonical encodings are rejected. A valid record of size $t$ has probability $(3/5)^t\,(2/(5R_2))^{t-1}$. If $R_2=0$ the proposal is the singleton root with probability one.
--   4. **Local operation.** Thin by $u_T/[B\,q(T)\,s^{|D_T|}]$ with $u_T=\prod_{b\in T}\lambda(\mathrm{Bad}_b)$; draw the events of $T$ from their one-event conditional laws; fill the remaining variables of $F_T$ from $\lambda$; keep the record only if every event of $F_T$ is satisfied.
--   5. **Sampler and FPRAS.** The sampler draws from $\lambda$ by coordinate draws and inserts the constraints one at a time in index order. The FPRAS is the product estimator of p.25 with the base copy count, under a work cap $K_0\,((L+\ell(\varepsilon)+1)\lceil 1/\varepsilon\rceil)^d$.
--
--   A weight triple selects what the call counter counts: recursive invocations (insertion kernel, deletion kernel, reciprocal coin), constraint evaluations, or one-event-access calls. Theorem 2.4 reads each count by setting one weight to $1$.
--
--   **Formalization Note** Each constraint evaluation and each oracle call is charged one tick for issuing it and is counted in the call counter under the weights; all other work is charged to the tick counter by the base charge table, with $L$ the input length.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 2.4, p.8; Appendix H, pp.70–72; (E4), p.71; proof of Theorem 5.1, p.25

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_RCSP

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-- Weights of the call counter: a recursive invocation (insertion kernel, deletion kernel, reciprocal
coin) counts `recs`, a constraint evaluation counts `evals`, a one-event-access oracle call counts
`accs`.
The theorem reads each count by setting one weight to `1` and the others to `0`. -/
structure CW where
  /-- Weight of a recursive invocation. -/
  recs : ℕ
  /-- Weight of a constraint evaluation. -/
  evals : ℕ
  /-- Weight of a one-event-access call. -/
  accs : ℕ

/-- Count recursive invocations. -/
def CW.recW : CW := ⟨1, 0, 0⟩
/-- Count constraint evaluations. -/
def CW.evalW : CW := ⟨0, 1, 0⟩
/-- Count one-event-access calls. -/
def CW.accW : CW := ⟨0, 0, 1⟩

namespace RCSP

variable {n m : ℕ} (P : RCSP n m) (O : P.Access)

/-! # The radius-two endpoint: the procedure of Appendix H

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), Theorem 2.4, p.8; proof in Appendix H, pp.70–72, on the execution machinery of Appendix A
and the proof of Theorem 5.1 (pp.19–25). -/

/-- One constraint evaluation: one tick for issuing it, one evaluation call. -/
noncomputable def evalAt (w : CW) (a : Fin m) (x : P.Config) : Proc Bool := do
  tick 1
  countCall w.evals
  pure (P.bad a x)

/-- One draw from `λ_v`: one tick, one access call. -/
noncomputable def drawV (w : CW) (v : Fin n) : Proc (Fin (P.dom v + 1)) := do
  tick 1
  countCall w.accs
  O.coord v

/-- One draw from `λ(· | Bad_b)`: one tick, one access call. -/
noncomputable def drawCond (w : CW) (b : Fin m) : Proc P.Config := do
  tick 1
  countCall w.accs
  O.cond b

/-- Redraw the variables of a list from the product law by coordinate draws. -/
noncomputable def oredraw (w : CW) : List (Fin n) → P.Config → Proc P.Config
  | [], x => pure x
  | v :: l, x => do
    let u ← P.drawV O w v
    oredraw w l (Function.update x v u)

/-- The radius-two search of Appendix H, p.70, for the task `(S, c)`: query the least unqueried event of
`S` outside `N_H[T]` at `H`-distance two from some member of `T`. -/
def r2Next (S : Finset (Fin m)) (_c : Fin m) : NextQuery m := fun Y N =>
  (List.finRange m).find? fun b =>
    decide (b ∈ S ∧ b ∉ Y ∧ b ∉ N ∧ (∀ a ∈ Y, ¬ P.H.Adj a b) ∧ ∃ a ∈ Y, P.DistTwo a b)

/-- `F_T`: the unqueried `H`-neighbours of `T` in the task family (p.70). -/
def r2F (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : Finset (Fin m) :=
  (insert c S).filter fun d => d ∉ t.1 ∧ d ∉ t.2 ∧ ∃ y ∈ t.1, P.H.Adj y d

/-- `R_T`: the unqueried events outside `N_H[T]` (p.70). -/
def r2R (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : Finset (Fin m) :=
  (insert c S).filter fun d => d ∉ t.1 ∧ d ∉ t.2 ∧ ¬ ∃ y ∈ t.1, P.H.Adj y d

/-- `D_T = (T ∖ {c}) ∪ (queried no) ∪ F_T`, in index order (p.70). -/
def r2D (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : List (Fin m) :=
  (List.finRange m).filter fun d => d ∈ t.1.erase c ∪ t.2 ∪ P.r2F S c t

/-- `W_T = vbl(T ∪ F_T)` (p.70). -/
def r2W (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : Finset (Fin n) :=
  (t.1 ∪ P.r2F S c t).biUnion P.vbl

/-- The ordered child tasks of the record `t`. -/
def r2Children (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : List (Finset (Fin m) × Fin m) :=
  chain (P.r2D S c t) (P.r2R S c t)

/-- The budget `B = 4p` with the algorithmic `p = 1/(8Q)` (p.70–71). -/
def r2B : ℚ := 1 / (2 * P.Q)

/-- The padded `H²`-neighbour slots of `a`: the events at `H`-distance one or two from `a`, in index
order; slots beyond the list are padding. -/
def nbrs (a : Fin m) : List (Fin m) :=
  (List.finRange m).filter fun b => decide (b ≠ a ∧ (P.H.Adj a b ∨ P.DistTwo a b))

/-- The children of one vertex of the Galton–Watson tree (E4), p.71: offspring `K` with
`P(K = j) = (3/5)(2/5)^j`, each child mapped to a uniform slot among `R₂` padded `H²`-neighbour slots of its
parent. Padding, a repetition, or an image outside the task family rejects (`none`). -/
noncomputable def gwKids (L R₂ : ℕ) (C : Finset (Fin m)) (a : Fin m) :
    ℕ → List (Fin m) → Finset (Fin m) → Proc (Option (List (Fin m) × Finset (Fin m)))
  | 0, _, _ => pure none
  | k + 1, kids, used => do
    tick L
    let more ← ratCoin (2 / 5)
    if more then do
      let j ← uniformFin (R₂ - 1)
      match (P.nbrs a)[(j : ℕ)]? with
      | none => pure none
      | some b =>
        if b ∈ C ∧ b ∉ used then gwKids L R₂ C a k (kids ++ [b]) (insert b used) else pure none
    else pure (some (kids, used))

/-- The Galton–Watson tree in breadth-first order: the generated plane tree as the list of each vertex
with its ordered children, and the set of images. -/
noncomputable def gwTree (L R₂ : ℕ) (C : Finset (Fin m)) :
    ℕ → List (Fin m) → Finset (Fin m) → List (Fin m × List (Fin m)) →
      Proc (Option (Finset (Fin m) × List (Fin m × List (Fin m))))
  | 0, _, _, _ => pure none
  | _ + 1, [], used, st => pure (some (used, st))
  | k + 1, a :: qu, used, st => do
    match ← P.gwKids L R₂ C a (m + 1) [] used with
    | none => pure none
    | some (kids, used') => gwTree L R₂ C k (qu ++ kids) used' (st ++ [(a, kids)])

/-- The canonical rooted spanning tree of `T` in `H²` (p.71), breadth first from `c`, each vertex's
children being its undiscovered `H²`-neighbours in `T`, in slot order. -/
def canon (T : Finset (Fin m)) : ℕ → List (Fin m) → Finset (Fin m) → List (Fin m × List (Fin m))
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | k + 1, a :: qu, disc =>
    let kids := (P.nbrs a).filter fun b => decide (b ∈ T ∧ b ∉ disc)
    (a, kids) :: canon T k (qu ++ kids) (disc ∪ kids.toFinset)

/-- The proposal (E4), p.71. If `R₂ = Q − 1 = 0`, the singleton root with probability one. Otherwise
generate the Galton–Watson tree and reject nonindependent images and noncanonical encodings (and a set
the search would not accept); a valid record of size `t` has probability `(3/5)^t (2/(5R₂))^{t−1}`. -/
noncomputable def r2Propose (L : ℕ) (S : Finset (Fin m)) (c : Fin m) :
    Proc (Option (Leaf m × ℚ)) := do
  let R₂ := P.Q - 1
  if R₂ = 0 then do
    tick (L ^ 3)
    pure (some (leafOf (P.r2Next S c) c {c}, 1))
  else do
    match ← P.gwTree L R₂ (insert c S) (m + 1) [c] {c} [] with
    | none => pure none
    | some (T, st) =>
      tick ((m + 1) * L ^ 3)
      if (∀ a ∈ T, ∀ b ∈ T, ¬ P.H.Adj a b) ∧ st = P.canon T (m + 1) [c] {c} ∧
          (leafOf (P.r2Next S c) c T).1 = T then do
        let q ← charge (cmul (cpow (cq (3 / 5)) T.card)
          (cpow (cdiv (cq 2) (cmul (cq 5) (cq R₂))) (T.card - 1)))
        pure (some (leafOf (P.r2Next S c) c T, q))
      else pure none

/-- `acc ∏_{b∈l} λ(Bad_b)`, charged. -/
noncomputable def uProdR : List (Fin m) → ℚ → Proc ℚ
  | [], acc => pure acc
  | b :: l, acc => do
    let acc' ← qmul acc (O.pBad b)
    uProdR l acc'

/-- Draw the events of `T`, in index order, from their one-event conditional laws, writing each draw on
its scope (the scopes are disjoint). -/
noncomputable def drawEvents (w : CW) : List (Fin m) → P.Config → Proc P.Config
  | [], x => pure x
  | b :: l, x => do
    let y ← P.drawCond O w b
    drawEvents w l fun v => if v ∈ P.vbl b then y v else x v

/-- All members of a list are satisfied, by evaluations in order. -/
noncomputable def allGood (w : CW) (x : P.Config) : List (Fin m) → Proc Bool
  | [] => pure true
  | d :: l => do
    let b ← P.evalAt w d x
    if b then pure false else allGood w x l

/-- The exact local operation of Appendix H, p.70: thin by `u_T / [B q(T) s^{|D_T|}]`,
`u_T = ∏_{b∈T} λ(Bad_b)`, `s = 1 − B`; on success draw the events of `T` from their one-event conditional
laws, fill the remaining variables of `F_T` from the product law, and keep the record only if every event
of `F_T` is satisfied. -/
noncomputable def r2Local (w : CW) (L : ℕ) (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) (q : ℚ) :
    Proc (Option P.Config) := do
  tick (L ^ 3)
  let u ← P.uProdR O ((List.finRange m).filter fun b => b ∈ t.1) 1
  let B ← charge (cdiv (cq 1) (cmul (cq 2) (cq P.Q)))
  let s ← qsub 1 B
  let sD ← charge (cpow (cq s) (P.r2D S c t).length)
  let d0 ← qmul B q
  let den ← qmul d0 sD
  let ratio ← qdiv u den
  let keep ← ratCoin ratio
  if keep then do
    let x ← P.drawEvents O w ((List.finRange m).filter fun b => b ∈ t.1) fun _ => 0
    let y ← P.oredraw O w ((List.finRange n).filter fun v =>
      v ∈ (P.r2F S c t).biUnion P.vbl ∧ v ∉ t.1.biUnion P.vbl) x
    let ok ← P.allGood w y ((List.finRange m).filter fun d => d ∈ P.r2F S c t)
    if ok then pure (some y) else pure none
  else pure none

/-- The scalar factory of Appendix A.4 with the data of Appendix H. -/
noncomputable def r2Factory (w : CW) (L : ℕ) : Factory (Finset (Fin m) × Fin m) (Leaf m) P.Config where
  budget _ := P.r2B
  budgetCost _ := qcost 1 (2 * P.Q)
  sgn := sign
  kids i t := P.r2Children i.1 i.2 t
  propose i := P.r2Propose L i.1 i.2
  localOp i := P.r2Local O w L i.1 i.2

/-- The three recursive operations of a level. -/
structure RK where
  /-- Insertion kernel of the task `(S, c)`. -/
  insert : Finset (Fin m) → Fin m → P.Config → Proc P.Config
  /-- Deletion kernel of the task `(S, c)`. -/
  delete : Finset (Fin m) → Fin m → P.Config → Proc P.Config
  /-- Reciprocal coin of the task `(S, c)`. -/
  coin : Finset (Fin m) → Fin m → Proc Bool

/-- Deletion chain along a list of tasks. -/
noncomputable def delChain (K : P.RK) : List (Finset (Fin m) × Fin m) → P.Config → Proc P.Config
  | [], x => pure x
  | (A, d) :: l, x => do
    let y ← K.delete A d x
    delChain K l y

/-- Insertion chain along a list of tasks. -/
noncomputable def insChain (K : P.RK) : List (Finset (Fin m) × Fin m) → P.Config → Proc P.Config
  | [], x => pure x
  | (A, d) :: l, x => do
    let y ← K.insert A d x
    insChain K l y

/-- The packet circuit of Lemma A.6 for the task `(S, c)` with the data of Appendix H: the entry row
deletes `D_T` in reverse order and writes the mark on `W_T`; the exit row redraws `W_T` from `λ` and
reinserts `D_T`; the router is the last-defect router, evaluating every constraint of the target family. -/
noncomputable def r2Circuit (w : CW) (L : ℕ) (K : P.RK) (S : Finset (Fin m)) (c : Fin m) :
    Circuit P.Config (Leaf m) P.Config where
  good x := do
    let b ← P.evalAt w c x
    pure (!b)
  gen := (P.r2Factory O w L).generator (fun j => K.coin j.1 j.2) (S, c)
  neg t := decide (sign t = -1)
  enter t mark x := do
    let y ← P.delChain K (P.r2Children S c t).reverse x
    tick L
    pure fun v => if v ∈ P.r2W S c t then mark v else y v
  exit t x := do
    tick L
    let y ← P.oredraw O w ((List.finRange n).filter fun v => v ∈ P.r2W S c t) x
    P.insChain K (P.r2Children S c t) y
  route t x := do
    tick ((m + 1) * (1 + 2 * L ^ 3))
    countCall (w.evals * (insert c S).card)
    let B := P.badSet (insert c S) x
    if B = {c} then pure none else pure (some (routerLeaf (P.r2Next S c) c B t))
  resid _ := do
    tick ((m + 1) * L ^ 3)
    pure (leafOf (P.r2Next S c) c {c})

/-- The kernels at target-size level `k`, as in the base `ExecData.level`: each insertion, deletion and
coin invocation counts `w.recs` once on entry. -/
noncomputable def r2Level (w : CW) (L : ℕ) : ℕ → P.RK
  | 0 => ⟨fun _ _ _ _ => 0, fun _ _ _ _ => 0, fun _ _ _ => 0⟩
  | k + 1 =>
    { insert := fun S c x => do
        countCall w.recs
        (P.r2Circuit O w L (r2Level w L k) S c).forward x
      delete := fun S c x => do
        countCall w.recs
        (P.r2Circuit O w L (r2Level w L k) S c).backward x
      coin := fun S c =>
        (P.r2Factory O w L).coinAt (fun _ => w.recs) (fun j => (r2Level w L k).coin j.1 j.2) (S, c) }

/-- Sequential insertion in index order. -/
noncomputable def r2InsertAll (K : P.RK) : List (Fin m) → P.Config → Proc P.Config
  | [], x => pure x
  | i :: l, x => do
    let y ← K.insert (rootSet i) i x
    r2InsertAll K l y

/-- The perfect sampler of Theorem 2.4: an initial draw from `λ` by coordinate draws, then the sequential
insertion of all constraints. The empty family is immediate. -/
noncomputable def r2Sampler (w : CW) : Proc P.Config := do
  let x ← P.oredraw O w (List.finRange n) fun _ => 0
  r2InsertAll P (P.r2Level O w (P.inputSize O) m) (List.finRange m) x

/-- The value `ε_t B` of an experiment outcome. -/
def r2Value (o : Option (Leaf m × P.Config)) : ℚ :=
  match o with
  | none => 0
  | some (t, _) => (sign t : ℚ) * P.r2B

/-- The sum of `N` independent signed experiments of the task `(S, c)`, added to `acc`. -/
noncomputable def r2SumCopies (w : CW) (K : P.RK) (S : Finset (Fin m)) (c : Fin m) :
    ℕ → ℚ → Proc ℚ
  | 0, acc => pure acc
  | k + 1, acc => do
    let o ← (P.r2Factory O w (P.inputSize O)).experiment (fun j => K.coin j.1 j.2) (S, c)
    let acc' ← qadd acc (P.r2Value o)
    r2SumCopies w K S c k acc'

/-- The clipped estimate of `r_i` with the copy count of p.25 (the base `ExecData.copies`). -/
noncomputable def r2Estimate (w : CW) (K : P.RK) (S : Finset (Fin m)) (c : Fin m) (ε : ℚ) :
    Proc ℚ := do
  tick (qcost 1 (2 * P.Q))
  let B := P.r2B
  let N ← ExecData.copies (m := m) B ε
  let total ← P.r2SumCopies O w K S c N 0
  let avg ← qdiv total (N : ℚ)
  let low ← qle avg 0
  if low then pure 0 else do
    let high ← qle B avg
    if high then pure B else pure avg

/-- The product of the factors `1 − r̂_i` along the insertion order. -/
noncomputable def r2ProductFrom (w : CW) (K : P.RK) (ε : ℚ) : List (Fin m) → ℚ → Proc ℚ
  | [], acc => pure acc
  | i :: l, acc => do
    let rhat ← P.r2Estimate O w K (rootSet i) i ε
    let f ← qsub 1 rhat
    let acc' ← qmul acc f
    r2ProductFrom w K ε l acc'

/-- The FPRAS of Theorem 2.4 (p.25 and p.72): the product estimator under the work cap
`K₀ ((L + bits ε + 1) ⌈1/ε⌉)^d`. -/
noncomputable def r2Fpras (w : CW) (K0 d : ℕ) (ε : ℚ) : Proc ℚ :=
  capped (K0 * ((P.inputSize O + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊) ^ d) 0
    (P.r2ProductFrom O w (P.r2Level O w (P.inputSize O) m) ε (List.finRange m) 1)

end RCSP

end SamplingLLL.Supplement


