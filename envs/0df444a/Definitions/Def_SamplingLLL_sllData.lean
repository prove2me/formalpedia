-- Prove2me | Definitions.Def_SamplingLLL_sllData
-- name    : SamplingLLL_sllData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:08.511193+00:00
-- url     : https://prove2.me/theorems/e947c172-5399-43b5-b136-cc9d46e3ca43
-- title:
--   The two-rule search, proposal and local operation of Appendix G; the sampler and FPRAS of Theorem 2.6
-- statement:
--   The instantiation of the Execution Theorem for atomic CSPs. The search of a task with family $C$ starts with $Y=\{c\}$ and repeatedly applies the first available rule: among pairs $(K,b)$ with $K$ an $H$-component of $Y$ containing an event of $G$ and $b$ an unqueried member of $C$ adjacent to $K$, query the least pair; otherwise query the least member of $C$ outside $N_H[Y]$ at $H$-distance two from an uncertified singleton component. At the end, $F_1$ is the set of unqueried members of $C$ at $H$-distance one from $Y$, $R$ is the set of other unqueried members, $D_t=(Y\setminus\{c\})\cup N\cup F_1$, and $W_t=\mathrm{vbl}(Y)\cup\mathrm{vbl}(F_1)$. The budget is $B_a=x_a/4$. The proposal answers a query of $b$ yes with probability $x_b/2$ and retains with probability $\prod_{d\in F_1}(1-x_d/2)$. The local operation thins by $u_t/[B_cq_c(t)\prod_{d\in D_t}\sigma_d]$, pins $\mathrm{vbl}(Y)$ to the forbidden words, draws the remaining variables of $F_1$ from the product law, and retains the mark when every member of $F_1$ is satisfied.
--
--   The sampler and FPRAS of Theorem 2.6 are the sampler and FPRAS of these data. The numbers $p_a$ appear nowhere in them.
--
--   **Formalization Note** All graph notions are in the full graph $H$. The charges are $L^3$ per search step and $L$ per test and move. The work cap of the FPRAS is $K((L+\mathrm{bits}(\varepsilon)+1)\lceil1/\varepsilon\rceil)^d$, with $K,d$ fixed by Theorem 2.6.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Appendix G, proof of Theorem 2.6, pp.66–68

import Mathlib
import Definitions.Def_SamplingLLL_ExecData

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL

open Proc

variable {n m : ℕ}

namespace AtomicCSP

variable (I : AtomicCSP n m) (G : Finset (Fin m)) (x : Fin m → ℚ)

/-- The `H`-component of `a` in `Y`, by `m` closure steps. All graph notions are in the full graph
`H`, never in a graph induced on the task family. -/
def comp (Y : Finset (Fin m)) (a : Fin m) : Finset (Fin m) :=
  (fun K => K ∪ Y.filter fun e => ∃ u ∈ K, I.H.Adj u e)^[m] {a}

/-- The first rule of Appendix G, p.66: among pairs `(K, b)`, `K` an `H`-component of `Y` containing a
sampling-good event and `b` an unqueried member of `C` adjacent to `K`, the least, ordering components
by their least member and then using the index order on `C`. -/
def rule1 (C Y N : Finset (Fin m)) : Option (Fin m) :=
  (List.finRange m).findSome? fun a =>
    if a ∈ Y ∧ (∀ e ∈ I.comp Y a, a ≤ e) ∧ (∃ g ∈ I.comp Y a, g ∈ G) then
      (List.finRange m).find? fun b =>
        decide (b ∈ C ∧ b ∉ Y ∧ b ∉ N ∧ ∃ e ∈ I.comp Y a, I.H.Adj e b)
    else none

/-- The second rule of Appendix G, p.66: the least unqueried member of `C` outside `N_H[Y]` at
`H`-distance two in the full graph from an uncertified singleton component `{a}`. -/
def rule2 (C Y N : Finset (Fin m)) : Option (Fin m) :=
  (List.finRange m).find? fun b =>
    decide (b ∈ C ∧ b ∉ Y ∧ b ∉ N ∧ (∀ a ∈ Y, ¬ I.H.Adj a b) ∧
      ∃ a ∈ Y, I.comp Y a = {a} ∧ a ∉ G ∧ I.DistTwo a b)

/-- The two-rule search of Appendix G, p.66, for the task `(S, c)`; the fixed order is `Fin m`. -/
def nextQ (S : Finset (Fin m)) (c : Fin m) : NextQuery m := fun Y N =>
  match I.rule1 G (insert c S) Y N with
  | some b => some b
  | none => I.rule2 G (insert c S) Y N

/-- `F1`, p.67: the unqueried members of `C` at `H`-distance one from `Y`. -/
def F1 (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : Finset (Fin m) :=
  (insert c S).filter fun d => d ∉ t.1 ∧ d ∉ t.2 ∧ ∃ y ∈ t.1, I.H.Adj y d

/-- `R`, p.67: the remaining unqueried members of `C`. -/
def R (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : Finset (Fin m) :=
  (insert c S).filter fun d => d ∉ t.1 ∧ d ∉ t.2 ∧ ¬ ∃ y ∈ t.1, I.H.Adj y d

/-- `D_t = (Y ∖ {c}) ∪ N ∪ F1`, p.67, in index order. -/
def Dlist (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : List (Fin m) :=
  (List.finRange m).filter fun d => d ∈ t.1.erase c ∪ t.2 ∪ I.F1 S c t

/-- `W_t = vbl(Y) ∪ vbl(F1)`. -/
def Wt (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) : Finset (Fin n) :=
  t.1.biUnion I.vbl ∪ (I.F1 S c t).biUnion I.vbl

/-- `E_t`, p.67: every member of `Y` is bad and every member of `F1` is good. -/
def Et (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) (y : (v : Fin n) → Fin (I.dom v + 1)) : Bool :=
  decide ((∀ b ∈ t.1, I.bad b y = true) ∧ ∀ d ∈ I.F1 S c t, I.bad d y = false)

/-- The forbidden words of `Y` agree. -/
def compat (Y : Finset (Fin m)) : Prop :=
  ∀ a ∈ Y, ∀ b ∈ Y, ∀ v, ∀ w w', I.word a v = some w → I.word b v = some w' → w = w'

instance (Y : Finset (Fin m)) : Decidable (I.compat Y) := by unfold compat; infer_instance

/-- The value that the forbidden words of `Y` fix on `v`, if any. -/
def pin (Y : Finset (Fin m)) (v : Fin n) : Option (Fin (I.dom v + 1)) :=
  (List.finRange m).findSome? fun a => if a ∈ Y then I.word a v else none

/-- The proposal, p.67: run the search, answering a query of `b` yes with an independent coin of bias
`x_b/2`, tracking the probability in `q` by charged operations. The fuel `m` is never exhausted. -/
noncomputable def proposeRun (L : ℕ) (S : Finset (Fin m)) (c : Fin m) :
    ℕ → Leaf m → ℚ → Proc (Leaf m × ℚ)
  | 0, t, q => pure (t, q)
  | k + 1, t, q => do
    tick (L ^ 3)
    match I.nextQ G S c t.1 t.2 with
    | none => pure (t, q)
    | some b =>
      let half ← qdiv (x b) 2
      let yes ← ratCoin half
      if yes then do
        let q' ← qmul q half
        proposeRun L S c k (insert b t.1, t.2) q'
      else do
        let no ← qsub 1 half
        let q' ← qmul q no
        proposeRun L S c k (t.1, insert b t.2) q'

/-- The retention of (A3), p.67: independent coins `1 - x_d/2` for `d ∈ F1` along the list, tracking
the probability; failure gives the null outcome. -/
noncomputable def retain : List (Fin m) → ℚ → Proc (Option ℚ)
  | [], q => pure (some q)
  | d :: l, q => do
    let half ← qdiv (x d) 2
    let keep ← qsub 1 half
    let b ← ratCoin keep
    if b then do
      let q' ← qmul q keep
      retain l q'
    else pure none

/-- The proposal of p.67, with distribution (A3). -/
noncomputable def proposal (L : ℕ) (S : Finset (Fin m)) (c : Fin m) :
    Proc (Option (Leaf m × ℚ)) := do
  let (t, q) ← I.proposeRun G x L S c m ({c}, ∅) 1
  match ← retain x ((List.finRange m).filter fun d => d ∈ I.F1 S c t) q with
  | none => pure none
  | some q' => pure (some (t, q'))

/-- `∏_{v∈l} λ_v(τ(v))`, multiplied into `acc`, by charged operations. -/
noncomputable def uProd (Y : Finset (Fin m)) : List (Fin n) → ℚ → Proc ℚ
  | [], acc => pure acc
  | v :: l, acc =>
    match I.pin Y v with
    | none => uProd Y l acc
    | some w => do
      let acc' ← qmul acc (I.lam v w)
      uProd Y l acc'

/-- `acc ∏_{d∈l} σ_d`, with `σ_d = 1 - x_d/4`, by charged operations. -/
noncomputable def sigmaProd : List (Fin m) → ℚ → Proc ℚ
  | [], acc => pure acc
  | d :: l, acc => do
    let b ← qdiv (x d) 4
    let s ← qsub 1 b
    let acc' ← qmul acc s
    sigmaProd l acc'

/-- The exact local operation, p.68: reject on disagreeing forbidden words; compute `u_t`; thin by
`u_t / (B_c q ∏_{d∈D_t} σ_d)`; pin `vbl(Y)` to the forbidden words and draw the remaining variables of
`F1` from the product law (`0` on all other variables of the mark); keep the mark when every member of
`F1` is satisfied. `F1` is tested after the thinning and is not pinned. -/
noncomputable def localOperation (L : ℕ) (S : Finset (Fin m)) (c : Fin m) (t : Leaf m) (q : ℚ) :
    Proc (Option ((v : Fin n) → Fin (I.dom v + 1))) := do
  tick L
  if I.compat t.1 then do
    let u ← I.uProd t.1 ((List.finRange n).filter fun v => v ∈ t.1.biUnion I.vbl) 1
    let B ← qdiv (x c) 4
    let d0 ← qmul B q
    let den ← sigmaProd x (I.Dlist S c t) d0
    let ratio ← qdiv u den
    let keep ← ratCoin ratio
    if keep then do
      tick L
      let mark ← I.toCSP.redraw
        ((List.finRange n).filter fun v =>
          v ∈ (I.F1 S c t).biUnion I.vbl ∧ v ∉ t.1.biUnion I.vbl)
        (fun v => (I.pin t.1 v).getD 0)
      tick (L * (I.F1 S c t).card)
      if ∀ d ∈ I.F1 S c t, I.bad d mark = false then pure (some mark) else pure none
    else pure none
  else pure none

/-- The application data of Appendix G. The numbers `p_a` appear nowhere: `sllData` is computed from
the CSP, `G` and the witnesses `x` alone (Theorem 2.6: they "need not be supplied"). Budgets are
`B_c = x_c/4` by (A2); charges are `L³` per search step and `L` per test and per move, with
`L = inputSize`. -/
noncomputable def sllData : ExecData I.toCSP where
  next := I.nextQ G
  rest := I.R
  restore := I.Dlist
  vars := I.Wt
  event := I.Et
  budget _ c := x c / 4
  budgetCost _ c := qcost (x c) 4
  propose := I.proposal G x (I.inputSize x)
  localOp := I.localOperation x (I.inputSize x)
  stepCost := I.inputSize x ^ 3
  testCost := I.inputSize x
  moveCost := I.inputSize x

/-- The perfect sampler of Theorem 2.6. -/
noncomputable def sampler : Proc I.toCSP.Config := (I.sllData G x).sampler

/-- The FPRAS of Theorem 2.6, with the work cap `K ((L + bits ε + 1) ⌈1/ε⌉)^d` of p.25 ("Cap the total
work"). `K` and `d` are chosen once for all instances in the theorem. -/
noncomputable def fpras (K d : ℕ) (ε : ℚ) : Proc ℚ :=
  (I.sllData G x).fpras (K * ((I.inputSize x + bits ε + 1) * ⌈(1 / ε : ℚ)⌉₊) ^ d) ε

end AtomicCSP

end SamplingLLL


