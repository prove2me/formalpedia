-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_recursive
-- name    : NearlyOptimalPPR_Computation_recursive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:36:18.518242+00:00
-- url     : https://prove2.me/theorems/03023861-0c96-42ac-aa36-92692ddadbe2
-- title:
--   Operational Normalize stack, budgets, cache solves, and completion
-- statement:
--   Algorithms 6–9 maintain a shared potential $x$ and, at every open level $j$, an active set $H_j$, reference $\xi^{(j)}$, work residual $r^{(j)}$, scale $N$, threshold $q_j$, block $b$, and a program counter. Relative potentials are $y^{(j)}=x-\xi^{(j)}$; $y^{(0)}=x$ is an alias. Root initialization has $x=0$, $H_0=\varnothing$, $r^{(0)}=e_s$. A child starts empty on its parent region and inherits the parent's residual, with a reference recorded when each row becomes available.
--
--   An episode records the drained mass $\mu$, opens $Q=\max\{\mu,q_jb\}$, $\theta=Q/b$, $W=0$, and only then performs a pending full solve. Internal episodes make one child call; leaf episodes use a monotone cache retaining the floor $\theta d$. Exterior pushes use
--
--   $$h=\min\{r_v^{(t)}/(5d_v),\ 3q_t/8-y_v^{(t)}\}.$$
--
--   They update shared potentials once, subtract $d_vh$ at earlier levels and $5d_vh$ at their own level, propagate neighbor flow, and charge $(1-\alpha)d_vh$ to every open budget at depth at least $t$. Activation releases $q_td_v/2$ and adds $(t+3)q_td_v/2$ to its local open budget. Full and cache solves compute exact principal-system increments and update all affected open records without a direct budget charge. Their solve domains must consist of stored positive-degree rows; invalid domains are charged and stuck, rather than granted an inverse default.
--
--   The crossing update finishes before a budget is tested. No subsequent solve occurs at or below an exhausted budget. Ancestor interruption returns control upward, retaining $x$; local exhaustion closes the local episode, drains with ancestors open, and restarts with a full solve. A successful episode returns normally only at $\theta=q_j$, otherwise deciding whether to request a full solve by $\mu_{out}\ge Q/2$.
--
--   Root component completion has priority: the maintained boundary-edge count detects completion, a principal solve with right-hand side $e_s$ supplies the exact output, and the solve and output are charged. Only exterior pushes acquire adjacency lists. Stored queues refresh touched keys; child initialization scans its parent once. Per-call work includes descendants and is charged to the producing call, including a crossing push and updates to open records.
--
--   A finite integer schedule selects fixed legal blocks or the balanced rule. The balanced block is found by a charged integer search testing $b^{\ell-j+2}\le N^{\ell-j+1}$; no real-power instruction is supplied. The operational state has no fields asserting correctness, termination, volume bounds, or runtime. Conditions 4.1 and 4.2 are separate predicates to be proved at normal returns.
--
--   Differences from the source:
--   - encoding: pseudocode operations and touched-row data structures → control-state transitions, stored key sets, fixed primitive charges and persistent call identifiers; reason: the state denotes the algorithm without assuming its invariants; full low-level implementation remains proof work
--   - encoding: b=floor(N^((ell-j+1)/(ell-j+2))) or a fixed legal block → an integer-power search for the balanced block and a finite integer schedule for fixed blocks; reason: the same legal blocks are represented and their preparation is charged
--   - encoding: exact full and cache solves, with the stated residual tolerances → exact inverse increments on stored positive-degree principal domains; reason: exact increments have zero leftover error and hence satisfy the full-solve tolerance q_j b/(2^12 N) and cache tolerance q_j/4
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Algorithms 6–9 pp.20–22; Conditions 4.1–4.2 p.17; completion p.15; work convention p.18

import Mathlib
import Definitions.Def_NearlyOptimalPPR_Computation_machine

set_option autoImplicit false

open Finset Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace NearlyOptimalPPR.Computation

attribute [local instance] Classical.propDecidable

/-! Operational records for Algorithms 6--9, pp.20--22. These records contain
no correctness, volume, termination, or runtime invariants. Queue sets denote
stored priority queues: only touched keys are refreshed. The low-level machine
in the separate module remains the computational model of the goal. -/

inductive NormalizePC where
  | initialDrain | beginEpisode | fullSolve | normalize | leafDrain
  | afterChild | finishEpisode | restartDrain | normal | interrupted
  deriving DecidableEq

/-- Zero selects the balanced block rule; a positive entry selects a fixed
block, clamped only to the legal range. Thus all legal fixed blocks are covered.
The schedule contains only integers, not graph-dependent functions. -/
abbrev BlockSchedule := List ℕ

/-- Integer search for the balanced block, using only integer powers and real
comparisons. The search stops at the first failing candidate. -/
def blockSearch (N : ℝ) (r fuel candidate : ℕ) : ℕ :=
  match fuel with
  | 0 => candidate
  | fuel + 1 =>
      if ((candidate + 1 : ℕ) : ℝ) ^ (r + 2) ≤ N ^ (r + 1) then
        blockSearch N r fuel (candidate + 1)
      else candidate

def blockScale (schedule : BlockSchedule) (ℓ j : ℕ) (N : ℝ) : ℕ :=
  match schedule[j]? with
  | some (b + 1) => max 1 (min (b + 1) ⌊N⌋₊)
  | _ => max 1 (blockSearch N (ℓ - j) (⌈N⌉₊ + 1) 0)

structure NormalizeFrame (n : ℕ) where
  id : ℕ
  N : ℝ
  q : ℝ
  block : ℕ
  active : Finset (Fin n)
  reference : Fin n → ℝ
  residual : Fin n → ℝ
  exterior : Finset (Fin n)
  high : Finset (Fin n)
  cache : Finset (Fin n)
  Q : ℝ
  W : ℝ
  theta : ℝ
  openBudget : Bool
  needFull : Bool
  childrenThisEpisode : ℕ
  pc : NormalizePC

def emptyFrame (n : ℕ) : NormalizeFrame n :=
  ⟨0, 1, 1, 1, ∅, fun _ => 0, fun _ => 0, ∅, ∅, ∅,
    0, 0, 0, false, true, 0, .initialDrain⟩

structure CallInformation where
  level : ℕ
  scale : ℝ
  block : ℕ

structure RecursiveState (n : ℕ) where
  x : Fin n → ℝ
  frames : ℕ → NormalizeFrame n
  top : ℕ
  nextId : ℕ
  stored : Finset (Fin n)
  boundaryEdges : ℤ
  information : ℕ → Option CallInformation
  closed : Finset ℕ
  episodes : ℕ → ℕ
  fullSolves : ℕ → ℕ
  episodeChildCounts : ℕ → List ℕ
  charged : ℕ → ℝ≥0∞
  work : ℝ≥0∞
  output : SparseOutput
  done : Bool

def parentDomain {n : ℕ} (st : RecursiveState n) (j : ℕ) : Finset (Fin n) :=
  if j = 0 then Finset.univ else (st.frames (j - 1)).active

def relative {n : ℕ} (st : RecursiveState n) (j : ℕ) (v : Fin n) : ℝ :=
  if j = 0 then st.x v else st.x v - (st.frames j).reference v

def volumeNat {n : ℕ} (g : InputGraph n) (T : Finset (Fin n)) : ℕ :=
  ∑ v ∈ T, (g.neighbors v).length

def touchedBy {n : ℕ} (g : InputGraph n) (T : Finset (Fin n)) : Finset (Fin n) :=
  T ∪ T.biUnion (fun v => (g.neighbors v).toFinset)

def keyCost {n : ℕ} (st : RecursiveState n) : ℕ :=
  1 + Nat.log2 (2 + st.stored.card +
    ∑ i ∈ Finset.range (st.top + 1), ((st.frames i).exterior.card + (st.frames i).active.card))

/-- Inclusive per-call accounts: an operation belongs to its producing call,
and is included in each ancestor's descendant account, exactly once per account.
An ancestor push is never charged to its suspended child. -/
def debit {n : ℕ} (st : RecursiveState n) (producer : ℕ) (cost : ℝ≥0∞) : RecursiveState n :=
  { st with work := st.work + cost
            charged := fun c => st.charged c +
              if ∃ i ≤ producer, (st.frames i).id = c then cost else 0 }

def changeFrame {n : ℕ} (st : RecursiveState n) (j : ℕ)
    (f : NormalizeFrame n → NormalizeFrame n) : RecursiveState n :=
  { st with frames := Function.update st.frames j (f (st.frames j)) }

def changePC {n : ℕ} (st : RecursiveState n) (pc : NormalizePC) : RecursiveState n :=
  changeFrame st st.top (fun f => { f with pc := pc })

/-- Update stored queue keys only on rows touched by the actual update. -/
def refreshKeys {n : ℕ} (g : InputGraph n) (st : RecursiveState n)
    (T : Finset (Fin n)) : RecursiveState n :=
  { st with frames := fun i =>
      if i ≤ st.top then
        let f := st.frames i
        { f with
          exterior := (f.exterior \ T) ∪ T.filter (fun v =>
            v ∈ parentDomain st i ∧ v ∉ f.active ∧
              f.q * LocalPush.deg g.graph v < f.residual v)
          high := (f.high \ T) ∪ T.filter (fun v =>
            v ∈ f.active ∧ 3 * f.theta * LocalPush.deg g.graph v ≤ f.residual v) }
      else st.frames i }

def exhausted {n : ℕ} (st : RecursiveState n) (i : ℕ) : Prop :=
  (st.frames i).openBudget = true ∧ (st.frames i).Q ≤ (st.frames i).W

def anyExhausted {n : ℕ} (st : RecursiveState n) : Prop :=
  ∃ i ≤ st.top, exhausted st i

def ancestorExhausted {n : ℕ} (st : RecursiveState n) : Prop :=
  ∃ i < st.top, exhausted st i

/-- Retrieve one queued exterior row, prioritizing the earliest open level. -/
def pendingPush {n : ℕ} (st : RecursiveState n) : Option (ℕ × Fin n) :=
  let levels := (Finset.range (st.top + 1)).filter fun i => (st.frames i).exterior.Nonempty
  if h : levels.Nonempty then
    let i := levels.min' h
    if h' : (st.frames i).exterior.Nonempty then
      some (i, (st.frames i).exterior.min' h')
    else none
  else none

/-- A principal solve from already stored rows, extended by zero. -/
def solveOn {n : ℕ} (g : InputGraph n) (α : ℝ) (T : Finset (Fin n))
    (b : Fin n → ℝ) : Fin n → ℝ :=
  let A : Matrix T T ℝ := (LocalPush.Lα g.graph α).submatrix Subtype.val Subtype.val
  let h := A⁻¹ *ᵥ (fun v : T => b v)
  fun v => if hv : v ∈ T then h ⟨v, hv⟩ else 0

/-- Algorithm 8's shared update, also used by Algorithm 9. The denotation uses
M*h; only T and its stored adjacency endpoints are touched by its implementation.
No budget receives a direct charge from a joint update. -/
def jointUpdate {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (h : Fin n → ℝ) : RecursiveState n :=
  { st with x := st.x + h
            frames := fun i => if i ≤ st.top then
              { st.frames i with residual := fun v =>
                  if v ∈ parentDomain st i then
                    (st.frames i).residual v - (LocalPush.Lα g.graph α *ᵥ h) v
                  else (st.frames i).residual v }
              else st.frames i }

def jointCost {n : ℕ} (m : SolveModel) (g : InputGraph n)
    (st : RecursiveState n) (T : Finset (Fin n)) : ℝ≥0∞ :=
  solveCharge m T.card (volumeNat g T + T.card) +
    (32 * (st.top + 1) * (volumeNat g T + T.card + 1) * keyCost st : ℕ)

/-- One entire crossing push is applied before testing budgets, Algorithm 7.
The root y=x is an alias; relative potentials at other levels are x-reference.
Only an exterior push opens and stores a new adjacency list. -/
def exteriorPush {n : ℕ} (g : InputGraph n) (α : ℝ)
    (st : RecursiveState n) (t : ℕ) (v : Fin n) : RecursiveState n :=
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let h := min (f.residual v / (5 * d)) (3 * f.q / 8 - relative st t v)
  let activated := relative st t v + h = 3 * f.q / 8
  let u : RecursiveState n :=
    { st with x := Function.update st.x v (st.x v + h)
              stored := insert v st.stored
              frames := fun i => if i ≤ st.top then
                let fi := st.frames i
                { fi with
                  residual := fun w => fi.residual w +
                    (if w = v then
                      if i < t then -d * h else if i = t then -5 * d * h else 0
                    else 0) +
                    (if w ∈ parentDomain st i ∧ g.graph.Adj w v then (1 - α) * h else 0)
                  W := fi.W + if fi.openBudget = true ∧ t ≤ i then (1 - α) * d * h else 0 }
                else st.frames i }
  let u := if activated then
    let u := changeFrame u t (fun fi =>
      { fi with active := insert v fi.active
                residual := Function.update fi.residual v (fi.residual v + f.q * d / 2)
                W := fi.W + if fi.openBudget then (t + 3 : ℕ) * f.q * d / 2 else 0 })
    let u := if t < st.top then
      changeFrame u (t + 1) (fun fc =>
        { fc with reference := Function.update fc.reference v (u.x v)
                  residual := Function.update fc.residual v ((u.frames t).residual v) })
      else u
    if t = 0 then
      { u with boundaryEdges := st.boundaryEdges + (g.neighbors v).length -
          2 * ((g.neighbors v).filter (fun w => w ∈ f.active)).length }
    else u
    else u
  let u := refreshKeys g u (insert v (g.neighbors v).toFinset)
  debit u t (32 * (st.top + 1) * ((g.neighbors v).length + 1) * keyCost u : ℕ)

def finishEpisode {n : ℕ} (st : RecursiveState n) : RecursiveState n :=
  let j := st.top
  let f := st.frames j
  changeFrame
    { st with episodeChildCounts := Function.update st.episodeChildCounts f.id (st.episodeChildCounts f.id ++ [f.childrenThisEpisode]) }
    j (fun fc => { fc with openBudget := false, cache := ∅ })

def sparseOn {n : ℕ} (T : Finset (Fin n)) (v : Fin n → ℝ) : SparseOutput :=
  (T.toList.filter (fun u => v u ≠ 0)).map fun u => ((u.val : ℤ), v u)

/-- Test via the maintained boundary count. Its maintenance inspects only the
activating row. This performs the completion solve, not an oracle PPR call. -/
def componentComplete {n : ℕ} (st : RecursiveState n) : Prop :=
  (st.frames 0).active.Nonempty ∧ st.boundaryEdges = 0

def completeComponent {n : ℕ} (m : SolveModel) (g : InputGraph n)
    (s : Fin n) (α : ℝ) (st : RecursiveState n) : RecursiveState n :=
  let H := (st.frames 0).active
  let p := solveOn g α H (LocalPush.e s)
  let o := sparseOn H (potentialOutput g.graph α p)
  let u := debit st 0 (jointCost m g st H + (H.card + 1 : ℕ))
  { u with done := true, output := o
           closed := u.closed ∪ (Finset.range (u.top + 1)).image (fun i => (u.frames i).id) }

def freshFrame {n : ℕ} (g : InputGraph n) (schedule : BlockSchedule)
    (ℓ j id : ℕ) (N q : ℝ) (domain : Finset (Fin n))
    (x r : Fin n → ℝ) : NormalizeFrame n :=
  { emptyFrame n with id := id, N := N, q := q, block := blockScale schedule ℓ j N
                      reference := x, residual := r
                      exterior := domain.filter (fun v => q * LocalPush.deg g.graph v < r v) }

/-- Root initialization touches only the seed. Computing the block by an integer
search is charged; no logarithm/square-root instruction is introduced. Depth is
an argument of this analysis routine, not free preparation in the goal machine. -/
def recursiveInit {n : ℕ} (g : InputGraph n) (s : Fin n)
    (q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) : RecursiveState n :=
  let f := freshFrame g schedule ℓ 0 0 (1 / q) q {s} (fun _ => 0) (LocalPush.e s)
  { x := fun _ => 0, frames := fun j => if j = 0 then f else emptyFrame n
    top := 0, nextId := 1, stored := ∅, boundaryEdges := 0
    information := fun id => if id = 0 then some ⟨0, 1 / q, f.block⟩ else none
    closed := ∅, episodes := fun _ => 0, fullSolves := fun _ => 0
    episodeChildCounts := fun _ => [],
    charged := fun id => if id = 0 then (8 * (ℓ + 2) * (⌈1 / q⌉₊ + 2) : ℕ) else 0
    work := (8 * (ℓ + 2) * (⌈1 / q⌉₊ + 2) : ℕ)
    output := [], done := false }

def endCall {n : ℕ} (g : InputGraph n) (α : ℝ) (st : RecursiveState n) : RecursiveState n :=
  let j := st.top
  let u := { st with closed := insert (st.frames j).id st.closed }
  if j = 0 then
    let H := (st.frames 0).active
    let o := sparseOn H (potentialOutput g.graph α (prune (st.frames 0).q st.x))
    { debit u 0 (8 * H.card + 1 : ℕ) with done := true, output := o }
  else { u with top := j - 1 }

/-- Algorithms 6--9 with explicit control states. Every transition is charged;
an invalid solve domain is stuck, rather than receiving a singular-inverse junk
answer. Reachability, not a stored invariant, must rule out invalid domains. -/
def recursiveStep {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (st : RecursiveState n) : RecursiveState n :=
  if st.done then st else
  if componentComplete st then completeComponent m g s α st else
  let j := st.top
  let f := st.frames j
  let cheap := debit st j 1
  let drain (next : NormalizePC) : RecursiveState n :=
    if anyExhausted st then changePC cheap next else
      match pendingPush st with
      | some (t, v) => exteriorPush g α st t v
      | none => changePC cheap next
  match f.pc with
  | .initialDrain =>
      if ancestorExhausted st then changePC cheap .interrupted else
      if (pendingPush st).isSome then drain .initialDrain else
      if f.active = ∅ then changePC cheap .normal else changePC cheap .beginEpisode
  | .beginEpisode =>
      let mu := ∑ v ∈ f.active, f.residual v
      let Q := max mu (f.q * f.block)
      let theta := Q / f.block
      let u := debit st j (16 * (volumeNat g f.active + 1) * keyCost st : ℕ)
      changeFrame { u with episodes := Function.update u.episodes f.id (u.episodes f.id + 1) }
        j (fun fc =>
          { fc with
            Q := Q
            W := 0
            theta := theta
            openBudget := true
            childrenThisEpisode := 0
            cache := ∅
            high := f.active.filter (fun v => 3 * theta * LocalPush.deg g.graph v ≤ f.residual v)
            pc := if f.needFull then .fullSolve else .normalize })
  | .fullSolve =>
      if anyExhausted st then changePC cheap .afterChild else
      if f.active ⊆ st.stored ∧ ∀ v ∈ f.active, 0 < g.graph.degree v then
        let h := solveOn g α f.active f.residual
        let u := refreshKeys g (jointUpdate g α st h) (touchedBy g f.active)
        let u := debit u j (jointCost m g st f.active)
        changePC { u with fullSolves := Function.update u.fullSolves f.id (u.fullSolves f.id + 1) } .normalize
      else cheap
  | .normalize =>
      if anyExhausted st then changePC cheap .afterChild else
      if j = ℓ then changePC cheap .leafDrain else
        let c := freshFrame g schedule ℓ (j + 1) st.nextId f.block f.theta f.active st.x f.residual
        let u := debit st j (16 * (volumeNat g f.active + 1) * keyCost st +
          8 * (ℓ + 2) * (f.block + 2) : ℕ)
        let u := changeFrame u j (fun fc => { fc with pc := .afterChild, childrenThisEpisode := fc.childrenThisEpisode + 1 })
        { u with top := j + 1, nextId := st.nextId + 1
                 frames := Function.update u.frames (j + 1) c
                 information := Function.update u.information c.id (some ⟨j + 1, f.block, c.block⟩) }
  | .leafDrain =>
      if anyExhausted st then changePC cheap .afterChild else
      if (pendingPush st).isSome then drain .leafDrain else
      if f.high = ∅ then changePC cheap .afterChild else
        let C := f.cache ∪ f.high
        if C ⊆ st.stored ∧ ∀ v ∈ C, 0 < g.graph.degree v then
          let h := solveOn g α C (fun v => f.residual v - f.theta * LocalPush.deg g.graph v)
          let u := changeFrame st j (fun fc => { fc with cache := C })
          let u := refreshKeys g (jointUpdate g α u h) (touchedBy g C)
          debit u j (jointCost m g st C)
        else cheap
  | .afterChild =>
      if ancestorExhausted st then changePC (finishEpisode cheap) .interrupted else
      if exhausted st j then changePC (finishEpisode cheap) .restartDrain else drain .finishEpisode
  | .finishEpisode =>
      if ancestorExhausted st then changePC (finishEpisode cheap) .interrupted else
      if exhausted st j then changePC (finishEpisode cheap) .restartDrain else
        let mu := ∑ v ∈ f.active, f.residual v
        let u := finishEpisode (debit st j (16 * (volumeNat g f.active + 1) : ℕ))
        changeFrame u j (fun fc =>
          { fc with
            needFull := decide (f.Q / 2 ≤ mu)
            pc := if f.theta = f.q then .normal else .beginEpisode })
  | .restartDrain =>
      if ancestorExhausted st then changePC cheap .interrupted else
      if (pendingPush st).isSome then drain .restartDrain else
        changeFrame cheap j (fun fc => { fc with needFull := true, pc := .beginEpisode })
  | .normal | .interrupted => endCall g α cheap

def recursiveRun {n : ℕ} (m : SolveModel) (g : InputGraph n) (s : Fin n)
    (α q : ℝ) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) : RecursiveState n :=
  (recursiveStep m g s α ℓ schedule)^[t] (recursiveInit g s q ℓ schedule)

/-- Conditions 4.1 and 4.2, all clauses including earlier inactive layers. -/
def returnConditions {n : ℕ} (g : InputGraph n) (ℓ j : ℕ) (st : RecursiveState n) : Prop :=
  (∀ v ∈ (st.frames j).active, 0 ≤ (st.frames j).residual v ∧
    (st.frames j).residual v ≤ kappa ℓ j * (st.frames j).q * LocalPush.deg g.graph v) ∧
  (∀ t ≤ j, ∀ v ∈ parentDomain st t \ (st.frames t).active,
    0 ≤ (st.frames t).residual v ∧ (st.frames t).residual v ≤ (st.frames t).q * LocalPush.deg g.graph v) ∧
  (∀ v ∈ parentDomain st j \ (st.frames j).active,
    0 ≤ relative st j v ∧ relative st j v ≤ 3 * (st.frames j).q / 8) ∧
  ∀ v ∈ (st.frames j).active, 3 * (st.frames j).q / 8 ≤ relative st j v

end NearlyOptimalPPR.Computation


