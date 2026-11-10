-- Prove2me | Definitions.Def_DecrAlmostLinearSSSP_Decremental_CutProtocol
-- name    : DecrAlmostLinearSSSP_Decremental_CutProtocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:52:25.779495+00:00
-- url     : https://prove2.me/theorems/b9411801-f5a2-444c-aa35-a55d55087e3f
-- title:
--   Costed dynamic-cut operation protocol and implementation specification
-- statement:
--   A physical undirected multigraph has reusable edge slots, positive supplied capacities $u_e$, zero-sum supplied vertex demand $\gamma$, and implicit vertex potentials $y$, initially zero. Connectivity means that a zero weighted seminorm forces a constant direction. For a returned cut $C$, numbers $G,U$ must satisfy
--
--   $$G<0,\quad U>0,\quad G=\gamma(C),\quad\operatorname{cut}_u(C)\le U,\quad \frac GU\le\frac1K\frac{\gamma\cdot x}{\|x\|_u}\quad(\|x\|_u>0).$$
--
--   Operations insert or delete a physical edge, apply the paired demand change $(+\delta,-\delta)$ at two vertices, obtain a ratio tuple, query a potential, or toggle the most recent cut by $0\le\tau\le1/U$. A toggle must report every edge whose supplied-capacity-weighted potential difference moved by at least the positive threshold $\xi$ since insertion or the last report. Baselines reset exactly on insertion or reporting.
--
--   A finite RAM implementation is specified through actual online operation runs, returned numbers, explicit report buffers and a mathematical view of implicit state. That view grants no evaluation primitive: potential queries and updates must be performed by the program. Initialization, correctness, complete detection, termination, report bounds and amortized instruction counts are properties to prove of the implementation, not assumed fields.
--
--   **Formalization Note** A fixed exponent bounds supplied positive capacities above and away from zero, and bounds demand magnitude, as required by the numerical-range discussion on p.16. Slots can be reused with different endpoints, so a stream can contain arbitrarily many operations. Min-ratio quality is expressed as a bound for every nonzero-norm direction, equivalent to the displayed minimum on the stated finite connected domain.
-- source:
--   Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #912 (October 2026), p. 9, §3.2.1 and Lemma 3.2 including footnote 2; p. 16, numerical-range paragraph; pinned PDF: https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf

import Mathlib
import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Potential

set_option autoImplicit false
open scoped ENNReal NNReal

namespace DecrAlmostLinearSSSP.Decremental

/-- A physical undirected multigraph is given an arbitrary endpoint orientation. Its capacities
are positive on active identifiers; demands and potentials belong to vertices. -/
structure Physical (n k : ℕ) where
  graph : Digraph n k
  active : Finset (Fin k)
  u : Fin k → ℝ
  gamma : Fin n → ℝ

noncomputable def physicalNorm {n k : ℕ} (h : Physical n k) (x : Fin n → ℝ) : ℝ :=
  ∑ e ∈ h.active, h.u e * |x (h.graph.tail e) - x (h.graph.head e)|

noncomputable def cutCapacity {n k : ℕ} (h : Physical n k) (C : Finset (Fin n)) : ℝ := by
  classical
  exact ∑ e ∈ h.active,
    if (h.graph.tail e ∈ C) ≠ (h.graph.head e ∈ C) then h.u e else 0

noncomputable def cutDemand {n k : ℕ} (h : Physical n k) (C : Finset (Fin n)) : ℝ :=
  ∑ v ∈ C, h.gamma v

/-- Writing the min-ratio guarantee as a bound for every nonzero-norm direction avoids
assigning an arbitrary real default to an empty infimum. -/
def RatioGuarantee {n k : ℕ} (h : Physical n k) (K G U : ℝ) (C : Finset (Fin n)) : Prop :=
  G < 0 ∧ 0 < U ∧ G = cutDemand h C ∧ cutCapacity h C ≤ U ∧
    ∀ x, 0 < physicalNorm h x → G / U ≤ (dot h.gamma x / physicalNorm h x) / K

/-- Numerical bounds are a fixed polynomial exponent, not an instance-dependent promise. -/
def Physical.Valid {n k : ℕ} (h : Physical n k) (m exponent : ℕ) : Prop :=
  n ≤ m ∧ k ≤ m ∧ 0 < n ∧
  (∀ e ∈ h.active, (max 2 m : ℝ) ^ (-(exponent : ℤ)) ≤ h.u e ∧
    h.u e ≤ (max 2 m : ℝ) ^ exponent) ∧
  (∑ v, h.gamma v) = 0 ∧ (∀ v, |h.gamma v| ≤ (max 2 m : ℝ) ^ exponent) ∧
  (∀ x, physicalNorm h x = 0 → ∀ v w, x v = x w)

structure CutState (n k : ℕ) where
  physical : Physical n k
  y : Fin n → ℝ
  baseline : Fin k → ℝ
  lastCut : Finset (Fin n)
  lastG : ℝ
  lastU : ℝ
  hasCut : Bool

inductive CutOp (n k : ℕ)
  | insert (e : Fin k) (a b : Fin n) (u : ℝ)
  | erase (e : Fin k)
  | paired (a b : Fin n) (delta : ℝ)
  | ratio
  | toggle (tau : ℝ)
  | queryY (v : Fin n)

def CutOp.Valid {n k : ℕ} (s : CutState n k) : CutOp n k → Prop
  | .insert e _ _ u => e ∉ s.physical.active ∧ 0 < u
  | .erase e => e ∈ s.physical.active
  | .paired _ _ _ => True
  | .ratio => True
  | .toggle tau => s.hasCut = true ∧ s.physical.gamma ≠ 0 ∧ 0 ≤ tau ∧ tau ≤ 1 / s.lastU
  | .queryY _ => True

noncomputable def applyPhysical {n k : ℕ} (h : Physical n k) (op : CutOp n k) : Physical n k := by
  classical
  exact match op with
    | .insert e a b u =>
      { h with
        graph := ⟨Function.update h.graph.tail e a, Function.update h.graph.head e b⟩
        active := insert e h.active
        u := Function.update h.u e u }
    | .erase e => {h with active := h.active.erase e}
    | .paired a b delta =>
      {h with gamma := fun v => h.gamma v + (if v = a then delta else 0) -
        (if v = b then delta else 0)}
    | _ => h

/-- Reports are ordinary identifiers explicitly emitted into machine memory. -/
def reportCount (c : Machine) : ℕ := c.natReg 7

def Reported {k : ℕ} (c : Machine) (e : Fin k) : Prop :=
  ∃ j < reportCount c, c.natMem j = e.val

/-- This is a specification to be proved of an implementation, not a field on an oracle. -/
noncomputable def CutTransition {n k : ℕ} (K ξ : ℝ) (s : CutState n k) (op : CutOp n k)
    (c : Machine) (t : CutState n k) : Prop := by
  classical
  exact t.physical = applyPhysical s.physical op ∧
  (match op with
    | .toggle tau =>
      (∀ v, t.y v = s.y v + if v ∈ s.lastCut then tau else 0) ∧
      t.hasCut = s.hasCut ∧ t.lastCut = s.lastCut ∧ t.lastG = s.lastG ∧ t.lastU = s.lastU ∧
      (∀ e ∈ t.physical.active,
        |t.physical.u e * (t.y (t.physical.graph.tail e) - t.y (t.physical.graph.head e) -
          s.baseline e)| ≥ ξ → Reported c e) ∧
      (∀ e, t.baseline e = if Reported c e then
        t.y (t.physical.graph.tail e) - t.y (t.physical.graph.head e) else s.baseline e)
    | .queryY v => t = s ∧ c.realReg 10 = s.y v ∧ reportCount c = 0
    | _ => t.y = s.y ∧ reportCount c = 0 ∧
      (∀ e, t.baseline e = match op with
        | .insert f a b _ => if e = f then s.y a - s.y b else s.baseline e
        | _ => s.baseline e) ∧
      (t.physical.gamma ≠ 0 →
        RatioGuarantee t.physical K (c.realReg 10) (c.realReg 11) t.lastCut ∧
        t.hasCut = true ∧ t.lastG = c.realReg 10 ∧ t.lastU = c.realReg 11))

/-- Fixed-size operation request in registers. Supplying a request has six charged setup
instructions in the cost predicate below; graph-array reads are performed by the program. -/
def cutRequest {n k : ℕ} (p : Program) (c : Machine) (op : CutOp n k) : Machine :=
  let base := resume c p.update
  match op with
  | .insert e a b u => { base with
      natReg := fun j => if j = 5 then 0 else if j = 6 then e.val else if j = 8 then a.val else if j = 9 then b.val else c.natReg j
      realReg := Function.update c.realReg 2 u }
  | .erase e => {base with natReg := fun j => if j = 5 then 1 else if j = 6 then e.val else c.natReg j}
  | .paired a b d => { base with
      natReg := fun j => if j = 5 then 2 else if j = 8 then a.val else if j = 9 then b.val else c.natReg j
      realReg := Function.update c.realReg 2 d }
  | .ratio => {base with natReg := Function.update c.natReg 5 3}
  | .toggle tau => { base with
      natReg := Function.update c.natReg 5 4
      realReg := Function.update c.realReg 2 tau }
  | .queryY v => {base with natReg := fun j => if j = 5 then 5 else if j = 6 then v.val else c.natReg j}

/-- Initial finite input representation for the dynamic cut implementation. No future
operations appear in the input. Output reports will occupy addresses from zero onward. -/
def cutInitial {n k : ℕ} (p : Program) (h : Physical n k) (m : ℕ) (ξ capacityBound : ℝ) : Machine := by
  classical
  exact {
    pc := p.initPC
    realReg := fun j => if j = 0 then ξ else if j = 1 then capacityBound else 0
    natReg := fun j => if j = 0 then n else if j = 1 then k else if j = 2 then m else 0
    realMem := fun j => if e : j < k then h.u ⟨j,e⟩ else if v : j-k < n then h.gamma ⟨j-k,v⟩ else 0
    natMem := fun j => if e : j / 3 < k then
      let v : Fin k := ⟨j/3,e⟩
      if j%3 = 0 then (h.graph.tail v).val else if j%3 = 1 then (h.graph.head v).val
      else if v ∈ h.active then 1 else 0 else 0
    halted := false
    fault := false
    work := 0 }

/-- A semantic view of implicit data does not grant evaluation as a primitive. QueryY must
actually compute it in the RAM; toggles must actually maintain it. -/
structure CutImplementation where
  program : Program
  view : (n k : ℕ) → Machine → CutState n k


/-- Only actually executed prefixes belong to this relation. Correctness is not a constructor
argument. An operation is admitted under its public preconditions and numerical promises. -/
inductive CutRun (impl : CutImplementation) (n k m exponent : ℕ) (first : Machine) :
    List (CutOp n k) → List Machine → Prop
  | start : CutRun impl n k m exponent first [] [first]
  | next {ops : List (CutOp n k)} {cs : List Machine} {c d : Machine}
      (hr : CutRun impl n k m exponent first ops cs) (hl : cs.getLast? = some c)
      (op : CutOp n k) (hv : CutOp.Valid (impl.view n k c) op)
      (hb : (applyPhysical (impl.view n k c).physical op).Valid m exponent)
      (he : Ends impl.program (cutRequest impl.program c op) d) :
      CutRun impl n k m exponent first (ops ++ [op]) (cs ++ [d])

/-- Totality, quality, complete detection and amortized work of a concrete finite RAM
implementation. No oracle law is assumed in the execution relation. -/
def ImplementsCut (impl : CutImplementation) (m exponent : ℕ) (K h Γ init ξ : ℝ) : Prop :=
  ∀ n k (graph : Physical n k) (capacityBound : ℝ), graph.Valid m exponent →
    0 < capacityBound → capacityBound ≤ (max 2 m : ℝ) ^ exponent →
    (∀ e ∈ graph.active, graph.u e ≤ capacityBound) →
    ∃ first, Ends impl.program (cutInitial impl.program graph m ξ capacityBound) first ∧
      (impl.view n k first).physical = graph ∧ (impl.view n k first).y = 0 ∧
      (impl.view n k first).baseline = 0 ∧ (impl.view n k first).hasCut = false ∧ (first.work : ℝ) ≤ init ∧
      ∀ ops cs, CutRun impl n k m exponent first ops cs →
        (∀ c, cs.getLast? = some c → ∀ op, CutOp.Valid (impl.view n k c) op →
          (applyPhysical (impl.view n k c).physical op).Valid m exponent →
          ∃ d, Ends impl.program (cutRequest impl.program c op) d ∧
            CutTransition K ξ (impl.view n k c) op d (impl.view n k d)) ∧
        (∀ (j : ℕ) c d op, cs[j]? = some c → cs[j+1]? = some d → ops[j]? = some op →
          CutTransition K ξ (impl.view n k c) op d (impl.view n k d)) ∧
        (let T := (ops.filter (fun op => match op with | .toggle _ => true | _ => false)).length
         let R := ((cs.drop 1).map reportCount).sum
         (R : ℝ) ≤ Γ * T / ξ ∧
           ∀ last, cs.getLast? = some last →
             (last.work + 6 * ops.length : ℕ) ≤ init + h * (ops.length + R))

end DecrAlmostLinearSSSP.Decremental


