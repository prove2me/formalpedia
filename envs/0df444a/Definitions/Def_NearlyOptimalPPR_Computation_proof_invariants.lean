-- Prove2me | Definitions.Def_NearlyOptimalPPR_Computation_proof_invariants
-- name    : NearlyOptimalPPR_Computation_proof_invariants
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:21:45.390218+00:00
-- url     : https://prove2.me/theorems/39e45d67-e69a-4aa8-9152-afe1bcb6dedf
-- title:
--   Operational invariants for recursive Normalize
-- statement:
--   These predicates describe the operational states of Algorithms 6–9 for a finite graph, seed $s$, teleportation parameter $\alpha$, and positive threshold $q$. Write $M=D-(1-\alpha)A$, $H$ for the root active set, $x$ for the shared potential and $r$ for a stored work residual. The root residual identity is
--
--   $$e_s-Mx=r+D\bigl(q\mathbf1_H+4x\mathbf1_{V\setminus H}\bigr).$$
--
--   For a child call with relative potential $y$ and threshold $q_j$, equation (4) expresses its parent's residual as the child's residual plus $q_jd_v$ on the child active set, and plus $4d_vy_v$ outside that set. Other predicates express nested domains, exact exterior and high queues, positive thresholds and blocks, budget and cache control, stored adjacency domains, and the numerical bounds
--
--   $$r_v\ge0,\qquad y_v\ge0,\qquad y_v\ge3q_j/8\ (v\text{ active}),\qquad y_v<3q_j/8\ (v\text{ inactive}).$$
--
--   The module also supplies the coordinate-update and admission stages, the graph boundary count, and cut-flux notation used in the proofs. These are analysis definitions of the existing transition system. Separate theorems establish them on every actual execution prefix; they impose no admissibility, correctness, termination, or work assumption on the goal program.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, equation (1) p.6; Lemma 3.7 pp.14–15; equation (4) and Conditions 4.1–4.2 p.17; Algorithms 6–9 pp.20–22.

import Definitions.Def_NearlyOptimalPPR_Computation_recursive

set_option autoImplicit false
open Finset Matrix
open scoped ENNReal
namespace NearlyOptimalPPR.Computation
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def RegionInvariant (st : RecursiveState n) : Prop :=
  ∀ i ≤ st.top,
    (st.frames i).active ⊆ parentDomain st i ∧
    (st.frames i).exterior ⊆ parentDomain st i \ (st.frames i).active ∧
    (st.frames i).high ⊆ (st.frames i).active ∧
    (st.frames i).cache ⊆ (st.frames i).active

def frameRegions (f : NormalizeFrame n) := (f.active,f.exterior,f.high,f.cache)

def exteriorKey (g : InputGraph n) (st : RecursiveState n) (i : ℕ) (v : Fin n) : Prop :=
  v ∈ parentDomain st i ∧ v ∉ (st.frames i).active ∧
    (st.frames i).q*LocalPush.deg g.graph v < (st.frames i).residual v

def highKey (g : InputGraph n) (st : RecursiveState n) (i : ℕ) (v : Fin n) : Prop :=
  v ∈ (st.frames i).active ∧
    3*(st.frames i).theta*LocalPush.deg g.graph v ≤ (st.frames i).residual v

def KeysInvariant (g : InputGraph n) (st : RecursiveState n) : Prop :=
  ∀ i ≤ st.top, (∀ v, v ∈ (st.frames i).exterior ↔ exteriorKey g st i v) ∧
    (∀ v, v ∈ (st.frames i).high ↔ highKey g st i v)

def RootIdentity (g : InputGraph n) (s : Fin n) (α : ℝ) (st : RecursiveState n) : Prop :=
  ∀ v, residual g.graph α s st.x v = (st.frames 0).residual v +
    LocalPush.deg g.graph v *
      (if v ∈ (st.frames 0).active then (st.frames 0).q else 4 * st.x v)

def LayerIdentity (g : InputGraph n) (st : RecursiveState n) : Prop :=
  ∀ j < st.top, ∀ v ∈ (st.frames j).active,
    (st.frames j).residual v = (st.frames (j+1)).residual v +
      LocalPush.deg g.graph v *
        (if v ∈ (st.frames (j+1)).active then (st.frames (j+1)).q
        else 4*relative st (j+1) v)

def layerView (f : NormalizeFrame n) := (f.q,f.active,f.reference,f.residual)

def rawExterior (g : InputGraph n) (α : ℝ) (st : RecursiveState n)
    (t : ℕ) (v : Fin n) (δ : ℝ) : RecursiveState n :=
  {st with
    x := Function.update st.x v (st.x v+δ)
    stored := insert v st.stored
    frames := fun i => if i ≤ st.top then
      let fi := st.frames i
      {fi with
        residual := fun w => fi.residual w +
          (if w = v then if i < t then -LocalPush.deg g.graph v*δ
            else if i = t then -5*LocalPush.deg g.graph v*δ else 0 else 0) +
          (if w ∈ parentDomain st i ∧ g.graph.Adj w v then (1-α)*δ else 0)
        W := fi.W+if fi.openBudget = true ∧ t ≤ i then (1-α)*LocalPush.deg g.graph v*δ else 0}
      else st.frames i}

def queueStaticView (f : NormalizeFrame n) := (f.q,f.theta,f.exterior,f.high)

def queueRowView (f : NormalizeFrame n) (v : Fin n) := (v ∈ f.active,f.residual v)

def frameParameters (f : NormalizeFrame n) := (f.q,f.theta,f.openBudget,f.pc,f.N,f.block,f.id)

def budgetPC : NormalizePC → Bool
  | .fullSolve | .normalize | .leafDrain | .afterChild | .finishEpisode => true
  | _ => false

def BudgetInvariant (st : RecursiveState n) : Prop :=
  ∀ i ≤ st.top, (st.frames i).openBudget = budgetPC (st.frames i).pc

def FrameParametersPositive (f : NormalizeFrame n) : Prop :=
  0 < f.q ∧ 1 ≤ f.block ∧ (f.openBudget = true → f.q ≤ f.theta)

def ParameterInvariant (st : RecursiveState n) : Prop :=
  ∀ i ≤ st.top, FrameParametersPositive (st.frames i)

def parameterView (f : NormalizeFrame n) := (f.q,f.block,f.theta,f.openBudget)

def graphCut (g : InputGraph n) (H : Finset (Fin n)) : ℤ :=
  ∑ v ∈ H, ∑ u, if g.graph.Adj v u ∧ u ∉ H then 1 else 0

def BoundaryIdentity (g : InputGraph n) (st : RecursiveState n) : Prop :=
  st.boundaryEdges = graphCut g (st.frames 0).active

def StoredInvariant (g : InputGraph n) (st : RecursiveState n) : Prop :=
  (∀ i ≤ st.top, (st.frames i).active ⊆ st.stored) ∧
    ∀ v ∈ st.stored, 0 < g.graph.degree v

def IsolateResidual (g : InputGraph n) (st : RecursiveState n) : Prop :=
  ∀ i ≤ st.top, ∀ v : Fin n, g.graph.degree v = 0 → (st.frames i).residual v = 0

def CacheControlInvariant (ℓ : ℕ) (st : RecursiveState n) : Prop :=
  ∀ i ≤ st.top,
    (i ≠ ℓ → (st.frames i).cache = ∅) ∧
    ((st.frames i).pc = .leafDrain → i = ℓ) ∧
    ((st.frames i).pc = .fullSolve → (st.frames i).cache = ∅)

def NumericalInvariant (g : InputGraph n) (st : RecursiveState n) : Prop :=
  ∀ i ≤ st.top,
    (∀ v ∈ parentDomain st i,
      0 ≤ (st.frames i).residual v ∧ 0 ≤ relative st i v ∧
      (v ∈ (st.frames i).active → 3*(st.frames i).q/8 ≤ relative st i v) ∧
      (v ∉ (st.frames i).active → relative st i v < 3*(st.frames i).q/8)) ∧
    ∀ v ∈ (st.frames i).cache,
      (st.frames i).theta*LocalPush.deg g.graph v ≤ (st.frames i).residual v

def RawNumericalInvariant (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) : Prop :=
  ∀ i ≤ st.top,
    (∀ w ∈ parentDomain st i,
      0 ≤ (st.frames i).residual w ∧ 0 ≤ relative st i w ∧
      (w ∈ (st.frames i).active → 3*(st.frames i).q/8 ≤ relative st i w) ∧
      (w ∉ (st.frames i).active →
        if i = t ∧ w = v then relative st i w ≤ 3*(st.frames i).q/8
        else relative st i w < 3*(st.frames i).q/8)) ∧
    ∀ w ∈ (st.frames i).cache,
      (st.frames i).theta*LocalPush.deg g.graph w ≤ (st.frames i).residual w

def admitStage (g : InputGraph n) (st : RecursiveState n) (t : ℕ) (v : Fin n) : RecursiveState n :=
  let f := st.frames t
  let d := LocalPush.deg g.graph v
  let u := changeFrame st t (fun fi =>
    {fi with
      active := insert v fi.active
      residual := Function.update fi.residual v (fi.residual v+f.q*d/2)
      W := fi.W + if fi.openBudget then (t+3 : ℕ)*f.q*d/2 else 0})
  let u := if t < st.top then changeFrame u (t+1) (fun fc =>
    {fc with
      reference := Function.update fc.reference v (u.x v)
      residual := Function.update fc.residual v ((u.frames t).residual v)}) else u
  if t = 0 then {u with boundaryEdges := st.boundaryEdges+(g.neighbors v).length-
    2*((g.neighbors v).filter (fun w => w ∈ f.active)).length} else u

def numericalView (f : NormalizeFrame n) := (f.q,f.theta,f.active,f.cache,f.reference,f.residual)

def ConnectedRootSet (g : InputGraph n) (s : Fin n) (H : Finset (Fin n)) : Prop :=
  H.Nonempty → s ∈ H ∧ (g.graph.induce (↑H : Set (Fin n))).Connected

def RootConnected (g : InputGraph n) (s : Fin n) (st : RecursiveState n) : Prop :=
  ConnectedRootSet g s (st.frames 0).active

def edgeDifference (g : InputGraph n) (z : Fin n → ℝ) (u v : Fin n) : ℝ :=
  if g.graph.Adj u v then z u-z v else 0

def boundaryFlux (g : InputGraph n) (z : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, edgeDifference g z u v

end
end NearlyOptimalPPR.Computation


