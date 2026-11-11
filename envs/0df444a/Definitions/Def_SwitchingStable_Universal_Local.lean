-- Prove2me | Definitions.Def_SwitchingStable_Universal_Local
-- name    : SwitchingStable_Universal_Local
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:19.939617+00:00
-- url     : https://prove2.me/theorems/04add3be-3d2d-4518-889f-71fee3025ce5
-- title:
--   Local cuts, mixed-layer inputs and exhaustive four-agent histories
-- statement:
--   The local cuts contain the selected next-owner witnesses, the further witness on $D$, the second-boundary witnesses for $F_a$ and nonexceptional $C_0$, and the third-boundary witness on $W$. The basic directional cost uses the paper's class-dependent constants, with the additional $D$ and $D_0$ increments. A mixed-layer input consists of actual elementary cuts, their type and depth, and an established full estimate when its type is zero.
--
--   The finite Appendix C model records an arbitrary sequence of directed single-cycle reassignments on four names, appending every newly visited pair and rejecting repetitions. Its four normalized terminal rows are stored exactly. The classification conclusion is part of Lemma 10.
--
--   These interfaces retain the actual residual
--   $$R_R=S_R-\sum F_i^R,\qquad R_L=S_L-\sum F_j^L,$$
--   so directional surplus is never made available twice.
-- source:
--   Hao Xu, Jinshan Zhang, Feng Wang, STOC 2027 submission #170 (October 2026), pp. 8–10, 18–20, 22–27, PDF pp. 9–11, 19–21, 23–28, Sections 4–5 and Appendices B–E

import Mathlib
import Definitions.Def_SwitchingStable_Universal_Transport

namespace SwitchingStable.Universal
open StableMatching MeasureTheory
variable {n : ℕ}

noncomputable def localCuts (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : Finset (Cut n) := by
  classical
  let first : Finset (Cut n) := if R I μ ε u then {realCut 1 (next I μ ε (next I μ ε u))} else ∅
  let extra : Finset (Cut n) := if D I μ ε u then {realCut 1 (next I μ ε (next I μ ε (next I μ ε u)))} else ∅
  let second : Finset (Cut n) := if E I μ ε u then {realCut 2 (next I μ ε (owner I μ ε u 2))}
    else if Fa I μ ε u ∨ (C0 I μ ε u ∧ ¬ Exceptional I μ ε u) then
      {if distance I μ u ε < 2 then endpointCut ε 2 else realCut 2 (chooseWitness I μ ε u 2)}
    else ∅
  let third : Finset (Cut n) := if W I μ ε u then {realCut 3 (next I μ ε (owner I μ ε u 3))} else ∅
  exact first ∪ extra ∪ second ∪ third
noncomputable def localBase (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : ℝ := by
  classical
  exact if R0 I μ ε u then alpha else if R1 I μ ε u then eta
    else if Eadj I μ ε u then zeta else if E I μ ε u then delta 2
    else if S I μ ε u then sigma else if W I μ ε u then gamma
    else if Fa I μ ε u then delta 2 else 0
noncomputable def fullLocalCost (I : Instance n) (μ : Matching n) (ε : Direction) (u : Fin n) : ℝ := by
  classical
  exact localBase I μ ε u + (if D I μ ε u then delta 2 else 0) +
    (if D0 I μ ε u then delta 2 + lambda else 0)
/-- Parameters of the mixed-layer lemma. Type zero consumes an established full estimate. -/
structure LayerChoice (n : ℕ) where
  typ : ℕ
  depth : ℕ
  terms : Finset (Cut n)
  cuts : Finset (Cut n)
  zeroCost : ℝ
noncomputable def LayerChoice.Valid (v : LayerChoice n) (I : Instance n) (μ : Matching n)
    (u : Fin n) (ε : Direction) : Prop :=
  v.typ ≤ 3 ∧ legalCuts I μ u ε v.cuts ∧ v.terms ⊆ v.cuts ∧
  (if v.typ = 0 then v.terms = ∅ ∧ v.zeroCost ≤ expected (saving I μ u ε v.cuts)
   else 1 ≤ v.depth ∧ v.depth ≤ 3 ∧
     v.terms.image Cut.layer = layers v.typ v.depth ∧
     Set.InjOn Cut.layer (v.terms : Set (Cut n)) ∧
     ∀ c ∈ v.terms, Elementary I μ u ε c)
noncomputable def LayerChoice.cost (v : LayerChoice n) : ℝ :=
  if v.typ = 0 then v.zeroCost else layerCost v.typ v.depth
noncomputable def LayerChoice.weight (v : LayerChoice n) : ℝ :=
  if v.typ = 0 then omega 0 else omega v.typ - penalty v.depth
noncomputable def LayerChoice.residual (v : LayerChoice n) (I : Instance n) (μ : Matching n)
    (u : Fin n) (ε : Direction) (t : Sample n) : ℝ :=
  if v.typ = 0 then 0 else saving I μ u ε v.cuts t - layerSum I μ u ε v.terms t

/-- Appendix C's exhaustive cycle histories, starting at the identity. -/
structure FourState where
  matching : Equiv.Perm (Fin 4)
  visits : Fin 4 → List (Fin 4)
def FourState.initial : FourState := ⟨Equiv.refl _, fun a => [a]⟩
def SingleCycle (σ : Equiv.Perm (Fin 4)) : Prop :=
  ∃ a, σ a ≠ a ∧ ∀ b, σ b ≠ b → ∃ t : ℕ, σ^[t] a = b
def FourState.step (s : FourState) (σ : Equiv.Perm (Fin 4)) : FourState :=
  ⟨σ.trans s.matching, fun a => if σ a = a then s.visits a else s.visits a ++ [s.matching (σ a)]⟩
def ValidHistory : FourState → List (Equiv.Perm (Fin 4)) → Prop
  | _, [] => True
  | s, σ::hs => SingleCycle σ ∧
    (∀ a, σ a ≠ a → s.matching (σ a) ∉ s.visits a) ∧ ValidHistory (s.step σ) hs
def FourState.finish (s : FourState) (hs : List (Equiv.Perm (Fin 4))) : FourState :=
  hs.foldl FourState.step s
def FourState.qualifies (s : FourState) : Prop :=
  (s.visits 0).length = 4 ∧ (∀ a, 2 ≤ (s.visits a).length) ∧
  (s.visits 0)[1]?.getD 0 = 1 ∧ (s.visits 1)[1]?.getD 1 = 2 ∧ (s.visits 2)[1]?.getD 2 = 1
def fourRows : Finset (Fin 4 → List (Fin 4)) :=
  { ![[0,1,3,2],[1,2,0],[2,1,0,3],[3,1]],
    ![[0,1,3,2],[1,2,3],[2,1,0],[3,1]],
    ![[0,1,3,2],[1,2,3],[2,1,3,0],[3,0,1]],
    ![[0,1,3,2],[1,2,3,0],[2,1,0,3],[3,1]] }

end SwitchingStable.Universal


