-- Prove2me | Definitions.Def_CommThresholdPR_StrongConverse_Simulation
-- name    : CommThresholdPR_StrongConverse_Simulation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:45.027695+00:00
-- url     : https://prove2.me/theorems/429a7ebe-7857-413a-9c66-9d807215406b
-- title:
--   Construction 5.1: operational simulation and independent public mixing
-- statement:
--   The single-instance simulation is an actual finite binary protocol. It publicly samples $J=i$ and $X_{<i}$ from the extracted law, independently of its fresh input. Alice privately samples $Y_{>i}$ conditional on her input and the sampled prefix and sends its binary encoding. Each subsequent bit of the actual augmented tree is sampled from the corresponding local conditional row. At a terminal history, the outputs are sampled independently from their local conditional laws.
--
--   $$P_{\pi}=\text{the joint law obtained by executing this protocol on }\mu.$$
--   The construction omits only publicly fixed empty alternating turns. Null conditioning rows have normalized arbitrary fallbacks. Neither a divergence estimate nor an information bound is required to define the protocol. An independent finite Bernoulli public mixture of two protocols retains the coin in its public history. These operations support the simulation and mixing statements without replacing operational protocols by arbitrary joint laws.
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Construction 5.1, pp. 16–17; §7.1, pp. 22–23, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Extraction

noncomputable section

namespace CommThresholdPR.StrongConverse
namespace Extraction
variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B] [Nonempty X] [Nonempty Y]
  [Nonempty A] [Nonempty B] {n : ℕ}

/-- Construction 5.1, pp.16–17. All kernels below are computed from the
conditioned experiment, without assuming its information or divergence bounds.
Publicly determined empty alternating turns are omitted. -/
def commonRow (e : Extraction X Y A B n) (i : Fin n)
    (px : Prefix X i) (sy : Suffix Y i) (h : List Bool) (z : Inputs X Y n) : Prop :=
  pre z i = px ∧ suf z i = sy ∧ h.IsPrefix (e.augmented.run z.1 z.2).1

def aliceRow (e : Extraction X Y A B n) (i : Fin n)
    (px : Prefix X i) (sy : Suffix Y i) (h : List Bool) (x : X) :=
  condition e.Q (fun z => z.1 i = x ∧ e.commonRow i px sy h z)

def bobRow (e : Extraction X Y A B n) (i : Fin n)
    (px : Prefix X i) (sy : Suffix Y i) (h : List Bool) (y : Y) :=
  condition e.Q (fun z => z.2 i = y ∧ e.commonRow i px sy h z)

def next (e : Extraction X Y A B n) (h : List Bool) (z : Inputs X Y n) : Bool :=
  ((e.augmented.run z.1 z.2).1[h.length]?).getD false

/-- Recurse through the actual augmented binary tree. At a leaf the full
history has been revealed, and the two final outputs are sampled independently
from their respective local conditional laws. -/
def simulateNode (e : Extraction X Y A B n) (i : Fin n)
    (px : Prefix X i) (sy : Suffix Y i) :
    DecisionTree (Fin n → X) (Fin n → Y) (Fin n → A) (Fin n → B) →
      List Bool → BinaryTree X Y A B
  | .leaf _ _, h => .leaf
      (fun x => (e.aliceRow i px sy h x).map (fun z => e.outputA z i))
      (fun y => (e.bobRow i px sy h y).map (fun z => e.outputB z i))
  | .alice _ l r, h => .alice
      (fun x => (e.aliceRow i px sy h x).map (e.next h))
      (simulateNode e i px sy l (h ++ [false]))
      (simulateNode e i px sy r (h ++ [true]))
  | .bob _ l r, h => .bob
      (fun y => (e.bobRow i px sy h y).map (e.next h))
      (simulateNode e i px sy l (h ++ [false]))
      (simulateNode e i px sy r (h ++ [true]))

abbrev PublicData (e : Extraction X Y A B n) := (i : Fin n) × Prefix X i

def simulationPublic (e : Extraction X Y A B n) (hn : 0 < n) : PMF e.PublicData :=
  (uniformIndex n hn).bind fun i => e.Q.map fun z => ⟨i, pre z i⟩

/-- The suffix is an actual binary message (using sendAlice), not public
randomness. Only (J,X_<J) is sampled publicly and independently of fresh inputs. -/
def simulationTree (e : Extraction X Y A B n) (u : e.PublicData) : BinaryTree X Y A B :=
  BinaryTree.sendAlice
    (fun x => (condition e.Q (fun z => z.1 u.1 = x ∧ pre z u.1 = u.2)).map
      (fun z => suf z u.1))
    (fun sy => e.simulateNode u.1 u.2 sy e.augmented [])

def simulation (e : Extraction X Y A B n) (hn : 0 < n) : Protocol X Y A B :=
  Protocol.withPublic (e.simulationPublic hn) e.simulationTree

end Extraction

/-- Independent public mixing. The coin is retained in the public history,
as required by §7.1. -/
def publicMix {X Y A B : Type} (π σ : Protocol X Y A B)
    (α : NNReal) (hα : α ≤ 1) : Protocol X Y A B :=
  Protocol.withPublic
    ((PMF.bernoulli α hα).bind fun b =>
      if b then π.publicLaw.map Sum.inl else σ.publicLaw.map Sum.inr)
    (fun r => match r with
      | Sum.inl r => π.tree r
      | Sum.inr r => σ.tree r)

end CommThresholdPR.StrongConverse


