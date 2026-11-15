-- Prove2me | Definitions.Def_CatalyticTreeEval_NativePrefixAddress
-- name    : CatalyticTreeEval_NativePrefixAddress
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T12:52:51.247539+00:00
-- url     : https://prove2.me/theorems/50dbf46c-e590-42d1-bddf-a2232afd97eb
-- title:
--   Native work-prefix addressing by read-only head distances
-- statement:
--   Finite binary machine templates for transferring an actual input-head or catalyst-head distance to the work-head position, followed by a write to a runtime-selected dense work-prefix cell. The tables use only origin sensors and fixed control; all distances are physical head positions. The shared interface records the exact running time and source trajectories. Preparing the head distances from binary banks is a separate native call.
-- source:
--   Original native auxiliary construction for Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/abs/2602.14320, supporting the machine implementation in Section 4. Formal source: https://github.com/sragavan99/lean-prove2me-fills/tree/codex/catalytic-tree-evaluation/Solutions/CatalyticTreeEvaluation. This helper and its explicit transition tables are new formalisation infrastructure, not a separately numbered assertion in the paper.

import Definitions.Def_CatalyticTreeEval_NativeBankAllocation

/- Bundled addressing definition: Definitions.Def_CatalyticTreeEval_NativeHeadDrain -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeHeadDrain

open CatalyticMatching.General
open NativeHeadStationary (Head position)

/-- Transfer an actual read-only head distance into the work-head position.
Each non-origin transition moves the selected head left and the work head
right. The last transition observes origin and halts. Neither a distance nor
an input-dependent address occurs in the finite control. -/
def machine (head : Head) : Main.Machine where
  states := 1
  start := 0
  table _ _ work _ io _ co :=
    let origin := match head with | .input => io | .catalyst => co
    { next := if origin then none else some 0
      workWrite := work
      catalystWrite := none
      inputMove := match head with
        | .input => if origin then .stay else .left
        | .catalyst => .stay
      workMove := if origin then .stay else .right
      catalystMove := match head with
        | .input => .stay
        | .catalyst => if origin then .stay else .left
      emit := none }

def cursor (head : Head) (c : Config (machine head))
    (remaining work : ℕ) (live : Bool) : Config (machine head) :=
  { c with
    state := if live then some (machine head).start else none
    inputHead := match head with | .input => remaining | .catalyst => c.inputHead
    catalystHead := match head with | .input => c.catalystHead | .catalyst => remaining
    workHead := work }

def envelope (head : Head) (c : Config (machine head)) : Envelope :=
  ⟨c.workHead, c.workHead + position head c + 1,
    match head with | .input => c.catalystHead | .catalyst => 0,
    c.catalystHead + 1⟩

end CatalyticTreeEval.Contracts.NativeHeadDrain
end

/- Bundled addressing definition: Definitions.Def_CatalyticTreeEval_WorkHome -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.WorkHome

open CatalyticMatching.General

/-- Return the work head to the native work origin; no remembered width or tags
are needed, so this remains valid after a scratch-bank erasure. -/
def machine : Main.Machine where
  states := 1
  start := 0
  table _ _ work _ _ origin _ :=
    { next := if origin then none else some 0
      workWrite := work
      catalystWrite := none
      inputMove := .stay
      workMove := if origin then .stay else .left
      catalystMove := .stay
      emit := none }

def cursor (c : Config machine) (head : ℕ) (live : Bool) : Config machine :=
  { c with
    state := if live then some machine.start else none
    workHead := head }

def envelope (c : Config machine) (head : ℕ) : Envelope :=
  ⟨0, head+1, c.catalystHead, c.catalystHead+1⟩

def footprint : Footprint := ⟨∅, ∅⟩

end CatalyticTreeEval.Contracts.WorkHome
end

/- Bundled addressing definition: Definitions.Def_CatalyticTreeEval_NativePrefixWrite -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativePrefixWrite

/-- The two real read-only heads carry the distances `p` and `G-p` before
entry. This fixed finite machine seeks the actual work origin, drains the
input head to reach `p`, writes the finite pending bit, then drains the
catalyst head to return to `G`. Setting up those distances is a separate,
charged native routine; this code never reads an integer from a host oracle. -/
def machine (bit : Bool) : Main.Machine :=
  Sequential.machine WorkHome.machine
    (Sequential.machine (NativeHeadDrain.machine .input)
      (Sequential.machine (NativeLiteral.machine .stay 0 (some bit))
        (NativeHeadDrain.machine .catalyst)))

def time {N : Main.Machine} (c : Config N) : ℕ :=
  (c.workHead+1) + ((c.inputHead+1) + (1+(c.catalystHead+1)))

end CatalyticTreeEval.Contracts.NativePrefixWrite
end


