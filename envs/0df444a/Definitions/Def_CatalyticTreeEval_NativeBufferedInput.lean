-- Prove2me | Definitions.Def_CatalyticTreeEval_NativeBufferedInput
-- name    : CatalyticTreeEval_NativeBufferedInput
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T15:08:03.67272+00:00
-- url     : https://prove2.me/theorems/67622257-8a98-4067-9e16-9c8b5d29580a
-- title:
--   Native buffered-input cursor and probe
-- statement:
--   A finite native input service for a binary stream stored in physical tagged work lanes. A unique bookmark represents virtual input position $i$, with origin at $i=0$, data at $1\le i\le R$, and EOF at $i=R+1$. Three distinct physical reply flags encode origin, presence, and payload. The interface records the actual tagged buffer, the fixed native locate-and-inspect program, its exact work footprint, and preservation of the buffered stream and cursor. The read-only real input and catalyst remain stationary. The buffer is an explicit precondition; constructing it is a separately charged operation.
-- source:
--   Native auxiliary construction for Section 4 of Catalytic Tree Evaluation from Matching Vectors, arXiv:2602.14320; physical input-service contracts for the machine formalisation.

import Definitions.Def_CatalyticTreeEval_NativePrefixAddress

/- Buffered input definition: Definitions.Def_CatalyticTreeEval_NativeInputInspect -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeInputInspect

/-- Fixed physical lanes for a buffered-input service. The executable table
does not contain the virtual input position, input length or buffer contents.
Clients additionally prove the roles distinct when asking for preservation. -/
structure Roles (lanes : ℕ) where
  bookmark : Fin lanes
  origin : Fin lanes
  data : Fin lanes
  replyOrigin : Fin lanes
  replyPresent : Fin lanes
  replyValue : Fin lanes

inductive Reply where
  | origin
  | eof
  | bit (value : Bool)
  deriving DecidableEq

def Reply.isOrigin : Reply → Bool
  | .origin => true
  | _ => false

def Reply.isPresent : Reply → Bool
  | .bit _ => true
  | _ => false

def Reply.value : Reply → Bool
  | .bit value => value
  | _ => false

def move {lanes : ℕ} (source target : Fin lanes) : Main.Machine :=
  NativeLiteral.machine (NativeLaneFlagCopy.forward source target)
    (NativeLaneFlagCopy.distance source target) none

def write {lanes : ℕ} (source target : Fin lanes) (value : Bool) : Main.Machine :=
  NativeLiteral.machine (NativeLaneFlagCopy.forward source target)
    (NativeLaneFlagCopy.distance source target) (some value)

/-- Materialize three reply bits in the same physical row as the cursor and
return at replyOrigin. Their row is carried by the actual work head. -/
def writeReply {lanes : ℕ} (r : Roles lanes) (source : Fin lanes) (reply : Reply) : Main.Machine :=
  Sequential.machine (write source r.replyOrigin reply.isOrigin)
    (Sequential.machine (write r.replyOrigin r.replyPresent reply.isPresent)
      (Sequential.machine (write r.replyPresent r.replyValue reply.value)
        (move r.replyValue r.replyOrigin)))

/-- The A payload is one logical row after its tag. Return to the tag row
before writing the captured finite Boolean reply. -/
def payloadReply {lanes : ℕ} (r : Roles lanes) (value : Bool) : Main.Machine :=
  Sequential.machine (NativeLiteral.machine .left (lanes+1) none)
    (writeReply r r.data (.bit value))

def readPayload {lanes : ℕ} (r : Roles lanes) : Main.Machine :=
  Sequential.machine (NativeLiteral.machine .right (lanes+1) none)
    (Branch.machine (payloadReply r true) (payloadReply r false))

def readData {lanes : ℕ} (r : Roles lanes) : Main.Machine :=
  Branch.machine (readPayload r) (writeReply r r.data .eof)

def nonOrigin {lanes : ℕ} (r : Roles lanes) : Main.Machine :=
  Sequential.machine (move r.origin r.data) (readData r)

/-- Start at an actual input-cursor bookmark. Read the origin metadata, then
the actual data tag/payload through native Boolean branches. False payload
and EOF are distinct. Only the three reply cells are written; a caller may
decode and clear them before moving the cursor, retaining the reply in finite
control. All hops and branch dispatches are real native transitions. -/
def machine {lanes : ℕ} (r : Roles lanes) : Main.Machine :=
  Sequential.machine (move r.bookmark r.origin)
    (Branch.machine (writeReply r r.origin .origin) (nonOrigin r))

/-- Pure readout of the actual buffered cells used in the execution theorem;
this function is not called by the transition table. -/
def observed {lanes : ℕ} (r : Roles lanes) (base row : ℕ) (work : ℕ → Bool) : Reply :=
  if work (WorkLanes.address r.origin base row) then .origin
  else if work (WorkLanes.address r.data base row) then
    .bit (work (WorkLanes.address r.data base (row+1))) else .eof

def footprint {lanes : ℕ} (r : Roles lanes) (base row : ℕ) : Footprint :=
  ⟨{WorkLanes.address r.replyOrigin base row,
    WorkLanes.address r.replyPresent base row,
    WorkLanes.address r.replyValue base row},∅⟩

end CatalyticTreeEval.Contracts.NativeInputInspect
end

/- Buffered input definition: Definitions.Def_CatalyticTreeEval_NativeInputLocate -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeInputLocate

def entryDistance {lanes : ℕ} (bookmark : Fin lanes) : ℕ :=
  3*(lanes+1)+bookmark.val-lanes

def padding (lanes : ℕ) : ℕ := 3*(lanes+1)-1

/-- From the actual origin column at row0, seek the unique input-cursor
bookmark on rows3,6,9,... . The cursor position is tape data, not a runtime
address embedded in the finite controller. -/
def machine {lanes : ℕ} (bookmark : Fin lanes) : Main.Machine :=
  Sequential.machine (NativeLiteral.machine .right (entryDistance bookmark) none)
    (NativeMarkerSeek.machine .right (padding lanes))

def time {lanes : ℕ} (bookmark : Fin lanes) (inputHead : ℕ) : ℕ :=
  (entryDistance bookmark+1)+(inputHead*(padding lanes+1)+1)

end CatalyticTreeEval.Contracts.NativeInputLocate
end

/- Buffered input definition: Definitions.Def_CatalyticTreeEval_NativeInputProbe -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeInputProbe

/-- Actual virtual-input probe from the physical work-origin column: locate
the unique input-cursor bookmark, inspect its metadata/tag/payload, and leave
three explicit reply bits at that row. -/
def machine {lanes : ℕ} (r : NativeInputInspect.Roles lanes) : Main.Machine :=
  Sequential.machine (NativeInputLocate.machine r.bookmark) (NativeInputInspect.machine r)

end CatalyticTreeEval.Contracts.NativeInputProbe
end

/- Buffered input definition: Definitions.Def_CatalyticTreeEval_NativeInputCursorMove -/
section

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeInputCursorMove

open CatalyticMatching.General

def selectedMove (direction : Move) (atOrigin : Bool) : Move :=
  match direction with
  | .left => if atOrigin then .stay else .left
  | .stay => .stay
  | .right => .right

def distance (lanes : ℕ) (direction : Move) (atOrigin : Bool) : ℕ :=
  match selectedMove direction atOrigin with
  | .stay => 0
  | _ => 3*(lanes+1)

/-- The direction and captured origin bit are finite source context. Clear
the current actual bookmark, perform the charged clamped cursor movement,
and mark the new position. No virtual input position enters the code. -/
def machine (lanes : ℕ) (direction : Move) (atOrigin : Bool) : Main.Machine :=
  Sequential.machine (NativeLiteral.machine .stay 0 (some false))
    (Sequential.machine
      (NativeLiteral.machine (selectedMove direction atOrigin) (distance lanes direction atOrigin) none)
      (NativeLiteral.machine .stay 0 (some true)))

def time (lanes : ℕ) (direction : Move) (atOrigin : Bool) : ℕ :=
  1+((distance lanes direction atOrigin+1)+1)

end CatalyticTreeEval.Contracts.NativeInputCursorMove
end

/- Pure public specification from Solutions.CatalyticTreeEvaluation.NativeInputInspectReply -/
section
namespace CatalyticTreeEval.Contracts.NativeInputInspect
def replyTime {lanes : ℕ} (r : Roles lanes) (source : Fin lanes) : ℕ :=
  (NativeLaneFlagCopy.distance source r.replyOrigin+1)+
    ((NativeLaneFlagCopy.distance r.replyOrigin r.replyPresent+1)+
      ((NativeLaneFlagCopy.distance r.replyPresent r.replyValue+1)+
        (NativeLaneFlagCopy.distance r.replyValue r.replyOrigin+1)))

end CatalyticTreeEval.Contracts.NativeInputInspect
end

/- Pure public specification from Solutions.CatalyticTreeEvaluation.NativeInputInspectPayload -/
section
namespace CatalyticTreeEval.Contracts.NativeInputInspect
def replyWork {lanes : ℕ} (r : Roles lanes) (rowBase : ℕ) (reply : Reply) (work : ℕ → Bool) : ℕ → Bool :=
  Function.update (Function.update (Function.update work
    (rowBase+r.replyOrigin.val) reply.isOrigin) (rowBase+r.replyPresent.val) reply.isPresent)
    (rowBase+r.replyValue.val) reply.value

def rowFootprint {lanes : ℕ} (r : Roles lanes) (rowBase : ℕ) : Footprint :=
  ⟨{rowBase+r.replyOrigin.val,rowBase+r.replyPresent.val,rowBase+r.replyValue.val},∅⟩

def Post {lanes : ℕ} {A B : Main.Machine} (r : Roles lanes) (rowBase : ℕ) (reply : Reply)
    (c : Config A) (d : Config B) : Prop :=
  d.workHead=rowBase+r.replyOrigin.val ∧ d.work=replyWork r rowBase reply c.work ∧
    d.inputHead=c.inputHead ∧ d.catalystHead=c.catalystHead ∧
    d.catalyst=c.catalyst ∧ d.output=c.output

end CatalyticTreeEval.Contracts.NativeInputInspect
end

/- Pure public specification from Solutions.CatalyticTreeEvaluation.NativeInputInspect -/
section
namespace CatalyticTreeEval.Contracts.NativeInputInspect
def dataCase {lanes : ℕ} (r : Roles lanes) (tag : Bool) : Main.Machine :=
  if tag then readPayload r else writeReply r r.data .eof

def dataTime {lanes : ℕ} (r : Roles lanes) (tag : Bool) : ℕ :=
  if tag then (lanes+2)+(1+((lanes+2)+replyTime r r.data)) else replyTime r r.data

def dataReply {lanes : ℕ} (r : Roles lanes) (rowBase : ℕ) (tag : Bool) (work : ℕ → Bool) : Reply :=
  if tag then .bit (work (rowBase+(lanes+1)+r.data.val)) else .eof

end CatalyticTreeEval.Contracts.NativeInputInspect
end

/- Pure public specification from Solutions.CatalyticTreeEvaluation.NativeInputInspect -/
section
namespace CatalyticTreeEval.Contracts.NativeInputInspect
def originCase {lanes : ℕ} (r : Roles lanes) (origin : Bool) : Main.Machine :=
  if origin then writeReply r r.origin .origin else nonOrigin r

def originTime {lanes : ℕ} (r : Roles lanes) (rowBase : ℕ) (work : ℕ → Bool) (origin : Bool) : ℕ :=
  if origin then replyTime r r.origin else
    (NativeLaneFlagCopy.distance r.origin r.data+1)+(1+dataTime r (work (rowBase+r.data.val)))

def localReply {lanes : ℕ} (r : Roles lanes) (rowBase : ℕ) (work : ℕ → Bool) : Reply :=
  if work (rowBase+r.origin.val) then .origin else
    dataReply r rowBase (work (rowBase+r.data.val)) work

end CatalyticTreeEval.Contracts.NativeInputInspect
end

/- Pure public specification from Solutions.CatalyticTreeEvaluation.NativeInputProbe -/
section
namespace CatalyticTreeEval.Contracts.NativeInputProbe
open NativeInputInspect (Roles)
def rowBase (lanes base inputHead : ℕ) : ℕ := base+(lanes+1)*(3+3*inputHead)

def bound (lanes base inputHead : ℕ) : ℕ := base+(lanes+1)*(5+3*inputHead)

def time {lanes : ℕ} (r : Roles lanes) (base inputHead : ℕ) (work : ℕ → Bool) : ℕ :=
  NativeInputLocate.time r.bookmark inputHead+
    ((NativeLaneFlagCopy.distance r.bookmark r.origin+1)+
      (1+NativeInputInspect.originTime r (rowBase lanes base inputHead) work
        (work (rowBase lanes base inputHead+r.origin.val))))

end CatalyticTreeEval.Contracts.NativeInputProbe
end

/- Pure public specification from Solutions.CatalyticTreeEvaluation.NativeInputProbeBuffer -/
section
namespace CatalyticTreeEval.Contracts.NativeInputProbe
open NativeInputInspect (Roles Reply)
/-- An actual finite buffered input, with its real false EOF tag and
separate origin metadata. The input bits are the physical A cells. -/
structure Buffer {lanes : ℕ} (r : Roles lanes) (base : ℕ)
    (params : List Bool) (work : ℕ → Bool) : Prop where
  origin : ∀ row, work (WorkLanes.address r.origin base row)=decide (row=3)
  tags : ∀ j < params.length, work (WorkLanes.address r.data base (6+3*j))=true
  values : ∀ (j : ℕ) (hj : j<params.length),
    work (WorkLanes.address r.data base (7+3*j))=params[j]
  terminator : work (WorkLanes.address r.data base (6+3*params.length))=false

def readReply (params : List Bool) (inputHead : ℕ) : Reply :=
  if inputHead=0 then .origin else
    match params[inputHead-1]? with
    | none => .eof
    | some bit => .bit bit

end CatalyticTreeEval.Contracts.NativeInputProbe
end


