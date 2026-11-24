-- Prove2me | Definitions.Def_StableMSR_RegionalProductionTable
-- name    : StableMSR_RegionalProductionTable
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T23:07:07.801825+00:00
-- url     : https://prove2.me/theorems/adcc4905-4dcb-48ca-a500-236c4612cef3
-- title:
--   Physical input table for one separator production stream
-- statement:
--   One regional slot supplies a signed exit handle and a stream of symbolic separator events. Integer scratch lanes hold opcodes, event references, and literal point memberships. A negative exit encodes an absent or stopped slot. The compiler assigns all gate addresses from this stream.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Formal implementation of the finite separator circuit.

import Definitions.Def_StableMSR_SeparatorProductionEvents
import Definitions.Def_StableMSR_RegionalPacketCalls
namespace StableMSR.Recovery.NativeWriter.Production
open Compiler OracleQueries SingleCircuit SingleCodes WindowCSP Relative
open scoped Classical
set_option autoImplicit false

structure Script where
  events : List Event
  exit : ℤ

def Script.packet (t : Script) : Packet :=
  if t.exit<0 then ⟨#[],t.exit⟩ else ⟨(play t.events).gates,(resolve (play t.events) t.exit.toNat:ℤ)⟩

noncomputable def regionalScript (x : World) (h w r : ℕ) : Script :=
  let u:=r/x.n
  let i:=r%x.n
  if i ∈ WindowProfiles.keys x u then
    if 0<scale x u then
      let t:=chart (instanceOf x (WindowProfiles.piece x u i) (scale x u) h) w
      ⟨t.1,(t.2:ℤ)⟩
    else ⟨[],-2⟩
  else ⟨[],-1⟩

/-- Scratch lanes zero through three hold the header, event kinds, handles, and point bits.
Lane four is available to the renderer for its event-to-gate table. -/
def cell (a i : ℕ) := word 7 (8*i+a)
def Event.tag : Event→ℤ | .mask _=>0 | .child _=>1 | .join _=>2 | .save=>3
def Event.arg : Event→ℤ | .child k | .join k=>(k:ℤ) | _=>0
def Event.bit (e : Event) (k : ℕ) : ℤ := match e with | .mask m=>if m.contains k then 1 else 0 | _=>0

def Stored (n : ℕ) (m : ℤ→ℤ) (t : Script) : Prop :=
  m (cell 0 0)=(t.events.length:ℤ) ∧ m (cell 0 1)=t.exit ∧
  ∀i (hi:i<t.events.length), let e:=t.events[i]
    m (cell 1 i)=e.tag ∧ m (cell 2 i)=e.arg ∧
      ∀pts,e=.mask pts → ∀k<n,m (cell 3 (i*n+k))=e.bit k

/-- A source can use scratch during enumeration and leaves all existing gate and directory columns intact. -/
def Source (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀(x : World) (s : Store),1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀r p : ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n →
  ∃t z,Executes x.dist cmd s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
    Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧
    (∀j,1≤j → j≤6 → ∀a,t.imem (word j a)=s.imem (word j a)) ∧
    Stored x.n t.imem (regionalScript x (budget (e:ℝ)) (widthBound (e:ℝ)) r)

end StableMSR.Recovery.NativeWriter.Production


