-- Prove2me | Definitions.Def_StableMSR_RegionalPacketCalls
-- name    : StableMSR_RegionalPacketCalls
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T22:45:04.598065+00:00
-- url     : https://prove2.me/theorems/2cb99e44-9dd1-4437-8db0-dc34638fdd48
-- title:
--   Native calling convention for one regional gate packet
-- statement:
--   A packet call receives the original ready scene, a slot index, and the next free gate index. It writes local relative gate records and, when appropriate, one signed-token and length entry. It returns the number of gates emitted, retains the earlier records and directory entries, and makes the original scene available for the next call. Three fixed packet shapes supply the initial gates, a padding stop, and an unused root row.
-- source:
--   Native implementation interface for the ordered separator circuits in Ravichandran and Reyzin, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_RelativeRegionReports
namespace StableMSR.Recovery.NativeWriter.Relative
open OracleQueries Compiler SingleCircuit WindowCSP
set_option autoImplicit false

/-- The four calls made by the global controller. Only a regional call inspects the scene. -/
inductive Request where | seed | region | pad | absent
noncomputable def payload (x : World) (h w r : ℕ) : Request → Gates
  | .seed=>#[.atom [],.stop] | .region=>(packet x h w r).gates | .pad=>#[.stop] | .absent=>#[]
noncomputable def directory (x : World) (h w r : ℕ) : Request → Option (ℤ×ℕ)
  | .region=>some ((packet x h w r).token,(packet x h w r).gates.size)
  | .absent=>some (-1,0) | _=>none
def DirAt (s : Store) (r : ℕ) (v : ℤ×ℕ) := s.imem (word 4 r)=v.1 ∧ s.imem (word 6 r)=(v.2:ℤ)

/-- A single packet call reads (slot, gate cursor) from registers 3 and 4.
It returns the length in register 7, preserves the original scene and earlier records,
and writes just the packet and its directory entry when present. -/
def PacketCall (x : World) (h w r p : ℕ) (q : Request) (s t : Store) : Prop :=
  let g:=payload x h w r q
  Ready x t ∧ (∀ i ∈ [3,4,5], t.ptrs i=s.ptrs i) ∧ t.ptrs 7=(g.size:ℤ) ∧
  (∀j<g.size, Record x.n t (p+j) j (gateAt g j)) ∧
  (∀v, directory x h w r q=some v → DirAt t r v) ∧
  (∀a<p,∀j op,Record x.n s a j op → Record x.n t a j op) ∧
  ∀a<r,∀v,DirAt s a v → DirAt t a v

def PacketGenerator (e : ℚ) (c D b : ℕ) (call : Request→Cmd) : Prop :=
  ∀(x : World) (s : Store), 1≤x.k → x.k<x.n → IsMetricArray x.dist → Ready x s →
  ∀(q : Request) (r p : ℕ), s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) →
    (q=Request.region → r<x.rows*x.n) →
    ∃t z, Executes x.dist (call q) s t z ∧ z≤c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      PacketCall x (budget (e:ℝ)) (widthBound (e:ℝ)) r p q s t

end StableMSR.Recovery.NativeWriter.Relative


