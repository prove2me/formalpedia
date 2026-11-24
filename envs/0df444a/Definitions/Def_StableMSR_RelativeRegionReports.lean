-- Prove2me | Definitions.Def_StableMSR_RelativeRegionReports
-- name    : StableMSR_RelativeRegionReports
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-23T22:34:19.513778+00:00
-- url     : https://prove2.me/theorems/1b74b037-290c-4d09-b132-30c5a0fdf171
-- title:
--   Regional gate records with signed local predecessor displacements
-- statement:
--   A positive-scale slot emits its local gates and a root token. Empty and stopped slots have zero length and distinct sentinel tokens. At local ordinal $j$, an edge to ordinal $u$ is recorded as $u-j$. This displacement is independent of the position at which the packet is appended. The stream also includes each slot length, the two initial records, stop padding, and the point-membership bits of its literals.
-- source:
--   Ravichandran and Reyzin, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Relative-address serialization interface for the mission’s ordered separator circuits.

import Definitions.Def_StableMSR_LogicalAssemblyColumns
namespace StableMSR.Recovery.NativeWriter.Relative
open OracleQueries Compiler SingleCircuit SingleCodes SingleRAM WindowCSP
open WindowProfiles (keys piece)
open scoped Classical
set_option autoImplicit false

/-- A slot carries its local gates and a signed root token. The absent and stopped tokens are -1 and -2. -/
structure Packet where
  gates : Gates
  token : ℤ
noncomputable def packet (x : World) (h w r : ℕ) : Packet :=
  if r%x.n ∈ keys x (r/x.n) then
    if 0 < scale x (r/x.n) then
      let c:=regionalCircuit x (piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) h w
      ⟨c.1,(c.2:ℤ)⟩
    else ⟨#[],-2⟩
  else ⟨#[],-1⟩
/-- The next output position in a sequential concatenation of local gate lists. -/
noncomputable def firstGate (x : World) (h w : ℕ) : ℕ → ℕ
  | 0=>2 | r+1=>firstGate x h w r+(packet x h w r).gates.size
noncomputable def total (x : World) (h w : ℕ) :=
  max (firstGate x h w (x.rows*x.n)) ((x.rows*x.n+2)/3)

def displacement (op : Gate) (j v : ℕ) : ℤ :=
  if 1≤opCode op then (v:ℤ)-(j:ℤ) else (v:ℤ)

/-- Each predecessor is a displacement from the local gate's own ordinal. -/
def Record (n : ℕ) (s : Store) (p j : ℕ) (op : Gate) : Prop :=
  s.imem (word 1 p)=opCode op ∧
  s.imem (word 2 p)=displacement op j (leftID op) ∧
  s.imem (word 3 p)=displacement op j (rightID op) ∧
  ∀ i<n, s.imem (word 5 (p*n+i))=(if (tinyMask op).contains i then 1 else 0)

/-- The stream consists of the two initial records, successive local gate lists,
stop padding, and a directory of pairs (local root token, gate count). -/
def Reports (x : World) (h w : ℕ) (s : Store) : Prop :=
  let R:=x.rows*x.n
  let G:=total x h w
  s.ptrs 0=(x.n:ℤ) ∧ s.ptrs 1=(x.k:ℤ) ∧
  s.imem (word 0 0)=(G:ℤ) ∧ s.imem (word 0 1)=(x.rows:ℤ) ∧
  Record x.n s 0 0 (.atom []) ∧ Record x.n s 1 1 .stop ∧
  (∀ r<R, let c:=packet x h w r
    ∀ j<c.gates.size, Record x.n s (firstGate x h w r+j) j (gateAt c.gates j)) ∧
  (∀ p, firstGate x h w R≤p → p<G → Record x.n s p 0 .stop) ∧
  ∀ r<3*G,
    s.imem (word 4 r)=(if r<R then (packet x h w r).token else -1) ∧
    s.imem (word 6 r)=(if r<R then ((packet x h w r).gates.size:ℤ) else 0)

def GeneratesReports (e : ℚ) (c D b : ℕ) (cmd : Cmd) : Prop :=
  ∀ (x : World) (s : Store), 1 ≤ x.k → x.k < x.n → IsMetricArray x.dist → Ready x s →
    ∃ t z, Executes x.dist cmd s t z ∧ z ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      Reports x (budget (e:ℝ)) (widthBound (e:ℝ)) t
end StableMSR.Recovery.NativeWriter.Relative


