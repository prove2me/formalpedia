-- Prove2me | Definitions.Def_StableMSR_InitializedSeparatorTraversal
-- name    : StableMSR_InitializedSeparatorTraversal
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T02:35:00.063777+00:00
-- url     : https://prove2.me/theorems/719b3953-b480-4a77-89ab-573dc82512b5
-- title:
--   The initialized geometry and separator traversal in the recovery algorithm
-- statement:
--   The initialized state fixes the radix, the eleven array addresses, the initially zero fresh words, and the empty stream. The middle segment consists of the geometry call, level-by-level separator enumeration, and final component requests before the finish marker. Its contract requires the exact canonical row records and component requests with a uniform running-time bound.
-- source:
--   Ravichandran and Reyzin, Appendix A.6, https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_SeparatorArenaLayout
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open WindowCSP OracleQueries Compiler SingleCircuit
def middleList:List Program:=((listOf src_generate).drop 45).take 6
def Prepared (n r h w:ℕ) (s:State):Prop:=
  let H:=h+1
  let rows:=n^(2*H)
  let M:=H*rows
  let layout:=offsets n M
  s.reg 6=1 ∧ s.reg 7=0 ∧ s.reg 64=(n:ℤ) ∧ s.reg 65=(r:ℤ) ∧
  s.reg 66=(h:ℤ) ∧ s.reg 67=(w:ℤ) ∧ s.reg 68=(H:ℤ) ∧ s.reg 69=(rows:ℤ) ∧
  s.reg 70=(M:ℤ) ∧ s.reg 82=0 ∧ s.reg 8=(cursorAt layout 11:ℤ) ∧
  (∀j:Fin 11,s.reg (71+j.val)=(cursorAt layout j.val:ℤ)) ∧
  (∀i<cursorAt layout 11,s.heap i=0) ∧ s.output=[] ∧ s.closed=false

end Logical
end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 20000

namespace Logical
open WindowCSP OracleQueries Compiler SingleCircuit TightLanguage
def middleRecords (d:Instance) (w:ℕ):List Instr :=
  rowTape Naming.name d w ++ (parts d (vertices d)).map (fun c=>.need (Naming.name (c,[])))
/-- Hoare contract for the geometry, separator traversal, and root-request
phases. The state contains the eleven initialized arrays. -/
def MiddleCorrect : Prop :=
  ∃c D b:ℕ,∀e:ℚ,0<e → e<1 →
  ∀(x:World) (s:Store),1 ≤ x.k → x.k<x.n → Ready x s → Bounded x.n s.imem →
  ∀r p:ℕ,s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → r<x.rows*x.n → r%x.n∈WindowProfiles.keys x (r/x.n) →
  ∀u:State,Prepared x.n r (budget (e:ℝ)) (widthBound (e:ℝ)) u →
    ∃t k,Executes x.n s.imem (chain middleList) u t k ∧
      k ≤ c*x.cap^D*x.n^(b*parameterEnvelope (e:ℝ)) ∧
      t.output=middleRecords (integerData x.n x.mem s.imem r (budget (e:ℝ))) (widthBound (e:ℝ))
end Logical

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM


