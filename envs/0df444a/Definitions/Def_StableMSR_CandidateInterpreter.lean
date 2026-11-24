-- Prove2me | Definitions.Def_StableMSR_CandidateInterpreter
-- name    : StableMSR_CandidateInterpreter
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T01:21:34.099423+00:00
-- url     : https://prove2.me/theorems/50046d11-4e4b-43b6-a3c5-ed7d0ba2e5ce
-- title:
--   Fuel-bounded integer execution and the explicit names of candidate keys
-- statement:
--   A computable evaluator executes a list of integer commands against register and memory banks. Each syntax inspection consumes one unit of fuel. The concrete candidate generator uses injective names for ordered tight keys, obtained by encoding the component, a zero delimiter, and the sequence of separator assignments.
-- source:
--   Implementation of Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_CanonicalCandidateProgram
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open Compiler
set_option autoImplicit false
set_option maxRecDepth 18000
set_option maxHeartbeats 2400000

structure Banks where
  reg : ℕ→ℤ
  mem : ℤ→ℤ
def Banks.put (s:Banks) (r:ℕ) (v:ℤ) : Banks := {s with reg:=Function.update s.reg r v}
def Banks.write (s:Banks) (i v:ℤ) : Banks := {s with mem:=Function.update s.mem i v}
def banks (s:Store) : Banks := ⟨s.ptrs,s.imem⟩
def restore (s:Store) (b:Banks) : Store := {s with ptrs:=b.reg,imem:=b.mem}
def IOp.act : IOp→Banks→Banks
  | .set d v,s=>s.put d v | .copy d r,s=>s.put d (s.reg r)
  | .inc d,s=>s.put d (s.reg d+1) | .dec d,s=>s.put d (s.reg d-1)
  | .add d a b,s=>s.put d (s.reg a+s.reg b) | .sub d a b,s=>s.put d (s.reg a-s.reg b)
  | .load d a,s=>s.put d (s.mem (s.reg a)) | .store a r,s=>s.write (s.reg a) (s.reg r)
/-- Fuel counts one inspection of a syntax node, including branches and empty commands. -/
def run : ℕ→List Code→Banks→Option Banks
  | _,[],s=>some s
  | 0,_::_,_=>none
  | f+1,.skip::ps,s=>run f ps s
  | f+1,.atom o::ps,s=>run f ps (o.act s)
  | f+1,.seq p q::ps,s=>run f (p::q::ps) s
  | f+1,.cond a b p q::ps,s=>if s.reg a ≤ s.reg b then run f (p::ps) s else run f (q::ps) s
  | f+1,.loop a b p::ps,s=>if s.reg a ≤ s.reg b then run f (p::.loop a b p::ps) s else run f ps s

def IOp.low : IOp→Bool
  | .set d _ | .copy d _ | .inc d | .dec d | .add d _ _ | .sub d _ _ | .load d _=>decide (6≤d)
  | .store _ _=>true
def Code.low : Code→Bool
  | .skip=>true | .atom o=>o.low | .seq p q | .cond _ _ p q=>p.low && q.low | .loop _ _ p=>p.low


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Naming
open SingleCircuit
set_option autoImplicit false

def pairs (a:Assignment) := a.flatMap (fun q=>[q.1,q.2])
def digits (key:Key) := key.1.map Nat.succ ++ [0] ++ pairs key.2
def push (a:ℕ) : ℕ→ℕ | 0=>2*a+1 | z+1=>2*push a z
def code : List ℕ→ℕ | []=>0 | z::zs=>push (code zs) z
def name (key:Key) := code (digits key).reverse


end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Naming


