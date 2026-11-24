-- Prove2me | Definitions.Def_StableMSR_IntegerRegionalGeometry
-- name    : StableMSR_IntegerRegionalGeometry
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-24T00:15:37.265802+00:00
-- url     : https://prove2.me/theorems/adc0c701-3ebe-4a9a-aaaf-2c059f9d7032
-- title:
--   Bounded integer distance tables for the exact regional candidate stream
-- statement:
--   Rank each directed point-pair distance by the number of strictly smaller point-pair distances. An offset encodes its band relative to twice, four times, and eight times the live scale. The integer table occupies one private word per ordered pair and supplies an instance of the same regional compiler at a fixed surrogate scale.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6. https://arxiv.org/abs/2611.03547

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
namespace StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open Compiler OracleQueries WindowCSP SingleCircuit
open scoped Classical
set_option autoImplicit false

def unit (n:ℕ) := n*n+1
def address {n:ℕ} (a b:Fin n) := cell 6 (a.val*n+b.val)
def samples (x:World) := (List.finRange x.n).flatMap fun a=>(List.finRange x.n).map (x.dist a)
noncomputable def rank (ds:List ℝ) (v:ℝ) := (ds.filter (fun z=>decide (z<v))).length
noncomputable def band (R v:ℝ) : ℕ := if v≤2*R then 0 else if v≤4*R then 3 else if v≤8*R then 5 else 9
noncomputable def scalar (n:ℕ) (ds:List ℝ) (R v:ℝ) := band R v*unit n+rank ds v
def Prepared (x:World) (R:ℝ) (m:ℤ→ℤ) := ∀a b:Fin x.n,m (address a b)=(scalar x.n (samples x) R (x.dist a b):ℤ)
def Bounded (n:ℕ) (m:ℤ→ℤ) := ∀a b:Fin n,0 ≤ m (address a b) ∧ m (address a b)<10*(unit n:ℤ)
def matrix (x:World) (m:ℤ→ℤ) : World := {x with dist:=fun a b=>(m (address a b):ℝ)}
noncomputable def data (x:World) (m:ℤ→ℤ) (r h:ℕ) :=
  SingleCodes.instanceOf (matrix x m) (WindowProfiles.piece x (r/x.n) (r%x.n)) (unit x.n:ℝ) h

def integerOp : Op→Prop
  | .pointerConst .. | .pointerCopy .. | .pointerInc .. | .pointerDec .. | .pointerAdd .. |
    .pointerSub .. | .integerLoad .. | .integerStore ..=>True
  | _=>False
def integerCond : Cond→Prop | .pointerLE ..=>True | .realNonpos _=>False
def IntegerCmd : Cmd→Prop
  | .skip=>True | .atom o=>integerOp o | .seq a b=>IntegerCmd a ∧ IntegerCmd b
  | .ite c a b=>integerCond c ∧ IntegerCmd a ∧ IntegerCmd b
  | .whileDo c b=>integerCond c ∧ IntegerCmd b

end StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry


