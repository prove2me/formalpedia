-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_SearchProblems
-- name    : CorrelatedAuctionComplexity_Main_SearchProblems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:58.319174+00:00
-- url     : https://prove2.me/theorems/ea8668a6-4227-4403-98d5-d4c551284708
-- title:
--   Encoded equilibrium and generalized-circuit search relations
-- statement:
--   The auction answer relations decode explicit rational mixed profiles and check the actual conditional MBNE inequalities or the incident-weight NE inequalities. The general problems cover every normalized explicit rational auction instance. The restricted problems require exactly $B=\{0,1/5,2/5\}$ for DFPA, or exactly $B=\{0,1/4\}$ and edge size at most four for HDFPA. Accuracy is fixed globally for the headline targets, and is any positive binary rational in the membership problems.
--
--   For input string $s$ and accuracy $\varepsilon$, answer codes have the polynomial witness bound
--
--   $$|t|\le (|s|+|\operatorname{code}(\varepsilon)|+2)^6.$$
--
--   This permits a rounded rational approximate equilibrium and rules out unbounded certificates; no rational exact equilibrium is assumed. Circuit records explicitly list nodes and SUM/NOT gates, and circuit answers satisfy the full $[0,1+\varepsilon]$ constraints. The witness bound and coding conventions are justified in the moderation notes.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Theorems 1, 2, 7; Lemmas 16, 20; Definitions 3, 4, 6; pp. 3–4, 9–12, 20–24 (PDF same pages)

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_PPAD
import Definitions.Def_CorrelatedAuctionComplexity_Main_GeneralizedCircuit

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


/-- A generous polynomial witness bound. Precision is logarithmic in 1/ε; ε is binary. -/
def witnessBound (s : Bits) (ε : ℚ) : ℕ := (s.length + (encodeRat ε).length + 2)^6

noncomputable def hAuctionSearch (ε : ℚ) (restricted : Bool := false) : TetrisHard.Rows.SearchProblem where
  valid s := 0 < ε ∧ ∃ (n : ℕ) (H : HDFPA (Fin n)), decodeH s = some ⟨n,H⟩ ∧ H.WellFormed 1 ∧
    (restricted = true → H.bids = {0,1/4} ∧ ∀ e ∈ H.edges, e.participants.card ≤ 4)
  answer s t := t.length ≤ witnessBound s ε ∧ ∃ (n : ℕ) (H : HDFPA (Fin n)) (p : H.RatProfile),
    decodeH s = some ⟨n,H⟩ ∧ H.WellFormed 1 ∧
    (restricted = true → H.bids = {0,1/4} ∧ ∀ e ∈ H.edges, e.participants.card ≤ 4) ∧
    decodeHProfile H t = some p ∧ H.IsNE (ε : ℝ) (H.realProfile p)

noncomputable def dAuctionSearch (ε : ℚ) (restricted : Bool := false) : TetrisHard.Rows.SearchProblem where
  valid s := 0 < ε ∧ ∃ (n : ℕ) (A : DFPA (Fin n)), decodeD s = some ⟨n,A⟩ ∧ A.WellFormed 1 ∧
    (restricted = true → A.bids = {0,1/5,2/5})
  answer s t := t.length ≤ witnessBound s ε ∧ ∃ (n : ℕ) (A : DFPA (Fin n)) (p : A.RatProfile),
    decodeD s = some ⟨n,A⟩ ∧ A.WellFormed 1 ∧
    (restricted = true → A.bids = {0,1/5,2/5}) ∧
    decodeDProfile A t = some p ∧ A.IsMBNE (ε : ℝ) (A.realProfile p)

/-- Every positive binary rational accuracy is an input, not a fixed or inverse-polynomial promise. -/
noncomputable def hVariableAccuracy : TetrisHard.Rows.SearchProblem where
  valid s := ∃ ε a, splitAccuracy s = some (ε,a) ∧ (hAuctionSearch ε).valid a
  answer s t := ∃ ε a, splitAccuracy s = some (ε,a) ∧ 0 < ε ∧ (hAuctionSearch ε).answer a t

noncomputable def dVariableAccuracy : TetrisHard.Rows.SearchProblem where
  valid s := ∃ ε a, splitAccuracy s = some (ε,a) ∧ (dAuctionSearch ε).valid a
  answer s t := ∃ ε a, splitAccuracy s = some (ε,a) ∧ 0 < ε ∧ (dAuctionSearch ε).answer a t

namespace GeneralizedCircuit

def gateData {n : ℕ} : Gate n → List ℕ
  | .sum u v w => [0,u.val,v.val,w.val]
  | .neg u w => [1,u.val,0,w.val]

def encode (C : GeneralizedCircuit) : Bits := pack ([C.n,C.gates.length] ++ List.range C.n ++ C.gates.flatMap gateData)

def readFin (n a : ℕ) : Option (Fin n) := if h : a < n then some ⟨a,h⟩ else none

def readGate (n : ℕ) (ns : List ℕ) (j : ℕ) : Option (Gate n) := do
  let u ← readFin n (ns.getD (3+n+4*j) 0)
  let w ← readFin n (ns.getD (5+n+4*j) 0)
  if ns.getD (2+n+4*j) 0 = 0 then
    let v ← readFin n (ns.getD (4+n+4*j) 0)
    pure (.sum u v w)
  else if ns.getD (2+n+4*j) 0 = 1 ∧ ns.getD (4+n+4*j) 0 = 0 then pure (.neg u w)
  else none

def decode (s : Bits) : Option GeneralizedCircuit := do
  let ns ← unpack s
  let n := ns.getD 0 0
  let m := ns.getD 1 0
  if n ≤ ns.length ∧ m ≤ ns.length ∧ ns.length = 2+n+4*m then
    let gs ← (List.range m).mapM (readGate n ns)
    let C : GeneralizedCircuit := ⟨n,gs⟩
    if C.encode = s then pure C else none
  else none

def encodeSolution (C : GeneralizedCircuit) (a : Fin C.n → ℚ) : Bits :=
  pack ((List.finRange C.n).flatMap fun i => ratCode (a i))

def decodeSolution (C : GeneralizedCircuit) (s : Bits) : Option (Fin C.n → ℚ) := do
  let ns ← unpack s
  if ns.length = 2*C.n then
    let a : Fin C.n → ℚ := fun i => ratAt ns (2*i.val)
    if C.encodeSolution a = s then pure a else none
  else none
end GeneralizedCircuit

/-- Bounded input use is checked on distinct incident gates, not input occurrences. -/
noncomputable def gcircuitSearch (ε : ℚ) : TetrisHard.Rows.SearchProblem where
  valid s := 0 < ε ∧ ∃ C, GeneralizedCircuit.decode s = some C ∧ C.WellFormed ∧ C.BoundedInput
  answer s t := t.length ≤ witnessBound s ε ∧ ∃ (C : GeneralizedCircuit) (a : Fin C.n → ℚ),
    GeneralizedCircuit.decode s = some C ∧ C.WellFormed ∧ C.BoundedInput ∧
    C.decodeSolution t = some a ∧ C.Solution (ε : ℝ) (fun i => (a i : ℝ))

end CorrelatedAuctionComplexity.Main


