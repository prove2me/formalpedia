-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Supplement_Oracle
-- name    : AMRangeAvoid_Characterization_Supplement_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:21:53.710197+00:00
-- url     : https://prove2.me/theorems/dd6ebada-793b-4e2e-aa85-92a899a2e4f4
-- title:
--   Relativized computation, circuits and SSLB
-- statement:
--   A binary language oracle returns a single membership bit for each finite query string. A finite oracle Turing machine executes ordinary Mathlib stack-machine transitions and an explicit query transition. Polynomial-time oracle computation requires one fixed program and polynomial clock for all inputs.
--
--   An oracle circuit consists of ordinary Boolean gates and query gates with an explicit ordered list of earlier wires. Both the membership circuit and the covering circuit of SSLB may query the same oracle. The promises retain the positive threshold, the exact covering-circuit arity, and the factor-four size gap.
--
--   $$\Pi^O_{\mathrm{YES}}:\ |S|\ge4\tau,\qquad \Pi^O_{\mathrm{NO}}:\ |S|\le\tau\ \land\ S\subseteq\operatorname{Im}(C^O).$$
--
--   Relativized prAM and deterministic many-one reductions use this same oracle. Hardness quantifies over every promise problem in relativized prAM; it is not hardness restricted to ordinary machines or circuits. This definition reuses the published general oracle-machine interface without any optimization-oracle assumption.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Theorem 3.10 and proof, printed p.19 (PDF p.21); Definitions 2.2,3.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_SSLB
import Definitions.Def_HMBinPacking_OracleMachine

namespace AMRangeAvoid.Characterization.Supplement

/-- A language oracle supplies one membership bit. All ordinary steps are actual
finite Mathlib TM2 steps; a query reads the designated binary stack. -/
def PolyTimeO (O : Bits → Bool) (f : Bits → Bits) : Prop :=
  ∃ M : HMBinPacking.OracleMachine, ∃ C k : ℕ, ∀ x,
    HMBinPacking.ORunsWithin M (fun q => [O q]) x (f x)
      (C * (x.length + 1) ^ k) (C * (x.length + 1) ^ k + x.length)

/-- Oracle query wires are ordered; the query length and every wire are explicit.
Ordinary gates keep the base Boolean circuit syntax. -/
inductive OGate where
  | ordinary (g : Gate)
  | query (wires : List ℕ)
  deriving DecidableEq, Repr, Inhabited

def OGate.eval (O : Bits → Bool) (x values : Bits) : OGate → Bool
  | .ordinary g => g.eval x values
  | .query ws => O (ws.map (fun i => values.getD i false))

def OGate.valid (inputs earlier : ℕ) : OGate → Bool
  | .ordinary g => g.valid inputs earlier
  | .query ws => ws.all (fun i => decide (i < earlier))

def OGate.code : OGate → Bits
  | .ordinary g => natCode 0 ++ g.code
  | .query ws => natCode 1 ++ natCode ws.length ++ (ws.map natCode).flatten

def readOGate (b : Bits) : Option (OGate × Bits) := do
  let (tag, rest) ← readNat b
  match tag with
  | 0 => let (g, tail) ← readGate rest; pure (.ordinary g, tail)
  | 1 =>
    let (n, tail) ← readNat rest
    let (ws, tail) ← readNats n tail
    pure (.query ws, tail)
  | _ => none

def readOGates : ℕ → Bits → Option (List OGate × Bits)
  | 0, b => some ([], b)
  | n + 1, b => do
    let (g, rest) ← readOGate b
    let (gs, tail) ← readOGates n rest
    pure (g :: gs, tail)

structure OCircuit where
  inputs : ℕ
  gates : List OGate
  outputs : List ℕ
  deriving DecidableEq, Repr, Inhabited

def OCircuit.eval (C : OCircuit) (O : Bits → Bool) (x : Bits) : Bits :=
  let values := C.gates.foldl (fun vs g => vs ++ [g.eval O x vs]) []
  C.outputs.map (fun i => values.getD i false)

def OCircuit.valid (C : OCircuit) : Bool :=
  C.gates.zipIdx.all (fun gi => gi.1.valid C.inputs gi.2) &&
    C.outputs.all (fun i => decide (i < C.gates.length))

def OCircuit.code (C : OCircuit) : Bits :=
  frame (List.replicate C.inputs false) ++ natCode C.gates.length ++
    (C.gates.map OGate.code).flatten ++ natCode C.outputs.length ++
      (C.outputs.map natCode).flatten

def readOCircuit (b : Bits) : Option (OCircuit × Bits) := do
  let (slots, rest) ← readFrame b
  if slots.any id then none else do
    let (ng, rest) ← readNat rest
    let (gs, rest) ← readOGates ng rest
    let (no, rest) ← readNat rest
    let (os, rest) ← readNats no rest
    let C : OCircuit := ⟨slots.length, gs, os⟩
    if C.valid then pure (C, rest) else none

def OCircuit.image (C : OCircuit) (O : Bits → Bool) : Set Bits :=
  {y | ∃ u : Word C.inputs, C.eval O (wordBits u) = y}

structure OInstance where
  n : ℕ
  witness : ℕ
  threshold : ℕ
  membership : OCircuit
  cover : OCircuit
  deriving DecidableEq, Repr, Inhabited

def OInstance.valid (I : OInstance) : Bool :=
  decide (0 < I.threshold ∧ I.membership.inputs = I.n + I.witness ∧
    I.membership.outputs.length = 1 ∧ I.cover.inputs = ceilLog2 I.threshold ∧
    I.cover.outputs.length = I.n) && I.membership.valid && I.cover.valid

def OInstance.code (I : OInstance) : Bits :=
  natCode I.n ++ natCode I.witness ++ natCode I.threshold ++
    I.membership.code ++ I.cover.code

def decodeOInstance (b : Bits) : Option OInstance := do
  let (n, rest) ← readNat b
  let (w, rest) ← readNat rest
  let (t, rest) ← readNat rest
  let (P, rest) ← readOCircuit rest
  let (C, rest) ← readOCircuit rest
  let I : OInstance := ⟨n, w, t, P, C⟩
  if rest = [] ∧ I.valid = true then pure I else none

def OInstance.elements (I : OInstance) (O : Bits → Bool) : Finset (Word I.n) :=
  Finset.univ.filter (fun s => ∃ w : Word I.witness,
    (I.membership.eval O (wordBits s ++ wordBits w)).getD 0 false = true)

def OYes (O : Bits → Bool) : Set Bits := {b |
  ∃ I, decodeOInstance b = some I ∧ 0 < I.threshold ∧
    4 * I.threshold ≤ (I.elements O).card}

def ONo (O : Bits → Bool) : Set Bits := {b |
  ∃ I, decodeOInstance b = some I ∧ 0 < I.threshold ∧
    (I.elements O).card ≤ I.threshold ∧
    ∀ s ∈ I.elements O, wordBits s ∈ I.cover.image O}

/-- The full relativization: BOTH circuits may query O. -/
def OracleSSLB (O : Bits → Bool) : PromiseProblem where
  yes := OYes O
  no := ONo O
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨I, hi, hp, hy⟩ ⟨J, hj, _, hn, _⟩
    have e : I = J := Option.some.inj (hi.symm.trans hj)
    subst J
    omega

def WitnessesAMO (O : Bits → Bool) (A : PromiseProblem) (V : AMVerifier) : Prop :=
  PolyTimeO O V.program ∧
    (∀ x ∈ A.yes, ∀ r : Word (V.random.value x.length),
      ∃ w : Word (V.response.value x.length), V.run x (wordBits r) (wordBits w) = true) ∧
    (∀ x ∈ A.no, 3 * V.answerableCount x ≤ 2 ^ V.random.value x.length)

def InPrAMO (O : Bits → Bool) (A : PromiseProblem) : Prop := ∃ V, WitnessesAMO O A V

def PromiseReducesO (O : Bits → Bool) (A B : PromiseProblem) : Prop :=
  ∃ f : Bits → Bits, PolyTimeO O f ∧
    (∀ x ∈ A.yes, f x ∈ B.yes) ∧ (∀ x ∈ A.no, f x ∈ B.no)

def IsPrAMHardO (O : Bits → Bool) (B : PromiseProblem) : Prop :=
  ∀ A : PromiseProblem, InPrAMO O A → PromiseReducesO O A B

end AMRangeAvoid.Characterization.Supplement


