-- Prove2me | Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Computability
-- name    : SpectralSharpness_NormalWindow_Supplement_Computability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:04:38.637643+00:00
-- url     : https://prove2.me/theorems/e08c682e-4d72-47b3-a023-a25fa5da22e0
-- title:
--   Finite oracle programs and real Cauchy realizers
-- statement:
--   A Cauchy name q for a real x supplies rational approximations with |q(n)−x|≤2^(−n). Finite oracle programs have zero, successor, pairing projections, oracle query, pairing, composition, primitive recursion and sequential unbounded search instructions. A fuel-indexed evaluator computes finite terminating executions; an unresolved earlier search candidate prevents moving to a later one.
--
--   A Type-2 computable real function has one program that, for every real input in the domain, every Cauchy name of that input and every requested precision, terminates with an appropriately accurate rational output. Names are not required to be computable. The program must work on all equivalent names, and correctness refers to the same real output. A discrete real-input function has one program terminating with its exact label. Computability of an individual real reuses DetParamSVP.IsComputableReal from the platform.
--
--   The halting-boundary construction uses Mathlib’s acceptable partial-recursive machine codes, their bounded evaluation at input zero, the finite dyadic approximants α_t and the infinite dyadic sum α. The boundary label is +1 exactly for x<α, with −1 at a tie. Many-one equivalence uses total computable reductions in both directions. These are effective definitions, with neither continuity nor a classification oracle assumed.
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, §5; Theorems 5.1–5.2, p. 12

import Mathlib
import Definitions.Def_DetParamSVP_ComputableReal
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Fourier

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

/-- Finite oracle programs for partial recursive functions, including an oracle instruction.
The fixed syntax makes the same program act on every input name. -/
inductive OracleProgram where
  | zero | succ | left | right | query
  | pair : OracleProgram → OracleProgram → OracleProgram
  | comp : OracleProgram → OracleProgram → OracleProgram
  | prec : OracleProgram → OracleProgram → OracleProgram
  | search : OracleProgram → OracleProgram
  deriving Inhabited

def oracleEval : ℕ → OracleProgram → (ℕ → ℕ) → ℕ → Option ℕ
  | 0, _, _, _ => none
  | fuel+1, c, q, a => match c with
    | .zero => some 0
    | .succ => some (a+1)
    | .left => some a.unpair.1
    | .right => some a.unpair.2
    | .query => some (q a)
    | .pair c d => do
        let u ← oracleEval fuel c q a
        let v ← oracleEval fuel d q a
        pure (Nat.pair u v)
    | .comp c d => do
        let u ← oracleEval fuel d q a
        oracleEval fuel c q u
    | .prec c d =>
        Nat.rec (oracleEval fuel c q a.unpair.1)
          (fun n r => do
            let v ← r
            oracleEval fuel d q (Nat.pair a.unpair.1 (Nat.pair n v))) a.unpair.2
    | .search c =>
        ((List.range (fuel+1)).foldl (fun r n => r.bind fun found =>
          match found with
          | some k => some (some k)
          | none => (oracleEval fuel c q (Nat.pair a n)).map fun v =>
              if v=0 then some n else none) (some none)).join

def decodeRational (n : ℕ) : ℚ := (Encodable.decode (α := ℚ) n).getD 0
def cauchyName (q : ℕ → ℚ) (x : ℝ) : Prop :=
  ∀ n, |(q n:ℝ)-x| ≤ (2:ℝ)^(-(n:ℤ))
def typeTwoComputable (S : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ c : OracleProgram, ∀ x ∈ S, ∀ q : ℕ → ℚ, cauchyName q x →
    ∀ n, ∃ fuel m, oracleEval fuel c (fun i => Encodable.encode (q i)) n = some m ∧
      |(decodeRational m:ℝ)-f x| ≤ (2:ℝ)^(-(n:ℤ))

def discreteComputable (S : Set ℝ) (c : ℝ → Fin 3) : Prop :=
  ∃ p : OracleProgram, ∀ x ∈ S, ∀ q : ℕ → ℚ, cauchyName q x →
    ∃ fuel, oracleEval fuel p (fun i => Encodable.encode (q i)) 0 = some (c x).val

abbrev Machine := Nat.Partrec.Code
/-- Mathlib's universal step-bounded evaluation; input fixed to zero. -/
def haltsWithin (M : Machine) (n : ℕ) : Bool := (M.evaln n 0).isSome
def halts (M : Machine) : Prop := (M.eval 0).Dom

def boundaryApprox (M : Machine) (t : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (t+1), if 0 < n ∧ haltsWithin M n then (2:ℚ)^(-(n:ℤ)) else 0
def haltingBoundary (M : Machine) : ℝ :=
  ∑' n : ℕ, if 0 < n ∧ haltsWithin M n then (2:ℝ)^(-(n:ℤ)) else 0
def boundaryLabel (M : Machine) (x : ℝ) : ℤ := if x < haltingBoundary M then 1 else -1

def manyOneEquivalent {α β : Type*} [Primcodable α] [Primcodable β]
    (P : α → Prop) (Q : β → Prop) : Prop :=
  (∃ h : α → β, Computable h ∧ ∀ a, P a ↔ Q (h a)) ∧
  (∃ h : β → α, Computable h ∧ ∀ b, Q b ↔ P (h b))

end SpectralSharpness.NormalWindow.Supplement


