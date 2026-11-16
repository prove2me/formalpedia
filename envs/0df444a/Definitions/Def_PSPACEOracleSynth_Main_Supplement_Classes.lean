-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_Supplement_Classes
-- name    : PSPACEOracleSynth_Main_Supplement_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T14:25:18.791375+00:00
-- url     : https://prove2.me/theorems/6244aed6-6c18-4b93-a1c2-1ac427e43c22
-- title:
--   Channel synthesis problems and uniform complexity classes
-- statement:
--   A synthesis problem assigns a partial isometry $U_x:A_x\to B_x$ to every finite string $x$. The qubit counts are polynomially bounded and $n_{\rm in}(x)\le n_{\rm out}(x)$. Size-computability is a separate predicate requiring a deterministic polynomial-time computation of both counts.
--
--   For every $x$ and integer $r\ge1$, the circuit at $(x,1^r)$ has diamond distance at most $1/r$ from one channel completion of $U_x$. The space class has one space-uniform generator and polynomial live space; the time classes have a time-uniform generator, with a bit-oracle permitted only in the oracle variant. Every generator is oracle free. The completion is chosen before the input state and can vary with $x,r$. The module also specifies deterministic P and bounded-error BQP with a classical oracle.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1740.pdf, Definition 2.9 and decision classes, pp. 10–11, 13–14

import Mathlib
import Definitions.Def_PSPACEOracleSynth_Main_Supplement_Circuit

open QAlgorithms QAlgorithms.Complexity QAdvFew.PoQOracle KTUnitary.Synth
open scoped Matrix ComplexOrder ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace PSPACEOracleSynth.Main.Supplement

/-! Definition 2.9, p. 14. The resource polynomials and machines precede every instance
and precision. The generator has no oracle, including in oracle classes. -/

structure SynthProblem where
  nin : Str → ℕ
  nout : Str → ℕ
  ordered : ∀ x, nin x ≤ nout x
  polySizes : ∃ p : Polynomial ℕ, ∀ x, nin x ≤ p.eval x.length ∧ nout x ≤ p.eval x.length
  target : (x : Str) → PartialIso (nin x) (nout x)

/-- Kept separate: all-problem equality in Theorem 6.5(ii) must not assume this. -/
def SizeComputable (U : SynthProblem) : Prop :=
  ∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ x, f x = tup [Nat.bits (U.nin x), Nat.bits (U.nout x)]

def precisionIndex (xr : Str × ℕ) : Str := tup [xr.1, unary xr.2]

/-- Correct interface and approximation of one completion before all test inputs. -/
def Approximates (U : SynthProblem) (A : Oracle)
    (C : Str → ℕ → GeneralCircuit) : Prop :=
  ∀ x r, 1 ≤ r → (C x r).valid ∧ (C x r).input = U.nin x ∧
    (C x r).output = U.nout x ∧ ∃ Φ, Completion (U.target x) Φ ∧
      diamond (fun ρ => (C x r).channel A (U.nin x) (U.nout x) ρ - Φ ρ) ≤
        ENNReal.ofReal (1 / (r : ℝ))

def SpaceFamily (C : Str → ℕ → GeneralCircuit) : Prop :=
  SpaceUniform precisionIndex (fun xr => (C xr.1 xr.2).code)
    (fun xr => (C xr.1 xr.2).gateCodes) ∧
  ∃ p : Polynomial ℕ, ∀ x r, (C x r).space ≤ p.eval (x.length + r)

def TimeFamily (C : Str → ℕ → GeneralCircuit) : Prop :=
  TimeUniform precisionIndex (fun xr => (C xr.1 xr.2).code)

def channelPSPACE : Set SynthProblem :=
  {U | ∃ C, SpaceFamily C ∧ (∀ x r, (C x r).oracleFree) ∧
    Approximates U (fun _ => false) C}

def channelBQPO (A : Oracle) : Set SynthProblem :=
  {U | ∃ C, TimeFamily C ∧ Approximates U A C}

def channelBQP : Set SynthProblem :=
  {U | ∃ C, TimeFamily C ∧ (∀ x r, (C x r).oracleFree) ∧
    Approximates U (fun _ => false) C}

/-- Decision BQP^A, pp. 10–11. Empty strings included; bounded error ≥2/3. -/
def decisionBQPO (A : Oracle) : Set (Set Str) :=
  {L | ∃ C : ℕ → GeneralCircuit,
    TimeUniform unary (fun n => (C n).code) ∧
    (∀ n, (C n).valid ∧ (C n).input = n ∧ (C n).output = 1) ∧
    ∀ x : Str, (2 : ℝ) / 3 ≤
      let ρ := (C x.length).channel A x.length 1
        (ket (Pi.single (fun i => x.get i) 1))
      ρ (fun _ => decide (x ∈ L)) (fun _ => decide (x ∈ L)) |>.re}

/-- Oracle-free deterministic polynomial-time decision, with a single machine. -/
def decisionP : Set (Set Str) :=
  {L | ∃ (M : OTM) (p : Polynomial ℕ), ∀ x,
    M.result (fun _ => false) x (p.eval x.length) = some (decide (x ∈ L))}

/-- Empty-oracle BQP is equivalent to using no bit-oracle gates. -/
def decisionBQP := decisionBQPO (fun _ => false)

end PSPACEOracleSynth.Main.Supplement


