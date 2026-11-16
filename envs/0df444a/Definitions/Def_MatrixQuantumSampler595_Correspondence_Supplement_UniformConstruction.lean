-- Prove2me | Definitions.Def_MatrixQuantumSampler595_Correspondence_Supplement_UniformConstruction
-- name    : MatrixQuantumSampler595_Correspondence_Supplement_UniformConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:55:12.064096+00:00
-- url     : https://prove2.me/theorems/02ffa64d-1446-40da-a5ac-c1dca54add8b
-- title:
--   Uniform construction families, finite computation and numeric controls
-- statement:
--   A **finite seeded map** consists of source length $r$, positive seed count $t$ when required by a theorem, output length $m$, and a deterministic map $\{0,1\}^r\times[t]\to\{0,1\}^m$. This raw data contains no security assertions. A construction family maps four integer controls $(n,q,e,u)$ to such data.
--
--   **Uniform explicitness** requires a single finite multi-stack Turing machine, with a single polynomial running-time bound, to compute every family's length header and every output sample. Its two input modes are a header request and a request containing the source string and binary sample index. Controls are unary, strings are self-delimiting, and the header writes its three lengths in binary; runtime counts actual machine steps using Mathlib's `TM2ComputableInPolyTime`.
--
--   The only controls used by the theorems are their length, $q=\lfloor16k\rfloor$ for varying entropy (or zero for a fixed rate), $e=\lceil16\log_2(1/\eta)\rceil$, and either zero, the tradeoff integer $\ell$, or the exact requested output length $M$. For sampling, the second and third controls are $\lceil16\Lambda\rceil$ and $\lceil16\log_2(1/\varepsilon)\rceil$. No arbitrary advice, cost function or real-number oracle is supplied to the machine.
--
--   The helper functions use actual base-two logarithms, except the paper's convention $\log a=\log_2\max\{2,a\}$ for entropy deficiency. Rounding fixes finite numerical requests while the security and resource conclusions still quantify over every real entropy/error parameter in the source. The requested $M$ in Theorem 5.3 is supplied as a length, avoiding any exact-real computation of its floor.
--
--   This interface keeps the polynomial-time and explicitness clauses mathematical, with resource constants and the evaluator chosen before the varying instances.
-- source:
--   Kuan Cheng, Ruiyang Wu, STOC 2027 submission #595 (October 2026), canonical held PDF (SHA-256 35e315808fa8dd8704a13971c8ca60bc3f785907b566f8914e4bb929c38b26af), §2, p.12 (logarithm convention); explicitness and runtime clauses in Theorems 1.6–1.8, pp.5–7, Theorem 5.3, p.21 and Theorem 6.4, p.29; constructions §§4–7, pp.18–32; Mathlib finite TM2 step semantics

import Mathlib
import Definitions.Def_MatrixQuantumSampler595_Correspondence_MatrixSampler

namespace MatrixQuantumSampler595.Correspondence.Supplement

/-- A finite seeded map, without security assumptions or computation oracles. -/
structure FiniteSeededMap where
  sourceLength : ℕ
  samples : ℕ
  outputLength : ℕ
  apply : BitString sourceLength → Fin samples → BitString outputLength

/-- Integer construction controls; the theorems specify every field, with no advice field.
For extractors length is n; for samplers it is the requested output length m.
The last control is either zero, the requested output length, or the tradeoff integer ell. -/
structure Controls where
  length : ℕ
  entropy : ℕ
  accuracy : ℕ
  auxiliary : ℕ

/-- A self-delimiting bit-string field. -/
def delimit (s : List Bool) : List Bool := s.flatMap (fun b => [true, b]) ++ [false]

/-- Unary controls make input length proportional to the analytic resource bounds. -/
def controlsCode (u : Controls) : List Bool :=
  [u.length, u.entropy, u.accuracy, u.auxiliary].flatMap
    (fun n => List.replicate n true ++ [false])

/-- Binary output header: source length, number of seeds, and output length.
In particular the potentially exponential number of seeds is not encoded in unary. -/
def mapHeader (F : FiniteSeededMap) : List Bool :=
  [F.sourceLength, F.samples, F.outputLength].flatMap
    (fun n => delimit (Nat.bits n))

/-- Explicitness means one finite multi-stack Turing machine computes the header and every
sample of the entire family in polynomial time. `TM2ComputableInPolyTime` includes the actual
machine, its polynomial, and its step-bounded halting semantics, rather than an assigned cost.
The family has no real oracle and no parameter-dependent table or circuit input. -/
def IsUniformExplicit (E : Controls → FiniteSeededMap) : Prop :=
  ∃ f : List Bool → List Bool,
    Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
    ∀ u : Controls,
      f (false :: controlsCode u) = mapHeader (E u) ∧
      ∀ (x : BitString (E u).sourceLength) (i : Fin (E u).samples),
        f (true :: (controlsCode u ++ delimit (List.ofFn x) ++ Nat.bits i.val)) =
          List.ofFn ((E u).apply x i)

/-- Actual binary logarithm. The theorem domains exclude every invalid argument. -/
noncomputable def logTwo (x : ℝ) : ℝ := Real.logb 2 x

/-- The paper's special entropy-deficiency convention, §2 p.12, including a=0. -/
noncomputable def deficiencyLog (a : ℝ) : ℝ := logTwo (max 2 a)

/-- Sixteenth-bit entropy control, rounded down. -/
noncomputable def entropyControl (k : ℝ) : ℕ := ⌊16 * k⌋₊

/-- Sixteenth-bit logarithmic control, rounded up. -/
noncomputable def upperControl (x : ℝ) : ℕ := ⌈16 * x⌉₊

/-- A public accuracy control encodes error 2^(-e/16) ≤ η. -/
noncomputable def accuracyControl (η : ℝ) : ℕ := upperControl (logTwo (1 / η))

end MatrixQuantumSampler595.Correspondence.Supplement


