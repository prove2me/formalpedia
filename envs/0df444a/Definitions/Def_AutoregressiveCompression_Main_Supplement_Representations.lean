-- Prove2me | Definitions.Def_AutoregressiveCompression_Main_Supplement_Representations
-- name    : AutoregressiveCompression_Main_Supplement_Representations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:08:16.37918+00:00
-- url     : https://prove2.me/theorems/57807b1e-c72c-4af6-a6b6-efffb66af5fc
-- title:
--   Rational evaluators and finite uniform-seed generator circuits
-- statement:
--   For a finite alphabet $\Sigma$, an evaluator is an existing rational-output circuit $E$ whose values on $\Sigma^N$ are nonnegative, at most one, and sum to one. Zeros are permitted. A generator is a finite Boolean circuit on $r$ fair seed bits whose output wires encode one word of $\Sigma^N$ for every seed. It represents the exact pushforward of the uniform seed. The source's arbitrary target laws are not restricted to such pushforwards.
--
--   The general multi-output circuit, its fan-in-two gates, gate evaluation and gate-count size are the published ErrAmpOV circuit interface. Symbols use the base mission's fixed one-hot encoding. Explicit descriptions include the seed length, output length, gates and output wires. Invalid forward gate references read false, as in the referenced circuit semantics. Output typing is certified by a concrete encoding condition. The mathematical output is recovered from these actual wires; no desired rate, decoding or learning property is a field.
--
--   These representations support Definition 4.5(a,b). A zero-length output is the unique empty word; a zero-bit seed is a singleton probability space. Finite seed generators represent dyadic laws exactly. Constructions that approximate a rational model or a uniform choice on a non-power-of-two set must budget their finite-bit error inside the requested accuracy and confidence; footnote 6 does not change target laws or give exact non-dyadic sampling.
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Definition 4.5(a,b), printed p.17 / PDF p.19; footnote 6, printed p.18 / PDF p.20

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Tasks
import Definitions.Def_ErrAmpOV_Circuit

noncomputable section

namespace AutoregressiveCompression.Main.Supplement

open scoped Classical

/-! Definition 4.5(a,b), printed p.17 / PDF p.19.
The published rational-output circuit is reused for evaluators. For generators,
the published general multi-output Boolean circuit supplies gate evaluation and
size. Symbols use the base interface's fixed one-hot encoding; inputs and output
wires are not gates. Gate references outside the earlier gate list read false,
exactly as in the published circuit semantics. No algorithm is a semantic oracle.
-/

/-- Rational evaluator mass, on the same fixed symbol encoding as the base model. -/
def evaluatorMass {Sym : Type} [Fintype Sym] (E : Circuit) (N : ℕ)
    (z : Word Sym N) : ℝ :=
  (E.value (stringBits (List.ofFn z)) : ℝ)

/-- Evaluators are normalized and nonnegative; zeros are permitted. -/
def IsEvaluator {Sym : Type} [Fintype Sym] (E : Circuit) (N : ℕ) : Prop :=
  (∀ z : Word Sym N, 0 ≤ evaluatorMass E N z ∧ evaluatorMass E N z ≤ 1) ∧
    ∑ z : Word Sym N, evaluatorMass E N z = 1

/-- Serialize a published Boolean wire. Tags distinguish inputs and gate wires. -/
def wireBits {r : ℕ} : ErrAmpOV.Wire (Fin r) → Bits
  | .inp i => frame [[false], natBits i.val]
  | .gate j => frame [[true], natBits j]

/-- Serialize a published Boolean gate with its actual input wires. -/
def vectorGateBits {r : ℕ} : ErrAmpOV.Gate (Fin r) → Bits
  | .const b => frame [[false, false], [b]]
  | .not a => frame [[false, true], wireBits a]
  | .and a b => frame [[true, false], wireBits a, wireBits b]
  | .or a b => frame [[true, true], wireBits a, wireBits b]

/-- Finite sampler description, with seed length and symbol output length. -/
structure SamplerCode where
  seedLength : ℕ
  length : ℕ
  circuit : ErrAmpOV.Circuit (Fin seedLength)

/-- Explicit finite bit description; every gate and output wire is written. -/
def SamplerCode.bits (G : SamplerCode) : Bits :=
  frame [unary G.seedLength, unary G.length,
    frame (G.circuit.gates.map vectorGateBits), frame (G.circuit.outs.map wireBits)]

/-- A sampler produces one encoded word on every seed. There is no positivity,
rationality or sampling requirement on the target law. -/
def SamplerCode.IsGenerator (G : SamplerCode) (Sym : Type) [Fintype Sym] : Prop :=
  ∀ u : Fin G.seedLength → Bool, ∃ z : Word Sym G.length,
    G.circuit.eval u = stringBits (List.ofFn z)

/-- Decode the actual output wires. The fixed one-hot encoding makes the witness
unique. The proof argument certifies output typing, not a target task or reduction. -/
def SamplerCode.output {Sym : Type} [Fintype Sym] (G : SamplerCode)
    (h : G.IsGenerator Sym) (u : Fin G.seedLength → Bool) : Word Sym G.length :=
  Classical.choose (h u)

/-- Structural decoding certificate: the recovered word is precisely the word
written on the evaluated output wires. -/
@[simp] theorem SamplerCode.output_spec {Sym : Type} [Fintype Sym]
    (G : SamplerCode) (h : G.IsGenerator Sym) (u : Fin G.seedLength → Bool) :
    G.circuit.eval u = stringBits (List.ofFn (G.output h u)) :=
  Classical.choose_spec (h u)

/-- The exact pushforward of a finite uniform seed. At length zero this is the
point mass on the unique empty word. Non-dyadic laws are not claimed to be exact
outputs of such a sampler. -/
def SamplerCode.law {Sym : Type} [Fintype Sym] (G : SamplerCode)
    (h : G.IsGenerator Sym) : PMF (Word Sym G.length) :=
  (coinLaw G.seedLength).map (G.output h)

/-- A string source constructed from its circuit and uniform seed. -/
def SamplerCode.source {Sym : Type} [Fintype Sym] (G : SamplerCode)
    (h : G.IsGenerator Sym) : Source Sym :=
  ⟨G.length, G.law h⟩

/-- Mass of a word under the evaluated sampler. Used only at the output length
when learning. The formula is a finite uniform probability, not supplied data. -/
def SamplerCode.modelMass {Sym : Type} [Fintype Sym] (G : SamplerCode) (N : ℕ)
    (z : Word Sym N) : ℝ :=
  eventProbability (coinLaw G.seedLength)
    (fun u => G.circuit.eval u = stringBits (List.ofFn z))

/-- Correctly typed generator hypothesis for an N-symbol target. -/
def IsGeneratorAt {Sym : Type} [Fintype Sym] (G : SamplerCode) (N : ℕ) : Prop :=
  G.length = N ∧ G.IsGenerator Sym

end AutoregressiveCompression.Main.Supplement


