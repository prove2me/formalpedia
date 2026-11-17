-- Prove2me | Definitions.Def_SingleInteraction_Supplement_Classes
-- name    : SingleInteraction_Supplement_Classes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:01:09.259274+00:00
-- url     : https://prove2.me/theorems/604181c0-9a05-4daa-be51-fde3a51fb23d
-- title:
--   Promise classes P, NP, BQP and PSPACE and their hardness notions
-- statement:
--   Complexity classes of promise problems $L=(L_{\mathrm{yes}},L_{\mathrm{no}})$ on bit strings, on the same machine model as the published class QMA.
--
--   1. **P**: a deterministic polynomial-time algorithm accepts every $x\in L_{\mathrm{yes}}$ and rejects every $x\in L_{\mathrm{no}}$.
--   2. **NP**: a polynomial-time verifier $V(x,w)$ and a polynomial $p$ such that every $x\in L_{\mathrm{yes}}$ has a witness $w$ with $|w|\le p(|x|)$ and $V(x,w)=1$, and no $x\in L_{\mathrm{no}}$ has one.
--   3. **BQP** (Definition 1): a deterministic polynomial-time algorithm outputs, for each $x$, a polynomial-size quantum circuit $U_x$ over $\{H,T,\mathrm{CNOT}\}$ on $|0\rangle$ ancillas; $\Pr(U_x\text{ accepts})\ge2/3$ for $x\in L_{\mathrm{yes}}$ and $\le1/3$ for $x\in L_{\mathrm{no}}$.
--   4. **PSPACE**: some language decided by a deterministic machine that halts on every input and uses polynomial space contains $L_{\mathrm{yes}}$ and is disjoint from $L_{\mathrm{no}}$.
--
--   A promise problem on instances presented by an encoding is **X-hard** if every bit-string promise problem in X reduces to it by a polynomial-time many-one reduction mapping YES to YES and NO to NO.
--
--   These classes, with QMA and StoqMA, are the ones in which the supplement's completeness theorems are stated (Theorems 63, 81, 82).
--
--   **Formalization Note** BQP is the published QMA verifier model with zero witness qubits. PSPACE uses the published polynomial-space machines of `OptimalQueuingComplexity.Restless.InPSPACE`. Witnesses and inputs of NP verifiers are paired with a self-delimiting bit-string code.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.2, pp.15–17: Definition 1 (BQP), eq. (1) (NP, PSPACE); Theorems 63, 81, 82

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

namespace Supplement

/-!
# The promise classes P, NP, BQP and PSPACE on the base bit-string layer

Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version,
sha256 19ddc444…), §2.2, pp.15–17: "A promise problem is a pair `L = (Lyes, Lno)` of disjoint sets of
strings"; Definition 1 (BQP, p.15); the classes NP, P and PSPACE of eq. (1), p.17, and Theorems 63
and 81.

**Formalization Note**
* Promise problems, polynomial-time many-one reductions and the bit-string layer are the published
  `OAI.ContinuumCoulomb.PromiseProblem`, `PolynomialManyOne`, `BitString`, `Codec`, as in the base
  mission's `InQMA` / `QMAHard`. Machines are Mathlib's `Turing.TM2ComputableInPolyTime`.
* BQP (Definition 1): a polynomial-time uniform family of polynomial-size circuits over the base
  gate set `{H, T, CNOT}` on the input-independent register with `|0⟩` ancillas, accepting with
  probability `≥ 2/3` on YES and `≤ 1/3` on NO. It is the published `QuantumVerifier` with no witness
  qubits, so the gate set, the uniformity and the acceptance measurement are those of the base
  `InQMA`.
* P: a polynomial-time decider accepting YES and rejecting NO inputs. NP: a polynomial-time
  verifier `V(x, w)` and a polynomial `p` with: YES ⇒ some `w` with `|w| ≤ p(|x|)` is accepted,
  NO ⇒ no such `w` is accepted. The pair `(x, w)` is presented with the self-delimiting bit-string
  code `bitsCodec`.
* PSPACE for promise problems: some language decided in polynomial space (the published
  `OptimalQueuingComplexity.Restless.InPSPACE`, multi-stack machines halting on every input with
  every reachable configuration of polynomial total stack length) contains every YES input and no NO
  input. This is the usual "a polynomial-space machine halts on every input, accepts YES and rejects
  NO".
* `X`-hardness: every bit-string promise problem in `X` reduces to the problem by a
  `PolynomialManyOne` reduction, as in the published `QMAHard`. -/

/-- A self-delimiting code for bit strings (each bit is preceded by a continuation flag). -/
def bitsCodec : Codec BitString where
  encode := encodeDigits
  read := readDigits
  read_encode := readDigits_encode

/-- Membership in P for a bit-string promise problem. -/
def InP (P : PromiseProblem BitString) : Prop :=
  ∃ f : BitString → Bool,
    Nonempty (Turing.TM2ComputableInPolyTime (id : BitString → BitString) (fun b : Bool => [b]) f) ∧
      (∀ x ∈ P.yes, f x = true) ∧ ∀ x ∈ P.no, f x = false

/-- Membership in NP for a bit-string promise problem. -/
def InNP (P : PromiseProblem BitString) : Prop :=
  ∃ (V : BitString × BitString → Bool) (p : Polynomial ℕ),
    Nonempty (Turing.TM2ComputableInPolyTime (pair bitsCodec bitsCodec).encode
      (fun b : Bool => [b]) V) ∧
    (∀ x ∈ P.yes, ∃ w : BitString, w.length ≤ p.eval x.length ∧ V (x, w) = true) ∧
    ∀ x ∈ P.no, ∀ w : BitString, w.length ≤ p.eval x.length → V (x, w) = false

/-- NP-hardness of a promise problem on instances `α` presented by `encoding`. -/
def NPHard {α : Type} (encoding : α → BitString) (Q : PromiseProblem α) : Prop :=
  ∀ P : PromiseProblem BitString, InNP P → Nonempty (PolynomialManyOne id encoding P Q)

/-- Membership in BQP (Definition 1): a uniform polynomial-size verifier with no witness qubits. -/
def InBQP (P : PromiseProblem BitString) : Prop :=
  ∃ V : QuantumVerifier, (∀ x, (V.generate x).witness = 0) ∧
    (∀ x ∈ P.yes, ∀ psi : EuclideanSpace ℂ (SourceSpinBasis (V.generate x).witness),
      ‖psi‖ = 1 → (2 : ℝ) / 3 ≤ qmaAcceptance (V.generate x) (V.wellFormed x) psi) ∧
    (∀ x ∈ P.no, ∀ psi : EuclideanSpace ℂ (SourceSpinBasis (V.generate x).witness),
      ‖psi‖ = 1 → qmaAcceptance (V.generate x) (V.wellFormed x) psi ≤ (1 : ℝ) / 3)

/-- BQP-hardness of a promise problem on instances `α` presented by `encoding`. -/
def BQPHard {α : Type} (encoding : α → BitString) (Q : PromiseProblem α) : Prop :=
  ∀ P : PromiseProblem BitString, InBQP P → Nonempty (PolynomialManyOne id encoding P Q)

/-- Membership in PSPACE for a bit-string promise problem: a polynomial-space decidable language
separates the YES inputs from the NO inputs. -/
def InPromisePSPACE (P : PromiseProblem BitString) : Prop :=
  ∃ L : BitString → Prop,
    OptimalQueuingComplexity.Restless.InPSPACE (id : BitString → BitString) L ∧
      (∀ x ∈ P.yes, L x) ∧ ∀ x ∈ P.no, ¬ L x

/-- PSPACE-hardness of a promise problem on instances `α` presented by `encoding`. -/
def PSPACEHard {α : Type} (encoding : α → BitString) (Q : PromiseProblem α) : Prop :=
  ∀ P : PromiseProblem BitString, InPromisePSPACE P →
    Nonempty (PolynomialManyOne id encoding P Q)

end Supplement

end SingleInteraction


