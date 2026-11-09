-- Prove2me | Definitions.Def_NOFSeparation750_CodedGIP_Programs
-- name    : NOFSeparation750_CodedGIP_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:41:17.568013+00:00
-- url     : https://prove2.me/theorems/8ec696aa-bba1-4536-ba6f-d3df3fdfd482
-- title:
--   Finite programs and uniform polynomial-time Boolean evaluation
-- statement:
--   A program has finite control, finitely many stacks, and a finite alphabet on every stack. Its input and output alphabets are binary. Execution and step counts use Mathlib's deterministic stack Turing-machine semantics. The predicate $\operatorname{OutputsWithin}(P,u,v,t)$ requires an actual halting computation from $u$ to the stated output $v$ within $t$ steps, rather than a freely assigned runtime.
--
--   An integer $n$ is serialized as $n$ one-bits followed by a zero-bit. An input of $k$ Boolean blocks of length $n$ is this length header followed by the blocks in order; its serialized length is $(k+1)n+1$. A total family $F=(F_n)_{n\ge0}$ is uniformly polynomial-time computable when
--   $$\exists P,p\;\forall n,x:\quad P(\operatorname{enc}(n,x))=[F_n(x)]\text{ within }p((k+1)n+1)\text{ steps}.$$
--   Here $P$ is one finite program and $p$ one polynomial with natural coefficients. For fixed $k$ this is polynomial time in the input length, with no advice or truth-table oracle. Requiring every internal alphabet to be finite rules out an infinite-alphabet computation oracle.
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), Theorem 1.1 and immediately following paragraph, p.3; Theorem 3.2, p.7; Appendix A.2–A.3, pp.12–13; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib

namespace NOFSeparation750.CodedGIP

/-- Finite machine control and finite alphabets on every stack. This excludes
hidden infinite-alphabet oracles; execution is Mathlib's deterministic TM2 step. -/
structure FiniteProgram where
  machine : Turing.TM2ComputableAux Bool Bool
  finiteAlphabet : ∀ i, Finite (machine.tm.Γ i)

/-- Actual halting execution within a step bound, with the stated output. -/
def OutputsWithin (P : FiniteProgram) (input output : List Bool) (time : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime P.machine.tm
    (input.map P.machine.inputAlphabet.symm)
    (some (output.map P.machine.outputAlphabet.symm)) time)

/-- Self-delimiting unary integers. Polynomial in the output block length is the
relevant bound for code generation; unary j has length O(r_j). -/
def unary (n : ℕ) : List Bool := List.replicate n true ++ [false]

abbrev BooleanFamily (k : ℕ) := (n : ℕ) → (Fin k → (Fin n → Bool)) → Bool

def evaluationInput {k n : ℕ} (x : Fin k → Fin n → Bool) : List Bool :=
  unary n ++ (List.ofFn fun i => List.ofFn (x i)).flatten

/-- One finite program and one polynomial for every length and every input;
there is no length-dependent advice, function oracle, or arbitrary runtime field. -/
def UniformPolyTime {k : ℕ} (F : BooleanFamily k) : Prop :=
  ∃ P : FiniteProgram, ∃ p : Polynomial ℕ, ∀ n x,
    OutputsWithin P (evaluationInput x) [F n x] (p.eval (k * n + n + 1))

end NOFSeparation750.CodedGIP


