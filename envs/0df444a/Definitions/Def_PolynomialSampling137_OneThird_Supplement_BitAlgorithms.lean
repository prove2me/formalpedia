-- Prove2me | Definitions.Def_PolynomialSampling137_OneThird_Supplement_BitAlgorithms
-- name    : PolynomialSampling137_OneThird_Supplement_BitAlgorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:46:38.544309+00:00
-- url     : https://prove2.me/theorems/48aff269-8702-4ca6-825e-527a2ce0642d
-- title:
--   Uniform bit algorithms and exact seed encodings
-- statement:
--   A bit program is a single finite-control machine on a fixed finite number of binary stacks, using the published stack-machine transition semantics. One step inspects only the stack tops and performs at most one constant-size operation on each stack. Its runtime is therefore a bit-cost bound up to a fixed program-dependent factor. All input and output alphabets and control sets are finite.
--
--   $$\operatorname{input}(N,k,x)=1^N0\,1^k0\,x,\qquad \operatorname{time}\le C(N+1)^a.$$
--
--   Uniform polynomial sampling requires one program and constants $C,a$, selected before every $N,k$ and seed, to halt with the exact $N$ output bits. The seed consists of exactly $k$ uniform bits; the length headers are deterministic. This is an operational runtime predicate, without field-arithmetic unit costs, advice, an assumed algorithm or a certificate of a mathematical conclusion.
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §2.5 and §4.3, printed pp. 9–10, 17–18; PDF pp. 11–12, 19–20

import Definitions.Def_CookPvsNP_StackModel
import Definitions.Def_PolynomialSampling137_OneThird_BooleanSources

namespace PolynomialSampling137.OneThird.Supplement

def WordBits {n : ℕ} (x : Word n) : List Bool := List.ofFn (fun i => decide (x i = 1))

/-- Unary length headers, followed by exactly the supplied seed bits. This is a
fixed injective encoding, of length N+k+2+k for a k-bit seed. -/
def SamplerInput {k : ℕ} (N : ℕ) (x : Word k) : List Bool :=
  List.replicate N true ++ [false] ++ List.replicate k true ++ [false] ++ WordBits x

/-- One finite deterministic multi-stack bit program, not a family of advice strings.
The published transition reads only the stack tops and performs at most one
push/pop on each of finitely many stackCount. Thus its steps are bit operations up to
a program-dependent constant. -/
structure BitProgram where
  stackCount : ℕ
  stateCount : ℕ
  positiveStacks : 0 < stackCount
  machine : CookPvsNP.StackMachine (Fin stackCount) Bool (Fin stateCount)

def BitProgram.init (P : BitProgram) (x : List Bool) :
    CookPvsNP.StackCfg (Fin P.stackCount) Bool (Fin P.stateCount) :=
  ⟨P.machine.initial, fun i => if i.val = 0 then x else []⟩

def BitProgram.run (P : BitProgram) (t : ℕ) (x : List Bool) :
    CookPvsNP.StackCfg (Fin P.stackCount) Bool (Fin P.stateCount) :=
  (P.machine.step)^[t] (P.init x)

def BitProgram.ComputesWithin (P : BitProgram) (t : ℕ) (x y : List Bool) : Prop :=
  P.machine.done (P.run t x).state = true ∧
    (P.run t x).store ⟨0, P.positiveStacks⟩ = y

/-- A uniform deterministic runtime bound, with C,a before all parameters.
No field operation has been assigned unit cost here. -/
def UniformlyPolynomial (F : ∀ N k : ℕ, Word k → Word N) : Prop :=
  ∃ (P : BitProgram) (C a : ℕ), 0 < C ∧ ∀ N k, k ≤ N → ∀ x : Word k,
    P.ComputesWithin (C * (N + 1) ^ a) (SamplerInput N x) (WordBits (F N k x))

end PolynomialSampling137.OneThird.Supplement


