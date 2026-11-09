-- Prove2me | Definitions.Def_RSListDecodingCapacity_AllRates_Algorithm1
-- name    : RSListDecodingCapacity_AllRates_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:40.633726+00:00
-- url     : https://prove2.me/theorems/75f577d3-3ec6-4a8c-8ecd-e9d2aa5b0012
-- title:
--   Algorithm 1: interpolation, differential-equation root finding and pruning with charged execution
-- statement:
--   An implementation of Algorithm 1 consists of three finite deterministic multi-stack Turing programs, with no assumed correctness or time bounds. The programs execute sequentially:
--
--   1. On the original decoding input, compute the parameters of (11), (12), (18), construct the interpolation space (19), and output a term listing of a nonzero $Q$ in that space satisfying (16) at every received point, together with the original input.
--   2. Consume that word and output all polynomials of degree less than $k$ solving $Q(X,P,P^{[1]},\ldots,P^{[d]})=0$, each once, together with the original input.
--   3. Consume that word and return exactly its sublist of polynomials having at least $A$ agreements, preserving their order.
--
--   `Algorithm1RunsWithin` asserts these intermediate specifications and actual executions as conclusions. The first two output words carry every bit of the next input; encoding and copying are performed by the machines. Its time bound charges the sum of the three Turing-machine step counts and two stage transitions. Thus interpolation and root finding are computations, not oracles. This finite sequential machine model has polynomial simulations with a single multi-stack Turing machine, preserving the source's $q^{O(f)}$ bounds. For fixed $\varepsilon,\theta$, the finite natural parameters $d,m,W$ and the bound defining $\mathcal B$ can be compiled into the first program; the varying agreement threshold $A$ is supplied in the input.
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, STOC 2027 submission #565 (October 2026), Algorithm 1, p.26, equations (19), (16), (26); computational analysis p.27

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_RSListDecodingCapacity_AllRates_InterpolationSpace
import Definitions.Def_RSListDecodingCapacity_AllRates_LocalConstraints

open Polynomial

namespace RSListDecodingCapacity.AllRates

/-- A finite implementation of Algorithm 1 (Brakensiek–Chen–Putterman–Zhang–Zheng,
STOC 2027 submission #565, p.26): an interpolation program (steps 1–3), a differential-equation
solver (step 4), and a pruning program (steps 5–6). The fields are finite Turing programs only;
they carry no correctness, termination, or cost assumptions. -/
structure Algorithm1Program where
  interpolate : Turing.TM2ComputableAux Bool Bool
  roots : Turing.TM2ComputableAux Bool Bool
  prune : Turing.TM2ComputableAux Bool Bool

/-- Execution of Algorithm 1, p.26, with charged computation at every stage.

The first machine starts on the original decoding input and produces that input together with
the root-finding input for a nonzero `Q` in (19) satisfying (16) at every received point. The
second machine consumes precisely this word and produces the original input together with the
complete differential-equation solution list. The third consumes that word and outputs its
agreement filter, in the same order. All encoding, copying, linear algebra, root finding and
filtering occur inside the machines and are charged by `OutputsWithin`.

The programs are run sequentially, handing the Boolean output stack to the next input stack;
the two changes of stage each cost one step. Work stacks are empty at each handoff, as required
by `OutputsWithin`. This finite three-stage machine model has polynomial simulations with a
single multi-stack Turing machine, preserving the source's `q^O(f)` bounds. The fixed natural
parameters `d,m,W` and the bound defining `𝓑` may be compiled into the program for fixed `ε,θ`.
The witnesses below are conclusions about actual machine outputs, not free oracles. -/
def Algorithm1RunsWithin (M : Algorithm1Program) (ε θ : ℝ) {q n : ℕ} (k : ℕ)
    (α y : Fin n → ZMod q) (L : List (ZMod q)[X]) (t : ℕ) : Prop :=
  ∃ Q : MvPolynomial (Option (Fin (paramD ε θ + 1))) (ZMod q),
    ∃ terms : List (((Option (Fin (paramD ε θ + 1))) →₀ ℕ) × ZMod q),
      ∃ candidates : List (ZMod q)[X], ∃ ti tr tp : ℕ,
        Q ∈ sourceQ (ZMod q) ε θ n k ∧ Q ≠ 0 ∧
        (∀ i, SatisfiesLocal (paramD ε θ) (paramM (paramD ε θ)) (α i) (y i) Q) ∧
        IsTermListing Q terms ∧
        HMBinPacking.OutputsWithin M.interpolate (encDecodingInput k (paramA ε n) α y)
          (encBits (encDecodingInput k (paramA ε n) α y) ++ encRootFindingInput k terms) ti ∧
        candidates.Nodup ∧
        (∀ P : (ZMod q)[X], P ∈ candidates ↔
          P.degree < (k : WithBot ℕ) ∧ hasseJetEval (paramD ε θ) Q P = 0) ∧
        HMBinPacking.OutputsWithin M.roots
          (encBits (encDecodingInput k (paramA ε n) α y) ++ encRootFindingInput k terms)
          (encBits (encDecodingInput k (paramA ε n) α y) ++ encPolyList k candidates) tr ∧
        (∀ P : (ZMod q)[X], P ∈ L ↔ P ∈ candidates ∧ paramA ε n ≤ agreement α y P) ∧
        L.Sublist candidates ∧
        HMBinPacking.OutputsWithin M.prune
          (encBits (encDecodingInput k (paramA ε n) α y) ++ encPolyList k candidates)
          (encPolyList k L) tp ∧
        ti + tr + tp + 2 ≤ t

end RSListDecodingCapacity.AllRates


