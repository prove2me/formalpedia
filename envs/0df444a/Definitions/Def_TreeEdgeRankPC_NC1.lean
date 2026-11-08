-- Prove2me | Definitions.Def_TreeEdgeRankPC_NC1
-- name    : TreeEdgeRankPC_NC1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:21.463199+00:00
-- url     : https://prove2.me/theorems/ee246b99-d07c-43b6-a5d1-266542a9a4b7
-- title:
--   Logspace uniformity, NC¹-computable functions, NC¹ many-one reductions and P-completeness
-- statement:
--   A circuit family $(C_n)$ is **logspace-uniform** if a deterministic transducer outputs $C_n$ from $1^n$ using $O(\log n)$ workspace. A function $f:\{0,1\}^*\to\{0,1\}^*$ is **NC¹-computable** if a logspace-uniform family of bounded-fan-in circuits of polynomial size and depth $O(\log n)$ computes the polynomial-length string $f(x)$ from $x$. An **NC¹ many-one reduction** from $A$ to $B$ is an NC¹-computable $f$ with
--   $$x\in A\iff f(x)\in B.$$
--   A language is **P-complete** if it belongs to P and every language in P reduces to it in this sense.
--
--   These are the reductions in which Theorem 1.1 is stated. The restriction to low-depth reductions matters: under polynomial-time reductions every nontrivial language in P would be hard.
--
--   **Formalization Note** One transducer and all constants are chosen before $n$. The workspace bound is $c(\lfloor\log_2(n+1)\rfloor+1)$, the size bound $n^k+k$, the depth bound $c\lfloor\log_2 n\rfloor+c$. A circuit has a fixed number of outputs while $|f(x)|$ may vary among inputs of a given length, so the outputs are pairs (valid bit, data bit): $(1,f(x)_i)$ for $i<|f(x)|$ and $(0,0)$ after that. The family is indexed by all $n$, including $n=0$. P is the published `CookPvsNP.P Bool`: languages over $\{0,1\}$ decided by a one-tape Turing machine within $|w|^k+k$ steps.
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), §3.2, p.12 (Complexity classes)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TreeEdgeRankPC_Circuit
import Definitions.Def_TreeEdgeRankPC_Transducer

namespace TreeEdgeRankPC

/-- A circuit family is **logspace-uniform**, §3.2, p.12 (arXiv:2610.12438, held version of 2026-11-02,
sha256 9e04ca7b…): "A circuit family (C_n)_{n≥1} is logspace-uniform if a deterministic transducer
outputs C_n from 1^n using O(log n) workspace [GHR95]."

**Formalization Note.** One transducer and one constant `c`, chosen before `n`. The workspace bound is
`c * (⌊log₂(n + 1)⌋ + 1)`, which is positive at every `n` and is `O(log n)`. The family is indexed by all
`n : ℕ`, including `n = 0`; the extra circuit is a constant-size circuit for the empty input, and it
changes no result. -/
def LogspaceUniform (C : ∀ n, BoolCircuit n) : Prop :=
  ∃ (M : Transducer) (c : ℕ), ∀ n,
    M.ComputesWithin (List.replicate n true) (C n).enc (c * (Nat.log 2 (n + 1) + 1))

/-- The output format of a circuit that computes a string `y` of length at most `ℓ`: one pair
(valid bit, data bit) per position, namely `(1, y_i)` for `i < |y|` and `(0, 0)` after that. -/
def paddedOutput (y : List Bool) (ℓ : ℕ) : List Bool :=
  y.flatMap (fun b => [true, b]) ++ List.replicate (2 * (ℓ - y.length)) false

/-- `f : {0,1}* → {0,1}*` is **computable in logspace-uniform NC¹**, for the sentence of §3.2, p.12:
"computes a polynomial-length encoding f(x) by a uniform family of bounded-fan-in circuits of polynomial
size and depth O(log |x|)".

**Formalization Note.** The constants `k` and `c`, the length bound `ℓ` and the family are all chosen
before `n` and `x`. "Uniform" is logspace-uniform: the only uniformity p.12 defines. A circuit has a
fixed number of outputs while `|f(x)|` may vary among inputs of the same length, so the outputs use the
standard (valid bit, data bit) padding `paddedOutput`. Fan-in is at most 2 by `CircuitNode`. The size
bound is `n^k + k`, the depth bound `c * ⌊log₂ n⌋ + c`. -/
def NC1Computable (f : List Bool → List Bool) : Prop :=
  ∃ (k c : ℕ) (ℓ : ℕ → ℕ) (C : ∀ n, BoolCircuit n),
    LogspaceUniform C ∧
    (∀ n, ℓ n ≤ n ^ k + k) ∧
    (∀ n, (C n).size ≤ n ^ k + k) ∧
    (∀ n, (C n).depth ≤ c * Nat.log 2 n + c) ∧
    ∀ x : List Bool, (f x).length ≤ ℓ x.length ∧
      (C x.length).eval x = paddedOutput (f x) (ℓ x.length)

/-- An **NC¹ many-one reduction** from `A` to `B`, §3.2, p.12: "An NC^1 many-one reduction from A to B
computes a polynomial-length encoding f(x) by a uniform family of bounded-fan-in circuits of polynomial
size and depth O(log |x|), with x ∈ A if and only if f(x) ∈ B." -/
def NC1Reducible (A B : Set (List Bool)) : Prop :=
  ∃ f, NC1Computable f ∧ ∀ x, x ∈ A ↔ f x ∈ B

/-- **P-completeness under NC¹ many-one reductions**, §3.2, p.12: "a problem is P-complete if it belongs
to P and every problem in P reduces to it in this sense [GHR95]."

**Formalization Note.** Problems are languages over `{0, 1}`, and `P` is the published `CookPvsNP.P Bool`:
languages decided by a one-tape Turing machine in `|w|^k + k` steps. -/
def PCompleteNC1 (L : Set (List Bool)) : Prop :=
  L ∈ CookPvsNP.P Bool ∧ ∀ L' ∈ CookPvsNP.P Bool, NC1Reducible L' L

end TreeEdgeRankPC


