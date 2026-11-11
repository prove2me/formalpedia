-- Prove2me | Definitions.Def_BipMatchNC_Weighted_NC
-- name    : BipMatchNC_Weighted_NC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:11:43.674172+00:00
-- url     : https://prove2.me/theorems/06e63765-93b3-4afb-afbb-ae07d8ec6a9a
-- title:
--   Logspace-uniform NC^k for search problems and languages, with explicit constants (§2)
-- statement:
--   A problem is in **$\mathrm{NC}^k$** if it is computed by a logspace-uniform family of polynomial-size Boolean circuits of depth $O(\log^k N)$, where $N$ is the input length; $\mathrm{NC}=\bigcup_k\mathrm{NC}^k$.
--
--   For a search problem with instances $x$, binary code $\mathrm{enc}(x)$ and correctness relation $R(x,y)$: there are a constant $c$, an output bound $\ell(N)\le N^c+c$ and a logspace-uniform family $(C_N)_{N\in\mathbb N}$ of fan-in-2 Boolean circuits, all fixed before the input, with
--   $$\mathrm{size}(C_N)\le N^c+c,\qquad \mathrm{depth}(C_N)\le c\,\lfloor\log_2N\rfloor^k+c,$$
--   such that for every instance $x$, $C_{|\mathrm{enc}(x)|}(\mathrm{enc}(x))$ is the padded encoding of some $y$ with $R(x,y)$ and $|y|\le\ell(|\mathrm{enc}(x)|)$. A language is in $\mathrm{NC}^k$ if such a family outputs the single bit $1$ on every word of the language and $0$ on every other word.
--
--   **Formalization Note.** Circuits, their size (number of vertices), depth (longest path) and binary code are the published `TreeEdgeRankPC.BoolCircuit`; logspace uniformity (`LogspaceUniform`: one deterministic transducer with workspace $c'(\lfloor\log_2(N+1)\rfloor+1)$ prints the code of $C_N$ from $1^N$) and the (valid bit, data bit) output format `paddedOutput` are the published `TreeEdgeRankPC_NC1` definitions. `SearchInNC k enc R` is a promise problem: outputs on words that are not codes are unconstrained. `LangInNC k Lang` constrains every word.
-- source:
--   Chatterjee, Ghosh, Gurjar, Raj, Thierauf, Bipartite Matching is in NC, STOC 2027 submission (manuscript sha256 c61e59cb…), p. 4 (PDF 5), §2

import Mathlib
import Definitions.Def_TreeEdgeRankPC_Circuit
import Definitions.Def_TreeEdgeRankPC_NC1

namespace BipMatchNC.Weighted

open TreeEdgeRankPC

/-- A search problem is **in (logspace-uniform) `NC^k`** (§2, p. 4: "all problems computable by
(logspace-) uniform polynomial-size boolean circuits of depth `O(log^k n)`"). Instances `x : I` are
given to the circuits by their binary code `enc x`; `R x y` says that `y` is a correct output for `x`.

There are one constant `c`, one output-length bound `ℓ` and one logspace-uniform family
`(C_N)_{N ∈ ℕ}` of fan-in-2 Boolean circuits (the published `TreeEdgeRankPC.BoolCircuit`), all chosen
before the input, such that `C_N` has size at most `N^c + c` and depth at most
`c ⌊log₂ N⌋^k + c`, and on the code of every instance `x` the circuit `C_{|enc x|}` outputs a correct
answer `y` for `x` of length at most `ℓ(|enc x|) ≤ |enc x|^c + c`.

**Formalization Note.** `N` is the input length. A circuit has a fixed number of outputs while `|y|`
may vary among inputs of one length, so the output is written in the published (valid bit, data bit)
format `TreeEdgeRankPC.paddedOutput`. Correctness is required on codes of instances only (a promise
problem); the outputs on other words are unconstrained. -/
def SearchInNC (k : ℕ) {I : Type*} (enc : I → List Bool) (R : I → List Bool → Prop) : Prop :=
  ∃ (c : ℕ) (ℓ : ℕ → ℕ) (C : ∀ N, BoolCircuit N),
    LogspaceUniform C ∧
    (∀ N, ℓ N ≤ N ^ c + c) ∧
    (∀ N, (C N).size ≤ N ^ c + c) ∧
    (∀ N, (C N).depth ≤ c * Nat.log 2 N ^ k + c) ∧
    ∀ x : I, ∃ y, R x y ∧ y.length ≤ ℓ (enc x).length ∧
      (C (enc x).length).eval (enc x) = paddedOutput y (ℓ (enc x).length)

/-- A language `Lang ⊆ {0,1}*` is **in (logspace-uniform) `NC^k`** (§2, p. 4): one constant `c` and
one logspace-uniform family of fan-in-2 Boolean circuits of size at most `N^c + c` and depth at most
`c ⌊log₂ N⌋^k + c`, chosen before the input, such that `C_{|x|}` outputs the single bit `1` on every
word `x ∈ Lang` and the single bit `0` on every word `x ∉ Lang`. -/
def LangInNC (k : ℕ) (Lang : Set (List Bool)) : Prop :=
  ∃ (c : ℕ) (C : ∀ N, BoolCircuit N),
    LogspaceUniform C ∧
    (∀ N, (C N).size ≤ N ^ c + c) ∧
    (∀ N, (C N).depth ≤ c * Nat.log 2 N ^ k + c) ∧
    ∀ x : List Bool, (x ∈ Lang ∧ (C x.length).eval x = [true]) ∨
      (x ∉ Lang ∧ (C x.length).eval x = [false])

end BipMatchNC.Weighted


