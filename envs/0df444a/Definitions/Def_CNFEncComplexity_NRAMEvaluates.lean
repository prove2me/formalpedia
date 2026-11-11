-- Prove2me | Definitions.Def_CNFEncComplexity_NRAMEvaluates
-- name    : CNFEncComplexity_NRAMEvaluates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:59.147655+00:00
-- url     : https://prove2.me/theorems/d69ac718-71a7-4bc0-95e5-c0c696918e28
-- title:
--   $f$ is evaluated in time $t$ by a nondeterministic RAM
-- statement:
--   A program $\pi$ **evaluates** $f:\{0,1\}^n\to\{0,1\}$ **in time $t$** if for every $x\in\{0,1\}^n$,
--   $$f(x)=1 \iff \pi \text{ accepts the input tape } x_1x_2\cdots x_n \text{ within logarithmic cost } t .$$
--
--   This is the hypothesis of Robson's theorem (Theorem 10).
--
--   **Formalization Note** Evaluation is nondeterministic: an input with $f(x)=0$ has no accepting run of cost at most $t$, and runs of larger cost are not constrained.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 10, p.10 (PDF 11), with the model of §3.1

import Mathlib
import Definitions.Def_CNFEncComplexity_Instr
import Definitions.Def_CNFEncComplexity_AcceptsWithin

namespace CNFEncComplexity

/-- **"f can be evaluated in time t by a nondeterministic RAM machine".** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), Theorem 10,
p.10 (PDF 11), with the model of §3.1.

`NRAMEvaluates prog t f`: for every input `x ∈ {0,1}ⁿ`, `f x = 1` iff the program `prog`, run on the
input tape `x₁ x₂ … xₙ`, has an accepting run of logarithmic cost at most `t` (`AcceptsWithin`).

**Formalization Note.** Nondeterministic evaluation: inputs with `f x = 0` have no accepting run of
cost `≤ t`; runs of larger cost are not constrained. -/
def NRAMEvaluates {n : ℕ} (prog : List Instr) (t : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x : Fin n → Bool, f x = true ↔ AcceptsWithin prog (List.ofFn x) t

end CNFEncComplexity


