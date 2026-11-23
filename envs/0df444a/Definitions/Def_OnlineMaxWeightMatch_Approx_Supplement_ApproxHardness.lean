-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_ApproxHardness
-- name    : OnlineMaxWeightMatch_Approx_Supplement_ApproxHardness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:16:46.389129+00:00
-- url     : https://prove2.me/theorems/62020abd-5e0e-48ca-a5eb-b3b7045d1181
-- title:
--   Approximation (§2, p. 4) and PSPACE-hardness of computing an $\alpha$-approximation
-- statement:
--   Following §2 of the paper, an **$\alpha$-approximation** to a quantity $Q\ge 0$, for $\alpha\in(0,1)$, is a number in the interval $[\alpha Q,\,Q]$.
--
--   Let $\mathcal X$ be a set of problem instances with a binary encoding $\mathrm{enc}:\mathcal X\to\{0,1\}^*$, let $\mathcal C\subseteq\mathcal X$ be a class of instances, and let $V:\mathcal X\to\mathbb R$ be a value. Computing an $\alpha$-approximation to $V$ on $\mathcal C$ is **PSPACE-hard** if for every language $L\subseteq\{0,1\}^*$ decidable in polynomial space there are
--
--   1. a polynomial-time computable map $f$ sending each word $w$ to an instance $f(w)\in\mathcal C$, and
--   2. a polynomial-time computable decoder $g$ which, given $w$ and a rational number $a$,
--
--   such that for every word $w$ and **every** rational $a$ with
--   $$\alpha\,V(f(w))\ \le\ a\ \le\ V(f(w)),$$
--   $g(w,a)$ accepts exactly when $w\in L$.
--
--   Thus a polynomial-time algorithm outputting $\alpha$-approximations on $\mathcal C$ would decide every PSPACE language in polynomial time with one call. The definition is used for MAX-SSAT (Lemma 3.1) and for RideHail (Theorem 1.1).
--
--   **Formalization Note** Both machines are Mathlib multi-stack Turing machines (`Turing.TM2ComputableInPolyTime`) on binary encodings; polynomial space is the published `InPSPACE`. The decoder reads the word with every bit doubled and a terminator, followed by the rational answer written as numerator and denominator in binary. The numerical output interface uses rational answers; both finite MAX-SSAT and rational RideHail instances have rational optimum values, and the reductions preserve rational answers.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 4, §2 (definition of α-approximation); p. 1, Theorem 1.1 and p. 6, Lemma 3.1 (PSPACE-hardness of approximation)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

namespace OnlineMaxWeightMatch.Approx.Supplement

open OptimalQueuingComplexity.Restless

/-- Self-delimiting binary code of a word: every bit written twice, then the terminator `01`. -/
def encWord (w : List Bool) : List Bool :=
  (w.flatMap fun b => [b, b]) ++ [false, true]

/-- Binary code of an oracle query: the input word `w` (self-delimiting) followed by the
rational answer `a` (numerator and denominator in binary, via `encRat`). -/
def encQuery (q : List Bool × ℚ) : List Bool :=
  encWord q.1 ++ encRat q.2

/-- **PSPACE-hardness of `α`-approximating a value** (§2, p. 4). An `α`-approximation to a
quantity `Q` is a number in `[α Q, Q]`. The problem "given an instance `x` of class `C`, output
an `α`-approximation to `V x`" is PSPACE-hard if every language `L` in PSPACE reduces to it in
polynomial time with one query: a polynomial-time map `f` sends each word `w` to an instance
`f w` of class `C`, and a polynomial-time decoder `g`, given `w` and **any** rational
`α`-approximation `a` of `V (f w)`, decides whether `w ∈ L`.

Both machines are Mathlib multi-stack Turing machines working on binary encodings (`eb` for
instances, `encQuery` for the decoder's input); PSPACE is the published `InPSPACE`. -/
def ApproxHard {β : Type} (eb : β → List Bool) (C : β → Prop) (V : β → ℝ) (α : ℝ) : Prop :=
  ∀ L : Language Bool, InPSPACE (id : List Bool → List Bool) (fun w => w ∈ L) →
    ∃ (f : List Bool → β) (g : List Bool × ℚ → Bool),
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) eb f) ∧
      Nonempty (Turing.TM2ComputableInPolyTime encQuery (fun b : Bool => [b]) g) ∧
      (∀ w, C (f w)) ∧
      ∀ (w : List Bool) (a : ℚ), α * V (f w) ≤ (a : ℝ) → (a : ℝ) ≤ V (f w) →
        (g (w, a) = true ↔ w ∈ L)

end OnlineMaxWeightMatch.Approx.Supplement


