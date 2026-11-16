-- Prove2me | Definitions.Def_CircTrichotomy_Supplement_membershipProblem
-- name    : CircTrichotomy_Supplement_membershipProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:13:29.819148+00:00
-- url     : https://prove2.me/theorems/604056f7-237f-415b-983b-6a0d7ab5b0a0
-- title:
--   The classes of almost logarithmic and linear circuit complexity, and the $\mathcal C$-membership problem for NFAs
-- statement:
--   Let $c(L)(n)$ be the circuit complexity of $L\subseteq\Sigma^+$: the least size of an unbounded fan-in $\wedge/\vee$ circuit deciding $L\cap\Sigma^n$. Following Theorem 2.1, $L$ has
--
--   1. **almost logarithmic circuit complexity** if $c(L)\in\Omega(\log n)\cap O(\log n\log\log n)$;
--   2. **linear circuit complexity** if $c(L)\in\Omega(n)\cap O(n)$,
--
--   where $\Omega$ is the Hardy–Littlewood $\Omega$ ($c(L)(n)\ge c\,g(n)$ for some $c>0$ and infinitely many $n$).
--
--   For a class $\mathcal C$ of regular languages, the **$\mathcal C$-membership problem** (Problem F.1) asks, given an NFA $A$, whether $L(A)\in\mathcal C$. As a language of bit strings it is
--   $$\{\operatorname{enc}(A) : A \text{ an NFA with } L(A)\in\mathcal C\},$$
--   where $\operatorname{enc}$ is the binary code of NFAs and $L(A)$ is taken over the automaton's own alphabet. Strings that encode no NFA are not in the language.
--
--   These are the two decision problems of Theorem 4.1.
--
--   **Formalization Note** The two classes are clauses (2) and (3) of the published goal `CircTrichotomy.theorem_2_1`, verbatim (`HLOmega`, `BigO`, `Real.logb 2`, `circuitComplexity`). The membership problem takes the class as a predicate `P s L` on languages over `Fin (s + 1)`.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.1, p.3; Theorem 4.1, p.10; Problem F.1, p.67

import Mathlib
import Definitions.Def_CircTrichotomy_circuitComplexity
import Definitions.Def_CircTrichotomy_BigO
import Definitions.Def_CircTrichotomy_HLOmega
import Definitions.Def_CircTrichotomy_Supplement_NFAInst

set_option autoImplicit false

namespace CircTrichotomy

namespace Supplement

/-- **Almost logarithmic circuit complexity** (Göller, Manuel, *A Circuit Complexity Trichotomy
For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…),
Theorem 2.1 (2), p.3): `c(L) ∈ Ω(log n) ∩ O(log n log log n)`, with the Hardy–Littlewood `Ω`.
This is clause (2) of the published `CircTrichotomy.theorem_2_1`, verbatim.

**Formalization Note** `log` is `Real.logb 2`, as in the published goal. -/
def IsAlmostLog {α : Type} (L : Language α) : Prop :=
  HLOmega (fun n => (circuitComplexity L n : ℝ)) (fun n => Real.logb 2 n) ∧
    BigO (fun n => (circuitComplexity L n : ℝ)) (fun n => Real.logb 2 n * Real.logb 2 (Real.logb 2 n))

/-- **Linear circuit complexity** (Theorem 2.1 (3), p.3): `c(L) ∈ Ω(n) ∩ O(n)`, with the
Hardy–Littlewood `Ω`. This is clause (3) of the published `CircTrichotomy.theorem_2_1`, verbatim. -/
def IsLinearCC {α : Type} (L : Language α) : Prop :=
  HLOmega (fun n => (circuitComplexity L n : ℝ)) (fun n => (n : ℝ)) ∧
    BigO (fun n => (circuitComplexity L n : ℝ)) (fun n => (n : ℝ))

/-- **The `C`-membership problem** (Problem F.1, p.67): "INPUT: An NFA A. QUESTION: Is L(A) in
C?", as a language of bit strings: the codes `A.enc` of the NFA instances `A` whose language
`L(A) ⊆ Σ⁺` (over the instance's own alphabet `Σ = Fin (numLetters + 1)`) has the property `P`.
Strings that encode no instance are not in the language.

**Formalization Note** `P s L` is the class `C`, stated for languages over `Fin (s + 1)`. -/
def membershipProblem (P : (s : ℕ) → Language (Fin (s + 1)) → Prop) : Set (List Bool) :=
  {x | ∃ A : NFAInst, x = A.enc ∧ P A.numLetters A.lang}

end Supplement

end CircTrichotomy


