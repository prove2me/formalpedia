-- Prove2me | Definitions.Def_PolyEulerFlow_Supplement_PromiseInPSPACE
-- name    : PolyEulerFlow_Supplement_PromiseInPSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:04:49.223197+00:00
-- url     : https://prove2.me/theorems/d14548af-87d3-48b9-82fa-b9200d3a8bbc
-- title:
--   Promise problems in PSPACE, PSPACE-hard and PSPACE-complete under polynomial-time many-one reductions
-- statement:
--   A **promise problem** on instances $a\in A$, encoded in binary by $\mathrm{enc}:A\to\{0,1\}^*$, is given by a relation $\mathrm{Val}(a,b)$: "$a$ satisfies the promise and its value is $b\in\{0,1\}$".
--
--   1. It is **in PSPACE** if one multi-stack machine, started on $\mathrm{enc}(a)$, halts on every instance $a$, outputs $b$ whenever $\mathrm{Val}(a,b)$ (and anything on instances outside the promise), and uses total stack length at most $p(|\mathrm{enc}(a)|)$ on every instance, for a polynomial $p$.
--   2. It is **PSPACE-hard** under polynomial-time many-one reductions if for every language $L\subseteq\{0,1\}^*$ in PSPACE there is a polynomial-time computable map $f$ from words to instances with $\mathrm{Val}(f(w),[w\in L])$ for every word $w$: the reduction lands on promised instances and preserves the value.
--   3. It is **PSPACE-complete** if both hold.
--
--   This is the notion of completeness in Theorem 10.
--
--   **Formalization Note** The space measure, the machine model and the polynomial-time maps are those of the published `OptimalQueuingComplexity.Restless` (`InPSPACE`, `TM2ComputableInPolyTime`).
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), Theorem 10, p.8 (PDF 10); proof pp.44–45 (PDF 46–47)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_PSPACEComplete

namespace PolyEulerFlow.Supplement

/-- A promise problem in PSPACE (Theorem 10, p.8, PDF 10). The promise problem is given by a relation `Val a b`, "`a` is a promised
instance and its value is `b`". It is in PSPACE when one multi-stack machine halts on the encoding of **every** instance, outputs the value
on every promised instance (anything elsewhere), and uses total stack length at most `p(|enc a|)` on every instance, with the space measure
of the published `OptimalQueuingComplexity.Restless.InPSPACE`.
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), p.8. -/
def PromiseInPSPACE {α : Type} (enc : α → List Bool) (Val : α → Bool → Prop) : Prop :=
  ∃ (g : α → Bool) (h : Turing.TM2Computable enc (fun b : Bool => [b]) g) (p : Polynomial ℕ),
    (∀ a b, Val a b → g a = b) ∧
    ∀ (a : α) (cfg : h.tm.Cfg),
      StateTransition.Reaches h.tm.step
        (Turing.initList h.tm (List.map h.inputAlphabet.invFun (enc a))) cfg →
      ∑ k ∈ @Finset.univ h.tm.K h.tm.kFin, (Turing.TM2.Cfg.stk cfg k).length ≤
        p.eval (enc a).length

/-- PSPACE-hardness of a promise problem under polynomial-time many-one reductions: every PSPACE language `L ⊆ {0,1}*` has a
polynomial-time computable map `f` into promised instances with value `[w ∈ L]`. -/
def PromisePSPACEHard {α : Type} (enc : α → List Bool) (Val : α → Bool → Prop) : Prop :=
  ∀ L : Language Bool, OptimalQueuingComplexity.Restless.InPSPACE (id : List Bool → List Bool) (fun w => w ∈ L) →
    ∃ f : List Bool → α, Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool) enc f) ∧
      ∀ w, Val (f w) (open Classical in decide (w ∈ L))

/-- PSPACE-completeness of a promise problem: in PSPACE and PSPACE-hard. -/
def PromisePSPACEComplete {α : Type} (enc : α → List Bool) (Val : α → Bool → Prop) : Prop :=
  PromiseInPSPACE enc Val ∧ PromisePSPACEHard enc Val

end PolyEulerFlow.Supplement


