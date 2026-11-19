-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_AdviceSelectors
-- name    : StudentTeacher976_Adaptivity_AdviceSelectors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T11:53:16.064245+00:00
-- url     : https://prove2.me/theorems/20e75992-32fa-4223-ac19-26655cf4b3ea
-- title:
--   Length-uniform oracle advice computation and total-search selectors
-- statement:
--   Fix a hierarchy level $i$. A string function $f$ belongs to $\mathrm{FP}^{\Sigma_i^p}/\mathrm{poly}$ if a single fixed oracle-polynomial function $G$, a polynomial $b$, and one advice word $a(n)$ for every input length satisfy
--
--   $$
--   |a(n)|\le b(n),\qquad f(x)=G(\langle x,a(|x|)\rangle).
--   $$
--
--   The function $G$ uses one fixed $\Sigma_i^p$ oracle and has a fixed polynomial clock on every encoded input, including malformed encodings. Advice need not be computable and is the same for all words of a given length.
--
--   The accompanying selector-collapse predicate is the explicit hypothesis that every total polynomially bounded search relation $T$ with an encoded graph in $\Delta_{i+1}^p$ has such a selector:
--
--   $$
--   \forall x\;T(x,f(x)).
--   $$
--
--   These predicates support analysis of presentation changes when the final lower-bound argument permits polynomial advice. They do not assert any collapse, hardness assumption or game separation.
-- source:
--   Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf, §1.2.1, pp.6–7, and the length-uniform advice condition of Theorem 1.4, p.7; functional and selector interfaces introduced explicitly for this development.

import Definitions.Def_StudentTeacher976_Adaptivity_Complexity
set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity.AdviceComputations

/-- A fixed oracle transducer, with one polynomially bounded advice word per input length.
Its underlying InFP program has a polynomial clock on every raw input string. -/
def InFPAdvice (i : ℕ) (f : Word → Word) : Prop :=
  ∃ (G : Word → Word) (b : Polynomial ℕ) (a : ℕ → Word),
    InFP i G ∧ (∀ n,(a n).length ≤ b.eval n) ∧
    ∀ x,G (tup [x,a x.length])=f x

end StudentTeacher976.Adaptivity.AdviceComputations
namespace StudentTeacher976.Adaptivity.AdviceSelectorTranslation

/-- An explicit search-class hypothesis allowing length-uniform polynomial advice.
It asserts no hardness condition or game separation. -/
def SelectorCollapse (i : ℕ) : Prop :=
  ∀ T : SearchRelation,{s | ∃ x y,s=tup [x,y] ∧ T x y}∈Delta i →
    (∀ x,∃ y,T x y) →
    ∀ b : Polynomial ℕ,(∀ x y,T x y → y.length ≤ b.eval x.length) →
      ∃ F : Word → Word,AdviceComputations.InFPAdvice i F ∧ ∀ x,T x (F x)

end StudentTeacher976.Adaptivity.AdviceSelectorTranslation


