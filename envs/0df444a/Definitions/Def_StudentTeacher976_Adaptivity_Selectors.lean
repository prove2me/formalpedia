-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_Selectors
-- name    : StudentTeacher976_Adaptivity_Selectors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T09:20:10.113208+00:00
-- url     : https://prove2.me/theorems/c0ee6ed6-29d8-4bd7-bb85-0f091854cff5
-- title:
--   Efficient selectors for total verifiable search
-- statement:
--   Fix a hierarchy level $i$. A total search relation $T$ has a verifier in $\Delta_{i+1}^p$ if membership of an encoded pair $(x,y)$ can be decided by one polynomial-time machine with a fixed $\Sigma_i^p$ oracle. Its permitted answers must have lengths bounded by one polynomial in the input length.
--
--   The predicate $\mathsf{SelectorCollapse}(i)$ states that every such relation has a uniform efficient selector:
--
--   $$
--   \forall T\in\mathrm{TFNP}^{\Sigma_i^p},\quad
--   \exists F\in\mathrm{FP}^{\Sigma_i^p}\ \forall x\ T(x,F(x)).
--   $$
--
--   This predicate is an explicit additional hypothesis for a proof case. It is not assumed in the mission's main theorem. The polynomial bound, oracle, program, and clock are fixed before all inputs, including the empty string and malformed encodings.
-- source:
--   Definition of total polynomially bounded verifiable search: Sam Buss, Proofs of Existence, Moscow April 2016 slides, PDF p.2, https://mathweb.ucsd.edu/~sbuss/ResearchWeb/Moscow_TFNP_April2016/talkslides.pdf. Oracle-relative variant using the fixed hierarchy and machine definitions of Ježil–Tsintsilidas, Parallelism and Adaptivity in Student-Teacher Witnessing, STOC 2027 submission #976, §1.2.1 pp.6–7. The selector-collapse predicate names a case assumption introduced in this development.

import Definitions.Def_StudentTeacher976_Adaptivity_Complexity
set_option autoImplicit false
open QAdvFew.PoQOracle
namespace StudentTeacher976.Adaptivity.SelectorPresentationTranslation

/-- Every total bounded search relation with a Delta_(i+1) verifier has a uniform
FP^Sigma_i selector. This is an explicit search-class predicate, not an axiom. -/
def SelectorCollapse (i : ℕ) : Prop :=
  ∀ T : SearchRelation,{s | ∃ x y,s=tup [x,y] ∧ T x y}∈Delta i →
    (∀ s,∃ v,T s v) →
    ∀ b : Polynomial ℕ,(∀ s v,T s v → v.length≤b.eval s.length) →
      ∃ F : Word → Word,InFP i F ∧ ∀ s,T s (F s)

end StudentTeacher976.Adaptivity.SelectorPresentationTranslation


