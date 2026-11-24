-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelation
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:06:05.75107+00:00
-- url     : https://prove2.me/theorems/bd5ed832-ad60-4316-9411-f7e3e5b374b4
-- title:
--   Bertini General Members No Derivative Relation
-- statement:
--   Definitions and structural lemmas for Bertini General Members No Derivative Relation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BertiniGeneralMembersNoDerivativeRelation.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentKaehlerDOfAlgebraicIndependentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.BertiniC
section Construction
variable {k A : Type} [Field k] [CommRing A] [Algebra k A] {n : ℕ}
  (δ : Fin n → Derivation k A A) {ι : Type} [Fintype ι] (f : ι → A) {M : ℕ}
  (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι)
abbrev Var (M : ℕ) (ι : Type) := (Fin M × ι) ⊕ (Fin M ⊕ Unit)
open MvPolynomial in

noncomputable def relIdeal : Ideal (MvPolynomial (Var M ι) A) :=
  Ideal.span {x | (∃ i ∈ J, x = ∑ p, X (Sum.inl (i, p)) * C (f p)) ∨
    (∃ l, x = ∑ i ∈ J, X (Sum.inr (Sum.inl i)) * ∑ p, X (Sum.inl (i, p)) * C (δ l (f p))) ∨
    x = X (Sum.inr (Sum.inl i₀)) - 1 ∨ x = X (Sum.inr (Sum.inr ())) * C (f p₀) - 1}
end Construction
end GlobalTheory.BertiniC


