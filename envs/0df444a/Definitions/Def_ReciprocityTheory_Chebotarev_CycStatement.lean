-- Prove2me | Definitions.Def_ReciprocityTheory_Chebotarev_CycStatement
-- name    : ReciprocityTheory_Chebotarev_CycStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:52.480248+00:00
-- url     : https://prove2.me/theorems/44d0c0be-1e25-4229-83b0-e68fea494c18
-- title:
--   Cyc Statement
-- statement:
--   Definitions and structural lemmas for Cyc Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/CycStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace ReciprocityTheory.Cheb
def Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (σ : Gal(K/ℚ)) (T : Finset ℕ),
    ∃ p : ℕ, p.Prime ∧ p ∉ T ∧ ∃ P : Ideal (𝓞 K), ∃ _ : P.IsPrime,
      P.LiesOver (Ideal.span {(p : ℤ)}) ∧ Algebra.IsUnramifiedAt ℤ P ∧ IsArithFrobAt ℤ σ P
def CycStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime], Irreducible (Polynomial.cyclotomic l E) →
    ∀ (a : (ZMod l)ˣ) (T : Finset ℕ), ∃ q : Ideal (𝓞 E), q.IsPrime ∧ (Ideal.absNorm q).Prime ∧ Ideal.absNorm q ∉ T ∧
      ((Ideal.absNorm q : ℕ) : ZMod l) = a
end ReciprocityTheory.Cheb


