-- Prove2me | solution 1 for AlgebraicPCSP.Theory.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:41:20.252028+00:00
-- url     : https://prove2.me/submissions/257e148f-7d1b-4c33-be29-3526fee83241

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion
import Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
import Definitions.Def_AlgebraicPCSP_Theory_PPConstruction

open PCSPBLPAff.Symmetric

open AlgebraicPCSP.Theory in
theorem solution {C D : Type} [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (M : Minion C D) {τ : Type} [Fintype τ] {ar : τ → ℕ} (har : ∀ R, 0 < ar R)
    {A : Type} [Fintype A] [DecidableEq A] [Nonempty A] (𝔸 : RelStruct τ ar A)
    {n : ℕ} (e : Fin n ≃ A) (m : τ → ℕ) (eR : (R : τ) → Fin (m R) ≃ 𝔸.rel R) :
    M.Satisfies (sigmaCondition 𝔸 (freeStructure M 𝔸 e m eR) e m eR) := by
  unfold Minion.Satisfies SatisfiedIn
  refine ⟨fun u => u.val, fun Cn => Classical.choose Cn.2.2, fun u => u.2,
    fun Cn => (Classical.choose_spec Cn.2.2).1, ?_⟩
  rintro ⟨⟨R, t, ht⟩, i⟩
  exact (Classical.choose_spec ht).2 i
