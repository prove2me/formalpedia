-- Prove2me | Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
-- name    : Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:37.949797+00:00
-- url     : https://prove2.me/theorems/7d81ef28-840b-4c38-b930-e908c76f65f0
-- title:
--   Laplace
-- statement:
--   Definitions and structural lemmas for Laplace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Laplace.lean

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Equiv
noncomputable section
namespace Formalism.ResultantValuation
namespace LaplaceProof
variable {a b : ℕ}
theorem shuffle_bijective (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b) :
    Function.Bijective (Sum.elim (J.orderEmbOfFin h) (Jᶜ.orderEmbOfFin hc)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  rintro (i | i) (j | j) hij
  · simp only [Sum.elim_inl] at hij
    rw [(J.orderEmbOfFin h).injective hij]
  · simp only [Sum.elim_inl, Sum.elim_inr] at hij
    have h1 := J.orderEmbOfFin_mem h i
    rw [hij] at h1
    exact absurd h1 (Finset.mem_compl.mp (Jᶜ.orderEmbOfFin_mem hc j))
  · simp only [Sum.elim_inl, Sum.elim_inr] at hij
    have h1 := J.orderEmbOfFin_mem h j
    rw [← hij] at h1
    exact absurd h1 (Finset.mem_compl.mp (Jᶜ.orderEmbOfFin_mem hc i))
  · simp only [Sum.elim_inr] at hij
    rw [(Jᶜ.orderEmbOfFin hc).injective hij]
def shuffle (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b) : Perm (Fin (a + b)) :=
  finSumFinEquiv.symm.trans (Equiv.ofBijective _ (shuffle_bijective J h hc))
theorem compl_card (J : {J : Finset (Fin (a + b)) // J.card = a}) : (J.1ᶜ).card = b := by
  rw [Finset.card_compl, Fintype.card_fin, J.2]
  omega
def glue (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a}, Perm (Fin a) × Perm (Fin b)) :
    Perm (Fin (a + b)) :=
  shuffle x.1.1 x.1.2 (compl_card x.1) * finSumFinEquiv.permCongr (Perm.sumCongr x.2.1 x.2.2)
end LaplaceProof
end Formalism.ResultantValuation


