-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:16.905509+00:00
-- url     : https://prove2.me/theorems/d3976efb-17e6-4f05-9684-659c997cf028
-- title:
--   Continuous Inv Upper
-- statement:
--   Definitions and structural lemmas for Continuous Inv Upper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
namespace Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance
instance sigmaFinite_muPi (β : ℂ) (ι : Type) [Fintype ι] : SigmaFinite (muPi β ι) := by
  unfold muPi; infer_instance
noncomputable def idxEquiv (n : ℕ) : UT n ⊕ Fin n ≃ UT (n + 1) :=
  Equiv.ofBijective
    (Sum.elim (fun p => ⟨(p.1.1.castSucc, p.1.2.castSucc), Fin.castSucc_lt_castSucc_iff.2 p.2⟩)
      (fun i => ⟨(i.castSucc, Fin.last n), Fin.castSucc_lt_last i⟩))
    (by
      constructor
      · rintro (⟨⟨i, j⟩, h⟩ | i) (⟨⟨i', j'⟩, h'⟩ | i') hh
        · simp only [Sum.elim_inl, Subtype.mk.injEq, Prod.mk.injEq, Fin.castSucc_inj] at hh
          simp [hh.1, hh.2]
        · simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Prod.mk.injEq] at hh
          exact absurd hh.2 (Fin.castSucc_lt_last j).ne
        · simp only [Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq, Prod.mk.injEq] at hh
          exact absurd hh.2.symm (Fin.castSucc_lt_last j').ne
        · simp only [Sum.elim_inr, Subtype.mk.injEq, Prod.mk.injEq, Fin.castSucc_inj, and_true] at hh
          rw [hh]
      · rintro ⟨⟨i, j⟩, h⟩
        have h' : i < j := h
        induction j using Fin.lastCases with
        | last =>
          induction i using Fin.lastCases with
          | last => exact absurd h' (lt_irrefl _)
          | cast i => exact ⟨Sum.inr i, rfl⟩
        | cast j =>
          induction i using Fin.lastCases with
          | last => exact absurd h' (not_lt.2 (Fin.castSucc_lt_last j).le)
          | cast i => exact ⟨Sum.inl ⟨(i, j), Fin.castSucc_lt_castSucc_iff.1 h'⟩, rfl⟩)
noncomputable def joinU {n : ℕ} (q : (UT n → ℂ) × (Fin n → ℂ)) : UT (n + 1) → ℂ :=
  fun p => Sum.elim q.1 q.2 ((idxEquiv n).symm p)
instance sigmaFinite_muBlock (β : ℂ) (n : ℕ) : SigmaFinite (muBlock β n) := by
  unfold muBlock; infer_instance
def revEquiv (n : ℕ) : UT n ≃ UT n where
  toFun p := ⟨(p.1.2.rev, p.1.1.rev), Fin.rev_lt_rev.2 p.2⟩
  invFun p := ⟨(p.1.2.rev, p.1.1.rev), Fin.rev_lt_rev.2 p.2⟩
  left_inv p := by simp
  right_inv p := by simp
end Formalism.FourierDecayAlt.P.G5
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
end Formalism.FourierDecayAlt.P


