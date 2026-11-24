-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemSmulOfMemFlagSubOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:35.360794+00:00
-- url     : https://prove2.me/theorems/185a42d6-792a-40ad-83b4-a1262b0cecd6
-- title:
--   Mem Smul Of Mem Flag Sub One
-- statement:
--   Definitions and structural lemmas for Mem Smul Of Mem Flag Sub One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemSmulOfMemFlagSubOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing
open scoped Pointwise ENNReal
noncomputable section
namespace GlobalTheory.LevelUnfold
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} {c : ℕ} {q : Unif k}
variable [Fintype n] [DecidableEq n]
omit [Fintype n] [DecidableEq n] in

def colEquiv (n n' : Type) (c : ℕ) :
    (Σ i : Fin c, n ⊕ Fin (i.val + 1)) ≃ {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} :=
  Equiv.ofBijective
    (fun t => ⟨(Sum.map id (Fin.castLE t.1.2) t.2, Sum.inr t.1.succ), by
      rcases t with ⟨i, j | j⟩
      · simp [Free]
      · simpa [Free] using j.2⟩) <| by
    constructor
    · rintro ⟨i, j⟩ ⟨i', j'⟩ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq, Sum.inr.injEq, Fin.succ_inj] at h
      obtain ⟨h, rfl⟩ := h
      rw [(Sum.map_injective.2 ⟨Function.injective_id, Fin.castLE_injective _⟩) h]
    · rintro ⟨⟨r | r, s | s⟩, h⟩
      · exact h.elim
      · have hs : s ≠ 0 := by rintro rfl; simp [Free] at h
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hs
        exact ⟨⟨i, Sum.inl r⟩, rfl⟩
      · simp [Free] at h
      · have hs : s ≠ 0 := by rintro rfl; simp [Free] at h
        obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hs
        exact ⟨⟨i, Sum.inr ⟨r.val, h⟩⟩, rfl⟩
end GlobalTheory.LevelUnfold


