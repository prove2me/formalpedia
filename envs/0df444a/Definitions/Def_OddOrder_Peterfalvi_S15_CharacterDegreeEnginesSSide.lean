-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
-- name    : OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:52:31.396214+00:00
-- url     : https://prove2.me/theorems/2365d50b-2c81-4470-b943-7cade3df2fa8
-- title:
--   Peterfalvi §13: $\tau_1$-supply engines and the character-degree core ($S$-side)
-- statement:
--   Formalizes the $\tau_1$-supply engines and the character-degree core of Peterfalvi §13 (pp. 75-86), including the (13.5)/(7.6) datum for $(S,H^\#)$ with a chosen base.
--
--   Main declarations: `H_sharp_hypothesis76_base` (The (13.5)/(7.6) datum for `(S, H^#)` with a chosen `𝒮₁`-base).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherence
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **The (13.5)/(7.6) datum for `(S, H^#)` with a chosen `𝒮₁`-base** (issue 2035 更新
#22/#24): the `H_sharp_hypothesis76` mirror through `hypothesis76OfDadeBase`, pinning
`ζ₀ = Ind_{PC}^S φ₀` for a *given* `φ₀` — Peterfalvi's per-application base choice ((13.5)
takes `ζ₀ ∈ 𝒮₁`, i.e. `P ⊄ Ker φ₀`; the (13.5.a/b/c) coefficient computations then convert
`(ζ_i − ζ₀)^{τ₁} ↔ Ind_S^G` through the *guarded* `CharacterDegreeCore` fields, which the
trivial-base instance cannot). -/
noncomputable def H_sharp_hypothesis76_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.H.subgroupOf hyp.S)) :
    OddOrder.Peterfalvi.S09.Hypothesis76 G
      (OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G)) hyp.S := by
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeBase
    (H_sharp_hypothesis71 hG hyp) ?_ hyp.H ?_ ?_ rfl φ₀
  · exact ((H_sharp_dadeHypothesis hG hyp).fullDadeIsometryData).toDadeIsometryData.isDadeIsometry
  · have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    change hyp.P ⊔ hyp.C ≤ hyp.S
    refine sup_le ?_ ?_
    · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
    · rw [hyp.C_eq]; exact le_trans inf_le_left hUS
  · intro l h hh
    by_cases h1 : h = 1
    · subst h1; simp
    · have hsh : h ∈ OddOrder.Peterfalvi.S04.sharp (hyp.H : Set G) :=
        OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨hh, h1⟩
      exact (OddOrder.Peterfalvi.S04.mem_sharp.mp (S_normalizes_H_sharp hG hyp l hsh)).1

end OddOrder.Peterfalvi.S15


