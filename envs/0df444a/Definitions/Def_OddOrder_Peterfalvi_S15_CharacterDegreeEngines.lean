-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
-- name    : OddOrder_Peterfalvi_S15_CharacterDegreeEngines
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:56:39.92711+00:00
-- url     : https://prove2.me/theorems/607e2ae8-1ba5-4ab6-9d36-634bd4c5cdc0
-- title:
--   Peterfalvi §13: $T$-side chosen-base (7.6) datum
-- statement:
--   Formalizes the $T$-side chosen-base (7.6) datum and distinguished index of Peterfalvi §13 (pp. 75-86), namely the (13.5)/(7.6) datum for $(T,Q^\#)$.
--
--   Main declarations: `Q_sharp_hypothesis76_base` (The (13.5)/(7.6) datum for `(T, Q^#)` with a chosen `𝒯₁`-base).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeEngines.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_CharacterDegreeEngines.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- **The (13.5)/(7.6) datum for `(T, Q^#)` with a chosen `𝒯₁`-base** (issue 2035 更新 #22
発見 2, the `T`-side twin of `H_sharp_hypothesis76_base`): the `Q_sharp_hypothesis76` mirror
through `hypothesis76OfDadeBase`, pinning `ζ₀ = Ind_Q^T φ₀` for a *given* `φ₀` —
Peterfalvi's per-application base choice for the `T`-side (13.5) of the (13.8)-for-`T`
estimate (`ζ₀ ∈ 𝒯₁`, i.e. `Q ⊄ Ker φ₀`; the trivial-base instance leaves the (13.5.a/b/c)
coefficient claims genuinely undetermined, exactly as on the `S`-side). -/
noncomputable def Q_sharp_hypothesis76_base [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (φ₀ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(hyp.Q.subgroupOf hyp.T)) :
    OddOrder.Peterfalvi.S09.Hypothesis76 G
      (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T := by
  refine OddOrder.Peterfalvi.S09.Cert.hypothesis76OfDadeBase
    (Q_sharp_hypothesis71 hG hyp hvd)
    (((Q_sharp_dadeHypothesis hG hyp
        hvd).fullDadeIsometryData).toDadeIsometryData.isDadeIsometry) hyp.Q ?_ ?_ rfl φ₀
  · rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  · intro l h hh
    have hnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
    have hlnorm : (l : G) ∈ Subgroup.normalizer (hyp.Q : Set G) := by
      rw [hnorm]; exact l.2
    exact (Subgroup.mem_set_normalizer_iff.mp hlnorm h).mp hh

end OddOrder.Peterfalvi.S15


