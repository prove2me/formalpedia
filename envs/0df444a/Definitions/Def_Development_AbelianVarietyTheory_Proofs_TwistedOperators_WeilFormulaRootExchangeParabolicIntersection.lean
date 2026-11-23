-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_WeilFormulaRootExchangeParabolicIntersection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:49.709744+00:00
-- url     : https://prove2.me/theorems/08a81c80-f9f9-4cd0-a8fa-1bf362e56212
-- title:
--   Weil Formula Root Exchange Parabolic Intersection
-- statement:
--   Definitions and structural lemmas for Weil Formula Root Exchange Parabolic Intersection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/WeilFormulaRootExchangeParabolicIntersection.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulus
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
noncomputable section
namespace GlobalTheory.RootEx.QuotStep
section Abstract
end Abstract
section Pattern
variable {k : Type} [Field k] {ι : Type} [Fintype ι] [DecidableEq ι]
open Classical in

def ext (S : ι × ι → Prop) (e : {rs // S rs} → k) : Matrix ι ι k :=
  Matrix.of fun r s => if h : S (r, s) then e ⟨(r, s), h⟩ else 0
omit [Fintype ι] [DecidableEq ι] in
theorem ext_neg {S : ι × ι → Prop} (e : {rs // S rs} → k) {r s : ι} (h : ¬ S (r, s)) :
    ext S e r s = 0 := by simp [ext, h]
variable {b : ι → ℕ} {S : ι × ι → Prop}
def chart (hS : ∀ rs, S rs → b rs.1 < b rs.2) (e : {rs // S rs} → k) : GL ι k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + ext S e) (by
    rw [Radical.Uni.det (b := b) fun r s hrs => by
      rw [Matrix.add_apply, ext_neg e fun h => absurd (hS _ h) (not_lt.2 hrs), add_zero]]
    exact one_ne_zero)
variable (hS : ∀ rs, S rs → b rs.1 < b rs.2)
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
end Pattern
section Concrete
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
abbrev Both (n : Type) (c p : ℕ) (rs : (n ⊕ Fin c) × (n ⊕ Fin c)) : Prop :=
  lev p rs.1 < lev p rs.2 ∧ lev (p + 1) rs.1 < lev (p + 1) rs.2
abbrev chartN (q : ℕ) (e : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev q rs.1 < lev q rs.2} → k) : GL (n ⊕ Fin c) k :=
  chart (b := lev q) (S := fun rs => lev q rs.1 < lev q rs.2) (fun _ h => h) e
abbrev chartB (p : ℕ) (e : {rs // Both n c p rs} → k) : GL (n ⊕ Fin c) k :=
  chart (b := lev p) (S := Both n c p) (fun _ h => h.1) e
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
def IsSplit (p q : ℕ) (E : (n → k) → GL (n ⊕ Fin c) k) : Prop :=
  ∃ T : (n → k) × ({rs // Both n c p rs} → k) →
      ({rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev q rs.1 < lev q rs.2} → k),
    MeasurePreserving T ((Measure.pi fun _ => ν).prod (Measure.pi fun _ => ν)) (Measure.pi fun _ => ν) ∧
      ∀ y, chartN q (T y) = chartB p y.2 * E y.1
end Concrete
end GlobalTheory.RootEx.QuotStep


