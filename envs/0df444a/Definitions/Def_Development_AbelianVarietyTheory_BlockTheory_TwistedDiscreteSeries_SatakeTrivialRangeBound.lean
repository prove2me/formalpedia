-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SatakeTrivialRangeBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:49.918427+00:00
-- url     : https://prove2.me/theorems/559d2fab-13e6-42d6-82cf-bdc5fcc52ddc
-- title:
--   Satake Trivial Range Bound
-- statement:
--   Definitions and structural lemmas for Satake Trivial Range Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/SatakeTrivialRangeBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_hasSatake_detRep
import Theorems.Thm_GlobalTheory_SmGL_isIrreducible_ofChar
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_of_isUnram
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_ofChar_iff
import Theorems.Thm_GlobalTheory_SmGL_isSpherical_detRep
import Theorems.Thm_GlobalTheory_SmGL_isUnitarisable_ofChar_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
namespace GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound
def InTrivialRange (q : ℕ) {n : ℕ} (α : Fin n → ℂˣ) : Prop :=
  ∀ i, (q : ℝ) ^ (-(((n : ℝ) - 1) / 2)) ≤ ‖(α i : ℂ)‖ ∧ ‖(α i : ℂ)‖ ≤ (q : ℝ) ^ (((n : ℝ) - 1) / 2)
def SatakeTrivialBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (α : Fin n → ℂˣ),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsSpherical π → HasSatake π α →
      InTrivialRange (resCard k) α
section Hecke
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
def diagJ (n : ℕ) (ϖ : kˣ) (j : ℕ) : GL (Fin n) k :=
  diagT k (Fin n) fun i => if (i : ℕ) < j then ϖ else 1
def HeckeEigen (π : Representation ℂ (GL (Fin n) k) V) (v : V) (t : GL (Fin n) k) (c : ℂ) : Prop :=
  ∃ S : Finset (GL (Fin n) k ⧸ KO k (Fin n)),
    (∀ g : GL (Fin n) k, (g : GL (Fin n) k ⧸ KO k (Fin n)) ∈ S ↔
      ∃ a ∈ KO k (Fin n), ∃ b ∈ KO k (Fin n), g = a * t * b) ∧
    ∑ x ∈ S, π x.out v = c • v
end Hecke
def SatakeTrivialBoundHecke : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (v : V) (ϖ : kˣ) (α : Fin n → ℂˣ),
    IsUnitarisable π → v ≠ 0 → v ∈ fixed π (KO k (Fin n)) → valuation k (ϖ : k) = uniformizer k →
    (∀ j : ℕ, 1 ≤ j → j ≤ n → HeckeEigen π v (diagJ n ϖ j)
      ((((resCard k : ℝ) ^ ((j : ℝ) * ((n : ℝ) - j) / 2) : ℝ) : ℂ) *
        (Finset.univ.val.map fun i => (α i : ℂ)).esymm j)) →
      InTrivialRange (resCard k) α
section Basic₂
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
example (n : ℕ) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) :
    IsSmooth (detRep (Fin n) (1 : kˣ →* ℂˣ)) ∧ (detRep (Fin n) (1 : kˣ →* ℂˣ)).IsIrreducible ∧
    IsUnitarisable (detRep (Fin n) (1 : kˣ →* ℂˣ)) ∧ IsSpherical (detRep (Fin n) (1 : kˣ →* ℂˣ)) ∧
    HasSatake (detRep (Fin n) (1 : kˣ →* ℂˣ))
      fun i => (1 : kˣ →* ℂˣ) ϖ * absPow k (((i : ℕ) : ℂ) - ((n : ℂ) - 1) / 2) ϖ := by
  have h : IsUnram (1 : kˣ →* ℂˣ) := fun _ _ => rfl
  refine ⟨(isSmooth_ofChar_iff _).2 (isSmoothChar_of_isUnram h).detChar, isIrreducible_ofChar _,
    (isUnitarisable_ofChar_iff _).2 fun g => by simp, isSpherical_detRep h, hasSatake_detRep h hϖ⟩
example (q : ℕ) (α : Fin 1 → ℂˣ) : InTrivialRange q α ↔ ‖(α 0 : ℂ)‖ = 1 := by
  simp only [InTrivialRange, Fin.forall_fin_one, Nat.cast_one, sub_self, zero_div, neg_zero,
    Real.rpow_zero]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound


