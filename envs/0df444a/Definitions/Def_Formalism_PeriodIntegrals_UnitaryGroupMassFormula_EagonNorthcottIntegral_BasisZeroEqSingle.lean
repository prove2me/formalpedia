-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_BasisZeroEqSingle
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_BasisZeroEqSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:38.042075+00:00
-- url     : https://prove2.me/theorems/2031d5c1-5828-43c8-aa24-f6c014c58755
-- title:
--   Basis Zero Eq Single
-- statement:
--   Definitions and structural lemmas for Basis Zero Eq Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/BasisZeroEqSingle.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_YHom
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EagonNorthcottZ
open MvPolynomial
def mon {D : ℕ} (α : Fin D → ℕ) : Fin D ⊕ Fin D →₀ ℕ := ∑ i, Finsupp.single (Sum.inr i) (α i)
def yp {D : ℕ} (α : Fin D → ℕ) : P D := ∏ i, ys i ^ α i
lemma noX_iff {D : ℕ} (f : P D) : NoX f ↔ ∃ g, rename Sum.inr g = f := Iff.rfl
lemma nox_zero {D : ℕ} : NoX (0 : P D) := (noX_iff _).2 ⟨0, map_zero _⟩
lemma nox_add {D : ℕ} {f g : P D} (hf : NoX f) (hg : NoX g) : NoX (f + g) := by
  obtain ⟨u, rfl⟩ := (noX_iff _).1 hf
  obtain ⟨v, rfl⟩ := (noX_iff _).1 hg
  exact (noX_iff _).2 ⟨u + v, map_add _ _ _⟩
lemma nox_smul {D : ℕ} (c : ℤ) {f : P D} (hf : NoX f) : NoX (c • f) := by
  obtain ⟨u, rfl⟩ := (noX_iff _).1 hf
  exact (noX_iff _).2 ⟨c • u, map_smul _ _ _⟩
lemma yhom_zero {D a : ℕ} : YHom (D := D) a 0 := by
  intro m hm
  simp at hm
lemma yhom_add {D a : ℕ} {f g : P D} (hf : YHom a f) (hg : YHom a g) : YHom a (f + g) := by
  classical
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  exacts [hf m h, hg m h]
lemma yhom_smul {D a : ℕ} (c : ℤ) {f : P D} (hf : YHom a f) : YHom a (c • f) :=
  fun m hm => hf m (support_smul hm)
lemma K_zero {D : ℕ} (t : Fin D → P D) : K t 0 = 0 := by
  funext J
  simp [K]
lemma K_add {D : ℕ} (t : Fin D → P D) (ω η : W D) : K t (ω + η) = K t ω + K t η := by
  funext J
  simp [K, mul_add, Finset.sum_add_distrib]
lemma K_smul {D : ℕ} (t : Fin D → P D) (c : ℤ) (ω : W D) : K t (c • ω) = c • K t ω := by
  funext J
  simp only [K, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_smul_comm]
lemma isZL_iff {D a j : ℕ} (ω : W D) : IsZL a j ω ↔
    (((∀ J, J.card ≠ j → ω J = 0) ∧ ∀ J, YHom a (ω J)) ∧ K ys ω = 0) ∧ ∀ J, NoX (ω J) := Iff.rfl
def ZL (D a j : ℕ) : Submodule ℤ (W D) where
  carrier := {ω | IsZL a j ω}
  zero_mem' := (isZL_iff _).2 ⟨⟨⟨fun _ _ => rfl, fun _ => yhom_zero⟩, K_zero _⟩, fun _ => nox_zero⟩
  add_mem' := by
    intro ω η hω hη
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := (isZL_iff _).1 hω
    obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := (isZL_iff _).1 hη
    refine (isZL_iff _).2 ⟨⟨⟨fun J hJ => ?_, fun J => yhom_add (h2 J) (g2 J)⟩, ?_⟩,
      fun J => nox_add (h4 J) (g4 J)⟩
    · simp [h1 J hJ, g1 J hJ]
    · rw [K_add, h3, g3, add_zero]
  smul_mem' := by
    intro c ω hω
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := (isZL_iff _).1 hω
    refine (isZL_iff _).2 ⟨⟨⟨fun J hJ => ?_, fun J => yhom_smul c (h2 J)⟩, ?_⟩,
      fun J => nox_smul c (h4 J)⟩
    · simp [h1 J hJ]
    · rw [K_smul, h3, smul_zero]
def G (D a : ℕ) : Set (W D) :=
  Set.range fun p : Finset (Fin D) × {α // α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin D)) a} =>
    (Pi.single p.1 (yp p.2.1) : W D)
end PI.EagonNorthcottZ


