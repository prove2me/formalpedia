-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormWithPoint_2137add7c40a5a9d
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__IsTorsionFormWithPoint_2137add7c40a5a9d
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:06:13.764787+00:00
-- url     : https://prove2.me/theorems/102a4ba0-2d87-4270-a1e9-776d7d848b9a
-- title:
--   Is Torsion Form With Point
-- statement:
--   Definitions and structural lemmas for Is Torsion Form With Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/IsTorsionFormWithPoint.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TranslationInv_27ddeabb7aac02dc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff ComplexConjugate
namespace GlobalTheory.TorsionForm
def str {m g : ℕ} (K : Ext (m + g) →L[ℂ] Ext (m + g)) : Ext m := fun S =>
  ∑ I : Finset (Fin g), (-1) ^ I.card * K (Pi.single (join ∅ I) 1) (join S I)
def baseMul {n : ℕ} (k : Matrix (Fin n) (Fin n) ℂ) (w : Ext (n + n)) : Ext (n + n) :=
  ∑ i, ∑ l, k i l • wedge (i.castAdd n) (wedge (l.natAdd n) w)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
  (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (j : Fl g → Pt E g → ℂ)
  (h : Pt E g → ℝ) (β : Fin n → E)
def IsHeatTraceWith (b : E) (k : Matrix (Fin n) (Fin n) ℂ) (F : ℝ → Ext (n + n)) : Prop :=
  ∃ D : Set (Fl g), IsAddFundamentalDomain M D volume ∧ ∀ u > 0, ∃ K,
    IsHeatKernel τ M j h β b u D K ∧
      F u = phi (∫ x in D, (strN (K 1 (per (τ b) x) (per (τ b) x)) +
        ((u : ℂ)⁻¹) • baseMul k (str (K 1 (per (τ b) x) (per (τ b) x)))))
def IsTorsionFormWith (b : E) (k : Matrix (Fin n) (Fin n) ℂ) (T : Ext (n + n)) : Prop :=
  ∃ F, IsHeatTraceWith τ M j h β b k F ∧ ∀ S, IsMellinDeriv (fun u => F u S) (T S)
def IsClosedHerm (B : Set E) (k : E → E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) : Prop :=
  (∀ v w, ContDiffOn ℝ ∞ (fun b => k b v w) B) ∧ ∀ b ∈ B, (∀ v w, k b w v = conj (k b v w)) ∧
    ∀ u v w, d10 (fun x => k x v w) b u = d10 (fun x => k x u w) b v
example (k : ℂ) : baseMul (n := 1) (of fun _ _ => k) (Pi.single ∅ 1) Finset.univ = k := by
  have e₁ : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have e₄ : (({1} : Finset (Fin 2)).filter (· = 0)).card = 0 := by decide
  have e₅ : Fin.castAdd 1 (0 : Fin 1) = (0 : Fin 2) := rfl
  have e₆ : Fin.natAdd 1 (0 : Fin 1) = (1 : Fin 2) := rfl
  simp [baseMul, wedge, sgn, e₁, e₄, e₅, e₆]
end GlobalTheory.TorsionForm


