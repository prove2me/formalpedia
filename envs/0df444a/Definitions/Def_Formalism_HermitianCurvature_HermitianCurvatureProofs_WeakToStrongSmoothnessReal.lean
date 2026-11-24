-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:42.96612+00:00
-- url     : https://prove2.me/theorems/a817b73b-6510-43a2-8453-11be0d768ffa
-- title:
--   Weak To Strong Smoothness Real
-- statement:
--   Definitions and structural lemmas for Weak To Strong Smoothness Real, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeakToStrongSmoothnessReal.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dw_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_len_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_lie_LR
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_sCkOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_unit_lie

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
namespace Formalism.FourierDecayAlt.P.Ux11
section real
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
def Norming {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (lam : I → V →L[ℝ] E) : Prop :=
  ∀ (v : V) (c : ℝ), (∀ i, ‖lam i v‖ ≤ c) → ‖v‖ ≤ c
variable [FiniteDimensional ℝ X]
end real
section thm
def Idx (k ρ mm : ℕ) : Type :=
  {t : List (B.Mat k ρ) × List (B.Mat k ρ) × B.Mat k ρ //
    U.unitW k ρ t.1 ∧ U.unitW k ρ t.2.1 ∧ t.1.length + t.2.1.length ≤ mm ∧ t.2.2 ∈ B.GV k ρ}
variable {k ρ mm : ℕ} {E V : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
  [NormedSpace ℂ V] {a : ℝ} {S : Set (B.Mat k ρ)}
lemma gNa_nonneg (γ : B.Mat k ρ) (a : ℝ) : 0 ≤ B.gN γ ^ a := Real.rpow_nonneg (Real.sqrt_nonneg _) a
lemma ev_add (M : U.CCModel k ρ E a mm S V) (w₁ w₂ : V) :
    M.ev (w₁ + w₂) = fun g => M.ev w₁ g + M.ev w₂ g := by
  rw [map_add]; rfl
lemma ev_smul (M : U.CCModel k ρ E a mm S V) (c : ℂ) (w : V) : M.ev (c • w) = fun g => c • M.ev w g := by
  rw [map_smul]; rfl
lemma ck_len (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) (w : V) :
    B.CkOn (((BetaSesquilinearity.wL t.1.1 ++ BetaSesquilinearity.wR t.1.2.1).length : ℕ) : ℕ∞) (B.GV k ρ) (M.ev w) :=
  BetaSesquilinearity.sCkOn_mono (by rw [BetaSesquilinearity.len_LR]; exact_mod_cast t.2.2.2.1) (M.mem w).1
def lamL (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) : V →ₗ[ℂ] E where
  toFun w := ((B.gN t.1.2.2 ^ a : ℝ) : ℂ) • B.dLR t.1.1 t.1.2.1 (M.ev w) t.1.2.2
  map_add' w₁ w₂ := by
    rw [ev_add, BetaSesquilinearity.dLR_eq, BetaSesquilinearity.Dw_add (BetaSesquilinearity.lie_LR (BetaSesquilinearity.unit_lie t.2.1) (BetaSesquilinearity.unit_lie t.2.2.1))
      (ck_len M t w₁) (ck_len M t w₂) _ t.2.2.2.2, ← BetaSesquilinearity.dLR_eq, ← BetaSesquilinearity.dLR_eq, smul_add]
  map_smul' c w := by
    simp only [ev_smul, BetaSesquilinearity.dLR_eq, BetaSesquilinearity.Dw_smul, RingHom.id_apply]
    exact smul_comm _ _ _
lemma lamL_norm (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) (w : V) : ‖lamL M t w‖ ≤ ‖w‖ := by
  show ‖((B.gN t.1.2.2 ^ a : ℝ) : ℂ) • B.dLR t.1.1 t.1.2.1 (M.ev w) t.1.2.2‖ ≤ ‖w‖
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (gNa_nonneg _ _)]
  exact (M.mem w).2 _ _ t.2.1 t.2.2.1 t.2.2.2.1 _ t.2.2.2.2
def lamC (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) : V →L[ℂ] E :=
  (lamL M t).mkContinuous 1 (fun w => by rw [one_mul]; exact lamL_norm M t w)
def sc (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℝ) : E →L[ℝ] E :=
  ((c : ℂ) • ContinuousLinearMap.id ℂ E).restrictScalars ℝ
end thm
end Formalism.FourierDecayAlt.P.Ux11


