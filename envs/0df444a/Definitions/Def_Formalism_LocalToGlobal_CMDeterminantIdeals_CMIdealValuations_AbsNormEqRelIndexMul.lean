-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:09:59.518159+00:00
-- url     : https://prove2.me/theorems/2cb840c7-706a-46ef-a290-f754c433d93b
-- title:
--   Abs Norm Eq Rel Index Mul
-- statement:
--   Definitions and structural lemmas for Abs Norm Eq Rel Index Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/AbsNormEqRelIndexMul.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
def IndexFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (M : Submodule (𝓞 K) (Fin m → K)) (b : Fin m → Fin m → K),
    M.FG → Submodule.span K (M : Set (Fin m → K)) = ⊤ → LinearIndependent K b → (∀ i, b i ∈ M) →
    ((FractionalIdeal.absNorm (MLat.mk (Submodule.span (𝓞 K) (Set.range b)) (fun _ => 0) : MLat K m).detIdeal : ℚ) : ℝ) =
      ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex M.toAddSubgroup : ℝ) *
        ((FractionalIdeal.absNorm (MLat.mk M (fun _ => 0) : MLat K m).detIdeal : ℚ) : ℝ)
namespace Dx
variable {K : Type} [Field K] [NumberField K]
def dS {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : Submodule (𝓞 K) K :=
  Submodule.span (𝓞 K) {d | ∃ x : Fin n → Fin n → K, (∀ i, x i ∈ M) ∧ d = (Matrix.of x).det}
def lastL (K : Type) [Field K] [NumberField K] (n : ℕ) : (Fin (n+1) → K) →ₗ[𝓞 K] K :=
  LinearMap.proj (Fin.last n)
def snocL (K : Type) [Field K] [NumberField K] (n : ℕ) : (Fin n → K) →ₗ[𝓞 K] (Fin (n+1) → K) where
  toFun w := Fin.snoc (α := fun _ => K) w 0
  map_add' u v := by
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c u := by
    ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
def Sand {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : Prop :=
  (∃ a : 𝓞 K, a ≠ 0 ∧ ∀ i, (Pi.single i (algebraMap (𝓞 K) K a) : Fin n → K) ∈ M) ∧
    ∃ b ∈ (𝓞 K)⁰, ∀ x ∈ M, ∀ i, IsLocalization.IsInteger (𝓞 K) (b • x i)
def fiD {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) : FractionalIdeal (𝓞 K)⁰ K :=
  (MLat.mk M (fun _ => 0) : MLat K n).detIdeal
theorem frac_map {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) :
    IsFractional (𝓞 K)⁰ (M.map (lastL K n)) := by
  obtain ⟨b, hb, hint⟩ := hM.2
  refine ⟨b, hb, fun y hy => ?_⟩
  obtain ⟨v, hv, rfl⟩ := hy
  exact hint v hv _
def imI {n : ℕ} (M : Submodule (𝓞 K) (Fin (n+1) → K)) (hM : Sand M) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨M.map (lastL K n), frac_map M hM⟩
end Dx
end Formalism.L2.LamCM


