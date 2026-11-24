-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:31.098701+00:00
-- url     : https://prove2.me/theorems/563ad4c8-8d8a-4564-9381-875cc27c07a7
-- title:
--   Local Density Sixth
-- statement:
--   Definitions and structural lemmas for Local Density Sixth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensitySixth.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
abbrev spanO (b : Basis κ K V) : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)
def bO (b : Basis κ K V) : Basis κ (𝓞 K) (spanO b) :=
  Basis.span (b.linearIndependent.restrict_scalars' (𝓞 K))
def crd (b : Basis κ K V) (y : spanO b) : κ → 𝓞 K := (bO b).equivFun y
def redL (b : Basis κ K V) (J : Ideal (𝓞 K)) : spanO b →ₗ[𝓞 K] (κ → 𝓞 K ⧸ J) :=
  (J.mkQ.compLeft κ) ∘ₗ (bO b).equivFun.toLinearMap
theorem redL_apply (b : Basis κ K V) (J : Ideal (𝓞 K)) (y : spanO b) :
    redL b J y = fun i => Ideal.Quotient.mk J (crd b y i) := rfl
theorem redL_surjective (b : Basis κ K V) (J : Ideal (𝓞 K)) : Function.Surjective (redL b J) := by
  intro x
  choose c hc using fun i => Ideal.Quotient.mk_surjective (x i)
  refine ⟨(bO b).equivFun.symm c, ?_⟩
  rw [redL_apply]
  funext i
  rw [crd, LinearEquiv.apply_symm_apply, hc]
theorem ker_redL (b : Basis κ K V) (J : Ideal (𝓞 K)) :
    LinearMap.ker (redL b J) = (J • ⊤ : Submodule (𝓞 K) (spanO b)) := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker, redL_apply] at hy
    rw [← (bO b).sum_equivFun y]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    exact Ideal.Quotient.eq_zero_iff_mem.1 (congrFun hy i)
  · rw [Submodule.smul_le]
    intro a ha y _
    rw [LinearMap.mem_ker, map_smul]
    funext i
    rw [Pi.smul_apply, redL_apply, Algebra.smul_def]
    have : algebraMap (𝓞 K) (𝓞 K ⧸ J) a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
    rw [this, zero_mul]
    rfl
def qE (b : Basis κ K V) (J : Ideal (𝓞 K)) :
    (spanO b ⧸ (J • ⊤ : Submodule (𝓞 K) (spanO b))) ≃ₗ[𝓞 K] (κ → 𝓞 K ⧸ J) :=
  (Submodule.quotEquivOfEq _ _ (ker_redL b J).symm).trans
    ((redL b J).quotKerEquivOfSurjective (redL_surjective b J))
variable [Fact (IsFixF K F)]
def eM (b : Basis κ K V) (J : Ideal (𝓞 K)) :
    Module.End (𝓞 K) (spanO b ⧸ (J • ⊤ : Submodule (𝓞 K) (spanO b))) ≃ Matrix κ κ (𝓞 K ⧸ J) :=
  (qE b J).conj.toEquiv.trans
    ((LinearMap.extendScalarsOfSurjectiveEquiv (R := 𝓞 K) (S := 𝓞 K ⧸ J)
      Ideal.Quotient.mk_surjective).toEquiv.trans LinearMap.toMatrix'.toEquiv)
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans


