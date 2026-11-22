-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:39.032804+00:00
-- url     : https://prove2.me/theorems/15f2bb11-215e-473e-85c3-b3dc2c7fd8f4
-- title:
--   Mem Pol KIff
-- statement:
--   Definitions and structural lemmas for Mem Pol KIff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MemPolKIff.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_LiftBoundOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
def vge (v : AddValuation K (WithTop ℚ)) (a : ℝ) (x : K) : Prop := ((a : ℝ) : WithTop ℝ) ≤ vR v x
def vle (v : AddValuation K (WithTop ℚ)) (a : ℝ) (x : K) : Prop := vR v x ≤ ((a : ℝ) : WithTop ℝ)
def cge (v : AddValuation K (WithTop ℚ)) (a : ℝ) {σ : Type} (F : MvPolynomial σ K) : Prop :=
  ∀ α, vge v a (F.coeff α)
def vN (v : AddValuation K (WithTop ℚ)) (n : ℕ) : ℝ := (((v (n : K)).untopD 0 : ℚ) : ℝ)
def bge (v : AddValuation K (WithTop ℚ)) (a : ℝ) {σ : Type} (F : MvPolynomial σ K) : Prop :=
  ∀ α, vge v (a - vN v (fact α) / 2) (F.coeff α)
def dg {σ : Type} (f : (σ →₀ ℕ) → K) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K :=
  (basisMonomials σ K).constr K fun α => monomial α (f α)
def ldeg {L : Type} {r : ℕ} (α : L × Fin r →₀ ℕ) (i : L) : ℕ := ∑ a : Fin r, α (i, a)
def vala {L : Type} [DecidableEq L] {r : ℕ} (sg : L → Bool) (S : Finset L) (θ : ℝ)
    (F : MvPolynomial (L × Fin r) K) : Prop :=
  ((θ : ℝ) : WithTop ℝ) ≤ toR (valS sg S F)
def eOut {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out] (α : L × Fin r →₀ ℕ) :
    L × Fin r →₀ ℕ := α.filter fun x => out x.1
def eIn {L : Type} {r : ℕ} (out : L → Prop) [DecidablePred out] (α : L × Fin r →₀ ℕ) :
    L × Fin r →₀ ℕ := α.filter fun x => ¬ out x.1
def coefOut {L : Type} [DecidableEq L] {r : ℕ} (out : L → Prop) [DecidablePred out] (μ : L × Fin r →₀ ℕ)
    (F : MvPolynomial (L × Fin r) K) : MvPolynomial (L × Fin r) K :=
  ∑ α ∈ F.support, if eOut out α = μ then monomial (eIn out α) (F.coeff α) else 0
end Formalism.MainNotions.PlaneGram


