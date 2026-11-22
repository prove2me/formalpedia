-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:35:52.485243+00:00
-- url     : https://prove2.me/theorems/a9a13a6e-dcaf-4ec2-99bd-d2171c9bce1f
-- title:
--   Omega Injective Holds
-- statement:
--   Definitions and structural lemmas for Omega Injective Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply


set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section Comp
variable {k σ : Type} [Field k]
noncomputable def compL (k : Type) [Field k] {σ : Type} (Pr : (σ →₀ ℕ) → Prop) :
    MvPolynomial σ k →ₗ[k] MvPolynomial σ k where
  toFun := compP Pr
  map_add' x y := by
    classical
    ext m
    simp only [coeff_compP, coeff_add]
    split_ifs <;> simp
  map_smul' c x := by
    classical
    ext m
    simp only [coeff_compP, coeff_smul, RingHom.id_apply]
    split_ifs <;> simp
end Comp
section WW
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
def wp (K : ℕ) {r : ℕ} (m : Fin (K + 1) × Fin r →₀ ℕ) : Fin r → ℤ := fun a => (m (Fin.last K, a) : ℤ)
noncomputable def cw (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (γ : Fin r → ℤ) :
    MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] :=
  compL ℚ_[p] (fun m => wp K m = γ)
def phiW {r : ℕ} (γ : Fin r → ℤ) : ℤ := ∑ c : Fin r, ((c : ℕ) : ℤ) * γ c
end WW
section HW
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
noncomputable def WS (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (γ : Fin r → ℤ) :
    Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  restrictSupport ℚ_[p] {m | wp K m = γ}
noncomputable def eW (p : ℕ) [Fact p.Prime] (K : ℕ) {r : ℕ} (s t : Fin r) :
    Module.End ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
  (LinearMap.mulLeft ℚ_[p] (X (Fin.last K, s))) ∘ₗ (pderiv (Fin.last K, t)).toLinearMap
def shiftN {r : ℕ} (γ : Fin r → ℤ) (c d : Fin r) (i : ℤ) : Fin r → ℤ :=
  fun c' => γ c' + (if c = c' then i else 0) - (if d = c' then i else 0)
variable (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r)) (th : Fin r → ℤ)
  (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ HWC p LL (K + 1) Cs th)
end HW
section Strip
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
end Strip
section OmegaTop
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
def Enum {r : ℕ} (ρ : Fin r) (c : ℤ) (o : ℕ) (th β : Fin r → ℤ) : ℤ :=
  (c - o) * (o + 1) - ∑ a ∈ univ.erase ρ, ∑ b ∈ univ.erase ρ,
    ((if a = b then β a * (th a - β a) else 0) - (if a < b then (β a + 1) * β b else 0))
end OmegaTop
section Arith
end Arith
section Final
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
end Final
end Formalism.InvariantFactorPaths.L4


