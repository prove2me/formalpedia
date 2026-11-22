-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:04.755019+00:00
-- url     : https://prove2.me/theorems/43e5dec5-ea27-47fd-8572-d9deacb1289d
-- title:
--   Ddiv On Letter Monomial
-- statement:
--   Definitions and structural lemmas for Ddiv On Letter Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/DdivOnLetterMonomial.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

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
section Gen
variable {σ : Type} [Fintype σ]
def bin (M α : σ →₀ ℕ) : K := ∏ x, ((α x).choose (M x) : K)
end Gen
section Letter
variable {L : Type} [DecidableEq L] {r : ℕ}
def letE (α : L × Fin r →₀ ℕ) (i : L) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => α (i, a)
def offE (i : L) (α : L × Fin r →₀ ℕ) : L × Fin r →₀ ℕ := α.filter fun x => x.1 ≠ i
end Letter
section Der
variable [CharZero K] (v : AddValuation K (WithTop ℚ)) (p : ℕ)
def divE {r : ℕ} (P : ℕ) (η : Fin r →₀ ℕ) : Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => η a / P
end Der
section App
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ}
def putL (i : L) (α : L × Fin r →₀ ℕ) : MvPolynomial (Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K :=
  (LinearMap.mulLeft K (monomial (offE i α) (1 : K))).comp (rename fun a : Fin r => (i, a)).toLinearMap
variable {I : Type} [Fintype I]
def appMon (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ))
    (α : L × Fin r →₀ ℕ) : MvPolynomial (L × Fin r) K :=
  ∑ s, if cls s = (fun a => α (i, a) % P) then
    monomial (offE i α + onLetter i (ρ' s + P • (δ s + (divE P (letE α i) - κ s))))
      (cf s * bin (κ s) (divE P (letE α i))) else 0
end App
section AppL
variable {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} {I : Type} [Fintype I]
def appL (i : L) (P : ℕ) (cls : I → Fin r → ℕ) (cf : I → K) (ρ' δ κ : I → (Fin r →₀ ℕ)) :
    MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K :=
  lsup (appMon i P cls cf ρ' δ κ)
end AppL
namespace TwistData
variable (D : TwistData K) (p : ℕ)
def emb (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) : D.EA :=
  Finsupp.equivFunOnFinite.symm fun x => Sum.elim (fun b => ζ (D.mb b, x.2))
    (fun t => ρ t x.2 + D.P p t * ζ (D.mw t, x.2)) x.1
variable (t : D.Tau)
def opS (μ κ1 : Fin D.r →₀ ℕ) (c1 : K) :
    MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K :=
  c1 • ((LinearMap.mulLeft K (monomial (onLetter (D.mw t) μ) (1 : K))).comp
    (ddivL (onLetter (D.mw t) κ1)))
end TwistData
end Formalism.MainNotions.PlaneGram


