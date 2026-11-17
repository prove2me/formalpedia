-- Prove2me | Definitions.Def_N25_CanonicalModularDictionaryGoodCharacteristic
-- name    : N25_CanonicalModularDictionaryGoodCharacteristic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:18:02.283275+00:00
-- url     : https://prove2.me/theorems/67f0f41a-3f9e-4d27-850a-c42a38b1f98d
-- title:
--   The canonical–modular dictionary in characteristics two and three
-- statement:
--   For $p∈\{2,3\}$ and any field $K$ of characteristic $p$, the file defines a $K$-algebra equivalence between the canonical function field and the modular function field by evaluating the plane coordinates at the prescribed modular units. It also names the prime-field specializations over $𝔽_2$, $𝔽_3$, and uniformly over $𝔽_p$. These equivalences transfer finite-field point and place counts between the explicit canonical model and the modular curve.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CanonicalFunctionFieldOverField
import Theorems.Thm_N25_Endgame_unitPlaneToXHGood25_surjective
import Definitions.Def_N25_UnitPlaneModularMapGoodCharacteristic
import Definitions.Def_N25_UnitPlaneFieldPointLiftOverField
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
/-! The coordinate-preserving canonical-to-modular dictionary in good characteristic. -/
noncomputable section
namespace N25.Endgame

/-- The canonical and modular function fields are identified by evaluation at the prescribed units. -/
def canonicalXHGoodCharAlgEquiv25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    N25.CanonicalFF25 K ≃ₐ[K] FBase K :=
  (N25.canonicalUnitPlaneAlgEquiv25C K).symm.trans
    (AlgEquiv.ofBijective (unitPlaneToXHGood25 p hp K)
      ⟨(unitPlaneToXHGood25 p hp K).injective, unitPlaneToXHGood25_surjective p hp K⟩)

/-- The specified dictionary over the prime coefficient field. -/
def canonicalXHGoodPrimeAlgEquiv25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) :
    N25.CanonicalFF25 (ZMod p) ≃ₐ[ZMod p] FBase (ZMod p) :=
  canonicalXHGoodCharAlgEquiv25 p hp (ZMod p)

end N25.Endgame

namespace N25

/-- The specified canonical-to-modular dictionary over the binary field. -/
def canonicalXHF2AlgEquiv25 :
    CanonicalFF25 (ZMod 2) ≃ₐ[ZMod 2] N25.Endgame.FBase (ZMod 2) :=
  N25.Endgame.canonicalXHGoodPrimeAlgEquiv25 2 (Or.inl rfl)

/-- The specified canonical-to-modular dictionary over the ternary field. -/
def canonicalXHF3AlgEquiv25 :
    CanonicalFF25 (ZMod 3) ≃ₐ[ZMod 3] N25.Endgame.FBase (ZMod 3) :=
  N25.Endgame.canonicalXHGoodPrimeAlgEquiv25 3 (Or.inr rfl)

/-- The prime-field dictionary for either of the two signed good primes. -/
def canonicalXHFpAlgEquiv25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) :
    CanonicalFF25 (ZMod p) ≃ₐ[ZMod p] N25.Endgame.FBase (ZMod p) :=
  N25.Endgame.canonicalXHGoodPrimeAlgEquiv25 p hp

end N25


