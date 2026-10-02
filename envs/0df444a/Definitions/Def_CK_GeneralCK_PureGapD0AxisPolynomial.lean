-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapD0AxisPolynomial
-- name    : CK_GeneralCK_PureGapD0AxisPolynomial
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T13:50:28.261022+00:00
-- url     : https://prove2.me/theorems/d95a034c-fa34-41f0-bdf7-04fc28c1c89b
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapD0AxisPolynomial` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapD0AxisPolynomial` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapD0AxisPolynomial` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapD0AxisPolynomial (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapD0AxisPolynomial.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginMixedKTransfer
import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceAffineReplay

-- ===== source module GeneralCK.PureGapD0AxisPolynomial =====
section

/-! Exact univariate axis replay, independent of the large bivariate degree
artifacts. The coefficient list is only data until `axis_identity` checks it. -/

namespace GeneralCK.PureGapD0AxisPolynomial
open Certificates E8OriginMixedKTransfer E8OriginRealTaylorTransfer
open E8OriginSourceAffineReplay E8OriginPolynomialLower E8ExactBivariatePolynomial

set_option maxRecDepth 100000

def leading : Rat := (3068881884948072461420067386932946870117693837373840078545780403397683571134819300051503608390385241 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat)
def rest : List Term := [
  { i := 27, j := 0, c := (1915849794948166641592525894038280341873742864295816034016082547669695490633604264059674655272375478129 / 6103515625000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 25, j := 0, c := (-116897112397721914904800224937833681386538537708089108502400828152685197720120451302799561608362801529873 / 2441406250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 23, j := 0, c := (233776130595463355797969815491527485627833422503799547831182104327094110363744318874551853653176637723 / 976562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 21, j := 0, c := (2484123372955067513723633628326811920421553301697228773663048324496752222227516861539357774378870501773403 / 39062500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 19, j := 0, c := (251733824161524772005354449884598307754999622726657519799134789668702137398688251690531454827245291911999 / 156250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 17, j := 0, c := (-48611409069801801302129622765676559655317530172371038790189667556815797223442599008502471176103241204327 / 12500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 15, j := 0, c := (-2115170481324258172615100927041340942710743541084111990505788115814881196366067903297199100829316447612559 / 1562500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 13, j := 0, c := (-1876823299026025166222904657720314946914547369034465909213729927887894976974645223712569356078533395200069 / 25000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 11, j := 0, c := (978254110210819513708259474695752357357120192386317616277905568449529038864292875568014982793104665023209 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 9, j := 0, c := (21379827983131797838664378543175681457639844398479863293908947629985847615905858890241408578878217326159 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 7, j := 0, c := (76304012879169501347740649017079131569435365109277338885373203613902519808153432756063310972508586973391 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) },
  { i := 5, j := 0, c := (1378934042220376757964687775136994034184000079814415585470792614367878901674163981373545505169317461419 / 6250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : Rat) }
]

set_option maxHeartbeats 1500000 in
theorem axis_identity (s : ℝ) :
    sourceKFormula s 0 = (leading : ℝ) * s ^ 3 + evalTerms rest s 0 := by
  simp only [sourceKFormula, add_zero, qSource_0_horner, qSource_1_horner,
    qSource_2_horner, qSource_3_horner]
  norm_num (config := { maxSteps := 1000000 })
    [qCoeffs0, qCoeffs1, qCoeffs2, qCoeffs3, leading, rest, evalTerms, evalTerm]
  ring

theorem polynomial_lower {s : ℝ} (hs : 0 ≤ s) (hR : s ≤ (2 / 25 : ℝ)) :
    (3 / 10000 : ℝ) * s ^ 3 ≤ sourceKFormula s 0 := by
  have hp := evalTerms_nonneg (xs := nonnegativePart rest) hs (le_refl 0)
    (coefficientsNonnegative_sound (by norm_num [coefficientsNonnegative, nonnegativePart, rest]))
  have hn := evalTerms_lower_negAggregate
    (xs := negativePart rest) hs (le_refl 0) (show s + 0 ≤ (2 / 25 : ℝ) by simpa using hR)
    (degreesAtLeastThree_sound (by norm_num [degreesAtLeastThree, negativePart, rest]))
    (coefficientsNonpositive_sound (by norm_num [coefficientsNonpositive, negativePart, rest]))
  have hag : (3 / 10000 : ℝ) ≤ (leading : ℝ) +
      negAggregate (2 / 25 : ℝ) (negativePart rest) := by
    norm_num [leading, negAggregate, negativePart, rest]
  have hparts := evalTerms_parts rest s 0
  rw [axis_identity]
  simp only [add_zero] at hn
  nlinarith [pow_nonneg hs 3]

#print axioms axis_identity
#print axioms polynomial_lower

end GeneralCK.PureGapD0AxisPolynomial

end


