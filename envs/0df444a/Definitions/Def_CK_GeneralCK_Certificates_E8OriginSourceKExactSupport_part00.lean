-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part00
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T03:49:45.293985+00:00
-- url     : https://prove2.me/theorems/6dc942fd-86da-4b48-895e-d580c23e2806
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 1 of 3)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactSupport (part 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactSupport (part 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactReplay

namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

def kSupport : Finset (Nat × Nat) :=
  ((Finset.range 28).product (Finset.range 28)).filter
    (fun e => 1 ≤ e.1 + e.2 ∧ e.1 + e.2 ≤ 27 ∧ (e.1 + e.2) % 2 = 1)

theorem coeffAt_degree_1 (i j : Nat) (h : i + j = 1) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 1 := by omega
  interval_cases i
  · have hj : j = 1 := by omega
    subst j
    exact coeff_0_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_1_0

theorem coeffAt_degree_3 (i j : Nat) (h : i + j = 3) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 3 := by omega
  interval_cases i
  · have hj : j = 3 := by omega
    subst j
    exact coeff_0_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_1_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_2_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_3_0

theorem coeffAt_degree_5 (i j : Nat) (h : i + j = 5) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 5 := by omega
  interval_cases i
  · have hj : j = 5 := by omega
    subst j
    exact coeff_0_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_1_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_2_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_3_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_4_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_5_0

theorem coeffAt_degree_7 (i j : Nat) (h : i + j = 7) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 7 := by omega
  interval_cases i
  · have hj : j = 7 := by omega
    subst j
    exact coeff_0_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_1_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_2_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_3_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_4_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_5_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_6_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_7_0

theorem coeffAt_degree_9 (i j : Nat) (h : i + j = 9) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 9 := by omega
  interval_cases i
  · have hj : j = 9 := by omega
    subst j
    exact coeff_0_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_1_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_2_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_3_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_4_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_5_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_6_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_7_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_8_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_9_0

theorem coeffAt_degree_11 (i j : Nat) (h : i + j = 11) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 11 := by omega
  interval_cases i
  · have hj : j = 11 := by omega
    subst j
    exact coeff_0_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_1_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_2_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_3_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_4_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_5_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_6_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_7_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_8_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_9_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_10_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_11_0

theorem coeffAt_degree_13 (i j : Nat) (h : i + j = 13) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 13 := by omega
  interval_cases i
  · have hj : j = 13 := by omega
    subst j
    exact coeff_0_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_1_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_2_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_3_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_4_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_5_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_6_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_7_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_8_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_9_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_10_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_11_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_12_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_13_0

theorem coeffAt_degree_15 (i j : Nat) (h : i + j = 15) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 15 := by omega
  interval_cases i
  · have hj : j = 15 := by omega
    subst j
    exact coeff_0_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_1_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_2_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_3_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_4_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_5_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_6_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_7_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_8_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_9_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_10_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_11_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_12_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_13_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_14_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_15_0

theorem coeffAt_degree_17 (i j : Nat) (h : i + j = 17) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 17 := by omega
  interval_cases i
  · have hj : j = 17 := by omega
    subst j
    exact coeff_0_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_1_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_2_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_3_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_4_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_5_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_6_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_7_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_8_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_9_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_10_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_11_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_12_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_13_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_14_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_15_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_16_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_17_0

theorem coeffAt_degree_19 (i j : Nat) (h : i + j = 19) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 19 := by omega
  interval_cases i
  · have hj : j = 19 := by omega
    subst j
    exact coeff_0_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_1_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_2_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_3_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_4_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_5_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_6_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_7_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_8_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_9_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_10_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_11_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_12_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_13_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_14_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_15_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_16_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_17_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_18_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_19_0

theorem coeffAt_degree_21 (i j : Nat) (h : i + j = 21) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 21 := by omega
  interval_cases i
  · have hj : j = 21 := by omega
    subst j
    exact coeff_0_21
  · have hj : j = 20 := by omega
    subst j
    exact coeff_1_20
  · have hj : j = 19 := by omega
    subst j
    exact coeff_2_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_3_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_4_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_5_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_6_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_7_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_8_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_9_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_10_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_11_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_12_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_13_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_14_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_15_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_16_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_17_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_18_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_19_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_20_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_21_0

theorem coeffAt_degree_23 (i j : Nat) (h : i + j = 23) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 23 := by omega
  interval_cases i
  · have hj : j = 23 := by omega
    subst j
    exact coeff_0_23
  · have hj : j = 22 := by omega
    subst j
    exact coeff_1_22
  · have hj : j = 21 := by omega
    subst j
    exact coeff_2_21
  · have hj : j = 20 := by omega
    subst j
    exact coeff_3_20
  · have hj : j = 19 := by omega
    subst j
    exact coeff_4_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_5_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_6_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_7_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_8_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_9_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_10_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_11_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_12_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_13_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_14_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_15_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_16_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_17_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_18_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_19_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_20_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_21_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_22_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_23_0


end GeneralCK.Certificates.E8OriginSourceKExactReplay


