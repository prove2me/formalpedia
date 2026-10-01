-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part01_q00
-- name    : CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part01_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:56:18.680015+00:00
-- url     : https://prove2.me/theorems/710effc5-56a6-4e3f-b8de-5e33f4cfccc9
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 1 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 1 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 1 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8OriginSourceKExactSupport (part 2 of 3) (piece 1 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8OriginSourceKExactSupport (part 2 of 3) (piece 1 of 4).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8OriginSourceKExactSupport_part00


namespace GeneralCK.Certificates.E8OriginSourceKExactReplay

open E8OriginPolynomialLower
open E8ExactBivariatePolynomial
open E8OriginSourceKProducts
open E8OriginSourceKCoefficientReplay

set_option maxRecDepth 100000

theorem coeffAt_degree_25 (i j : Nat) (h : i + j = 25) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 25 := by omega
  interval_cases i
  · have hj : j = 25 := by omega
    subst j
    exact coeff_0_25
  · have hj : j = 24 := by omega
    subst j
    exact coeff_1_24
  · have hj : j = 23 := by omega
    subst j
    exact coeff_2_23
  · have hj : j = 22 := by omega
    subst j
    exact coeff_3_22
  · have hj : j = 21 := by omega
    subst j
    exact coeff_4_21
  · have hj : j = 20 := by omega
    subst j
    exact coeff_5_20
  · have hj : j = 19 := by omega
    subst j
    exact coeff_6_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_7_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_8_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_9_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_10_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_11_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_12_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_13_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_14_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_15_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_16_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_17_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_18_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_19_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_20_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_21_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_22_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_23_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_24_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_25_0

theorem coeffAt_degree_27 (i j : Nat) (h : i + j = 27) :
    coeffAt productData i j = coeffAt kData i j := by
  have hi : i ≤ 27 := by omega
  interval_cases i
  · have hj : j = 27 := by omega
    subst j
    exact coeff_0_27
  · have hj : j = 26 := by omega
    subst j
    exact coeff_1_26
  · have hj : j = 25 := by omega
    subst j
    exact coeff_2_25
  · have hj : j = 24 := by omega
    subst j
    exact coeff_3_24
  · have hj : j = 23 := by omega
    subst j
    exact coeff_4_23
  · have hj : j = 22 := by omega
    subst j
    exact coeff_5_22
  · have hj : j = 21 := by omega
    subst j
    exact coeff_6_21
  · have hj : j = 20 := by omega
    subst j
    exact coeff_7_20
  · have hj : j = 19 := by omega
    subst j
    exact coeff_8_19
  · have hj : j = 18 := by omega
    subst j
    exact coeff_9_18
  · have hj : j = 17 := by omega
    subst j
    exact coeff_10_17
  · have hj : j = 16 := by omega
    subst j
    exact coeff_11_16
  · have hj : j = 15 := by omega
    subst j
    exact coeff_12_15
  · have hj : j = 14 := by omega
    subst j
    exact coeff_13_14
  · have hj : j = 13 := by omega
    subst j
    exact coeff_14_13
  · have hj : j = 12 := by omega
    subst j
    exact coeff_15_12
  · have hj : j = 11 := by omega
    subst j
    exact coeff_16_11
  · have hj : j = 10 := by omega
    subst j
    exact coeff_17_10
  · have hj : j = 9 := by omega
    subst j
    exact coeff_18_9
  · have hj : j = 8 := by omega
    subst j
    exact coeff_19_8
  · have hj : j = 7 := by omega
    subst j
    exact coeff_20_7
  · have hj : j = 6 := by omega
    subst j
    exact coeff_21_6
  · have hj : j = 5 := by omega
    subst j
    exact coeff_22_5
  · have hj : j = 4 := by omega
    subst j
    exact coeff_23_4
  · have hj : j = 3 := by omega
    subst j
    exact coeff_24_3
  · have hj : j = 2 := by omega
    subst j
    exact coeff_25_2
  · have hj : j = 1 := by omega
    subst j
    exact coeff_26_1
  · have hj : j = 0 := by omega
    subst j
    exact coeff_27_0

theorem coeffAt_productData_eq_kData_on_support
    (e : Nat × Nat) (he : e ∈ kSupport) :
    coeffAt productData e.1 e.2 = coeffAt kData e.1 e.2 := by
  rcases e with ⟨i, j⟩
  simp [kSupport] at he
  have hd : i + j = 1 ∨ i + j = 3 ∨ i + j = 5 ∨ i + j = 7 ∨
      i + j = 9 ∨ i + j = 11 ∨ i + j = 13 ∨ i + j = 15 ∨
      i + j = 17 ∨ i + j = 19 ∨ i + j = 21 ∨ i + j = 23 ∨
      i + j = 25 ∨ i + j = 27 := by omega
  rcases hd with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact coeffAt_degree_1 i j h
  · exact coeffAt_degree_3 i j h
  · exact coeffAt_degree_5 i j h
  · exact coeffAt_degree_7 i j h
  · exact coeffAt_degree_9 i j h
  · exact coeffAt_degree_11 i j h
  · exact coeffAt_degree_13 i j h
  · exact coeffAt_degree_15 i j h
  · exact coeffAt_degree_17 i j h
  · exact coeffAt_degree_19 i j h
  · exact coeffAt_degree_21 i j h
  · exact coeffAt_degree_23 i j h
  · exact coeffAt_degree_25 i j h
  · exact coeffAt_degree_27 i j h

theorem p0Data_mem_kSupport (r : Term)
    (hr : r ∈ E8OriginSourceKProducts.p0Data) : (r.i, r.j) ∈ kSupport := by
  simp only [E8OriginSourceKProducts.p0Data, List.mem_cons, List.not_mem_nil,
    or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]
  · norm_num [kSupport]

end GeneralCK.Certificates.E8OriginSourceKExactReplay


