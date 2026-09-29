-- Prove2me | Definitions.Def_mme_dwz_table2_integer_counts
-- name    : mme_dwz_table2_integer_counts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T11:56:34.578197+00:00
-- url     : https://prove2.me/theorems/c2c8e869-e03c-43ae-babe-cd16802ee9a9
-- title:
--   DWZ Table 2: exact integral histograms at scale 10^16
-- statement:
--   Encode every terminating-decimal weight in DWZ Table 2 at the common exact scale 10^16. The module records the 15 component counts, all 45 Z-split counts, the Definition 6.4 3 by 3 typical-pair histogram gamma, the Z marginal, and the interior (+,+,k) masses and split numerators. These natural-valued histograms are the integral data needed to instantiate exact multinomial counts and entropy estimates for Equation (23); no asymptotic or tensor-value assertion is included.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 6.4, Lemma 6.7, Section 6.3 and Table 2 (printed pp. 54-59 / PDF pp. 55-60).

import Mathlib

open BigOperators Finset

set_option autoImplicit false

namespace MME.DWZTable2Counts

/-- A common integral scale for every Table-2 component/split product. -/
def scale : ℕ := 10000000000000000

/-- The fifteen component counts at `scale = 10^16`. -/
def component : Fin 15 → ℕ :=
  ![2086000000000, 2473100000000, 2473100000000,
    121115300000000, 133331800000000, 121115300000000,
    125175800000000, 133331800000000, 125175800000000,
    1036694500000000, 1036694500000000, 1004579100000000,
    2008862300000000, 2073445800000000, 2073445800000000]

/-- Exact left/right split counts of every component at scale `10^16`. -/
def split : Fin 15 → Fin 3 → ℕ :=
  ![![0, 0, 2086000000000],
    ![2473100000000, 0, 0],
    ![2473100000000, 0, 0],
    ![0, 60557650000000, 60557650000000],
    ![66665900000000, 66665900000000, 0],
    ![0, 60557650000000, 60557650000000],
    ![125175800000000, 0, 0],
    ![66665900000000, 66665900000000, 0],
    ![125175800000000, 0, 0],
    ![36050045643835, 964594408712330, 36050045643835],
    ![36050045643835, 964594408712330, 36050045643835],
    ![1004579100000000, 0, 0],
    ![422162412345, 2008017975175310, 422162412345],
    ![1036722900000000, 1036722900000000, 0],
    ![1036722900000000, 1036722900000000, 0]]

/-- Exact typical pair histogram `gamma` at scale `10^16`. -/
def gamma : Fin 3 × Fin 3 → ℕ := fun p =>
  (![![1259876900000000, 2206777600000000, 72522253700015],
      ![2206777600000000, 3937206792599970, 121115300000000],
      ![72522253700015, 121115300000000, 2086000000000]] p.1) p.2

/-- Exact Z-marginal histogram at scale `10^16`. -/
def alphaZ : Fin 5 → ℕ :=
  ![1259876900000000, 4413555200000000, 4082251300000000,
    242230600000000, 2086000000000]

/-- Exact interior masses `alpha(+,+,k)` at scale `10^16`. -/
def plusMass : Fin 5 → ℕ :=
  ![1254930700000000, 4146891600000000, 2008862300000000, 0, 0]

/-- Interior `(+,+,k)` split counts at scale `10^16`. -/
def plusSplit : Fin 5 → Fin 3 → ℕ :=
  ![![1254930700000000, 0, 0],
    ![2073445800000000, 2073445800000000, 0],
    ![422162412345, 2008017975175310, 422162412345],
    ![0, 0, 0],
    ![0, 0, 0]]

end MME.DWZTable2Counts


