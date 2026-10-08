-- Prove2me | Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
-- name    : PhilipponMultiplicity_MixedFlagParameters
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-04T19:53:16.497853+00:00
-- url     : https://prove2.me/theorems/c43752e2-8825-4c70-9cb1-86f49f7a4383
-- title:
--   Coefficient matrices and prefix ideals of mixed linear flags
-- statement:
--   For a finite multiprojective space with coordinate ring $A$, a coefficient row $a$ and a selected block $i$ define the linear form $\sum_j a_{(i,j)}X_{ij}$. For an ordered list $l$ of blocks and a coefficient matrix $c$, write $P_j(c)$ for the corresponding block-linear form in row $j$. Given an ideal $I\subseteq A$, the prefix ideal at $k$ is $I+(P_j(c):j<k)$. All rows use the same coordinate-index set; entries outside the selected block are ignored. These are only parameter definitions, with linearity supplied by the linear-map constructor; no existence, avoidance, or smoothness theorem is asserted.
-- source:
--   Auxiliary notation for coefficient-space generic mixed flags. Philippon, Bull. SMF 114 (1986), pp.363–364, https://numdam.org/articles/10.24033/bsmf.2060/ ; Manh–Viet, arXiv:0901.3825v1, Definition 2.1 and Proposition 2.6, https://arxiv.org/pdf/0901.3825 .

import Definitions.Def_PhilipponMultiplicity_Geometry

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.MixedFlag
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Coefficients outside the selected coordinate block are unused. -/
def rowForm (i : M.FactorIndex) : (M.Variable → K) →ₗ[K] M.CoordinateRing where
  toFun a := ∑ j : Fin (M.ambientDimension i + 1),
    a ⟨i,j⟩ • MvPolynomial.X ⟨i,j⟩
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.smul_sum, smul_smul]

/-- The block-linear equation in a row of an ordered coefficient matrix. -/
def polynomial (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (j : Fin l.length) : M.CoordinateRing :=
  rowForm M l[j] (c j)

/-- The initial ideal together with the first k equations of a flag. -/
def ideal (I : Ideal M.CoordinateRing) (l : List M.FactorIndex)
    (c : Fin l.length → M.Variable → K) (k : ℕ) : Ideal M.CoordinateRing :=
  I ⊔ ⨆ (j : Fin l.length) (_ : j.val < k), Ideal.span {polynomial M l c j}

end PhilipponMultiplicity.MixedFlag


