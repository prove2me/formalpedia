-- Prove2me | Definitions.Def_InverseGalois_regular_action
-- name    : InverseGalois_regular_action
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-14T01:32:08.888867+00:00
-- url     : https://prove2.me/theorems/647b760b-774f-4cdb-b31f-ac476bd2b93b
-- title:
--   Regular permutation action on a rational-function field
-- statement:
--   Let $G$ act on an index set $I$. This interface equips the polynomial ring $R[X_i : i ∈ I]$ with the induced action obtained by permuting variables, $g · X_i = X_{g · i}$. For a finite group $G$, it also names the polynomial ring over $ℚ$ indexed by the regular $G$-set and its field of fractions.
--
--   These definitions provide the reusable ambient field for the regular-representation construction in inverse Galois theory.
--
--   **Formalization Note** The regular index type is replaced by its universe-zero `Shrink`, allowing the resulting fraction field to live in the same universe as subfields of $ℂ$.
-- source:
--   Mathlib, MvPolynomial.rename, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/MvPolynomial/Rename.lean#L54-L83; Cayley's theorem (regular action), https://en.wikipedia.org/wiki/Cayley%27s_theorem

import Mathlib

set_option autoImplicit false

noncomputable section

namespace InverseGalois

universe u

/-- The action on a multivariable polynomial ring induced by permuting its variables. -/
def mvPolynomialMulSemiringAction (G I R : Type*) [Group G] [CommRing R]
    [MulAction G I] : MulSemiringAction G (MvPolynomial I R) where
  smul g p := MvPolynomial.rename (g • ·) p
  one_smul p := by
    change MvPolynomial.rename ((1 : G) • ·) p = p
    rw [show ((1 : G) • ·) = id by funext i; exact one_smul G i]
    exact MvPolynomial.rename_id_apply p
  mul_smul g h p := by
    change MvPolynomial.rename ((g * h) • ·) p =
      MvPolynomial.rename (g • ·) (MvPolynomial.rename (h • ·) p)
    rw [MvPolynomial.rename_rename]
    congr
    funext i
    exact mul_smul g h i
  smul_zero g := map_zero _
  smul_add g p q := map_add _ _ _
  smul_one g := map_one _
  smul_mul g p q := map_mul _ _ _

/-- A rational polynomial ring whose variables are indexed by the regular `G`-set. -/
abbrev RegularPolynomialRing (G : Type u) [Fintype G] :=
  MvPolynomial (Shrink.{0} G) ℚ

/-- The rational-function field of the regular `G`-set. -/
abbrev RegularFractionField (G : Type u) [Fintype G] :=
  FractionRing (RegularPolynomialRing G)

end InverseGalois


