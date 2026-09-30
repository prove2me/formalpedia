-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_SubgroupCoordinateCases
-- name    : WeierstrassEllipticZeta_SubgroupCoordinateCases
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-25T01:20:39.803104+00:00
-- url     : https://prove2.me/theorems/d3a5e6a9-7072-4664-ae77-3b159c4eca26
-- title:
--   Homogeneous equation sets for the subgroups in Lemma A.1
-- statement:
--   For a compatible Weierstrass model M and an algebraic subgroup H, having the equations of a parametrized locus means that a bihomogeneous polynomial vanishes on H exactly when it vanishes on every point of that locus. This compares projective closures through their actual homogeneous equations.
--
--   The paper subgroup types are the identity point, the extension factor {0} × G₂, the additive plane with coordinates ([1:t],[0:0:1:0:ρ+u]), and its nonconstant lines ([1:at],[0:0:1:0:ρ+bt]). The offset ρ permits an arbitrary vertical origin. These predicates contain no degree, dimension, curve-intersection bound, or multiplicity conclusion. They do not assert that any subgroup has one of the types; that classification is a separate theorem.
-- source:
--   Senthil Kumar, https://doi.org/10.1017/S001309152610145X, Appendix A, Lemma A.1 and the subgroup cases in Proposition A.1.

import Definitions.Def_WeierstrassEllipticZeta_PhilipponModel
import Definitions.Def_WeierstrassEllipticZeta_ProjectiveExtensionFiberModel

set_option autoImplicit false
noncomputable section

namespace WeierstrassEllipticZeta.PhilipponApplication
open PhilipponMultiplicity MvPolynomial

/-- A subgroup and a parametrized coordinate locus have exactly the same
bihomogeneous equations. This is an equality of projective closures, not an
assumption about Hilbert functions or multiplicity estimates. -/
def Model.HasParametricEquations {S : Fin 5 → ℂ → ℂ} (M : Model S)
    (H : AlgebraicSubgroup M.group) {T : Type*} (v : T → Fin 7 → ℂ) : Prop :=
  ∀ (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ), Bihomogeneous Q m n →
    ((∀ g ∈ H.carrier, M.group.ambient.eval (M.polynomial Q) (M.group.embedding g) = 0) ↔
      ∀ t, MvPolynomial.eval (v t) Q = 0)

/-- The point, extension factor, additive plane, and additive lines of the
paper's Lemma A.1, expressed through their homogeneous equations in a compatible
model. The free origin ρ allows the chosen homogeneous lift at the identity. -/
def Model.HasPaperSubgroupType (L : PeriodPair)
    {S : Fin 5 → ℂ → ℂ} (M : Model S) (H : AlgebraicSubgroup M.group) : Prop :=
  H.carrier = {0} ∨
    M.HasParametricEquations H
      (fun p : ProjectiveExtensionChartLocus L.g₂ L.g₃ =>
        ![1, 0, p.val.val.rep 0, p.val.val.rep 1, p.val.val.rep 2,
          p.val.val.rep 3, p.val.val.rep 4]) ∨
    (∃ ρ : ℂ, M.HasParametricEquations H
      (fun t : Fin 2 → ℂ => ![1, t 0, 0, 0, 1, 0, ρ + t 1])) ∨
    ∃ a b ρ : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ M.HasParametricEquations H
      (fun t : ℂ => ![1, a * t, 0, 0, 1, 0, ρ + b * t])

end WeierstrassEllipticZeta.PhilipponApplication


