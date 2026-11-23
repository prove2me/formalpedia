-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_KillAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:49.893792+00:00
-- url     : https://prove2.me/theorems/2c4fa203-a929-4941-a533-a0a01b3e58cc
-- title:
--   Kill Add
-- statement:
--   Definitions and structural lemmas for Kill Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/KillAdd.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
variable {k : Type} [CommRing k] {d n : ℕ}
def dAdd (u : Fin d → k) (b : Fin n) (G : PS k n d) : PS k n d :=
  ∑ j : Fin d, C (u j) * pderiv k (b, j) G
def polyAdd {ι : Type} [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial (ι × Fin n) k) (G : PS k n d) :
    PS k n d :=
  ∑ m ∈ P.support, C (P.coeff m) *
    (Finset.univ : Finset (ι × Fin n)).toList.foldr (fun p g => (dAdd (u p.1) p.2)^[m p] g) G
def quadCol (β : Matrix (Fin d) (Fin d) k) : PS k n d :=
  ∑ b : Fin n, ∑ i : Fin d, ∑ j : Fin d, C (β i j) * X (b, i) * X (b, j)
def KillAddSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d n : ℕ) (ι : Type) [Fintype ι] (u : ι → Fin d → k)
    (β : Matrix (Fin d) (Fin d) k) (P : MvPolynomial (ι × Fin n) k),
    secondOrder k (fun p p' : ι × Fin n => if p.2 = p'.2 then
      dotProduct (u p.1) (β.mulVec (u p'.1)) + dotProduct (u p'.1) (β.mulVec (u p.1)) else 0) P = 0 →
    ∀ (m : k) (g : PS k n d),
      constantCoeff (polyAdd u P (FB.expS k (m • quadCol (n := n) β) * g)) = constantCoeff (polyAdd u P g)
end ReciprocityTheory.ChartRestriction.G.TB


