-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:32:28.667906+00:00
-- url     : https://prove2.me/theorems/25f3169a-b588-4553-a1ae-f3cb85f4c6b3
-- title:
--   GEWick
-- statement:
--   Definitions and structural lemmas for GEWick, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GEWick.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
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
namespace ReciprocityTheory.ChartRestriction.G.TB.GE
def HalfSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
    (u : ι → Fin d → k) (c : ι → ι → k) (q : PS k 1 d),
    (∀ l l', c l l' = c l' l) → constantCoeff q = 0 → (∀ l, constantCoeff (Dof F (u l) q) = 0) →
    (∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l')) →
    ∀ (P : MvPolynomial ι k) (A : PS k 1 d),
      constantCoeff (DpolyOf F u P (A * q)) =
        algebraMap ℚ k (1 / 2) * constantCoeff (DpolyOf F u (secondOrder k c P) A)
variable {k : Type} [CommRing k] {d : ℕ}
section lin
variable (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k)
end lin
section deg
variable {ι : Type} [Fintype ι]
def DegLt (n : ℕ) (P : MvPolynomial ι k) : Prop := ∀ m : ι →₀ ℕ, n ≤ m.degree → MvPolynomial.coeff m P = 0
end deg
section wick
variable [Algebra ℚ k]
end wick
end ReciprocityTheory.ChartRestriction.G.TB.GE


