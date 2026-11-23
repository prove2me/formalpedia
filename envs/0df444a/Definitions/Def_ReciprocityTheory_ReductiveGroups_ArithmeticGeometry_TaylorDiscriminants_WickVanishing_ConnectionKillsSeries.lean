-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:36.088039+00:00
-- url     : https://prove2.me/theorems/eb9ab49e-11bc-4206-a90d-adac840c1d5b
-- title:
--   Connection Kills Series
-- statement:
--   Definitions and structural lemmas for Connection Kills Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ConnectionKillsSeries.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
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
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
section VF
variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]
def vf (c : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) : MvPowerSeries τ k := ∑ t, c t * pderiv k t G
end VF
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
theorem liftX_hs : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
def liftHom : PS k 1 d →+* AA k d := (substAlgHom (liftX_hs (d := d) k)).toRingHom
def cf (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) : Fin d ⊕ Fin d → AA k d :=
  Sum.elim (fun j => liftX k (∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (B.FK k j))))
    (fun i => liftX k (Dof (B.FK k) u (sgOf k h i)) + C (φ i))
def fm (h : PS k 2 d) (u : Fin d → k) : AA k d := ∑ i : Fin d, (X (Sum.inr i) - liftX k (sgOf k h i)) * C (u i)
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab


