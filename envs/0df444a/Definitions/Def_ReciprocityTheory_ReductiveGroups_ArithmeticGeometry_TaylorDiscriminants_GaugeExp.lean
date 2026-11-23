-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:36.872349+00:00
-- url     : https://prove2.me/theorems/dadcef14-54ff-44c7-9cae-c9b593dcf4d6
-- title:
--   Gauge Exp
-- statement:
--   Definitions and structural lemmas for Gauge Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/GaugeExp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB
def expSecond (k : Type) [CommRing k] [Algebra ℚ k] {ι : Type} [Fintype ι] (c : ι → ι → k) (t : k) (N : ℕ)
    (Q : MvPolynomial ι k) : MvPolynomial ι k :=
  ∑ i ∈ Finset.range (N + 1), (t ^ i * algebraMap ℚ k (1 / (Nat.factorial i : ℚ))) • (secondOrder k c)^[i] Q
def GaugeExpSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k]
    [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' →
    ∀ (w0 : O) (m : ℕ) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (Q : MvPolynomial ι k) (f : PS k 1 d),
      B.nabVal k h' w0 m f u Q =
        B.nabVal k h w0 m f u (expSecond k (fun l l' =>
          dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
          dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))))
          ((m : k) * algebraMap ℚ k (1 / 2)) Q.totalDegree Q)
end ReciprocityTheory.ChartRestriction.G.TB


