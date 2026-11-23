-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:14.9984+00:00
-- url     : https://prove2.me/theorems/c607baf2-a495-491e-b28f-bd8d10f061f1
-- title:
--   Fourier Coeff Int St
-- statement:
--   Definitions and structural lemmas for Fourier Coeff Int St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/FourierCoeffIntSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
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
def FourierInvSt : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (K : Type) [Field K] [Fintype (AddChar A K)],
    ((Fintype.card A : K) ≠ 0) → Fintype.card (AddChar A K) = Fintype.card A →
    ∀ φ : A → K, ∀ a,
      φ a = ∑ χ : AddChar A K, ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) * χ a
def FourierCoeffIntSt : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Fintype A] (K : Type) [Field K] (O : Subring K) (φ : A → K),
    (∀ a, φ a ∈ O) → ∀ χ : AddChar A K, (∀ a, χ a ∈ O) →
      (Fintype.card A : K) * ((Fintype.card A : K)⁻¹ * ∑ b, φ b * χ (-b)) ∈ O ∨ (Fintype.card A : K) = 0
def mulN {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) : ℕ → Pt R 1 d
  | 0 => 0
  | n + 1 => G.add (mulN G n) (pt R d 0)
def NChainSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (n : ℕ) {ι : Type} [Fintype ι] (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (k : ℕ), P.IsHomogeneous k → ∀ f : PS R 1 d,
      constantCoeff (DpolyOf G.F u P (ev ![mulN G n] f)) = (n : R) ^ k * constantCoeff (DpolyOf G.F u P f)
end ReciprocityTheory.ChartRestriction.G.TB


