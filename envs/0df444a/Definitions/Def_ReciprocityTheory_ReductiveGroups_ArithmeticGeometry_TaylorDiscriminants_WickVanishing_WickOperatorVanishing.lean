-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:42.608803+00:00
-- url     : https://prove2.me/theorems/d46499ab-510e-4146-bfa3-ce1786cc23be
-- title:
--   Wick Operator Vanishing
-- statement:
--   Definitions and structural lemmas for Wick Operator Vanishing, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/WickOperatorVanishing.lean

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
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
def ExpAddZeroConstant : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d : ℕ) (f g : PS k n d), constantCoeff f = 0 →
    constantCoeff g = 0 → FB.expS k (f + g) = FB.expS k f * FB.expS k g
def ConstantCoeffSubstitution : Prop :=
  ∀ (k : Type) [CommRing k] (d m n : ℕ) (a : Fin m → Pt k n d) (f : PS k m d),
    (∀ j i, constantCoeff (a j i) = 0) → constantCoeff (ev a f) = constantCoeff f
def IsBiadd {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (g : PS k 2 d) : Prop :=
  ev (n := 1) ![0, pt k d 0] g = 0 ∧ ev (n := 1) ![pt k d 0, 0] g = 0 ∧
    ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] g ∧
    ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] g ∧
    ∀ a : O, ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] g =
      ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] g
def CanonicalGaugeDiffBiadditive : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d),
    B.IsCanonGauge k h → B.IsCanonGauge k h' → IsBiadd B k (h' - h)
def QuadraticFormDerivatives : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) (g : PS k 2 d), IsBiadd B k g → ∀ w0 : O,
    constantCoeff (ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] g) = 0 ∧
    (∀ u, constantCoeff (Dof (B.FK k) u (ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] g)) = 0) ∧
    ∀ u v, Dof (B.FK k) u (Dof (B.FK k) v (ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] g)) =
      C (dotProduct u ((bilinPart k g).mulVec ((dAct k B w0).mulVec v)) +
        dotProduct v ((bilinPart k g).mulVec ((dAct k B w0).mulVec u)))
def WickOperatorVanishing : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
    (u : ι → Fin d → k) (c : ι → ι → k) (P : MvPolynomial ι k) (q : PS k 1 d),
    (∀ l l', c l l' = c l' l) → constantCoeff q = 0 → (∀ l, constantCoeff (Dof F (u l) q) = 0) →
    (∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l')) → secondOrder k c P = 0 →
    ∀ (m : k) (G : PS k 1 d),
      constantCoeff (DpolyOf F u P (G * FB.expS k (m • q))) = constantCoeff (DpolyOf F u P G)
end ReciprocityTheory.ChartRestriction.G.TB.G2


