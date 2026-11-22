-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:04:37.73615+00:00
-- url     : https://prove2.me/theorems/a907840e-d5f3-4b8a-be0f-bde571371cfe
-- title:
--   One Arc St
-- statement:
--   Definitions and structural lemmas for One Arc St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/OneArcSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidArc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
def PullCubCompSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → m'.IsPullCubical c'' c' → n.IsPullCubical c'' c
def PullCubCancelSt : Prop :=
  ∀ (S S' S'' : Scheme.{0}) (G : Over S) (G' : Over S') (G'' : Over S'') [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G''] (m : CubeMap G' G) (m' : CubeMap G'' G') (n : CubeMap G'' G)
    (L : RigLB G) (L' : RigLB G') (L'' : RigLB G'') (c : CubicalStr G L) (c' : CubicalStr G' L')
    (c'' : CubicalStr G'' L''), n.F = m'.F ≫ m.F → n.F3 = m'.F3 ≫ m.F3 → n.e = m'.e ≫ m.e →
    m.IsPullCubical c' c → n.IsPullCubical c'' c → m'.IsPullCubical c'' c'
def SABCompSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (m' : SABMap t'' t' g),
    ∃ n : SABMap t'' t (g ≫ f), n.φ = m'.φ ≫ m.φ
def SABCancelSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' S'' : Scheme.{0}) (t : SAB H S)
    (t' : SAB H S') (t'' : SAB H S'') (f : S' ⟶ S) (g : S'' ⟶ S') (m : SABMap t' t f) (n : SABMap t'' t (g ≫ f)),
    ∃ m' : SABMap t'' t' g, n.φ = m'.φ ≫ m.φ
def AbLocusOneSt : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (K : Type) [Field K] (t : Sp K ⟶ S),
    IsProper (pullback.snd G.hom t) → Set.range t ⊆ abLocus G
def ProjProperSt : Prop :=
  ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsProjOver f → IsProper f
def OneArcSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (O₀ O O' : Type) [CommRing O₀] [CommRing O] [CommRing O'] (β₀ : O₀ →+* c.F) (β : O →+* c.F) (β' : O' →+* c.F)
    (b : O₀ →+* O) (b' : O₀ →+* O') (Yg : Model Xo c β₀) (Y : Model Xo c β) (Y' : Model Xo c β'),
    β.comp b = β₀ → β'.comp b' = β₀ → Mono (spMap β') → Dominates Yg Y b → Dominates Yg Y' b' →
    ∀ (χ : Sp (PowerSeries k) ⟶ Y.X)
      (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
      (y : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c),
      χ ≫ Y.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β) → y ≫ Y.j = Out.jK (PowerSeries k) ≫ χ →
      y ≫ pullback.snd _ _ = Out.jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
      ∃ (χ' : Sp (PowerSeries k) ⟶ Y'.X)
        (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ'),
        χ' ≫ Y'.s = spMap (PowerSeries.C (R := k)) ≫ spMap (bF.comp β') ∧ y ≫ Y'.j = Out.jK (PowerSeries k) ≫ χ' ∧
        (∀ x, χ' x ∈ abLocus Y'.t.G ↔ χ x ∈ abLocus Y.t.G) ∧ W'.t = W.t ∧ HEq W'.P W.P ∧ HEq W'.φ W.φ ∧
        HEq W'.w W.w ∧ HEq W'.e W.e ∧
        ∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g' : T ⟶ W'.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left)
          (g₂ : T ⟶ Y'.oF.t.G.left) (τ : T ⟶ Sp (FractionRing (PowerSeries k))), HEq g' g →
          g ≫ W.t.G.hom = τ ≫ Out.jK (PowerSeries k) → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ W.m.φ = g₁ ≫ Y.m.φ →
          g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
          g' ≫ W'.m.φ = g₂ ≫ Y'.m.φ
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


