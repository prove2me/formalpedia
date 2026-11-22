-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:09:50.926318+00:00
-- url     : https://prove2.me/theorems/ceb7d46e-b3b8-443a-a5e8-e416546c0c2d
-- title:
--   Pull Cub
-- statement:
--   Definitions and structural lemmas for Pull Cub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/PullCub.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArcSt
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
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
section Stalk
variable {X Y Z : Scheme.{0}}
open Classical in

def gm (f : Y ⟶ X) (y : Y) (U : X.Opens) : Γ(X, U)ˣ →* (Y.presheaf.stalk y)ˣ :=
  if h : f y ∈ U then (Units.map (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.toMonoidHom).comp (pullU f U) else 1
variable {X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}
def gw (w : LB.Iso L' (L.pull F)) (f : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
  gm f y ((L.pull F).U (fun _ => j) ⊓ L'.U k) (w.s (fun _ => j, k))
def PGen (w : LB.Iso L' (L.pull F)) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X') (y : Y) (j j' : L.ι) (k k' : L'.ι), F (f y) ∈ L.U j → F (f y) ∈ L.U j' → f y ∈ L'.U k →
    f y ∈ L'.U k' → gw w f y j k = gm (f ≫ F) y _ (L.g j j') * (gm f y _ (L'.g k k'))⁻¹ * gw w f y j' k'
def PMaps (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)) (t : LB.Gen (LB.LinComb L φ ε)) (h : Y' ⟶ Y) :
    Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι), (∀ k, F (φ' k (r z)) ∈ L.U (p k)) →
    (∀ k, φ' k (r z) ∈ L'.U (q k)) →
    gm (r ≫ h) z (LB.wchart L φ p) (t.s p) =
      (∏ k, gw w (r ≫ φ' k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ' q) (a.s q)
end Stalk
section Tri
variable {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}
def Tri (w : LB.Iso L' (L.pull F)) (w' : LB.Iso L'' (L'.pull F')) (w'' : LB.Iso L'' (L.pull (F' ≫ F))) : Prop :=
  ∀ (Y : Scheme.{0}) (f : Y ⟶ X'') (y : Y) (j : L.ι) (i : L'.ι) (k : L''.ι), F (F' (f y)) ∈ L.U j → F' (f y) ∈ L'.U i →
    f y ∈ L''.U k → gw w'' f y j k = gw w (f ≫ F') y j i * gw w' f y i k
variable {w : LB.Iso L' (L.pull F)} {w' : LB.Iso L'' (L'.pull F')} {w'' : LB.Iso L'' (L.pull (F' ≫ F))}
variable {K : Type} [Fintype K] {Y Y' Y'' : Scheme.{0}} {φ : K → (Y ⟶ X)} {φ' : K → (Y' ⟶ X')} {φ'' : K → (Y'' ⟶ X'')}
  {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L' φ' ε)} {t'' : LB.Gen (LB.LinComb L'' φ'' ε)}
  {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
end Tri
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


