-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UniformizationClosedSplit
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_UniformizationClosedSplit
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:37:37.563796+00:00
-- url     : https://prove2.me/theorems/285785e5-6ecf-40b6-b270-2d911d88114b
-- title:
--   Uniformization Closed Split
-- statement:
--   Definitions and structural lemmas for Uniformization Closed Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/UniformizationClosedSplit.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
def PrimeToLevel (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) : Prop :=
  ((l.M' : ℕ) : 𝓞 c.F) ∉ la.asIdeal
def HasModel (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) : Prop :=
  ∃ (O : Type) (_ : CommRing O) (β : O →+* c.F) (b : O →+* T.V) (Y : Model Xo c β),
    (∀ x : O, algebraMap T.V T.Fr (b x) = io (β x)) ∧ Y.N3
def ClosedSplit (T : CDVR) (G : SAB H (Sp T.V)) : Prop :=
  ∃ S : SplitExt (Sp (IsLocalRing.ResidueField T.V)),
    S.IsGt ((Over.pullback (spMap (IsLocalRing.residue T.V))).obj G.G)
def HasUnif (T : CDVR) (G : SAB H (Sp T.V)) : Prop :=
  ∃ P : PELUnif (IsLocalRing.maximalIdeal T.V) G, P.TorsionIso
variable (Xo : Moduli Dw l) (c : Coeff l)
def ModelAt : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → HasModel Xo c T io
def UnifOfModel : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), HasModel Xo c T io →
    ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G
def UnifAt : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), PrimeToLevel c la →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
      ∀ (y : IntFr Xo c T io) (I : IntData Xo c T io y.1), ClosedSplit T I.G → HasUnif T I.G
variable {Xo c}
example {O : Type} [CommRing O] (T : CDVR) (b : O →+* T.V) (n : ℕ) (hn : ¬ IsUnit (n : T.V)) : ¬ IsUnit (n : O) :=
  fun h => hn (by simpa using h.map b)
end General
def Statement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ModelAt Xo c ∧ UnifOfModel Xo c
end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationClosedSplit


