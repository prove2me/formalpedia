-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AlgebraicPointWeights
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AlgebraicPointWeights
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:50.728398+00:00
-- url     : https://prove2.me/theorems/73425f70-cbd9-42c7-9b2a-109b07808f10
-- title:
--   Algebraic Point Weights
-- statement:
--   Definitions and structural lemmas for Algebraic Point Weights, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/AlgebraicPointWeights.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def WeightOverFields : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n →
    ∀ (S : Type) [Field S] [Algebra c.F S] (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' →
      evR Xo c f y' = wchar (ex Dw a n) t * evR Xo c f y
def IntegralDiagUnit : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y y' : IntFr Xo c T io) (t : Ix Dw → T.Frˣ),
    (letI := io.toAlgebra; FrBor t y.1 y'.1) →
      ∀ i : Ix Dw, ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = (t i : T.Fr)
def AlgebraicPointOver : Prop :=
  ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ),
    OverLa la T.V io e ∧ T.FinRes ∧ Nonempty (letI := io.toAlgebra; FrPt Xo c T.Fr)
def IntegralFrameAfterExt : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e →
    letI := io.toAlgebra
    ∀ y : FrPt Xo c T.Fr, ∃ (T' : CDVR) (io' : c.F →+* T'.Fr),
      letI := io'.toAlgebra
      ∃ (φ : T.Fr →ₐ[c.F] T'.Fr) (r : ℕ), 0 < r ∧ (∀ x : T.Fr, vV T'.V (φ x) = (r : ℤ) * vV T.V x) ∧
        φ.toRingHom.Finite ∧ (T.FinRes → T'.FinRes) ∧
        ∃ (z : FrPt Xo c T'.Fr) (y' : IntFr Xo c T' io') (t : Ix Dw → T'.Frˣ), FrMap φ y z ∧ FrBor t z y'.1
structure AlgebraicLaws : Prop where
  weight : WeightOverFields Xo c
  unitDiag : IntegralDiagUnit Xo c
  algPoint : AlgebraicPointOver Xo c
  intFrame : IntegralFrameAfterExt Xo c
variable {Xo c}
end GlobalTheory.IndefiniteRowSideFullHecke.AlgebraicPointWeights


