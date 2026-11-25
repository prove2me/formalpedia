-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:51:01.690004+00:00
-- url     : https://prove2.me/theorems/c6378c1e-ae1b-4fde-a633-c7e03e7c744f
-- title:
--   Integral Frame Acquisition
-- statement:
--   Definitions and structural lemmas for Integral Frame Acquisition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/IntegralFrameAcquisition.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PtFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
def IsFiniteValuedExt (T T' : CDVR) (j : T.Fr →+* T'.Fr) (r : ℕ) : Prop :=
  j.Finite ∧ 0 < r ∧ ∀ x : T.Fr, vV T'.V (j x) = (r : ℤ) * vV T.V x
def algHomOver {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (io : K →+* A) (j : A →+* B) :
    letI := io.toAlgebra
    letI := (j.comp io).toAlgebra
    A →ₐ[K] B :=
  letI := io.toAlgebra
  letI := (j.comp io).toAlgebra
  { j with commutes' := fun _ => rfl }
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
def IsIntegralFrameOf {T T' : CDVR} {io : c.F →+* T.Fr} (j : T.Fr →+* T'.Fr)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (y' : IntFr Xo c T' (j.comp io)) : Prop :=
  letI := io.toAlgebra
  letI := (j.comp io).toAlgebra
  ∃ (z : FrPt Xo c T'.Fr) (t : Ix Dw → T'.Frˣ), FrMap (algHomOver io j) y z ∧ FrBor t z y'.1
def AcquiresIntegralFrame (la : HeightOneSpectrum (𝓞 c.F)) {T : CDVR} {io : c.F →+* T.Fr} (e : ℕ)
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) : Prop :=
  ∃ (T' : CDVR) (j : T.Fr →+* T'.Fr) (r : ℕ) (y' : IntFr Xo c T' (j.comp io)),
    IsFiniteValuedExt T T' j r ∧ OverLa la T'.V (j.comp io) (r * e) ∧ y'.IsAlg ∧ IsIntegralFrameOf j y y'
variable (Xo c)
def AllAcquireIntegralFrame : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ),
    OverLa la T.V io e → T.FinRes →
      ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr), AcquiresIntegralFrame la e y
def AllTestAcquireIntegralFrame : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ),
    OverLa la T.V io e → T.FinRes →
      ∀ y : (letI := io.toAlgebra; FrPt Xo c T.Fr),
        (letI := io.toAlgebra
         FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) →
        AcquiresIntegralFrame la e y
variable {Xo c}
end GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition


