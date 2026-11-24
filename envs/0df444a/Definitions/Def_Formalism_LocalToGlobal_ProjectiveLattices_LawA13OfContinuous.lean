-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LawA13OfContinuous
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_LawA13OfContinuous
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:35.158543+00:00
-- url     : https://prove2.me/theorems/0656738e-3f10-4de2-8463-9da9a6cd267a
-- title:
--   Law A13 Of Continuous
-- statement:
--   Definitions and structural lemmas for Law A13 Of Continuous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LawA13OfContinuous.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open MeasureTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
section Gen
variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))
def A13ContinuousOffNull : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∃ S : Set (Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1),
      MeasurableSet S ∧ d.sphMeasure S = 0 ∧
      ContinuousOn (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
        ∑ᶠ P ∈ d.ST Z sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
          Real.log (d.nrm Z G f P)) Sᶜ
end Gen
def NrmContOff (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) : Prop :=
  ∀ Z (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∃ S : Set (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1),
      MeasurableSet S ∧
      Measure.pi (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere) S = 0 ∧
      ContinuousOn (fun t : Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1 =>
        ∑ᶠ P ∈ {P : Om Z →+* ℂ | P ∈ PT sg ∧ ∀ i, ∑ j, (t i : EuclideanSpace ℂ (Fin (N + 1))) j *
            P (ratio (Ω := Om Z) (valG h uL (wR j) Z) (valG h uL (wR (jc Z)) Z)) = 0},
          Real.log (nrmC fn (yP Z) G f P)) Sᶜ
end Formalism.L2.Pj


