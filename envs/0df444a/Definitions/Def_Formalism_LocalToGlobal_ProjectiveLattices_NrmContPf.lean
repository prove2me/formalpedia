-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NrmContPf
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_NrmContPf
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T11:20:08.146165+00:00
-- url     : https://prove2.me/theorems/f44c8392-d3b4-4b8b-a7df-4581e821288d
-- title:
--   Nrm Cont Pf
-- statement:
--   Definitions and structural lemmas for Nrm Cont Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/NrmContPf.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LawA13OfContinuous
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
open MeasureTheory Topology NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
def STLoc (h : GenFrEx Xo c) (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c)
    (jc : Comp Xo c → Fin (N + 1)) : Prop :=
  FnTrdeg Xo c Dd → FnFG Xo c → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → ∀ (Z : Comp Xo c) (sg : c.F →+* ℂ),
    ∃ S : Set (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1),
      MeasurableSet S ∧
      Measure.pi (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere) S = 0 ∧
      ∀ t0 ∈ Sᶜ, ∃ U ∈ 𝓝 t0, ∃ (n : ℕ)
        (Q : Fin n → (Fin Dd → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Om Z →+* ℂ)),
        (∀ k (a : Om Z), ContinuousOn (fun t => Q k t a) (U ∩ Sᶜ)) ∧
        ∀ t ∈ U ∩ Sᶜ, Function.Injective (fun k => Q k t) ∧
          Set.range (fun k => Q k t) = {P : Om Z →+* ℂ | P ∈ PT sg ∧ ∀ i, ∑ j,
            (t i : EuclideanSpace ℂ (Fin (N + 1))) j *
              P (ratio (Ω := Om Z) (valG h uL (wR j) Z) (valG h uL (wR (jc Z)) Z)) = 0}
def NrmAlong (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) : Prop :=
  ∀ (Z : Comp Xo c) (sg : c.F →+* ℂ) {G : WTZ E} {f : AC Z}, f ∈ AG Z G → f ≠ 0 →
    ∀ {X : Type} [TopologicalSpace X] (U : Set X) (Q : X → (Om Z →+* ℂ)), (∀ x ∈ U, Q x ∈ PT sg) →
      (∀ a, ContinuousOn (fun x => Q x a) U) → ContinuousOn (fun x => nrmC fn (yP Z) G f (Q x)) U
end Formalism.L2.Pj


