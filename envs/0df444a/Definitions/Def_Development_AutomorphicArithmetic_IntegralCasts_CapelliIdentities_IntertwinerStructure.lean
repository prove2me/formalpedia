-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntertwinerStructure
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntertwinerStructure
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T06:04:25.213234+00:00
-- url     : https://prove2.me/theorems/b23f54a4-f929-4d3d-8e5f-612e3987e004
-- title:
--   Intertwiner Structure
-- statement:
--   Definitions and structural lemmas for Intertwiner Structure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntertwinerStructure.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementMA
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.IntertwinerStructure.Intw :
    {Wp Wq : Type} →
      [inst : NormedAddCommGroup Wp] →
        [inst_1 : InnerProductSpace ℂ Wp] →
          [inst_2 : NormedAddCommGroup Wq] →
            [inst_3 : InnerProductSpace ℂ Wq] →
              [FiniteDimensional ℂ Wq] →
                (P : Formalism.FourierDecayAlt.M.Par) →
                  (Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq) →
                    (Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp) →
                      Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') →
                        Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P) → Prop :=
    fun {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
        [FiniteDimensional ℂ Wq] (P : Formalism.FourierDecayAlt.M.Par) (Bs : Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq)
        (e : Formalism.FourierDecayAlt.M.Ty P → ℂ → Wq →L[ℂ] Wp) (A : Formalism.FourierDecayAlt.Q.Pr ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
        (A' : Formalism.FourierDecayAlt.MA.A P (Formalism.FourierDecayAlt.MA.DQ P)) ↦
      ∀ (Φ : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
        Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e
                  ((A.1 : ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') → ↥(Formalism.FourierDecayAlt.Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
                    Φ) =
          Formalism.FourierDecayAlt.MA.actA P A' (Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.trR P Bs e Φ)


