-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LocHaarRR
-- name    : Formalism_PeriodIntegrals_LocHaarRR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:04.719521+00:00
-- url     : https://prove2.me/theorems/6284036f-7122-491a-b2f4-83e4dc71484b
-- title:
--   Loc Haar RR
-- statement:
--   Definitions and structural lemmas for Loc Haar RR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LocHaarRR.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open IsDedekindDomain NumberField ValuativeRel MeasureTheory
namespace PI.LocHaarRR
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
def ordR {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}
    (sg : Formalism.MainNotions.S.Loc.SplitAt A.Fp A.Ep A.cj (Formalism.MainNotions.S.Loc.resChar p)) : Subring A.Ep :=
  let S : Subring (𝒪[A.Fp] × 𝒪[A.Fp]) :=
    RingHom.eqLocus ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.fst _ _))
      ((Ideal.Quotient.mk (Ideal.span {sg.q})).comp (RingHom.snd _ _))
  (S.map ((𝒪[A.Fp]).subtype.prodMap (𝒪[A.Fp]).subtype)).comap sg.e.toRingEquiv.toRingHom
def RR (A : Formalism.MainNotions.S.Loc.LocAt F E sig p) : Set A.Ep :=
  match A.split with
  | none => (A.O : Set A.Ep)
  | some sg => (ordR sg : Set A.Ep)
end
def Target : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (p : HeightOneSpectrum (𝓞 F)) (A : Formalism.MainNotions.S.Loc.LocAt F E sig p),
    IsReduced A.Ep → ∃ μ : Measure A.Ep, μ.IsAddHaarMeasure ∧ SigmaFinite μ ∧ μ (RR A) = 1
end PI.LocHaarRR


