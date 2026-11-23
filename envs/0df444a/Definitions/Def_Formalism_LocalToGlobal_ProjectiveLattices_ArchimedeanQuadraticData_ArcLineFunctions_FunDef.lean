-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ArcLineFunctions_FunDef
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ArcLineFunctions_FunDef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:14.819803+00:00
-- url     : https://prove2.me/theorems/784277a2-6aff-4135-bd68-a76128824b00
-- title:
--   Fun Def
-- statement:
--   Definitions and structural lemmas for Fun Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/ArcLineFunctions/FunDef.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.Pj.QAt
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
noncomputable def arcNum {K₁ : Type} [Field K₁] (s : ArcS Dw K₁) :
    MvPolynomial (ArcLt Dw) (LaurentSeries K₁) := by
  classical
  exact if h : ∃ P, algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁) P = s
    then h.choose else 0
variable {Xo : Moduli Dw l} {c : Coeff l}
noncomputable def cfOf {K₁ : Type} [Field K₁] [Algebra c.F (ArcS Dw K₁)]
    (yF : FrPt Xo c (ArcS Dw K₁)) (μ : ArcLt Dw →₀ ℕ) (j : ℤ) (F : Rul Xo c) : K₁ :=
  (MvPolynomial.coeff μ (arcNum (evR Xo c F yF))).coeff j
end Formalism.L2.Pj.QAt


