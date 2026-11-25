-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:01:22.088549+00:00
-- url     : https://prove2.me/theorems/9d85a8e2-3ca7-498a-9cd6-09ac4b6aa134
-- title:
--   Cut GCore GTConn Gauge A
-- statement:
--   Definitions and structural lemmas for Cut GCore GTConn Gauge A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTConnGaugeA.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
section frame
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end frame
section trans
theorem comp_snd_mem_smSub (P : M.Par) {v : ℂ → ℂ} (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v (Ann P)) :
    (fun q : MA.Qp P.r P.TT => v q.1.2) ∈ MA.smSub P.r P.TT := by
  show ContDiffOn ℝ MA.sm (MA.ext (fun q : MA.Qp P.r P.TT => v q.1.2)) (MA.Qset P.r P.TT)
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : MA.E P.r => v x.2) (MA.Qset P.r P.TT) :=
    hv.comp contDiff_snd.contDiffOn (fun x hx => show P.TT < Complex.normSq x.2 from hx.2)
  exact h1.congr (fun x hx => by simp [MA.ext, hx])
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end trans
section act
def mulQ (P : M.Par) (x : (MA.DQ P).Pr) (f : MA.SmQ P.r P.TT) : MA.SmQ P.r P.TT := x.1 f
end act
section kap
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end kap
end
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


