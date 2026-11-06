-- Prove2me | Definitions.Def_BianchiIX_Algebra_Flux
-- name    : BianchiIX_Algebra_Flux
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-05T05:25:33.269675+00:00
-- url     : https://prove2.me/theorems/045db78e-f8bc-43ec-a324-f8e1ad6b590a
-- title:
--   Wall amplitude and corrected divergence
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Define $H(a,b,c)=(abc)^{2/3}$ and
--   $$\Delta(q,h)=\frac{2(q+4h)}{1+4h}.$$
--   Real powers and division have their total Lean meanings.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Flux.lean

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

/-! The sharp curvature bound and the positive corrected divergence, Section 5.2. -/

namespace BianchiIX

noncomputable section









def correctedDivergence (q h : ℝ) : ℝ := 2 * (q + 4 * h) / (1 + 4 * h)







def wallAmplitude (a b c : ℝ) : ℝ := (a * b * c) ^ (2 / 3 : ℝ)









end

end BianchiIX


