-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_RadialDerivatives
-- name    : OAI_Probability_ThreeState_RadialDerivatives
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:34:18.219225+00:00
-- url     : https://prove2.me/theorems/a0fbdad6-377d-44e0-9e1f-741e8de6b4d0
-- title:
--   Ray, logarithmic variances, energy and gap functionals for three-coordinate perturbations
-- statement:
--   Let $v\in\mathbb{R}^3$. Use the average $\operatorname{avg}$, the moment $X(v)=\frac12\operatorname{avg}(v^2)$, the centered logarithms $c_i(v)=\log(1+v_i)-\operatorname{avg}_j\log(1+v_j)$, the inverse moments $I_k(v)=\operatorname{avg}((1+v_i)^{-k})$ and $J_k(v)=\operatorname{avg}(c_i(v)(1+v_i)^{-k})$, and $M(v)=\operatorname{avg}(v_ic_i(v))$. The file defines the following.
--
--   1. **Ray.** $\operatorname{ray}(v,t)=t\,v$ for $t\in\mathbb{R}$.
--   2. **Logarithmic average and variances.**
--   $$
--   \Lambda(v)=\operatorname{avg}\bigl(\log(1+v_i)\bigr),\qquad V(v)=\operatorname{avg}\bigl(c_i(v)^2\bigr),\qquad V_w(v)=\operatorname{avg}\bigl((1+v_i)\,c_i(v)^2\bigr).
--   $$
--   3. **Energy.** $\mathcal E(v)=3\Lambda(v)+2M(v)+\tfrac25V_w(v)$.
--   4. **Gap functionals.**
--   $$
--   \begin{aligned}
--   Y(v)&=1-I_1-6\Lambda-2M-\tfrac25V_w-\tfrac25V+\tfrac45I_1M-X^2,\\
--   Z(v)&=6\Lambda-5+\tfrac{26}{5}I_1-I_2+\tfrac45V+\tfrac45(I_2-2I_1)M+\tfrac45J_1+\tfrac45I_1^2-3X^2,
--   \end{aligned}
--   $$
--   where all quantities on the right are evaluated at $v$.
--
--   At $v=0$ every one of these quantities vanishes, except $I_k(0)=1$; in particular $\mathcal E(0)=Y(0)=Z(0)=0$. These evaluations are recorded as simplification lemmas. The functionals are the ingredients of the radial derivative computations behind an entropy inequality for three-state messages.
--
--   **Formalization Note** Vectors are functions `Fin 3 → ℝ`. Lean's conventions $\log x=\log|x|$ (with $\log0=0$) and $0^{-1}=0$ apply outside the intended domain $1+v_i>0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/RadialDerivatives.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/RadialDerivatives.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical
import Definitions.Def_OAI_Probability_ThreeState_Basic
import Definitions.Def_OAI_Probability_ThreeState_Expectations
import Definitions.Def_OAI_Probability_ThreeState_Messages
import Definitions.Def_OAI_Probability_ThreeState_Observation
import Definitions.Def_OAI_Probability_ThreeState_Update
import Definitions.Def_OAI_Probability_ThreeState_RadialMoments

namespace OAI

/-! Radial logarithmic derivatives and the entropy inequality. -/

namespace ThreeState.Radial

noncomputable def ray (v : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ := fun i => t*v i
noncomputable def logAvg (v : Fin 3 → ℝ) := avg (fun i => Real.log (1+v i))
noncomputable def logVariance (v : Fin 3 → ℝ) := avg (fun i => (centeredLog v i)^2)
noncomputable def weightedLogVariance (v : Fin 3 → ℝ) :=
  avg (fun i => (1+v i)*(centeredLog v i)^2)
 
noncomputable def energy (v : Fin 3 → ℝ) :=
  3*logAvg v+2*logMoment v+(2/5 : ℝ)*weightedLogVariance v
 
noncomputable def gapY (v : Fin 3 → ℝ) :=
  1-invMoment v 1-6*logAvg v-2*logMoment v-(2/5 : ℝ)*weightedLogVariance v-
    (2/5 : ℝ)*logVariance v+(4/5 : ℝ)*invMoment v 1*logMoment v-(momentX v)^2
 
noncomputable def gapZ (v : Fin 3 → ℝ) :=
  6*logAvg v-5+(26/5 : ℝ)*invMoment v 1-invMoment v 2+
    (4/5 : ℝ)*logVariance v+(4/5 : ℝ)*(invMoment v 2-2*invMoment v 1)*logMoment v+
    (4/5 : ℝ)*logInvMoment v 1+(4/5 : ℝ)*(invMoment v 1)^2-3*(momentX v)^2

end ThreeState.Radial
namespace ThreeState.Radial

@[simp] lemma ray_zero (v : Fin 3 → ℝ) : ray v 0 = 0 := by ext i; simp [ray]
@[simp] lemma ray_one (v : Fin 3 → ℝ) : ray v 1 = v := by ext i; simp [ray]
@[simp] lemma logAvg_zero : logAvg 0 = 0 := by norm_num [logAvg, avg_expand]
@[simp] lemma centeredLog_zero (i : Fin 3) : centeredLog 0 i = 0 := by
  norm_num [centeredLog, avg_expand]
@[simp] lemma logMoment_zero : logMoment 0 = 0 := by norm_num [logMoment, avg_expand]
@[simp] lemma logVariance_zero : logVariance 0 = 0 := by norm_num [logVariance, avg_expand]
@[simp] lemma weightedLogVariance_zero : weightedLogVariance 0 = 0 := by
  norm_num [weightedLogVariance, avg_expand]
@[simp] lemma invMoment_zero (n : ℕ) : invMoment 0 n = 1 := by
  norm_num [invMoment, avg_expand]
@[simp] lemma logInvMoment_zero (n : ℕ) : logInvMoment 0 n = 0 := by
  norm_num [logInvMoment, avg_expand]
@[simp] lemma momentX_zero : momentX 0 = 0 := by norm_num [momentX, avg_expand]
@[simp] lemma energy_zero : energy 0 = 0 := by norm_num [energy]
@[simp] lemma gapY_zero : gapY 0 = 0 := by norm_num [gapY]
@[simp] lemma gapZ_zero : gapZ 0 = 0 := by norm_num [gapZ]

 
end ThreeState.Radial
namespace ThreeState.Radial

 
 
end ThreeState.Radial

end OAI


