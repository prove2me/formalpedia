-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_RadialMoments
-- name    : OAI_Probability_ThreeState_RadialMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:32:03.964895+00:00
-- url     : https://prove2.me/theorems/e4d229e9-1860-4b3e-9f21-ca6e8e7cc8e6
-- title:
--   Averages, logarithmic and inverse moments of a three-coordinate perturbation
-- statement:
--   Let $v=(v_0,v_1,v_2)\in\mathbb{R}^3$, thought of as a perturbation $1+v_i$ of the uninformative message. The file defines the following averages.
--
--   1. **Average.** $\operatorname{avg}(v)=\frac13(v_0+v_1+v_2)$.
--   2. **Quadratic moment.** $X(v)=\frac12\operatorname{avg}(v^2)=\frac16(v_0^2+v_1^2+v_2^2)$.
--   3. **Centered logarithm.** For $i\in\{0,1,2\}$,
--   $$
--   c_i(v)=\log(1+v_i)-\frac13\sum_{j=0}^{2}\log(1+v_j).
--   $$
--   4. **Inverse moments.** For $k\in\mathbb{N}$, $I_k(v)=\operatorname{avg}\bigl((1+v_i)^{-k}\bigr)$ and $J_k(v)=\operatorname{avg}\bigl(c_i(v)\,(1+v_i)^{-k}\bigr)$.
--   5. **Logarithmic moment.** $M(v)=\operatorname{avg}\bigl(v_i\,c_i(v)\bigr)$.
--
--   These quantities enter the expansion of entropy-type functionals along rays $t\mapsto tv$.
--
--   **Formalization Note** Vectors are functions `Fin 3 → ℝ`. Lean's conventions apply: `Real.log x` equals $\log|x|$ for $x\neq0$ and $\log 0=0$, and $0^{-1}=0$. The intended domain is $1+v_i>0$. The lemma `avg_expand` rewrites `avg v` as `(v 0 + v 1 + v 2)/3`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/RadialMoments.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/RadialMoments.lean by skeleton subtraction
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

namespace OAI

/-! Three-coordinate moment identities and positive radial polynomials. -/

namespace ThreeState.Radial

end ThreeState.Radial

 

namespace ThreeState.Radial

noncomputable def avg (v : Fin 3 → ℝ) : ℝ := (∑ i, v i) / 3
noncomputable def momentX (v : Fin 3 → ℝ) : ℝ := avg (fun i => (v i)^2) / 2
noncomputable def centeredLog (v : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  Real.log (1+v i) - avg (fun j => Real.log (1+v j))

lemma avg_expand (v : Fin 3 → ℝ) : avg v = (v 0+v 1+v 2)/3 := by
  simp [avg, Fin.sum_univ_succ]; ring

noncomputable def invMoment (v : Fin 3 → ℝ) (j : ℕ) :=
  avg (fun i => ((1+v i)⁻¹)^j)
noncomputable def logInvMoment (v : Fin 3 → ℝ) (j : ℕ) :=
  avg (fun i => centeredLog v i*((1+v i)⁻¹)^j)
noncomputable def logMoment (v : Fin 3 → ℝ) := avg (fun i => v i*centeredLog v i)

 
 

end ThreeState.Radial

end OAI


