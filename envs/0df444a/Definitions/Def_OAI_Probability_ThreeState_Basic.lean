-- Prove2me | Definitions.Def_OAI_Probability_ThreeState_Basic
-- name    : OAI_Probability_ThreeState_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:28:02.85066+00:00
-- url     : https://prove2.me/theorems/95596f56-af85-45ed-8899-fdbfc31b201f
-- title:
--   Real point masses and total variation distance of discrete probability laws
-- statement:
--   This file fixes two basic quantities for discrete probability distributions (probability mass functions) $p,q$ on a type $\alpha$.
--
--   1. **Point mass.** For $a\in\alpha$, $\mathrm{mass}_p(a)=p(\{a\})\in[0,1]$ is the probability of the outcome $a$, viewed as a real number. Below it is simply written $p(a)$.
--   2. **Total variation distance.**
--   $$
--   d_{\mathrm{TV}}(p,q)=\frac12\sum_{a\in\alpha}\bigl|p(a)-q(a)\bigr| .
--   $$
--
--   These are the real-valued quantities in which the posterior advantage of the three-state broadcast model is rewritten and compared under further processing of the observation.
--
--   **Formalization Note** A probability mass function takes values in $[0,\infty]$, so `mass p a` is `(p a).toReal`. The sum is Lean's unconditional sum `tsum`; here it converges, since its terms are bounded by $p(a)+q(a)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThreeState/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeState/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThreeStateSupercritical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThreeStateSupercritical

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Three-state symmetric broadcast experiments, posterior advantage and total variation. -/

namespace ThreeState

 
 
 

 
 

 
 
 

 
 
 
end ThreeState
namespace ThreeState

noncomputable def mass {α : Type*} (p : PMF α) (a : α) : ℝ := (p a).toReal

 
noncomputable def tvMass {α : Type*} (p q : PMF α) : ℝ :=
  (∑' a, |mass p a-mass q a|)/2

 
end ThreeState

end OAI


