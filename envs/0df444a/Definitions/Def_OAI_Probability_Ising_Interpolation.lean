-- Prove2me | Definitions.Def_OAI_Probability_Ising_Interpolation
-- name    : OAI_Probability_Ising_Interpolation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:06:41.750975+00:00
-- url     : https://prove2.me/theorems/f4e28ab7-2f86-4259-8b68-81f09d76b453
-- title:
--   The single-spin field update map $(a,c)\mapsto (a+c)/(1+ac)$
-- statement:
--   For real numbers $a$ and $c$ the update map is
--
--   $$\operatorname{upd}(a,c)=\frac{a+c}{1+ac} .$$
--
--   It is the addition law of the hyperbolic tangent: if $a=\tanh x$ and $c=\tanh y$ then $\operatorname{upd}(a,c)=\tanh(x+y)$. In the Ising model it describes how the magnetization at a site reacts to an extra external field at that same site: if $m$ is the magnetization at $v$ and a field $t$ is added at $v$, the new magnetization at $v$ is $\operatorname{upd}(m,\tanh t)$. The interpolation inequalities of this module compare $\operatorname{upd}(a,c)$ and $\operatorname{upd}(b,-c)$ with mixtures of $\operatorname{upd}(a,d)$, $\operatorname{upd}(b,d)$ and $\pm1$ for a common parameter $d$; they are the analytic input to the inductive proof of the influence bound.
--
--   **Formalization Note** The Lean name is `OAI.BufferedIsing.DSS.update`. When $1+ac=0$, Lean's division convention gives the value $0$; the results that use the map keep $a$ and $c$ in $(-1,1)$, where the denominator is positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Interpolation.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Interpolation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

/-- The rational single-spin field update. -/
noncomputable def update (a c : ℝ) : ℝ := (a + c) / (1 + a * c)

end BufferedIsing.DSS

end OAI


