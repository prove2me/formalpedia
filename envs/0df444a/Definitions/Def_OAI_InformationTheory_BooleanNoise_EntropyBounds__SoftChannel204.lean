-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
-- name    : OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:56:41.874387+00:00
-- url     : https://prove2.me/theorems/46206b3f-fd86-4e7f-ae05-8a8bac1f3961
-- title:
--   The even power series of $\psi$
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   For $v\in\mathbb{R}$ define
--   $$
--   \Psi(v)=\sum_{k=0}^{\infty}\frac{v^{2k+2}}{(2k+2)(2k+1)} .
--   $$
--
--   For $|v|\le1$ the series converges, and it is used to prove two-sided polynomial bounds on $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$.
--
--   **Formalization Note** The sum is Lean's `tsum`, which is $0$ for non-summable families, i.e. for $|v|>1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/EntropyBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/EntropyBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SoftChannel204 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204

namespace OAI

noncomputable section

open Set Filter Finset
open scoped Topology BigOperators

namespace LeanBlast.CourtadeKumar

def psiSeries (v : ℝ) : ℝ := ∑' k : ℕ, psiCoeff k * v ^ (2 * (k + 1))

end LeanBlast.CourtadeKumar

end

end OAI


