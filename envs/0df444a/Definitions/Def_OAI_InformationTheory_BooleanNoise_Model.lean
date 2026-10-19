-- Prove2me | Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
-- name    : OAI_InformationTheory_BooleanNoise_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:49:27.04467+00:00
-- url     : https://prove2.me/theorems/83712112-f512-4510-bcb3-8e0ff00b51d6
-- title:
--   Cube averages, binary entropy and dictators
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   1. **Cube and average.** The Boolean cube $\{0,1\}^n$ of bit vectors, and the uniform average $\mathbb Eg=2^{-n}\sum_xg(x)$.
--   2. **Logarithmic constants.** $\log2$, and $t\log t$.
--   3. **Binary entropy in bits.**
--   $$
--   H(\varepsilon)=-\frac{\varepsilon\log\varepsilon+(1-\varepsilon)\log(1-\varepsilon)}{\log2}.
--   $$
--   4. **Dictators.** The Boolean functions $x\mapsto x_i$ and $x\mapsto\neg x_i$.
--
--   Dictators attain the Courtade–Kumar bound $1-H(\varepsilon)$ for the mutual information between $f(X)$ and a noisy copy $Y$ of $X$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/BooleanNoise/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SoftChannel204 mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model

namespace OAI

noncomputable section

open scoped BigOperators

namespace LeanBlast.CourtadeKumar

abbrev Cube (n : ℕ) := LeanBlast.GotsmanLinial.Cube n

def cubeAverage {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  (∑ x, g x) / (2 : ℝ) ^ n

def ell : ℝ := Real.log 2

def xlogx (t : ℝ) : ℝ := t * Real.log t

def binaryEntropy (ε : ℝ) : ℝ :=
  -(xlogx ε + xlogx (1 - ε)) / ell

def dictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := x i

def complementDictator {n : ℕ} (i : Fin n) (x : Cube n) : Bool := !(x i)

end LeanBlast.CourtadeKumar

end

end OAI


