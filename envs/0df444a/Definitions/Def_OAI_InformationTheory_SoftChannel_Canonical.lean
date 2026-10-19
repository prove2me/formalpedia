-- Prove2me | Definitions.Def_OAI_InformationTheory_SoftChannel_Canonical
-- name    : OAI_InformationTheory_SoftChannel_Canonical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T14:35:54.380344+00:00
-- url     : https://prove2.me/theorems/0fa8a9d6-8150-4218-a143-0cbfcd5036b3
-- title:
--   Bose occupations, normalized entropy and joining costs
-- statement:
--   These notions belong to a formal proof of sharp information inequalities for soft channels on the Boolean cube. For $g:\{0,1\}^n\to[-1,1]$ let $h(v)=\log2-\psi(v)$, where $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$, so $h(v)$ is the entropy in nats of a random sign with mean $v$. The information of $g$ is $I(g)=h(\mathbb Eg)-\mathbb Eh(g)$, and $T_\rho$ is the noise operator with correlation $\rho$. The main results are the soft contraction $I(T_\rho g)\le\psi(|\rho|\,\psi^{-1}(I(g)))$ and its attainment by scaled dictators. Further results identify $I(T_\rho g)$ with a mutual information and give the Courtade–Kumar bound of $1-H(\varepsilon)$ bits for Boolean functions. The last is the sharp production inequality $r(I(g))\le\mathcal D(g)$, where $\mathcal D(g)=\sum_i\mathbb E[\operatorname{artanh}(g)\,\partial_ig]$ and $r(s)=\psi^{-1}(s)\operatorname{artanh}\psi^{-1}(s)$.
--
--   1. **Bose occupation.** $b(z)=(e^z-1)^{-1}$ and $Q(z)=z\,b(z)-\log(1-e^{-z})$, the entropy of the geometric law with occupation $b(z)$.
--   2. **Normalized entropy.** With $u=b(z)$, $v=b(w)$, $n=1+u+v$,
--   $$
--   \mathcal N(z,w)=n\log n-\tfrac12\bigl((u+1)\log(u+1)+u\log u+(v+1)\log(v+1)+v\log v\bigr),
--   $$
--   its $z$-derivative, and the group terms of its series expansion as a combination of exponentials $e^{-(iz+jw)}$, which make it jointly convex.
--   3. **Joining coordinates and cost.** For $-1<y<x<1$, $Z=\log\frac{1+x}{1+y}$ and $W=\log\frac{1-y}{1-x}$, and the cost $\frac{x-y}4(\operatorname{artanh}x-\operatorname{artanh}y)$.
--   4. **Prices and corner configurations.** The price $-(8\,\partial_z\mathcal N)^{-1}$, a correction $\gamma$, and a core constant $\kappa$. The one-corner points $1-(1-m\mp d)/k$ with their entropy, and the reflected entropy $(d/r)\,h(r)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/SoftChannel/Canonical.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/SoftChannel/Canonical.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeVariance__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_NormalizedPair__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveLogTrapezoid__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveCalculus__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PerspectiveInequality__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Comparison__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment__SoftChannel204

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology
namespace LeanBlast.CourtadeKumar

def bose (z : ℝ) : ℝ := (Real.exp z - 1)⁻¹

def canonicalQ (z : ℝ) : ℝ := z * bose z - Real.log (1 - Real.exp (-z))

def normalizedEntropy (z w : ℝ) : ℝ :=
  let u := bose z
  let v := bose w
  let n := 1 + u + v
  n * Real.log n - ((u + 1) * Real.log (u + 1) + u * Real.log u +
    (v + 1) * Real.log (v + 1) + v * Real.log v) / 2

def canonicalGroup (z w : ℝ) (n : ℕ) : ℝ :=
  ((∑ j ∈ Finset.range (n + 1), Real.exp (-((n + 1 : ℕ) * z + (j + 1 : ℕ) * w))) +
    ∑ i ∈ Finset.range n, Real.exp (-((i + 1 : ℕ) * z + (n + 1 : ℕ) * w))) /
    (n + 1 : ℕ)

def normalizedEntropyDz (z w : ℝ) : ℝ :=
  -bose z * (bose z + 1) * (Real.log (1 + bose z + bose w) -
    (Real.log (bose z + 1) + Real.log (bose z)) / 2)

def canonicalPrice (z w : ℝ) : ℝ := -(8 * normalizedEntropyDz z w)⁻¹

def canonicalGamma (z w : ℝ) : ℝ :=
  (1/8 + canonicalPrice z w * normalizedEntropyDz w z) / (2 * bose w * (bose w + 1))

def joiningZ (x y : ℝ) : ℝ := Real.log ((1+x)/(1+y))
def joiningW (x y : ℝ) : ℝ := Real.log ((1-y)/(1-x))
def joiningCost (x y : ℝ) : ℝ := (x-y)/4 * (Real.artanh x - Real.artanh y)

def coreKappa (z w : ℝ) : ℝ :=
  (z+w)/8 + canonicalPrice z w * normalizedEntropy z w + canonicalGamma z w * (1+2*bose w)

def onecornerX (m d k : ℝ) : ℝ := 1-(1-m-d)/k
def onecornerY (m d k : ℝ) : ℝ := 1-(1-m+d)/k
def onecornerEntropy (m d k : ℝ) : ℝ :=
  k*(entropy (onecornerX m d k)+entropy (onecornerY m d k))/2

def reflectedEntropy (d r : ℝ) : ℝ := (d/r)*entropy r

end LeanBlast.CourtadeKumar
end
end

end OAI


