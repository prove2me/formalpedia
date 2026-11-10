-- Prove2me | Definitions.Def_EzeunalaJiangKS_Signing_FaceCalculus
-- name    : EzeunalaJiangKS_Signing_FaceCalculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:02:51.290392+00:00
-- url     : https://prove2.me/theorems/986380cc-c8ad-4f36-9a82-e0106a241a89
-- title:
--   Open faces, derivatives, and drift covariance pairing
-- statement:
--   A coordinate is active when $|x_i|<1$. The face map replaces active coordinates by real variables and fixes all frozen coordinates at their values in $x$. Its open domain requires exactly the active variables to lie in $(-1,1)$.
--   $$\mathcal D f=\sum_i\partial_i f\,\mu_i+\tfrac12\operatorname{Tr}((\nabla^2 f)\Sigma).$$
--   Derivatives are Fréchet derivatives of the composition with this face map. Vectors and covariance matrices use $N$ coordinates with zeros in frozen positions; the active count is the cardinality of the active set. This is equivalent to relabeling the active coordinates by $[n]$. It also specifies the zero-dimensional vertex faces. Outside differentiability domains Mathlib's derivative defaults apply; no theorem assumes their correctness there.
-- source:
--   Ekene Ezeunala, Haotian Jiang, STOC 2027 submission #1226 (October 2026), §3 standing assumptions and Lemma 3.2, printed p. 4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1226.pdf

import Definitions.Def_EzeunalaJiangKS_Signing_Potential

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace EzeunalaJiangKS.Signing

attribute [local instance] Classical.propDecidable

def active {N : ℕ} (x : State N) : Finset (Fin N) := Finset.univ.filter (fun i => |x i| < 1)
def activeCount {N : ℕ} (x : State N) : ℕ := (active x).card

def faceMap {N : ℕ} (x z : State N) : State N :=
  fun i => if i ∈ active x then z i else x i

def faceDomain {N : ℕ} (x : State N) : Set (State N) :=
  {z | ∀ i ∈ active x, |z i| < 1}

def facePartial {N : ℕ} (f : State N → ℝ) (x : State N) (i : Fin N) : ℝ :=
  fderiv ℝ (fun z => f (faceMap x z)) x (Pi.single i 1)

def faceHessian {N : ℕ} (f : State N → ℝ) (x : State N) : RMat N :=
  fun i j => fderiv ℝ (fderiv ℝ (fun z => f (faceMap x z))) x
    (Pi.single i 1) (Pi.single j 1)

def faceDirection {N : ℕ} (x h : State N) : Prop := ∀ i, i ∉ active x → h i = 0

def faceCovariance {N : ℕ} (x : State N) (U : RMat N) : Prop :=
  ∀ i j, i ∉ active x ∨ j ∉ active x → U i j = 0

def quadratic {N : ℕ} (U : RMat N) (h : State N) : ℝ := ∑ i, ∑ j, h i * U i j * h j

def generator {N : ℕ} (f : State N → ℝ) (x mu : State N) (U : RMat N) : ℝ :=
  (∑ i, facePartial f x i * mu i) + (1 / 2 : ℝ) * ((faceHessian f x * U).trace)

end EzeunalaJiangKS.Signing


