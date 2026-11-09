-- Prove2me | Definitions.Def_CaiZhuInfo_Matrix_compoundPoissonPoint
-- name    : CaiZhuInfo_Matrix_compoundPoissonPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:13.558859+00:00
-- url     : https://prove2.me/theorems/6d733b61-5605-49a9-bd19-d7a5e6950316
-- title:
--   Ordered convolution and the full compound-Poisson law
-- statement:
--   On any discrete group $G$, the convolution of $P$ and $Q$ is the law of the ordered product of independent variables with those laws. The convolution power $Q^{*k}$ is computed recursively with $Q^{*0}=\delta_e$. For $\lambda\ge0$, define the Poisson weights and point probabilities by
--   $$w_\lambda(k)=e^{-\lambda}\frac{\lambda^k}{k!},\qquad P_\lambda(g)=\sum_{k=0}^\infty w_\lambda(k)Q^{*k}(g).$$
--   The largest point probability is $\sup_gP(g)$. The input entropy is evaluated on the finite positive-support subtype using the published entropy in bits. The group need not be finite, countable or commutative, and the compound-Poisson law can have infinite support. The nonnegative Poisson series are summable for every nonnegative finite rate, and all point probabilities lie in $[0,1]$. This supplies the full probability objects for Corollary 4.4 without truncating counts or imposing a topology on the ambient group.
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), §3 and Corollary 4.4, printed pp.10,14 / PDF pp.11,15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_conditionalInformation

namespace CaiZhuInfo.Matrix
noncomputable section

variable {G : Type} [Group G]

/-- Ordered independent convolution on an arbitrary discrete group; no
countability or commutativity of the ambient group is assumed. -/
def convolution (P Q : PMF G) : PMF G :=
  P.bind fun x => Q.map fun y => x * y

def convolutionPower (Q : PMF G) : ℕ → PMF G
  | 0 => PMF.pure 1
  | k + 1 => convolution (convolutionPower Q k) Q

def poissonWeight (rate : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-rate) * rate ^ k / (k.factorial : ℝ)

/-- The full infinite Poisson mixture, §3 and Corollary 4.4.
For rate ≥ 0 these nonnegative series converge to probability masses. -/
def compoundPoissonPoint (Q : PMF G) (rate : ℝ) (g : G) : ℝ :=
  ∑' k : ℕ, poissonWeight rate k * mass (convolutionPower Q k) g

/-- All point-mass functions used here are bounded in [0,1], on a nonempty group. -/
def largestPoint (p : G → ℝ) : ℝ := sSup (Set.range p)

/-- Finite-support entropy on the support subtype, using the published bit entropy. -/
def supportedEntropy (Q : PMF G) (h : Q.support.Finite) : ℝ :=
  letI := h.fintype
  FuchsVdGraaf.entropy (fun g : Q.support => mass Q g.val)

end
end CaiZhuInfo.Matrix


