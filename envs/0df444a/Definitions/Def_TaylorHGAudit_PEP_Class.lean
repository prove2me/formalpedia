-- Prove2me | Definitions.Def_TaylorHGAudit_PEP_Class
-- name    : TaylorHGAudit_PEP_Class
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:47:03.225015+00:00
-- url     : https://prove2.me/theorems/36663980-008d-4f3f-bb82-b5639242ee5c
-- title:
--   Full extended-valued smooth strongly convex class and interpolation
-- statement:
--   Let $E=\mathbb R^d$ with its Euclidean inner product. A proper closed convex function $F:E\to\mathbb R\cup\{+\infty\}$ lies in $\mathcal F_{\mu,L}$ when
--
--   $$
--   L^{-1}\|g_1-g_2\|\le\|x_1-x_2\|\quad(g_k\in\partial F(x_k)),\qquad
--   x\mapsto F(x)-\frac\mu2\|x\|^2\text{ is convex}.
--   $$
--
--   Here $0\le\mu<L\le+\infty$, $\mu$ is finite, and $1/+\infty=0$. An oracle triple $(x,g,v)$ means $F(x)=v\in\mathbb R$ and $g\in\partial F(x)$. A finite family is interpolable if one function in this class realizes every triple. Interpolation is defined by function existence, independently of the ordered-pair criterion.
--
--   The published proper closed convex predicate, global subdifferential, and extended-real conjugate are reused. Curvature subtraction removes a finite real quadratic value, and `realLift` embeds real-valued witnesses without restricting the source class. These objects support both nonsmooth constrained functions and smooth functions on the entire continuous space.
--
--   **Formalization Note** `GammaZero` uses lower semicontinuity, equivalent here to a closed epigraph. It excludes $-\infty$ and the everywhere $+\infty$ function. `HasOracle` pins a real value before the supporting inequality is used. No arbitrary function value is converted to a real number. The source conjugate is the imported `MoreauProx.Decomposition.conj`, an actual `EReal` supremum.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, Definitions 1–3, pp. 5, 8 (PDF 5, 8); Theorem 3, p. 8 (PDF 8).

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_ConvexDuality
import Definitions.Def_ProxAlg_FixedPoint_Basic
import Definitions.Def_TaylorHG_PEP_Interp

namespace TaylorHGAudit.PEP

/-- Continuous Euclidean space; the dimension is never a discretization of the domain. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Definition 1, p. 5: reciprocal smoothness, including `1/∞ = 0`.
Only used at `0 < L`; `toReal` is applied to a finite reciprocal, never to a function value. -/
noncomputable def invL (L : ENNReal) : ℝ := (L⁻¹).toReal

/-- Minimal curvature subtraction (Theorem 3, p. 8). Only a finite real is subtracted. -/
noncomputable def subtractCurvature {d : ℕ} (μ : NNReal) (F : E d → EReal) : E d → EReal :=
  fun x => F x - (((μ : ℝ) / 2 * ‖x‖ ^ 2 : ℝ) : EReal)

/-- Definition 1, p. 5, over the full proper closed extended-valued class.
`GammaZero` is the published proper/lower-semicontinuous/convex-epigraph predicate;
in finite-dimensional Euclidean space this is precisely the nonempty closed convex epigraph
convention of the source. Parameters satisfy `μ < L` in each theorem. -/
def FClass {d : ℕ} (μ : NNReal) (L : ENNReal) (F : E d → EReal) : Prop :=
  MoreauProx.Decomposition.GammaZero F ∧
  (∀ x₁ x₂ g₁ g₂,
    g₁ ∈ ProxAlg.FixedPoint.subdifferential F x₁ →
    g₂ ∈ ProxAlg.FixedPoint.subdifferential F x₂ →
    invL L * ‖g₁ - g₂‖ ≤ ‖x₁ - x₂‖) ∧
  Convex ℝ {p : E d × ℝ | subtractCurvature μ F p.1 ≤ (p.2 : EReal)}

/-- A finite-valued oracle response, with the genuine global supporting inequality.
No value of an arbitrary extended-valued function is converted to a real number. -/
def HasOracle {d : ℕ} (F : E d → EReal) (x g : E d) (v : ℝ) : Prop :=
  F x = (v : EReal) ∧ g ∈ ProxAlg.FixedPoint.subdifferential F x

/-- Definition 2, p. 5: one source-class function realizes all finite triples.
This definition contains no interpolation inequalities or realization assumption. -/
def Interpolable {d : ℕ} {ι : Type*} [Fintype ι] (μ : NNReal) (L : ENNReal)
    (x g : ι → E d) (v : ι → ℝ) : Prop :=
  ∃ F : E d → EReal, FClass μ L F ∧ ∀ i, HasOracle F (x i) (g i) (v i)

/-- The explicit embedding used for published real-valued interpolation witnesses.
It is an adapter of witnesses, not a restriction on source-class functions. -/
def realLift {d : ℕ} (f : E d → ℝ) : E d → EReal := fun x => (f x : EReal)

end TaylorHGAudit.PEP


