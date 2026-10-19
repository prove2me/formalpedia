-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_Spreading
-- name    : OAI_Analysis_Littlewood_Spreading
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:02:06.919658+00:00
-- url     : https://prove2.me/theorems/8a514d53-e784-440c-a21b-791b3607db8d
-- title:
--   Multi-index boxes, integer row forms, and the finite Fourier packets produced by spreading
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$, $e(\theta)=e^{2\pi i\theta}$, and for $B,\beta\in\mathbb{R}$ let $\mathrm{Box}(B,\beta)=\{m\in\mathbb{Z}:\ |m|\le\lfloor B|\beta|/2\rfloor\}$ be the one-dimensional box of the quadratic-tail construction. Let $I$ and $J$ be finite index sets.
--
--   1. **Multi-box.** For $B\in\mathbb{R}$ and $\beta\in\mathbb{R}^I$,
--   $$
--   \mathrm{Box}(B,\beta)=\prod_{i\in I}\mathrm{Box}(B,\beta_i)=\{u\in\mathbb{Z}^I:\ |u_i|\le\lfloor B|\beta_i|/2\rfloor\ \text{for all } i\in I\}.
--   $$
--
--   2. **Determinant.** $\Delta(\beta)=\prod_{i\in I}|\beta_i|$, the volume to which the number of points of the multi-box is compared after scaling by $B^{|I|}$.
--
--   3. **Row form.** For $s\in\mathbb{Z}^n$, the real linear functional $\ell_s:\mathbb{R}^n\to\mathbb{R}$, $\ell_s(x)=\sum_{k}s_k x_k$.
--
--   4. **Raw packet data** on $(I,J)$ with parameter $\delta\in\mathbb{R}$: integer frequency vectors $a_i\in\mathbb{Z}^J$ and complex coefficients $c_i$ for $i\in I$, and a velocity $v\in\mathbb{R}^J$. Writing
--   $$
--   F(y)=\sum_{i\in I}c_i\,e\bigl(\langle a_i,y\rangle\bigr)\quad(y\in\mathbb{T}^J),\qquad \lambda_i=\langle a_i,v\rangle=\sum_{j\in J}a_{ij}v_j,
--   $$
--   the data must satisfy: (a) $a_i\ne0$ for every $i$; (b) for $i\ne i'$ there is no real $\tau$ with $a_i=\tau a_{i'}$; (c) $|F(y)+\overline{F(y)}|\le1$, i.e. $|2\operatorname{Re}F(y)|\le1$, for all $y\in\mathbb{T}^J$; (d) $(1-3\delta)^2\le2\sum_{i}|c_i|^2$; (e) $\lambda_i\ne0$ for every $i$; (f) $2\sum_{i}|\lambda_i|<1$; (g) $|c_i|^2\le\frac{(1+\delta)^3}{1-\delta}\,|\lambda_i|$ for every $i$.
--
--   5. **Finite packet.** A finite packet with parameter $\delta$ consists of finite index sets $I$ (nonempty) and $J$ together with raw packet data on $(I,J)$.
--
--   A packet describes the real trigonometric polynomial $2\operatorname{Re}F$ on the torus $\mathbb{T}^J$, which by (c) is bounded by $1$; by (a), (b) and Parseval its mean square is $2\sum_i|c_i|^2$, which (d) makes at least $(1-3\delta)^2$. Each frequency carries a nonzero curvature $\lambda_i$ that governs the chirp along which it is later sampled into a sequence of length $N$: condition (f) leaves room to place disjoint signed arcs of lengths proportional to $|\lambda_i|$ on the circle, and for $\delta<1$ condition (g) says $|c_i|/\sqrt{|\lambda_i|}\le\sqrt{(1+\delta)^3/(1-\delta)}$, which becomes the sup-norm constant of the normalized sampled polynomial on the unit circle. The existence of a finite packet for every $0<\delta<1/20$ is the output of the Fourier-spreading construction, assembled from binary polynomials, row forms, multi-boxes and truncated chirps.
--
--   **Formalization Note** `multiBox B β` is `Fintype.piFinset` of the one-dimensional `box`; `determinant β` and `rowForm s` (a `LinearMap`) are as above. `RawData I J δ` is a structure with data fields `frequency`, `coefficient`, `velocity` and proof fields `nonzero`, `nonparallel`, `bounded`, `energy`, `curvature`, `width`, `size`, in the order (a) to (g); the character $e(\langle a_i,y\rangle)$ is `mFourier (frequency i) y` on `J → UnitAddCircle`. `FinitePacket δ` bundles `I J : Type`, their `Fintype` instances, `Nonempty I` and the data, and these fields are registered as instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Spreading.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Spreading.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

universe uI uE uJ uK

namespace AsymptoticallyMinimalLittlewood
namespace Spreading
noncomputable section
open QuadraticTail MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff FourierTransform SchwartzMap

variable {I : Type uI} [Fintype I] [DecidableEq I]

def multiBox (B : ℝ) (β : I → ℝ) : Finset (I → ℤ) :=
  Fintype.piFinset (fun i ↦ box B (β i))

def determinant (β : I → ℝ) : ℝ := ∏ i, |β i|

end
end Spreading
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex

def rowForm {n : ℕ} (s : Fin n → ℤ) : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
  ∑ k, (s k : ℝ) • LinearMap.proj k

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

structure RawData (I J : Type) [Fintype I] [Fintype J] (δ : ℝ) where
  frequency : I → J → ℤ
  coefficient : I → ℂ
  velocity : J → ℝ
  nonzero : ∀ i, frequency i ≠ 0
  nonparallel : ∀ i i', i≠i' → ∀ t : ℝ,
    ¬∀ j, (frequency i j : ℝ)=t*(frequency i' j : ℝ)
  bounded : ∀ y : J → UnitAddCircle,
    ‖(∑ i, coefficient i*mFourier (frequency i) y)+
      conj (∑ i, coefficient i*mFourier (frequency i) y)‖≤1
  energy : (1-3*δ)^2 ≤ 2*∑ i, ‖coefficient i‖^2
  curvature : ∀ i, (∑ j, (frequency i j : ℝ)*velocity j)≠0
  width : 2*∑ i, |∑ j, (frequency i j : ℝ)*velocity j| < 1
  size : ∀ i, ‖coefficient i‖^2 ≤ ((1+δ)^3/(1-δ))*
    |∑ j, (frequency i j : ℝ)*velocity j|

structure FinitePacket (δ : ℝ) where
  I : Type
  J : Type
  fintypeI : Fintype I
  fintypeJ : Fintype J
  nonemptyI : Nonempty I
  data : @RawData I J fintypeI fintypeJ δ

attribute [instance] FinitePacket.fintypeI FinitePacket.fintypeJ FinitePacket.nonemptyI

end
end AsymptoticallyMinimalLittlewood.Auxiliary

namespace AsymptoticallyMinimalLittlewood.Auxiliary
noncomputable section
open scoped BigOperators Topology ContDiff ComplexConjugate
open MeasureTheory Filter Finset UnitAddTorus Complex QuadraticTail Spreading

end
end AsymptoticallyMinimalLittlewood.Auxiliary

end OAI


