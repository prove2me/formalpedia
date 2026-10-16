-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
-- name    : OAI_Geometry_ConjugatePoints_Returning
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:23:19.98864+00:00
-- url     : https://prove2.me/theorems/1866ec09-ffae-45c5-ab75-dd107601c999
-- title:
--   Index densities, turning fields and potentials for geodesics returning through the neck
-- statement:
--   This file defines the quantities used to bound the index form along geodesic segments that enter the neck of the three-manifold and return: an index-form density for normal fields, energy densities, turning fields, and the potential and force of the reduced one-dimensional motion.
--
--   **Notation.** Vectors $U = (U_1, U_2) \in \mathbb{R} \times \mathbb{R}^2$; for a real $2\times 2$ matrix $A$ and $u, v \in \mathbb{R}^2$, $\langle u, v\rangle_A = u \cdot (Av)$. For $2 \times 2$ matrices $Q, P, A, B$ (in applications: the torus metric $Q$, $P = Q^{-1}$, $A = Q'$, $B = Q''$ for a neck metric $dt^2 + Q(t)$) put
--   $$
--   \langle U, V\rangle_Q = U_1V_1 + \langle U_2, V_2\rangle_Q, \qquad \Gamma(U,V) = \Bigl(-\tfrac12\langle U_2,V_2\rangle_A,\ \tfrac12\bigl(U_1\,PAV_2 + V_1\,PAU_2\bigr)\Bigr),
--   $$
--   $\Gamma'(U,V) = \bigl(-\tfrac12\langle U_2,V_2\rangle_B,\ \tfrac12(U_1 (PB-PAPA)V_2 + V_1(PB-PAPA)U_2)\bigr)$ and $R(U,V)W = U_1\Gamma'(V,W) - V_1\Gamma'(U,W) + \Gamma(U,\Gamma(V,W)) - \Gamma(V,\Gamma(U,W))$. The neck profile functions are $a(u) = e^{-1/(2/3-u)}$ for $u < 2/3$ and $a(u) = 0$ otherwise, $A(u) = \int_0^u a$, and $\chi(t) = \psi(6(t - 5/12))$ with $\psi$ the standard smooth transition function ($0$ on $(-\infty,0]$, $1$ on $[1,\infty)$). For $\delta \in \mathbb{R}$, with $d_1 = 1 + \delta A(u)$, $d_2 = 1 + \delta A(1-u)$, $\sigma = \delta^2\chi(u)$, the left coordinate cometric is $C^{\mathrm{L}}_\delta(u) = \begin{pmatrix} d_1 + d_2\sigma^2 & d_2\sigma \\ d_2\sigma & d_2\end{pmatrix}$ and the right one is $C^{\mathrm{R}}_\delta(u) = K\, C^{\mathrm{L}}_\delta(1-u)\, K^{\mathsf T}$ with $K = \begin{pmatrix} 0 & 1 \\ 1 & -\delta^2\end{pmatrix}$; below $C$ denotes either of them.
--
--   1. **Normal index density.** For $T, V, D \in \mathbb{R}\times\mathbb{R}^2$, with $\nabla = D + \Gamma(T, V)$,
--   $$
--   \mathcal{N}(P,Q,A,B;\,T,V,D) = \langle \nabla, \nabla\rangle_Q - \bigl\langle V,\ R(V,T)T\bigr\rangle_Q - \langle \nabla, T\rangle_Q^2 .
--   $$
--   2. **Turning constants.** $\beta = \tfrac12\bigl(1 + e^{-9/26}\bigr)$, $a_0 = e^{-3/2}$, and for $C_e, C_m \in \mathbb{R}$ the parameter $\delta$ is *small* if $0 < \delta \le 1$, $\delta \le \frac{1}{2C_m}$ and $\delta \le \frac{1 - \beta}{2C_m + C_e a_0}$.
--   3. **Direct energy density.** For functions $Q : \mathbb{R} \to \mathbb{R}^{2\times 2}$, $k, z' : \mathbb{R} \to \mathbb{R}^2$ and $h, w, w' : \mathbb{R} \to \mathbb{R}$: $E(s) = \langle z'(s) - w(s)k(s),\ z'(s) - w(s)k(s)\rangle_{Q(s)} + w'(s)^2 + h(s)\,w(s)^2$.
--   4. **Auxiliary objects.** The vector $e = (1, 0) \in \mathbb{R}^2$; for $F_1 : \mathbb{R} \to \mathbb{R}$ the planar vector field $(x_1, x_2) \mapsto (x_2, -F_1(x_1)/2)$; and the constant $S(c) = a(0) + \sqrt{2c\,a(0)} + 2\sqrt{2c\,a(0)/3}$.
--   5. **Potential and force.** For a momentum $p \in \mathbb{R}^2$: potential $p \cdot C(u)p$, force $p \cdot C'(u)p$ and force derivative $p\cdot C''(u)p$.
--   6. **Turning field.** For $L, v_0 \in \mathbb{R}$, curves $V, T : \mathbb{R} \to \mathbb{R}\times\mathbb{R}^2$ and $Q : \mathbb{R} \to \mathbb{R}^{2\times 2}$, let $q(r) = \langle V(r), T(r)\rangle_{Q(r)}$ and
--   $$
--   \alpha(s) = q(0) - \frac{V_1(0)}{v_0} + \frac{s}{L}\Bigl[\Bigl(q(L) + \frac{V_1(L)}{v_0}\Bigr) - \Bigl(q(0) - \frac{V_1(0)}{v_0}\Bigr)\Bigr],
--   $$
--   the affine interpolation; the turning change is $\theta(s) = \alpha(s) - q(s)$ and the turning field is $V(s) + \theta(s)\,T(s)$.
--   7. **Returning passage.** The metric of the passage is $C(u)^{-1}$. For curves $t, v : \mathbb{R} \to \mathbb{R}$ (height and height velocity) the momentum velocity is $\dot\gamma(s) = (v(s),\ C(t(s))\,p)$, and for $V, D : \mathbb{R} \to \mathbb{R}\times\mathbb{R}^2$ the return normal density at $s$ is $\mathcal N$ evaluated at $P = C(t(s))$, $Q = C(t(s))^{-1}$, $A = (C^{-1})'(t(s))$, $B = (C^{-1})''(t(s))$, $T = \dot\gamma(s)$, $V = V(s)$, $D = D(s)$.
--
--   In a neck metric $dt^2 + C(t)^{-1}$ the torus momentum $p$ of a geodesic is conserved, so its velocity has the form $(t', C(t)p)$; the potential and force describe the resulting one-dimensional height motion, and the densities and turning fields above are the integrands and test fields used to bound the index form along geodesic segments that enter the neck and return.
--
--   **Formalization Note** The Lean names are `Neck.normalDensity`, `Turning.beta`, `aZero`, `SmallParameter Ce Cm δ`, `DirectTurning.energyDensity`, `ReturningCoefficients.e`, `PassageDynamics.scalarVectorField`, `ReturningPassage.potential`, `force`, `forceDerivative`, `sourceMixed`, `Neck.turningAffine`, `turningChange`, `turningField`, `ReturningPassage.metricInverse`, `momentumVelocity`, `returnNormalDensity`; the side is a Boolean `right` selecting `coordinateCometric right δ`. Derivatives of $C$ and $C^{-1}$ are `deriv`, and $C^{-1}$ is Mathlib's matrix inverse ($0$ for a singular matrix). All divisions (by $v_0$, $L$, $2C_m$ and $2C_m + C_e a_0$) follow Lean's convention $x/0 = 0$, and $\sqrt{\cdot}$ is `Real.sqrt` ($0$ on negative arguments).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/Returning.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/Returning.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates

namespace OAI

noncomputable section

/-!
# Returning neck geodesics, passage dynamics, and index bounds.
-/

open Set Manifold Bundle Filter Topology
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.Neck
open Matrix
open scoped Matrix.Norms.Elementwise

def normalDensity (P Q A B : TMat) (T V D : Vec) : ℝ :=
  metric Q (D + gamma P A T V) (D + gamma P A T V) -
    metric Q V (curvatureJet P A B V T T) -
    (metric Q (D + gamma P A T V) T) ^ 2

end ThreeManifold.Neck

namespace ThreeManifold.Turning

def beta : ℝ := (1 + Real.exp (-(9 : ℝ) / 26)) / 2

def aZero : ℝ := Real.exp (-(3 : ℝ) / 2)

def SmallParameter (Ce Cm δ : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧ δ ≤ 1 / (2 * Cm) ∧
    δ ≤ (1 - beta) / (2 * Cm + Ce * aZero)

end ThreeManifold.Turning

namespace ThreeManifold.DirectTurning

section
open Set MeasureTheory Neck Matrix
open scoped Interval Topology

end

open Neck Matrix Set MeasureTheory Turning
open scoped Interval Topology Matrix.Norms.Elementwise

def energyDensity (Q : ℝ → TMat) (k : ℝ → TVec) (h : ℝ → ℝ)
    (z' : ℝ → TVec) (w w' : ℝ → ℝ) (s : ℝ) : ℝ :=
  pairing (Q s) (z' s - w s • k s) (z' s - w s • k s) + w' s ^ 2 + h s * w s ^ 2

end ThreeManifold.DirectTurning

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningTime

end ThreeManifold.ReturningTime

open Set MeasureTheory
open scoped Interval
namespace ThreeManifold.ReturningCoefficients
open Neck Matrix

end ThreeManifold.ReturningCoefficients

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck Matrix

end ThreeManifold.Cometric

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningCoefficients
open Neck Cometric Matrix

def e : TVec := ![1, 0]

end ThreeManifold.ReturningCoefficients

open Set Filter
open scoped Topology ContDiff
namespace ThreeManifold.PassageDynamics

def scalarVectorField (F₁ : ℝ → ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (x.2, -F₁ x.1 / 2)

end ThreeManifold.PassageDynamics

open Set MeasureTheory
open scoped Interval Topology ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage

section
-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix
open Neck Cometric ReturningCoefficients PassageDynamics Matrix

def potential (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) : ℝ :=
  pairing (coordinateCometric right δ u) p p

def force (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) : ℝ :=
  pairing (deriv (coordinateCometric right δ) u) p p

def forceDerivative (right : Bool) (δ : ℝ) (p : TVec) (u : ℝ) : ℝ :=
  pairing (deriv (deriv (coordinateCometric right δ)) u) p p

end

-- [generator] trimmed: open Neck Cometric ReturningCoefficients ReturningTime PassageDynamics Matrix DirectTurning Turning
open Neck Cometric ReturningCoefficients PassageDynamics Matrix DirectTurning Turning

def sourceMixed (C : ℝ) : ℝ := a 0 + Real.sqrt (2 * C * a 0) + 2 * Real.sqrt (2 * C * a 0 / 3)

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck

section
open Set Matrix MeasureTheory
open scoped ContDiff Interval Topology Matrix.Norms.Elementwise

def turningAffine (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) (s : ℝ) : ℝ :=
  let q := fun r => metric (Q r) (V r) (T r)
  q 0 - (V 0).1 / v₀ + s / L *
    ((q L + (V L).1 / v₀) - (q 0 - (V 0).1 / v₀))

def turningChange (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) (s : ℝ) : ℝ :=
  turningAffine L v₀ V T Q s - metric (Q s) (V s) (T s)

def turningField (L v₀ : ℝ) (V T : ℝ → Vec) (Q : ℝ → TMat) (s : ℝ) : Vec :=
  V s + turningChange L v₀ V T Q s • T s

end

section
open Set Matrix Filter
open scoped ContDiff Topology Matrix.Norms.Elementwise

end

open Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

def metricInverse (right : Bool) (δ u : ℝ) : TMat := (coordinateCometric right δ u)⁻¹

def momentumVelocity (right : Bool) (δ : ℝ) (p : TVec) (t v : ℝ → ℝ) (s : ℝ) : Vec :=
  (v s, coordinateCometric right δ (t s) *ᵥ p)

end

section
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning
open scoped ContDiff Topology Matrix.Norms.Elementwise

def returnNormalDensity (right : Bool) (δ : ℝ) (p : TVec) (t v : ℝ → ℝ)
    (V D : ℝ → Vec) (s : ℝ) : ℝ :=
  normalDensity (coordinateCometric right δ (t s)) (metricInverse right δ (t s))
    (deriv (metricInverse right δ) (t s)) (deriv (deriv (metricInverse right δ)) (t s))
    (momentumVelocity right δ p t v s) (V s) (D s)

end

open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

namespace ThreeManifold.Neck
open Set Matrix MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.Neck

namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning Set Matrix Filter MeasureTheory DirectTurning ReturningCoefficients
open scoped ContDiff Topology Matrix.Norms.Elementwise

end ThreeManifold.ReturningPassage

end

end OAI


