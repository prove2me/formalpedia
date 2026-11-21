-- Prove2me | Definitions.Def_TorusEuler_Statement
-- name    : TorusEuler_Statement
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T19:36:56.357242+00:00
-- url     : https://prove2.me/theorems/55540786-bdb0-4d00-b99f-7f28e8af7df4
-- title:
--   Periodic Euler solutions and the singularity witness of Theorem 1.1
-- statement:
--   The definition layer of the main theorem, fixing the function-theoretic setting on the flat torus.
--
--   Write $\mathrm{Vec3} = \mathbb{R}^3$ with its Euclidean norm (`EuclideanSpace ℝ (Fin 3)`), `Velocity` for maps $\mathbb{R}\to\mathbb{R}^3\to\mathbb{R}^3$ and `Pressure` for maps $\mathbb{R}\to\mathbb{R}^3\to\mathbb{R}$. A function is **spatially periodic** (`SpatiallyPeriodic`) if it is invariant under translation by every integer vector; such functions descend to the torus $\mathbb{T}^3 = \mathbb{R}^3/\mathbb{Z}^3$. The **centered cell** is $[-1/2,1/2]^3$, and `offOrigin` is the complement of the integer lattice. For a field $f$, `torusLInf f` is the essential supremum $\|f\|_{L^\infty(\mathrm{cell})}$, valued in $[0,\infty]$. Divergence and curl are defined from the Fréchet derivative: $\operatorname{div} v(x) = \sum_i (Dv(x)e_i)_i$, and $\operatorname{curl} v(x)$ is the usual antisymmetric combination of the entries of $Dv(x)$. The time derivative `timeDerivative T u t x` is the derivative of $r\mapsto u(r,x)$ **within the slab** $[0,T)$.
--
--   `IsEulerSolution T u p` asserts: $T>0$; $u$ and $p$ are $C^\infty$ on $[0,T)\times\mathbb{R}^3$; both are spatially periodic at each time; the pressure has mean zero on the centered cell; and pointwise on the slab,
--   $$\partial_t u + (u\cdot\nabla)u + \nabla p = 0,\qquad \operatorname{div} u = 0.$$
--   `IsMaximalEulerSolution` adds that no smooth periodic Euler solution on a longer slab $[0,S)$, $S>T$, agrees with $u$ on $[0,T)$. `HasOffOriginLimits T f` says that for every compact $K$ disjoint from the lattice and every order $m$, there are an open neighborhood $U\supseteq K$ inside the punctured space and a $C^m$ function $g$ on $U$ such that all spatial jets of order $j\le m$ of $f(t)$ converge uniformly on $K$ to those of $g$ as $t\uparrow T$ within the slab.
--
--   `EulerSingularityWitness u₀ T u p` bundles the conclusions of Theorem 1.1: $u_0$ is smooth, periodic, odd and divergence-free; $(u,p)$ is maximal with $u(0)=u_0$; $u(t)$ is odd; both lintegrals $\int_0^T \|\nabla u(t)\|_\infty\,dt$ and $\int_0^T\|\operatorname{curl}u(t)\|_\infty\,dt$ equal $\infty$; $\|u(t)\|_\infty$ is uniformly bounded; $|\operatorname{curl}u(t,0)|\to\infty$ as $t\uparrow T$; and both $u$ and $\partial_t u$ have off-origin limits. Finally `Theorem11` is the existential statement $\exists u_0\,T\,u\,p,\ \mathrm{EulerSingularityWitness}\ u_0\ T\ u\ p$.
--
--   **Formalization Note** The pressure normalization (mean zero) fixes the additive constant in $p$. All suprema are essential suprema over the centered cell; for the smooth fields involved they agree with ordinary suprema. Time derivatives at both slab endpoints are taken from within the slab.
-- source:
--   Alpöge–Buckmaster–Coiculescu, *Finite-Time Singularity Formation for the Three-Dimensional Euler Equations*, frozen manuscript of 18 November 2026 (torus-paper-freeze-2026-11-18). Lean: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/formalization/lean/TorusEuler/Statement.lean; TeX: https://github.com/mcoiculescu/EulerBlowupPublic/blob/36d3961161f8e7bba9cc8f671e5d0c4a27281239/frozen-manuscript/sections/01_problem.tex (Theorem 1.1, label cc:target:unforced).

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.UniformSpace.UniformConvergence

open Filter MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace TorusEuler

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)
abbrev Velocity := ℝ → Vec3 → Vec3
abbrev Pressure := ℝ → Vec3 → ℝ

def latticeVector (n : Fin 3 → ℤ) : Vec3 :=
  WithLp.toLp 2 (fun i => (n i : ℝ))

/-- Period-one functions in the three spatial coordinates descend to the flat torus. -/
def SpatiallyPeriodic {α : Type*} (f : Vec3 → α) : Prop :=
  ∀ (n : Fin 3 → ℤ) (x : Vec3), f (x + latticeVector n) = f x

def centeredCell : Set Vec3 :=
  {x | ∀ i, x i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)}

def offOrigin : Set Vec3 :=
  (range latticeVector)ᶜ

noncomputable def torusLInf {F : Type*} [NormedAddCommGroup F] (f : Vec3 → F) : ℝ≥0∞ :=
  eLpNormEssSup f (volume.restrict centeredCell)

noncomputable def divergence (v : Vec3 → Vec3) (x : Vec3) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ v x (EuclideanSpace.single i 1)) i

noncomputable def curlOfDerivative (D : Vec3 →L[ℝ] Vec3) : Vec3 :=
  let D₀ := D (EuclideanSpace.single 0 1)
  let D₁ := D (EuclideanSpace.single 1 1)
  let D₂ := D (EuclideanSpace.single 2 1)
  WithLp.toLp 2 ![D₁ 2 - D₂ 1, D₂ 0 - D₀ 2, D₀ 1 - D₁ 0]

noncomputable def curl (v : Vec3 → Vec3) (x : Vec3) : Vec3 :=
  curlOfDerivative (fderiv ℝ v x)

noncomputable def timeDerivative (T : ℝ) (u : Velocity) (t : ℝ) (x : Vec3) : Vec3 :=
  derivWithin (fun r => u r x) (Ico 0 T) t

/-- Smooth Euler flow on the half-open time slab, with mean-zero pressure.
    Derivatives in time at zero are taken from within the slab. -/
structure IsEulerSolution (T : ℝ) (u : Velocity) (p : Pressure) : Prop where
  time_pos : 0 < T
  smooth_velocity : ContDiffOn ℝ ∞ (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set Vec3))
  smooth_pressure : ContDiffOn ℝ ∞ (Function.uncurry p) (Ico 0 T ×ˢ (univ : Set Vec3))
  periodic_velocity : ∀ t ∈ Ico 0 T, SpatiallyPeriodic (u t)
  periodic_pressure : ∀ t ∈ Ico 0 T, SpatiallyPeriodic (p t)
  mean_zero_pressure : ∀ t ∈ Ico 0 T, (∫ x in centeredCell, p t x) = 0
  momentum : ∀ t ∈ Ico 0 T, ∀ x,
    timeDerivative T u t x + fderiv ℝ (u t) x (u t x) + gradient (p t) x = 0
  incompressible : ∀ t ∈ Ico 0 T, ∀ x, divergence (u t) x = 0

/-- The velocity has no smooth Euler continuation to any longer time interval. -/
def IsMaximalEulerSolution (T : ℝ) (u : Velocity) (p : Pressure) : Prop :=
  IsEulerSolution T u p ∧
    ∀ S > T, ¬ ∃ (v : Velocity) (q : Pressure),
      IsEulerSolution S v q ∧ ∀ t ∈ Ico 0 T, v t = u t

/-- Convergence of the ambient spatial jets on compact subsets of the punctured lift. -/
def HasOffOriginLimits (T : ℝ) (f : Velocity) : Prop :=
  ∀ K : Set Vec3, IsCompact K → K ⊆ offOrigin → ∀ m : ℕ,
    ∃ (U : Set Vec3) (g : Vec3 → Vec3),
      IsOpen U ∧ K ⊆ U ∧ U ⊆ offOrigin ∧ ContDiffOn ℝ m g U ∧
        ∀ j ≤ m, TendstoUniformlyOn
          (fun t => iteratedFDeriv ℝ j (f t)) (iteratedFDeriv ℝ j g) (𝓝[Ico 0 T] T) K

/-- The conclusions of Theorem 1.1 for a given Euler solution and initial datum. -/
def EulerSingularityWitness (u₀ : Vec3 → Vec3) (T : ℝ) (u : Velocity) (p : Pressure) : Prop :=
    ContDiff ℝ ∞ u₀ ∧ SpatiallyPeriodic u₀ ∧ Function.Odd u₀ ∧
    (∀ x, divergence u₀ x = 0) ∧
    IsMaximalEulerSolution T u p ∧
    u 0 = u₀ ∧
    (∀ t ∈ Ico 0 T, Function.Odd (u t)) ∧
    (∫⁻ t in Ico 0 T, torusLInf (fderiv ℝ (u t))) = ⊤ ∧
    (∫⁻ t in Ico 0 T, torusLInf (curl (u t))) = ⊤ ∧
    (∃ C : ℝ, ∀ t ∈ Ico 0 T, torusLInf (u t) ≤ ENNReal.ofReal C) ∧
    Tendsto (fun t => ‖curl (u t) 0‖) (𝓝[Ico 0 T] T) atTop ∧
    HasOffOriginLimits T u ∧ HasOffOriginLimits T (timeDerivative T u)

/-- The proposition of frozen Theorem 1.1 (label cc:target:unforced). -/
def Theorem11 : Prop :=
  ∃ (u₀ : Vec3 → Vec3) (T : ℝ) (u : Velocity) (p : Pressure), EulerSingularityWitness u₀ T u p

end TorusEuler


