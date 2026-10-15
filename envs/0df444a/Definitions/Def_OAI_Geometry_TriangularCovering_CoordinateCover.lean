-- Prove2me | Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
-- name    : OAI_Geometry_TriangularCovering_CoordinateCover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:35:30.897574+00:00
-- url     : https://prove2.me/theorems/61c12b66-850e-4573-aac8-c09f7cf67abf
-- title:
--   Secant coefficients, uniform mesh and sector-and-cutoff conditions for a tilted-cylinder cover of the tetrahedron
-- statement:
--   This file fixes the scalar data of an explicit covering of the tetrahedron
--   $$
--   K=\{(x,y,\sqrt2\,t):\ 0\le t\le1,\ |x|\le1-t,\ |y|\le t\}\subset\mathbb{R}^3
--   $$
--   by tilted triangular cylinders. Points of $K$ are described by the coordinates $(x,y,t)$, and all objects below are real-valued functions of real or natural-number parameters.
--
--   1. **Margin.** The constant $\eta=1/1000$.
--   2. **Secant coefficients.** For $a,b\in\mathbb{R}$,
--   $$
--   \alpha(a,b)=\frac{1+ab}{4},\qquad \beta(a,b)=\frac{a+b}{4}.
--   $$
--   The affine function $m\mapsto\alpha(a,b)-m\,\beta(a,b)$ is the secant of the parabola $m\mapsto(1-m^2)/4$ through $m=a$ and $m=b$.
--   3. **Quartic weight and cutoff coefficient.**
--   $$
--   d(q)=\frac{q^2(1+q^2)}{16},\qquad M(a,b)=\eta+\max\{d(a),d(b)\}.
--   $$
--   4. **Uniform mesh.** For $N\in\mathbb{N}$ the step is $h_N=2/N$ and the mesh points are $m_{N,i}=-1+i\,h_N$ for $i\in\mathbb{N}$. Included facts: for $N\ge1$, $h_N>0$ and $m_{N,N}=1$; for every $N$, $m_{N,0}=-1$ and $m_{N,i+1}-m_{N,i}=h_N$.
--   5. **Sector predicate.** $\mathrm{Sector}(a,b,\rho,z)$ means $0\le\rho$ and $a\rho\le z\le b\rho$, i.e. the point $(\rho,z)$ lies in the closed planar cone between the rays $z=a\rho$ and $z=b\rho$, $\rho\ge0$.
--   6. **Cutoff height.** $T_\varepsilon(a,b)=\frac12+\varepsilon^2M(a,b)$.
--   7. **Lower and upper hits.** Fix $N,j\in\mathbb{N}$ and $\varepsilon,x,y,t\in\mathbb{R}$, and put $a=m_{N,j}$, $b=m_{N,j+1}$. The *lower hit* condition $\mathrm{LowerHit}(N,j,\varepsilon,x,y,t)$ says that $\rho=t-\varepsilon x\,\beta(a,b)$ and $Y=y-\varepsilon x\,\alpha(a,b)$ satisfy $\mathrm{Sector}(a,b,\rho,Y)$ and $\rho\le T_\varepsilon(a,b)$, that is
--   $$
--   0\le\rho\le T_\varepsilon(a,b),\qquad a\rho\le Y\le b\rho .
--   $$
--   The *upper hit* condition $\mathrm{UpperHit}(N,j,\varepsilon,x,y,t)$ says the same for $\sigma=1-t+\varepsilon y\,\beta(a,b)$ and $X=x+\varepsilon y\,\alpha(a,b)$:
--   $$
--   0\le\sigma\le T_\varepsilon(a,b),\qquad a\sigma\le X\le b\sigma .
--   $$
--   8. **Speed and normalized area term.**
--   $$
--   S(a,b)=\alpha(a,b)^2+2\beta(a,b)^2,\qquad \nu_\varepsilon(a,b)=\frac{(b-a)\,T_\varepsilon(a,b)^2}{\sqrt{1+\varepsilon^2S(a,b)}} .
--   $$
--   The file also records that $\lceil 2/\varepsilon^2\rceil\ge1$ for every $\varepsilon>0$.
--
--   The lower hit condition is the coordinate form of membership of $(x,y,\sqrt2t)$ in a lower cylinder: moving from this point along the direction $(1,\varepsilon\alpha,\sqrt2\varepsilon\beta)$ back to the plane $x=0$ gives the point $(0,Y,\sqrt2\rho)$, which must lie in the triangle with apex at the origin, side slopes $a,b$ and height $T_\varepsilon(a,b)$. The upper hit condition is the analogue for cylinders in direction $(-\varepsilon\alpha,1,\sqrt2\varepsilon\beta)$ whose base triangle lies in the plane $y=0$ with apex $(0,0,\sqrt2)$. The quantity $\sqrt2\,\nu_\varepsilon(a,b)$ is the combined base area of the lower and the upper cylinder attached to the mesh cell $[a,b]$, so the total base area of the whole family is $\sqrt2\sum_j\nu_\varepsilon(m_{N,j},m_{N,j+1})$.
--
--   **Formalization Note** The Lean names are `η`, `alpha`, `beta`, `d`, `cutoffCoeff` ($M$), `step` ($h_N$), `mesh`, `Sector`, `cutoff` ($T_\varepsilon$), `LowerHit`, `UpperHit`, `speedSq` ($S$) and `normalizedTerm` ($\nu_\varepsilon$); the small facts are `step_pos`, `mesh_zero`, `mesh_last`, `mesh_succ` and `ceil_count_pos` (with the natural-number ceiling). Since Lean's division by zero returns $0$, the step for $N=0$ is $0$; every result about the mesh assumes $N\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularCovering

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def η : ℝ := 1 / 1000

def alpha (a b : ℝ) : ℝ := (1 + a * b) / 4

def beta (a b : ℝ) : ℝ := (a + b) / 4

def d (q : ℝ) : ℝ := q ^ 2 * (1 + q ^ 2) / 16

def cutoffCoeff (a b : ℝ) : ℝ := η + max (d a) (d b)

def step (N : ℕ) : ℝ := 2 / N

def mesh (N i : ℕ) : ℝ := -1 + i * step N

theorem step_pos {N : ℕ} (hN : 0 < N) : 0 < step N := by
  unfold step
  exact div_pos (by norm_num) (by exact_mod_cast hN)

@[simp] theorem mesh_zero (N : ℕ) : mesh N 0 = -1 := by simp [mesh]

@[simp] theorem mesh_last {N : ℕ} (hN : 0 < N) : mesh N N = 1 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  dsimp [mesh, step]
  field_simp
  ring

theorem mesh_succ (N j : ℕ) : mesh N (j + 1) - mesh N j = step N := by
  simp [mesh]
  ring

/-- Both closed angular inequalities, including a nonnegative radial coordinate. -/
def Sector (a b r z : ℝ) : Prop := 0 ≤ r ∧ a * r ≤ z ∧ z ≤ b * r

def cutoff (ε a b : ℝ) : ℝ := 1 / 2 + ε ^ 2 * cutoffCoeff a b

/-- Coordinate form of membership in the first intercept cylinder. -/
def LowerHit (N j : ℕ) (ε x y t : ℝ) : Prop :=
  Sector (mesh N j) (mesh N (j + 1))
    (t - ε * x * beta (mesh N j) (mesh N (j + 1)))
    (y - ε * x * alpha (mesh N j) (mesh N (j + 1))) ∧
  t - ε * x * beta (mesh N j) (mesh N (j + 1)) ≤ cutoff ε (mesh N j) (mesh N (j + 1))

/-- Coordinate form of membership in the second intercept cylinder. -/
def UpperHit (N j : ℕ) (ε x y t : ℝ) : Prop :=
  Sector (mesh N j) (mesh N (j + 1))
    (1 - t + ε * y * beta (mesh N j) (mesh N (j + 1)))
    (x + ε * y * alpha (mesh N j) (mesh N (j + 1))) ∧
  1 - t + ε * y * beta (mesh N j) (mesh N (j + 1)) ≤ cutoff ε (mesh N j) (mesh N (j + 1))

theorem ceil_count_pos {ε : ℝ} (he : 0 < ε) : 0 < ⌈2 / ε ^ 2⌉₊ := by
  rw [Nat.ceil_pos]
  positivity

end TriangularCovering

namespace TriangularCovering

def speedSq (a b : ℝ) : ℝ := (alpha a b)^2 + 2*(beta a b)^2

def normalizedTerm (ε a b : ℝ) : ℝ :=
  (b-a) * (cutoff ε a b)^2 / Real.sqrt (1+ε^2*speedSq a b)

end TriangularCovering

end

end OAI


