-- Prove2me | Definitions.Def_BallPolyApprox_VertexBudget_RandomPolytope
-- name    : BallPolyApprox_VertexBudget_RandomPolytope
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:54:26.057264+00:00
-- url     : https://prove2.me/theorems/2ccfb4af-ea10-4f54-b99d-c420942b65fc
-- title:
--   Random antipodal polytope, $G_d$, $R_{d,M}$, $\mathbb E\Delta_d(R_{d,M}^{-1}P)$, the boundary law $\nu$ (38), the height $H$ and its law, $L$, $L_0$ and $t_0$ (40)
-- statement:
--   Let $U_1,\dots,U_M$ be independent and uniform on $S^{d-1}$ ($\sigma$ the normalized surface measure) and $P=\operatorname{conv}\{\pm U_i:i\le M\}$. Set
--   $$G_d(t)=\sigma\{u\in S^{d-1}:u_1^2\le t\},\qquad G_d'(t)=\frac{t^{-1/2}(1-t)^{(d-3)/2}}{B(\tfrac12,\tfrac{d-1}2)}.$$
--   With $\kappa_d=|B_d|$, the **volume-balancing radius** $R_{d,M}$ is defined by $R_{d,M}^d\kappa_d=\mathbb E|P|$, and $\mathbb E\Delta_d(R_{d,M}^{-1}P)$ is the expected error of the rescaled polytope.
--
--   **Boundary law** (38): $\mathbb E_\nu f(Y)=\mathbb E\big[\sum_{F\text{ facet of }P}|\operatorname{conv}\{o,F\}|\frac1{|F|}\int_Ff(y)\,dy\big]/\mathbb E|P|$. $H$ is the squared distance from the origin of the supporting hyperplane of the facet containing $Y$.
--
--   **Height law.** $H$ has density proportional to $(1-t)^{d(d-1)/2-1}G_d(t)^{M-d}$ on $(0,1)$. $L=-\log(1-H)$, $L_0$ is the mode of the density of $L$, and $t_0=1-e^{-L_0}$; $t_0$ is the solution in $(0,1)$ of the **mode equation**
--   $$(M-d)(1-t_0)\frac{G_d'(t_0)}{G_d(t_0)}=\frac{d(d-1)}2\quad(40),$$
--   unique because the left side decreases strictly from $\infty$ to $0$.
--
--   **Formalization Note.** $\sigma$ is the published `RGGDetect.unifSphere d`. Expectations of nonnegative quantities are lower Lebesgue integrals (`∫⁻`, values in $[0,\infty]$). $\nu$ uses the gauge encoding: $\mathbb E_\nu f(P,Y)=\mathbb E\big[\int_Pf(P,x/\|x\|_P)\,dx\big]/\mathbb E|P|$ with $\|\cdot\|_P$ the gauge of $P$. This equals (38) because $P$ contains the origin in its interior almost surely and the radial projection of a uniform point of the cone $\operatorname{conv}\{o,F\}$ onto $F$ is uniform on $F$. The test function may depend on the realization $P$, which is how $H$ enters. $H$ at a boundary point $y$ is $1/|a|^2$ for the supporting hyperplane $\{z:\langle a,z\rangle=1\}$ at $y$ (`supportSqDist`, a supremum, which is attained by the unique hyperplane for $\nu$-a.e. $y$). `lawH d M` is the normalized density on $(0,1)$; $M-d$ is natural subtraction, used only with $M\ge2d$. `modeT0` is the root of (40), chosen by choice ($0$ if there is none). $B(a,b)=\Gamma(a)\Gamma(b)/\Gamma(a+b)$.
-- source:
--   Gorodzha, Hoehner, Kur, Approximating the Euclidean Ball by Polytopes, arXiv:2610.34651 (sha256 164dc885…), §5.3.1, (38)–(40), pp. 16–17 (PDF 18–19)

import Mathlib
import Definitions.Def_RGGDetect_unifSphere
import Definitions.Def_BallPolyApprox_VertexBudget_VolumeError

set_option autoImplicit false

open MeasureTheory
open scoped Pointwise

namespace BallPolyApprox.VertexBudget

noncomputable section

/-!
# The random antipodal polytope, its boundary law `ν`, and the height law of `H`

Gorodzha, Hoehner, Kur, *Approximating the Euclidean Ball by Polytopes*, arXiv:2610.34651
(sha256 164dc885…), §5.3.1, (38)–(40), pp. 16–17 (PDF 18–19).

`U_1, …, U_M` are independent uniform on `S^{d−1}` (normalized surface measure `σ`, the published
`RGGDetect.unifSphere d`) and `P = conv{±U_i : i ≤ M}`.
`G_d(t) = σ{u ∈ S^{d−1} : u_1² ≤ t}` and `G'_d(t) = t^{−1/2}(1 − t)^{(d−3)/2} / B(1/2, (d−1)/2)`.
`κ_d = |B_d|`, and the volume-balancing radius `R_{d,M}` is defined by `R_{d,M}^d κ_d = E|P|`.

**Boundary law (38), gauge encoding.** For a test function `f ≥ 0` of the polytope and a boundary
point, `E_ν f(Y) = E[∫_P f(x/‖x‖_P) dx] / E|P|`, where `‖x‖_P` is the gauge of `P`. Since `P`
contains the origin in its interior almost surely, and radial projection of a uniform point of the
cone `conv{o, F}` onto the facet `F` is uniform on `F`, this equals
`E[Σ_F |conv{o, F}| (1/|F|) ∫_F f(y) dy] / E|P|` of (38).

`H` is the squared distance from the origin of the supporting hyperplane of `P` at the boundary
point `Y`; writing that hyperplane as `{z : ⟨a, z⟩ = 1}` (it misses the origin), `H = 1/|a|²`. For
`ν`-almost every `Y` (relative interiors of facets) the hyperplane is unique.

The density of `H` is proportional to `(1 − t)^{d(d−1)/2 − 1} G_d(t)^{M−d}` on `(0, 1)`;
`L = −log(1 − H)`, `L_0` is the mode of the density of `L`, and `t_0 = 1 − e^{−L_0}`, which is the
unique solution in `(0, 1)` of the mode equation
`(M − d)(1 − t_0) G'_d(t_0) / G_d(t_0) = d(d − 1)/2` (40).
-/

/-- The first coordinate `u_1` of a point of `ℝ^d` (`0` when `d = 0`). -/
def firstCoord {d : ℕ} (u : Rd d) : ℝ := if h : 0 < d then u ⟨0, h⟩ else 0

/-- `G_d(t) = σ{u ∈ S^{d−1} : u_1² ≤ t}`. -/
def Gd (d : ℕ) (t : ℝ) : ℝ :=
  (RGGDetect.unifSphere d).real {u | firstCoord (u : Rd d) ^ 2 ≤ t}

/-- The Beta function `B(a, b) = Γ(a)Γ(b)/Γ(a + b)`. -/
def betaFn (a b : ℝ) : ℝ := Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)

/-- `G'_d(t) = t^{−1/2}(1 − t)^{(d−3)/2} / B(1/2, (d−1)/2)`, the density of `u_1²`. -/
def GdDeriv (d : ℕ) (t : ℝ) : ℝ :=
  t ^ (-(1 : ℝ) / 2) * (1 - t) ^ (((d : ℝ) - 3) / 2) / betaFn (1 / 2) (((d : ℝ) - 1) / 2)

/-- `M` independent uniform points `U_1, …, U_M` of `S^{d−1}`. -/
def sphereSample (d M : ℕ) : Measure (Fin M → RGGDetect.Sph d) :=
  Measure.pi fun _ => RGGDetect.unifSphere d

/-- The vertex set `{±U_i : i ≤ M}`. -/
def antipodalVerts {d M : ℕ} (U : Fin M → RGGDetect.Sph d) : Finset (Rd d) := by
  classical
  exact Finset.univ.image (fun i => (U i : Rd d)) ∪ Finset.univ.image (fun i => -(U i : Rd d))

/-- The random antipodal polytope `P = conv{±U_i : i ≤ M}`. -/
def antipodalPolytope {d M : ℕ} (U : Fin M → RGGDetect.Sph d) : Set (Rd d) :=
  polytope (antipodalVerts U)

/-- `E|P|`, the expected volume of the random antipodal polytope. -/
def expVol (d M : ℕ) : ENNReal :=
  ∫⁻ U, volume (antipodalPolytope U) ∂sphereSample d M

/-- `κ_d = |B_d|`. -/
def ballVol (d : ℕ) : ℝ := (volume (unitBall d)).toReal

/-- The volume-balancing radius `R_{d,M}`: `R_{d,M}^d κ_d = E|P|`. -/
def balancingRadius (d M : ℕ) : ℝ :=
  ((expVol d M).toReal / ballVol d) ^ (1 / (d : ℝ))

/-- `E Δ_d(R_{d,M}^{−1} P)`, the expected relative volume error of the rescaled random polytope. -/
def expErrScaled (d M : ℕ) : ENNReal :=
  ∫⁻ U, ENNReal.ofReal (ballErr ((balancingRadius d M)⁻¹ • antipodalPolytope U)) ∂sphereSample d M

/-- Radial projection `x ↦ x / ‖x‖_P` of a point onto the boundary of `P`, with `‖·‖_P` the gauge
(Minkowski functional) of `P`. -/
def radialProj {d : ℕ} (P : Set (Rd d)) (x : Rd d) : Rd d := (gauge P x)⁻¹ • x

/-- `H`: the squared distance from the origin of the supporting hyperplane `{z : ⟨a, z⟩ = 1}` of
`P` at the boundary point `y`, i.e. `1/|a|²` (the supremum over supporting hyperplanes at `y`,
which is unique for `y` in the relative interior of a facet). -/
def supportSqDist {d : ℕ} (P : Set (Rd d)) (y : Rd d) : ℝ :=
  sSup {h : ℝ | ∃ a : Rd d, (∀ x ∈ P, inner ℝ a x ≤ 1) ∧ inner ℝ a y = 1 ∧ h = 1 / ‖a‖ ^ 2}

/-- The boundary law `ν` of (38), as the expectation `E_ν f(P, Y)` of a test function
`f ≥ 0` of the realization `P` and the boundary point `Y`:
`E[∫_P f(P, x/‖x‖_P) dx] / E|P|` (gauge encoding of `E[Σ_F |conv{o,F}| (1/|F|) ∫_F f] / E|P|`). -/
def nuExp (d M : ℕ) (f : Set (Rd d) → Rd d → ENNReal) : ENNReal :=
  (∫⁻ U, ∫⁻ x in antipodalPolytope U,
      f (antipodalPolytope U) (radialProj (antipodalPolytope U) x) ∂volume ∂sphereSample d M) /
    expVol d M

/-- The unnormalized density `(1 − t)^{d(d−1)/2 − 1} G_d(t)^{M−d}` of `H` on `(0, 1)`
(used with `M ≥ 2d`, so `M − d` is not truncated). -/
def hDensUnnorm (d M : ℕ) (t : ℝ) : ℝ :=
  (1 - t) ^ ((d : ℝ) * ((d : ℝ) - 1) / 2 - 1) * Gd d t ^ (M - d)

/-- The normalizing constant `∫_0^1 (1 − t)^{d(d−1)/2 − 1} G_d(t)^{M−d} dt`. -/
def hNormConst (d M : ℕ) : ℝ := ∫ t in Set.Ioo (0 : ℝ) 1, hDensUnnorm d M t

/-- The law of `H`: density `hDensUnnorm d M t / hNormConst d M` on `(0, 1)`. -/
def lawH (d M : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity
    fun t => ENNReal.ofReal (hDensUnnorm d M t / hNormConst d M)

/-- The left side of the mode equation (40): `(M − d)(1 − t) G'_d(t) / G_d(t)`. -/
def modeLHS (d M : ℕ) (t : ℝ) : ℝ :=
  ((M : ℝ) - d) * (1 - t) * GdDeriv d t / Gd d t

/-- `t_0 = 1 − e^{−L_0}`: the solution in `(0, 1)` of the mode equation (40),
`(M − d)(1 − t_0) G'_d(t_0)/G_d(t_0) = d(d − 1)/2` (unique, the left side decreasing strictly from
`∞` to `0`; `0` if there is none). -/
def modeT0 (d M : ℕ) : ℝ := by
  classical
  exact if h : ∃ t ∈ Set.Ioo (0 : ℝ) 1, modeLHS d M t = (d : ℝ) * ((d : ℝ) - 1) / 2
    then h.choose else 0

/-- The logarithmic height `L = −log(1 − H)`, as a function of the value `t` of `H`. -/
def logHeight (t : ℝ) : ℝ := -Real.log (1 - t)

/-- `L_0 = −log(1 − t_0)`, the mode of the density of `L = −log(1 − H)`. -/
def modeL0 (d M : ℕ) : ℝ := logHeight (modeT0 d M)

end

end BallPolyApprox.VertexBudget


