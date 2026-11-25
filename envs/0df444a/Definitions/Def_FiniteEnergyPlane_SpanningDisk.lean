-- Prove2me | Definitions.Def_FiniteEnergyPlane_SpanningDisk
-- name    : FiniteEnergyPlane_SpanningDisk
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-25T20:33:22.82618+00:00
-- url     : https://prove2.me/theorems/0adcebca-b7e0-4bcc-9393-630014d68e92
-- title:
--   Spanning disks of periodic Reeb orbits and pseudoholomorphic disks with boundary on them
-- statement:
--   Disks in a strictly star-shaped level $S=H^{-1}(1)\subset\mathbb{R}^4$, their characteristic foliation, and pseudoholomorphic disks in the symplectization $\mathbb{R}\times S\cong\mathbb{R}^4\setminus\{0\}$, $y=e^{2a}x$, with boundary on such a disk. The setting is that of `FiniteEnergyPlane_Setting`, `FiniteEnergyPlane_Winding`, `FiniteEnergyPlane_Compactness` and `FiniteEnergyPlane_Fredholm` with $n=1$. A disk in $S$ is given by a smooth map $e:\mathbb{C}\to\mathbb{R}^4$; the surface $\{0\}\times e(D)$ is the set $e(D)\subset\mathbb{R}^4$ itself. Write $D$ for the closed unit disk, $\mathring D$ for the open one, $B_\rho$ for the open disk of radius $\rho$ about $0$, and $P=(x,T)$ for a periodic Reeb orbit.
--
--   1. **`charField e`**, the characteristic field, is the vector field $V$ on the parameter plane with $(ds\wedge dt)(V,\cdot)=e^*\lambda_0$, that is
--   $$V=\lambda_0(\partial_te)-i\,\lambda_0(\partial_se).$$
--   2. **`IsEmbeddedDisk H e ρ`.** $e$ is smooth on $\mathbb{C}$, $\rho>1$, and $e$ maps $B_\rho$ into $S$, injectively and with injective derivative.
--   3. **`HasNicelyEllipticPoint e z₀ ρ`.** $z_0\in\mathring D$ is the only zero of $V$ in $B_\rho$, and there are real $a,b>0$ with $\mathrm{tr}\,DV(z_0)=a+b$ and $\det DV(z_0)=ab$.
--   4. **`LeavesRadiateFrom e z₀`.** Every $z\in D\setminus\{z_0\}$ lies on an integral curve of $V$ on some $(-\infty,b]$, $b\ge0$, passing through $z$ at time $0$, which tends to $z_0$ at $-\infty$, stays in $\mathring D$ before time $b$, and is on the unit circle at time $b$.
--   5. **`SameLeaf e p q`.** An integral curve of $V$ in $D$ joins $p$ and $q$.
--   6. **`diskArea e`** is $\int_{\mathring D}\max(\omega_0(\partial_se,\partial_te),0)\,ds\,dt$.
--   7. **`IsSpecialSpanningDisk H P e z₀`.** For some $\rho$, 2 and 3 hold; $e$ maps the unit circle onto $x(\mathbb{R})$, with $\lambda_0(De(z)\,iz)>0$ for $|z|=1$; 4 holds; there is $\delta>0$ such that $R(e(z))$ is not tangent to the disk for $1-\delta<|z|<1$; and every periodic Reeb orbit contained in $e(D)$ has image $x(\mathbb{R})$.
--   8. **`HasDiskBoundary e z₀ A u c`.** $c$ is a loop in $A\subset\mathbb{C}$ with winding number $1$ around $z_0$, and $u(e^{2\pi it})=e(c(t))$.
--   9. **`IsDiskCurve H J e z₀ A Γ u`.** $\Gamma\subset\mathring D$ is finite; $u$ is smooth on $D\setminus\Gamma$ and avoids $0$; $u$ is $\tilde J$-holomorphic with finite Hofer energy on $\mathring D\setminus\Gamma$; and 8 holds for some $c$.
--   10. **`IsEmbeddedOnDisk Γ u`.** $u$ is injective on $D\setminus\Gamma$ with injective derivative there.
--   11. **`IsEmbeddedHoloDisk H J e z₀ A u`.** 9 and 10 with $\Gamma=\emptyset$.
--   12. **`TendstoCInftyLocWithin f g D N`.** For every compact $K\subset D\setminus N$ and every $m$, the $m$-th derivatives of $f_\nu$ within $D$ converge to those of $g$ uniformly on $K$.
--   13. **`IsXiClose H k ε J J₀`.** All derivatives of $J-J_0$ of order at most $k$ are bounded by $\varepsilon$ at the points of $S$.
--
--   These notions state the boundary value problem for punctured pseudoholomorphic disks and the geometric data under which fast planes are obtained; 1–6 are independent of the symplectization and can be reused for surfaces in star-shaped levels.
--
--   **Formalization Note** In 3, $a$ and $b$ are the eigenvalues of $DV(z_0)$, and $a=b$ is allowed. The zeros of $V$ are the points where the disk is tangent to $\xi$, and the sign of a zero is that of the divergence of $V$, since $d(e^*\lambda_0)=(\operatorname{div}V)\,ds\wedge dt$. Maps on the closed disk are prescribed only there: derivatives at boundary points are derivatives within $D$, and the Cauchy–Riemann equation is imposed in the interior. In 12 the second set is arbitrary and only the closed unit disk is used. In 7 the disk is defined slightly beyond its boundary orbit, as in Hofer–Wysocki–Zehnder (1999), and the property in 4 is the assumption of Hofer–Wysocki–Zehnder that all characteristics emerge from the singular point and leave through the boundary. Hofer–Wysocki–Zehnder moreover prescribe a homotopy class of the disks; on $S\cong S^3$ the winding number of $c$ determines it, since $\pi_2(S^3,F\setminus\{p\})\cong\pi_1(F\setminus\{p\})\cong\mathbb{Z}$ for an embedded disk $F$ and $p\in F$, so it is not restated.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, §§ 3.1–3.2, formulas (19), (32), (33) and Lemma 3.3; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectizations III: Fredholm theory, in Topics in Nonlinear Analysis, Birkhäuser 1999, 381–475, formulas (17)–(18) and Section 11; H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Sections 2 and 3

import Definitions.Def_FiniteEnergyPlane_Fredholm
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace

/-!
# Spanning disks of periodic Reeb orbits and pseudoholomorphic disks with boundary on them

U. Hryniewicz, J. Symplectic Geom. 12 (2014), §§ 3.1–3.2; U. Hryniewicz, Trans. AMS 364 (2012), § 5.2;
H. Hofer, Invent. Math. 114 (1993), § 2.2 and § 3; H. Hofer, K. Wysocki, E. Zehnder, *Properties of
pseudoholomorphic curves in symplectizations III* (1999), § 1 and § 11. Everything is in the setting of
`FiniteEnergyPlane_Setting`, `FiniteEnergyPlane_Winding`, `FiniteEnergyPlane_Compactness` and
`FiniteEnergyPlane_Fredholm` for `n = 1`: `S = H⁻¹(1) ⊂ V 1 = ℝ⁴` strictly star-shaped, and the
symplectization `ℝ × S` is `V 1 \ {0}` with `y = e^{2 aCoord y} • proj y`.

Conventions.
* A disk in `S` is given by a smooth parametrization `e : ℂ → V 1`, used on the closed unit disk and
  slightly beyond it. The surface `{0} × e(D)` of `ℝ × S` is the set `e(D) ⊂ V 1` itself.
* The characteristic field of the disk is transported to the parameter plane: it is the vector field
  `V` on `ℂ` with `(ds ∧ dt)(V, ·) = e*λ₀`. Its zeros are the points where the disk is tangent to `ξ`.
* A map `u` on the closed unit disk is only prescribed there. Smoothness is `ContDiffOn` on the closed
  disk (minus the punctures), derivatives at boundary points are taken within the closed disk, and the
  Cauchy–Riemann equation is imposed in the interior.
* The boundary condition `u(∂D) ⊂ {0} × e(A \ {z₀})`, with winding number `1` around `e(z₀)`, is
  expressed by a loop `c` in the parameter set `A` with `u(e^{2πit}) = e(c(t))`.
-/

namespace FiniteEnergyPlane

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-! ### The characteristic field of a disk -/

/-- The characteristic field of the parametrized surface `e`, on the parameter plane: the vector `V`
with `(ds ∧ dt)(V, w) = λ₀(e z)(De(z) w)` for all `w`, i.e.
`V = λ₀(∂ₜe) - i λ₀(∂ₛe)`. -/
def charField (e : ℂ → V 1) (z : ℂ) : ℂ :=
  ⟨liouville (e z) (dt e z), -liouville (e z) (ds e z)⟩

/-- `e` is a smooth map `ℂ → V 1` that embeds the open disk of radius `ρ > 1` into `S`. -/
def IsEmbeddedDisk (H : V 1 → ℝ) (e : ℂ → V 1) (ρ : ℝ) : Prop :=
  ContDiff ℝ ∞ e ∧ 1 < ρ ∧ Set.MapsTo e (ball 0 ρ) (energySurface H) ∧ Set.InjOn e (ball 0 ρ) ∧
    ∀ z ∈ ball (0 : ℂ) ρ, Function.Injective (fderiv ℝ e z)

/-- On the disk of radius `ρ` the characteristic field of `e` vanishes exactly at `z₀`, which lies in
the open unit disk and is a positive nicely elliptic point: the linearization at `z₀` has trace `a + b`
and determinant `a b` with real `a, b > 0` (its eigenvalues, possibly equal). -/
def HasNicelyEllipticPoint (e : ℂ → V 1) (z₀ : ℂ) (ρ : ℝ) : Prop :=
  z₀ ∈ ball (0 : ℂ) 1 ∧ (∀ z ∈ ball (0 : ℂ) ρ, charField e z = 0 ↔ z = z₀) ∧
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      LinearMap.trace ℝ ℂ (fderiv ℝ (charField e) z₀ : ℂ →ₗ[ℝ] ℂ) = a + b ∧
      LinearMap.det (fderiv ℝ (charField e) z₀ : ℂ →ₗ[ℝ] ℂ) = a * b

/-- Every characteristic leaf of `e` on the closed unit disk issues from `z₀` and reaches the unit
circle: through every point `z ≠ z₀` of the closed disk there is an integral curve `σ` of the
characteristic field on `(-∞, b]`, `b ≥ 0`, with `σ 0 = z`, `σ → z₀` at `-∞`, `σ` in the open
disk before `b`, and `σ b` on the unit circle. -/
def LeavesRadiateFrom (e : ℂ → V 1) (z₀ : ℂ) : Prop :=
  ∀ z ∈ closedBall (0 : ℂ) 1, z ≠ z₀ → ∃ (σ : ℝ → ℂ) (b : ℝ), 0 ≤ b ∧ σ 0 = z ∧
    Tendsto σ atBot (𝓝 z₀) ∧
    (∀ τ ≤ b, HasDerivWithinAt σ (charField e (σ τ)) (Set.Iic b) τ) ∧
    (∀ τ < b, σ τ ∈ ball (0 : ℂ) 1) ∧ σ b ∈ sphere (0 : ℂ) 1

/-- `p` and `q` lie on the same characteristic leaf of `e` in the closed unit disk: some integral
curve of the characteristic field in the closed disk joins them (in one of the two directions). -/
def SameLeaf (e : ℂ → V 1) (p q : ℂ) : Prop :=
  ∃ (σ : ℝ → ℂ) (a b : ℝ), σ a = p ∧ σ b = q ∧ ∀ τ ∈ Set.uIcc a b,
    σ τ ∈ closedBall (0 : ℂ) 1 ∧ HasDerivWithinAt σ (charField e (σ τ)) (Set.uIcc a b) τ

/-- The positive part of the `dλ₀`-area of the disk `e`: `∫_D max(ω₀(∂ₛe, ∂ₜe), 0) ds dt`. -/
def diskArea (e : ℂ → V 1) : ℝ≥0∞ :=
  ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (omega0 (ds e z) (dt e z))

/-- `e` is a special spanning disk for the periodic orbit `P` with singular point `e z₀` (Hryniewicz
(2014), Lemma 3.3, at a fixed contact form; Hofer–Wysocki–Zehnder (1999), § 11):
* `e` embeds a disk slightly larger than the closed unit disk into `S`, and on it the characteristic
  field has exactly one zero `z₀`, in the open unit disk, which is positive and nicely elliptic;
* `e` maps the unit circle onto `x(ℝ)`, in the direction of the Reeb field;
* every characteristic leaf of the closed unit disk issues from `z₀` and reaches the unit circle;
* near the unit circle, inside the open disk, the Reeb field is not tangent to the disk;
* the closed disk contains no periodic Reeb orbit other than `x(ℝ)`. -/
def IsSpecialSpanningDisk (H : V 1 → ℝ) (P : ReebOrbit H) (e : ℂ → V 1) (z₀ : ℂ) : Prop :=
  (∃ ρ : ℝ, IsEmbeddedDisk H e ρ ∧ HasNicelyEllipticPoint e z₀ ρ) ∧
    e '' sphere 0 1 = Set.range P.x ∧
    (∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z))) ∧
    LeavesRadiateFrom e z₀ ∧
    (∃ δ > 0, ∀ z : ℂ, 1 - δ < ‖z‖ → ‖z‖ < 1 → reeb H (e z) ∉ Set.range (fderiv ℝ e z)) ∧
    ∀ Q : ReebOrbit H, Set.range Q.x ⊆ e '' closedBall 0 1 → Set.range Q.x = Set.range P.x

/-! ### Pseudoholomorphic disks with boundary on a disk in `S` -/

/-- The boundary loop of `u` is `t ↦ e(c(t))`, where `c` is a loop in `A` with winding number `1`
around `z₀`. -/
def HasDiskBoundary (e : ℂ → V 1) (z₀ : ℂ) (A : Set ℂ) (u : ℂ → V 1) (c : ℝ → ℂ) : Prop :=
  (∀ t, c t ∈ A ∧ u (ccwLoop 1 t) = e (c t)) ∧ HasLoopWind (fun t => c t - z₀) 1

/-- `u` is a finite-energy `J̃`-holomorphic punctured disk with boundary on the disk `e` (Hofer–Wysocki–
Zehnder (1999), (17)–(18); Hryniewicz (2014), (33)): `Γ` is a finite subset of the open unit disk, `u` is
smooth on the closed unit disk minus `Γ` and avoids `0`, it is `J̃`-holomorphic with finite Hofer
energy in the interior, and its boundary loop lies in `e(A)` and winds once around `e z₀`. -/
def IsDiskCurve (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (e : ℂ → V 1) (z₀ : ℂ) (A : Set ℂ)
    (Γ : Finset ℂ) (u : ℂ → V 1) : Prop :=
  (Γ : Set ℂ) ⊆ ball 0 1 ∧ ContDiffOn ℝ ∞ u (closedBall 0 1 \ Γ) ∧
    (∀ z ∈ closedBall (0 : ℂ) 1 \ Γ, u z ≠ 0) ∧
    JHolomorphic.IsJHolomorphicOn (Jtilde H J) (ball 0 1 \ Γ) u ∧
    energy H (ball 0 1 \ Γ) u < ⊤ ∧ ∃ c : ℝ → ℂ, HasDiskBoundary e z₀ A u c

/-- `u` is an embedding of the closed unit disk minus `Γ`: it is injective there and its derivative
(within the closed disk) is injective at every point. -/
def IsEmbeddedOnDisk (Γ : Finset ℂ) (u : ℂ → V 1) : Prop :=
  Set.InjOn u (closedBall 0 1 \ Γ) ∧
    ∀ z ∈ closedBall (0 : ℂ) 1 \ Γ, Function.Injective (fderivWithin ℝ u (closedBall 0 1) z)

/-- Hryniewicz (2014), (32): `u` is an embedded `J̃`-holomorphic disk without punctures whose boundary
loop lies in `e(A)` and winds once around `e z₀`. -/
def IsEmbeddedHoloDisk (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (e : ℂ → V 1) (z₀ : ℂ)
    (A : Set ℂ) (u : ℂ → V 1) : Prop :=
  IsDiskCurve H J e z₀ A ∅ u ∧ IsEmbeddedOnDisk ∅ u

/-- `f ν → g` in `C^∞_loc` on `D \ N`, up to the boundary of the closed set `D`: for every compact
`K ⊆ D \ N` and every `m`, the `m`-th derivatives within `D` converge uniformly on `K`. -/
def TendstoCInftyLocWithin (f : ℕ → ℂ → V 1) (g : ℂ → V 1) (D N : Set ℂ) : Prop :=
  ∀ K ⊆ D \ N, IsCompact K → ∀ m : ℕ,
    TendstoUniformlyOn (fun ν => iteratedFDerivWithin ℝ m (f ν) D) (iteratedFDerivWithin ℝ m g D)
      atTop K

/-- `J` and `J₀` are `ε`-close in `C^k` on `S`: all derivatives of `J - J₀` of order at most `k` have
norm at most `ε` at the points of `S`. -/
def IsXiClose (H : V 1 → ℝ) (k : ℕ) (ε : ℝ) (J J₀ : V 1 → V 1 →L[ℝ] V 1) : Prop :=
  ∀ m ≤ k, ∀ x ∈ energySurface H, ‖iteratedFDeriv ℝ m (fun y => J y - J₀ y) x‖ ≤ ε

end

end FiniteEnergyPlane


