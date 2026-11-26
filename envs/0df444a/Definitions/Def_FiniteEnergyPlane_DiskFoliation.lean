-- Prove2me | Definitions.Def_FiniteEnergyPlane_DiskFoliation
-- name    : FiniteEnergyPlane_DiskFoliation
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-25T23:03:22.811996+00:00
-- url     : https://prove2.me/theorems/94c3586e-b597-52e9-8f37-0ab35781a46a
-- title:
--   The characteristic foliation of a disk in a star-shaped level
-- statement:
--   Zeros and leaves of the characteristic foliation of a disk in a strictly star-shaped level $S=H^{-1}(1)\subset\mathbb{R}^4$. A disk is given by a smooth map $e:\mathbb{C}\to\mathbb{R}^4$, and its **characteristic field** $V$ is the field `charField e` of `FiniteEnergyPlane_SpanningDisk`, with $(ds\wedge dt)(V,\cdot)=e^*\lambda_0$. Write $D$ for the closed unit disk and $B_\rho$ for the open disk of radius $\rho$ about $0$ in the parameter plane.
--
--   1. **`charTrace e z`, `charDet e z`** are $\mathrm{tr}\,DV(z)$ and $\det DV(z)$.
--   2. **`IsNicelyEllipticZero e z`.** $V(z)=0$, and $DV(z)$ has two real eigenvalues, possibly equal, of the same sign: $\det DV(z)>0$ and $4\det DV(z)\le(\mathrm{tr}\,DV(z))^2$.
--   3. **`IsCharCurve e σ`.** $\sigma:\mathbb{R}\to\mathbb{C}$ satisfies $\sigma'=V(\sigma)$.
--   4. **`IsPeriodicLeaf e σ T`.** 3 holds, $T>0$, $\sigma(\tau+T)=\sigma(\tau)$, and $\sigma$ is not constant. The image of $\sigma$ is a **closed leaf**.
--   5. **`IsSpanningDisk H C e ρ`.** $e$ embeds $B_\rho$, $\rho>1$, into $S$ and maps the unit circle onto the set $C$, with $\lambda_0(De(z)\,iz)>0$ for $|z|=1$.
--   6. **`IsImmersedDisk H e ρ`.** $e$ is smooth, $\rho>1$, and $e$ maps $B_\rho$ into $S$ with injective derivative.
--   7. **`IsClosedLeafDisk e ρ σ T Ω z₀`.** $\sigma$ is a closed leaf, of period $T$; $\Omega$ is open and connected, with closure in $B_\rho$ and frontier $\sigma(\mathbb{R})$; $z_0\in\Omega$ is the only zero of $V$ in $\Omega$, is nicely elliptic, and $\mathrm{tr}\,DV(z_0)>0$; and $\Omega$ contains no closed leaf.
--   8. **`LeavesIssueFrom e z₀ W`.** Through every point of $W$ there is an integral curve of $V$ on $(-\infty,0]$ that stays in $W$ and tends to $z_0$ at $-\infty$.
--   9. **`roundH`** is $y\mapsto|y|^2$, so that its level $1$ is the **round sphere**; **`roundJ`** is the constant field of the standard complex structure $j_0$ of $\mathbb{R}^4=\mathbb{C}^2$.
--
--   A zero $z$ of $V$ is nondegenerate if $\det DV(z)\ne0$, elliptic if $\det DV(z)>0$, hyperbolic if $\det DV(z)<0$, and positive or negative according to the sign of $\mathrm{tr}\,DV(z)$. These notions concern surfaces in star-shaped levels only, and 1–8 do not refer to the symplectization.
--
--   **Formalization Note** Integral curves in 3 and 4 are parametrized by all of $\mathbb{R}$. Since $d(e^*\lambda_0)=(\operatorname{div}V)\,ds\wedge dt$, the trace is $\omega_0(\partial_se,\partial_te)$. In 5 the set $C$ is arbitrary; for a periodic Reeb orbit $P=(x,T)$ it is $x(\mathbb{R})$, and the disk is parametrized slightly beyond its boundary. The constant curve at $z_0$ satisfies the requirement of 8 at the point $z_0$ itself.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Section 5; H. Hofer, K. Wysocki, E. Zehnder, A characterization of the tight 3-sphere II, Comm. Pure Appl. Math. 52 (1999), 1139–1177, Section 3; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), 791–862, arXiv:1105.2077, § 3.1

import Definitions.Def_FiniteEnergyPlane_SpanningDisk

/-!
# The characteristic foliation of a disk in a star-shaped level

H. Hofer, Invent. Math. 114 (1993), § 5; H. Hofer, K. Wysocki, E. Zehnder, *A characterization of the
tight 3-sphere II*, Comm. Pure Appl. Math. 52 (1999), § 3; U. Hryniewicz, J. Symplectic Geom. 12 (2014),
§ 3.1. Everything is in the setting of `FiniteEnergyPlane_SpanningDisk`: `S = H⁻¹(1) ⊂ V 1 = ℝ⁴` strictly
star-shaped, a disk given by `e : ℂ → V 1`, and its characteristic field `charField e` on the parameter
plane, `(ds ∧ dt)(V, ·) = e*λ₀`.

Conventions.
* A zero of `charField e` is nondegenerate if the linearization there has nonzero determinant, elliptic if
  the determinant is positive and hyperbolic if it is negative. The trace of the linearization is
  `ω₀(∂ₛe, ∂ₜe)`; the zero is positive if the trace is positive and negative if it is negative.
* Integral curves of `charField e` are parametrized by all of `ℝ`.
* The round sphere is `H y = |y|²`, with Reeb field `2 j0 y`; its standard complex structure on `ξ` is `j0`.
-/

namespace FiniteEnergyPlane

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The trace of the linearization of the characteristic field of `e` at `z`. -/
def charTrace (e : ℂ → V 1) (z : ℂ) : ℝ :=
  LinearMap.trace ℝ ℂ (fderiv ℝ (charField e) z : ℂ →ₗ[ℝ] ℂ)

/-- The determinant of the linearization of the characteristic field of `e` at `z`. -/
def charDet (e : ℂ → V 1) (z : ℂ) : ℝ :=
  LinearMap.det (fderiv ℝ (charField e) z : ℂ →ₗ[ℝ] ℂ)

/-- `z` is a nicely elliptic zero of the characteristic field of `e`: the linearization has two real
eigenvalues (possibly equal) of the same sign. -/
def IsNicelyEllipticZero (e : ℂ → V 1) (z : ℂ) : Prop :=
  charField e z = 0 ∧ 0 < charDet e z ∧ 4 * charDet e z ≤ charTrace e z ^ 2

/-- `σ : ℝ → ℂ` is an integral curve of the characteristic field of `e`. -/
def IsCharCurve (e : ℂ → V 1) (σ : ℝ → ℂ) : Prop :=
  ∀ τ, HasDerivAt σ (charField e (σ τ)) τ

/-- `σ` is a nonconstant `T`-periodic integral curve of the characteristic field of `e`. -/
def IsPeriodicLeaf (e : ℂ → V 1) (σ : ℝ → ℂ) (T : ℝ) : Prop :=
  0 < T ∧ charField e (σ 0) ≠ 0 ∧ IsCharCurve e σ ∧ ∀ τ, σ (τ + T) = σ τ

/-- `e` embeds the disk of radius `ρ > 1` into `S`, and it maps the unit circle onto `C`, positively with
respect to `λ₀`. For a periodic Reeb orbit `P` and `C = x(ℝ)`, `e` is a spanning disk of `x(ℝ)`
parametrized slightly beyond its boundary. -/
def IsSpanningDisk (H : V 1 → ℝ) (C : Set (V 1)) (e : ℂ → V 1) (ρ : ℝ) : Prop :=
  IsEmbeddedDisk H e ρ ∧ e '' sphere 0 1 = C ∧
    ∀ z ∈ sphere (0 : ℂ) 1, 0 < liouville (e z) (fderiv ℝ e z (Complex.I * z))

/-- `e` is a smooth map `ℂ → V 1` that immerses the open disk of radius `ρ > 1` into `S`. -/
def IsImmersedDisk (H : V 1 → ℝ) (e : ℂ → V 1) (ρ : ℝ) : Prop :=
  ContDiff ℝ ∞ e ∧ 1 < ρ ∧ Set.MapsTo e (ball 0 ρ) (energySurface H) ∧
    ∀ z ∈ ball (0 : ℂ) ρ, Function.Injective (fderiv ℝ e z)

/-- `σ` is a closed characteristic leaf of `e` that bounds the domain `Ω ∋ z₀` in the disk of radius `ρ`;
`z₀` is the only zero in `Ω` and is positive and nicely elliptic; and `Ω` contains no closed leaf. -/
def IsClosedLeafDisk (e : ℂ → V 1) (ρ : ℝ) (σ : ℝ → ℂ) (T : ℝ) (Ω : Set ℂ) (z₀ : ℂ) : Prop :=
  IsPeriodicLeaf e σ T ∧ IsOpen Ω ∧ IsConnected Ω ∧ closure Ω ⊆ ball 0 ρ ∧
    frontier Ω = Set.range σ ∧ z₀ ∈ Ω ∧ (∀ z ∈ Ω, charField e z = 0 ↔ z = z₀) ∧
    IsNicelyEllipticZero e z₀ ∧ 0 < charTrace e z₀ ∧
    ∀ (σ' : ℝ → ℂ) (T' : ℝ), IsPeriodicLeaf e σ' T' → ¬ Set.range σ' ⊆ Ω

/-- Through every point of `W` there is an integral curve of the characteristic field of `e` on `(-∞, 0]`
that stays in `W` and tends to `z₀` at `-∞`. -/
def LeavesIssueFrom (e : ℂ → V 1) (z₀ : ℂ) (W : Set ℂ) : Prop :=
  ∀ z ∈ W, ∃ σ : ℝ → ℂ, σ 0 = z ∧ Tendsto σ atBot (𝓝 z₀) ∧
    ∀ τ ≤ 0, σ τ ∈ W ∧ HasDerivWithinAt σ (charField e (σ τ)) (Set.Iic 0) τ

/-- The round sphere is the level `1` of `y ↦ |y|²`. -/
def roundH (y : V 1) : ℝ := dot y y

/-- The constant field `j0` of complex structures on `V 1`. -/
def roundJ (_ : V 1) : V 1 →L[ℝ] V 1 :=
  ContinuousLinearMap.pi fun k : Fin (2 * (1 + 1)) =>
    if h : (k : ℕ) % 2 = 0 then
      -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ)
        ⟨k + 1, by have := k.2; omega⟩)
    else ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (1 + 1)) => ℝ)
        ⟨k - 1, by have := k.2; omega⟩

end

end FiniteEnergyPlane


