-- Prove2me | Definitions.Def_FiniteEnergyPlane_Setting
-- name    : FiniteEnergyPlane_Setting
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-20T23:21:48.954039+00:00
-- url     : https://prove2.me/theorems/8d396fb4-b851-4cb8-bbbb-80f3a468c66c
-- title:
--   Finite-energy pseudoholomorphic curves in the symplectization of a star-shaped level
-- statement:
--   Objects for finite-energy pseudoholomorphic curves in the symplectization of a strictly star-shaped hypersurface $S\subset\mathbb{R}^{2n+2}$ (H. Hofer 1993, § 3; U. Hryniewicz 2014, § 2.2; C. Wendl, *Lectures on Symplectic Field Theory*, Lecture 9).
--
--   1. **Linear data.** $V=\mathbb{R}^{2n+2}$ with coordinates $(q_1,p_1,\dots,q_{n+1},p_{n+1})$; $j_0$ is multiplication by $i$ on $q_k+ip_k$; $\omega_0=\sum_k dq_k\wedge dp_k$, $\omega_0(u,v)=\langle j_0u,v\rangle$; $\lambda_0=\tfrac12\sum_k(q_k\,dp_k-p_k\,dq_k)$, so $\lambda_0(x)v=\tfrac12\omega_0(x,v)$; $X_H=j_0\nabla H$.
--   2. **Star-shaped level.** $H:V\to\mathbb{R}$ is $C^\infty$, every ray from the origin meets $S=H^{-1}(1)$ in exactly one point, and $dH(x)x>0$ on $S$.
--   3. **Reeb field and contact planes.** $R=X_H/\lambda_0(X_H)$ on $S$; $\xi_x=\ker\lambda_0(x)\cap\ker dH(x)$.
--   4. **Compatible structure on $\xi$.** $J:V\to\operatorname{End}_{\mathbb{R}}(V)$ is $C^\infty$ and, for $x\in S$, preserves $\xi_x$, satisfies $J^2=-1$ there, $\omega_0(v,Jv)>0$ for $0\ne v\in\xi_x$, and $\omega_0(Jv,Jw)=\omega_0(v,w)$ on $\xi_x$.
--   5. **Symplectization coordinates.** $\mathbb{R}\times S$ is identified with $V\setminus\{0\}$ by $(a,x)\mapsto e^{2a}x$. For $y\neq0$, $\mathrm{proj}(y)\in S$ is the point of $S$ on the ray through $y$ and $a(y)$ is the number with $y=e^{2a(y)}\mathrm{proj}(y)$.
--   6. **The almost complex structure $\tilde J$** on $V\setminus\{0\}$: with $x=\mathrm{proj}(y)$, every $v$ splits uniquely as $v=\alpha\,\partial_a+\beta\,\tilde R+w$ with $\partial_a=2y$, $\tilde R=e^{2a(y)}R(x)$ and $w\in\xi_x$; then $\tilde J(y)v=\alpha\tilde R-\beta\,\partial_a+J(x)w$.
--   7. **Energies.** For $u:\mathbb{C}\to V$ on an open $U\subseteq\mathbb{C}$, write $a=a\circ u$, $w=\mathrm{proj}\circ u$ and $z=s+it$. Hofer's energy is
--   $$E(u)=\sup_{\varphi\in\Sigma}\int_U u^*d(\varphi(a)\lambda_0),$$
--   where $\Sigma$ is the set of $C^\infty$ nondecreasing $\varphi:\mathbb{R}\to[0,1]$ and the integrand is $\varphi'(a)\big(\partial_sa\,\lambda_0(\partial_tw)-\partial_ta\,\lambda_0(\partial_sw)\big)+\varphi(a)\,\omega_0(\partial_sw,\partial_tw)$. The $d\lambda$-energy is $\int_U\omega_0(\partial_sw,\partial_tw)$.
--   8. **Finite-energy curves.** $u$ is a finite-energy $\tilde J$-holomorphic curve on $U$ if it is $C^\infty$ on $U$, never $0$ there, satisfies $\partial_su+\tilde J(u)\partial_tu=0$ on $U$, and $E(u)<\infty$.
--   9. **Periodic Reeb orbits.** $P=(x,T)$ with $x:\mathbb{R}\to S$, $\dot x=R(x)$, $T>0$ and $x(\tau+T)=x(\tau)$ ($T$ need not be minimal). $P$ is *isolated* if some open set containing $x(\mathbb{R})$ meets no $T$-periodic orbit whose image is not contained in $x(\mathbb{R})$. The trivial cylinder over $P$ is $F_P(w)=|w|^{T/\pi}\,x\big(T\arg w/2\pi\big)$ on $\mathbb{C}\setminus\{0\}$, i.e. $F_P(e^{2\pi(s+it)})=e^{2Ts}x(Tt)$.
--   10. **Loops and charge.** The clockwise loop of radius $\rho$ about $z_0$ is $t\mapsto z_0+\rho e^{-2\pi it}$, the counterclockwise loop about $0$ is $t\mapsto Re^{2\pi it}$, and the action of a loop $\gamma$ is $\int_0^1\lambda_0(w(t))\,\dot w(t)\,dt$ with $w=\mathrm{proj}\circ u\circ\gamma$. $C^\infty$ convergence of maps $\mathbb{R}\to V$ is uniform convergence of every derivative on $\mathbb{R}$.
--   11. **Removable puncture.** The puncture $z_0$ of $u$ on $B_\varepsilon(z_0)\setminus\{z_0\}$ is removable if $u$ agrees there with a $C^\infty$ $\tilde J$-holomorphic map on $B_\varepsilon(z_0)$ that never takes the value $0$.
--
--   **Formalization Note** $V$ is `Fin (2 * (n + 1)) → ℝ` with interleaved coordinates (index $2k$ is $q_{k+1}$, index $2k+1$ is $p_{k+1}$); for $n=1$ this is the coordinate order of `HryniewiczCriterion.R4`. The radial data are `scaleToS H y` (the $r>0$ with $H(ry)=1$, default $1$), `proj H y = scaleToS H y • y` and `aCoord H y = -½ log (scaleToS H y)`. Energies are `ℝ≥0∞`-valued lower Lebesgue integrals `∫⁻ z in U, ENNReal.ofReal (…)`, so negative parts of an integrand are counted as $0$ and $E(u)<\infty$ is a genuine restriction. $\partial_s f$, $\partial_t f$ are `fderiv ℝ f z 1` and `fderiv ℝ f z Complex.I`; `gradNorm` is $\|D(a\circ u)\|+\|D(\mathrm{proj}\circ u)\|$ (operator norms), a size of the derivative that is invariant under $y\mapsto cy$. $J$-holomorphicity is `JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u` from the imported `JHolomorphic` setting.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515–563, Sections 1 and 3; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 9 (pp. 151–170)

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Finite-energy pseudoholomorphic curves in the symplectization of a star-shaped level

H. Hofer, *Pseudoholomorphic curves in symplectizations with applications to the Weinstein
conjecture in dimension three*, Invent. Math. 114 (1993); C. Wendl, *Lectures on Symplectic Field
Theory*, arXiv:1612.01009, Lecture 9; U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 2.2.

Conventions.
* `V n = ℝ^{2n+2}` with interleaved coordinates `(q₁, p₁, …, q_{n+1}, p_{n+1})`: index `2i` is
  `qᵢ₊₁` and index `2i + 1` is `pᵢ₊₁`. For `n = 1` this is `HryniewiczCriterion.R4`.
* `j0 v = (-p₁, q₁, …)` (multiplication by `i` on `qₖ + i pₖ`), `ω₀(u, v) = ⟨j0 u, v⟩ = Σ dqₖ ∧ dpₖ`
  and `λ₀(x) v = ½ ω₀(x, v) = ½ Σ (qₖ dpₖ - pₖ dqₖ)`.
* `X_H = j0 ∇H`, so `ω₀(X_H, ·) = -dH`.
* `H` has a strictly star-shaped level `S = H⁻¹(1)`. The Reeb field of `λ₀|S` is
  `R = X_H / λ₀(X_H)` and `ξ_x = ker λ₀(x) ∩ ker dH(x)`.
* The symplectization `ℝ × S` is identified with `V n \ {0}` by `(a, x) ↦ e^{2a} x`. For `y ≠ 0`,
  `scaleToS H y` is the `r > 0` with `H (r • y) = 1`, `proj H y = r • y ∈ S`, and
  `aCoord H y = -½ log r`. Hence `y = e^{2 aCoord y} • proj y`.
* `Jtilde H J` is the almost complex structure on `V n \ {0}` with `∂ₐ ↦ R`, `R ↦ -∂ₐ` and
  `J` on `ξ`. Here `∂ₐ = 2y` and `R` is lifted to `y` as `e^{2a} R(x)`.
* For a map `u : ℂ → V n` the coordinates are `a = aCoord ∘ u` and `w = proj ∘ u`. Hofer's energy
  is `E(u) = sup_{φ ∈ Σ} ∫ u*d(φ(a) λ)`, where `Σ` is the set of smooth nondecreasing
  `φ : ℝ → [0, 1]`. The `dλ`-energy is `∫ w*dλ₀`. Both are `ℝ≥0∞`-valued lower integrals.
* Loops around a puncture `z₀` are clockwise, `t ↦ z₀ + ρ e^{-2π i t}` (Wendl (9.4)). Loops near
  `∞` are counterclockwise, `t ↦ R e^{2π i t}`.
-/

namespace FiniteEnergyPlane

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `ℝ^{2n+2}` with interleaved coordinates `(q₁, p₁, …, q_{n+1}, p_{n+1})`. -/
abbrev V (n : ℕ) := Fin (2 * (n + 1)) → ℝ

variable {n : ℕ}

/-- Multiplication by `i` in the coordinates `qₖ + i pₖ`: `(j0 v)_{2i} = -v_{2i+1}` and
`(j0 v)_{2i+1} = v_{2i}`. -/
def j0 (v : V n) : V n := fun k =>
  if h : (k : ℕ) % 2 = 0 then -v ⟨k + 1, by have := k.2; omega⟩
  else v ⟨k - 1, by have := k.2; omega⟩

/-- The Euclidean inner product `⟨u, v⟩ = Σ uₖ vₖ`. -/
def dot (u v : V n) : ℝ := ∑ k, u k * v k

/-- The standard symplectic form `ω₀(u, v) = ⟨j0 u, v⟩ = Σ (dqₖ ∧ dpₖ)(u, v)`. -/
def omega0 (u v : V n) : ℝ := dot (j0 u) v

/-- The Liouville form `λ₀ = ½ Σ (qₖ dpₖ - pₖ dqₖ)` at `x`, applied to `v`. -/
def liouville (x v : V n) : ℝ := omega0 x v / 2

/-- The gradient `∇H(x) = (∂H/∂x₀, …)`. -/
def grad (H : V n → ℝ) (x : V n) : V n := fun k => fderiv ℝ H x (Pi.single k 1)

/-- The Hamiltonian vector field `X_H = j0 ∇H`, i.e. `ω₀(X_H, ·) = -dH`. -/
def hamVF (H : V n → ℝ) (x : V n) : V n := j0 (grad H x)

/-- The level set `S = H⁻¹(1)`. -/
def energySurface (H : V n → ℝ) : Set (V n) := {x | H x = 1}

/-- `S = H⁻¹(1)` is strictly star-shaped: `H` is smooth, every ray from the origin meets `S`
exactly once, and it crosses `S` transversally, `dH(x) x > 0`. -/
def IsStrictlyStarShapedLevel (H : V n → ℝ) : Prop :=
  ContDiff ℝ ∞ H ∧
  (∀ u : V n, u ≠ 0 → ∃! r : ℝ, 0 < r ∧ H (r • u) = 1) ∧
  (∀ x : V n, H x = 1 → 0 < fderiv ℝ H x x)

/-- The Reeb vector field `R = X_H / λ₀(X_H)` of `λ₀|S`. -/
def reeb (H : V n → ℝ) (x : V n) : V n := (liouville x (hamVF H x))⁻¹ • hamVF H x

/-- `v` lies in the contact plane `ξ_x = ker λ₀(x) ∩ ker dH(x)`. -/
def IsInXi (H : V n → ℝ) (x v : V n) : Prop := liouville x v = 0 ∧ fderiv ℝ H x v = 0

/-- `J` is a smooth `dλ₀`-compatible complex structure on `ξ` over `S`: `J` is smooth, and for
`x ∈ S` it preserves `ξ_x`, squares to `-1` on `ξ_x`, satisfies `ω₀(v, J v) > 0` for
`0 ≠ v ∈ ξ_x`, and preserves `ω₀` on `ξ_x`. -/
def IsCompatibleXiStructure (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) : Prop :=
  ContDiff ℝ ∞ J ∧ ∀ x ∈ energySurface H, ∀ v w : V n, IsInXi H x v → IsInXi H x w →
    IsInXi H x (J x v) ∧ J x (J x v) = -v ∧ (v ≠ 0 → 0 < omega0 v (J x v)) ∧
    omega0 (J x v) (J x w) = omega0 v w

open Classical in
/-- For `y ≠ 0`, the scalar `r > 0` with `H (r • y) = 1` (unique on a strictly star-shaped
level); `1` if no such scalar exists. -/
def scaleToS (H : V n → ℝ) (y : V n) : ℝ :=
  if h : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 then Classical.choose h else 1

/-- The radial projection `V n \ {0} → S`, `y ↦ scaleToS H y • y`. -/
def proj (H : V n → ℝ) (y : V n) : V n := scaleToS H y • y

/-- The symplectization coordinate `a` of `y = e^{2a} x` with `x ∈ S`: `a = -½ log r`. -/
def aCoord (H : V n → ℝ) (y : V n) : ℝ := -Real.log (scaleToS H y) / 2

/-- The Liouville form at `x` as a continuous linear functional. -/
def liouvilleCLM (x : V n) : V n →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ k, (j0 x k) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k

/-- The symplectization almost complex structure `J̃` at `y ≠ 0`. With `x = proj y`,
`r = scaleToS y`, `∂ₐ = 2y` and the lifted Reeb vector `r⁻¹ R(x)`, every `v` splits uniquely as
`v = α ∂ₐ + β r⁻¹ R(x) + w` with `w ∈ ξ_x`, where `α = r dH(x) v / (2 dH(x) x)` and
`β = r λ₀(x) v`. Then `J̃ v = α r⁻¹ R(x) - β ∂ₐ + J(x) w`. -/
def Jtilde (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (y : V n) : V n →L[ℝ] V n :=
  let x := proj H y
  let r := scaleToS H y
  let α : V n →L[ℝ] ℝ := (r / (2 * fderiv ℝ H x x)) • fderiv ℝ H x
  let β : V n →L[ℝ] ℝ := r • liouvilleCLM x
  let w : V n →L[ℝ] V n := ContinuousLinearMap.id ℝ (V n) - α.smulRight ((2 : ℝ) • y) -
    β.smulRight (r⁻¹ • reeb H x)
  α.smulRight (r⁻¹ • reeb H x) - β.smulRight ((2 : ℝ) • y) + (J x).comp w

/-- The admissible functions `Σ` in Hofer's energy: smooth, nondecreasing, values in `[0, 1]`. -/
def Admissible (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ Monotone φ ∧ ∀ s, 0 ≤ φ s ∧ φ s ≤ 1

/-- `∂ₛf(z) = Df(z) 1`. -/
def ds {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℂ → F) (z : ℂ) : F :=
  fderiv ℝ f z 1

/-- `∂ₜf(z) = Df(z) i`. -/
def dt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℂ → F) (z : ℂ) : F :=
  fderiv ℝ f z Complex.I

/-- The integrand of `u*d(φ(a) λ)` with respect to `ds ∧ dt`, in the coordinates `a = aCoord ∘ u`
and `w = proj ∘ u`: `φ'(a) (∂ₛa λ(∂ₜw) - ∂ₜa λ(∂ₛw)) + φ(a) ω₀(∂ₛw, ∂ₜw)`. -/
def energyDensity (H : V n → ℝ) (φ : ℝ → ℝ) (u : ℂ → V n) (z : ℂ) : ℝ :=
  let a := fun z => aCoord H (u z)
  let w := fun z => proj H (u z)
  deriv φ (a z) * (ds a z * liouville (w z) (dt w z) - dt a z * liouville (w z) (ds w z)) +
    φ (a z) * omega0 (ds w z) (dt w z)

/-- The integrand of `u*dλ`: `ω₀(∂ₛw, ∂ₜw)` with `w = proj ∘ u`. -/
def dlambdaDensity (H : V n → ℝ) (u : ℂ → V n) (z : ℂ) : ℝ :=
  omega0 (ds (fun z => proj H (u z)) z) (dt (fun z => proj H (u z)) z)

/-- Hofer's energy of `u` on `U`: `sup_{φ ∈ Σ} ∫_U u*d(φ(a) λ)`. -/
def energy (H : V n → ℝ) (U : Set ℂ) (u : ℂ → V n) : ℝ≥0∞ :=
  ⨆ (φ : ℝ → ℝ) (_ : Admissible φ), ∫⁻ z in U, ENNReal.ofReal (energyDensity H φ u z)

/-- The `dλ`-energy `∫_U u*dλ` of `u` on `U`. -/
def dlambdaEnergy (H : V n → ℝ) (U : Set ℂ) (u : ℂ → V n) : ℝ≥0∞ :=
  ∫⁻ z in U, ENNReal.ofReal (dlambdaDensity H u z)

/-- `u` is a finite-energy `J̃`-holomorphic curve on the open set `U`: it is smooth on `U`, avoids
`0`, is `J̃`-holomorphic, and has finite Hofer energy. -/
def IsFiniteEnergyCurve (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (U : Set ℂ) (u : ℂ → V n) :
    Prop :=
  ContDiffOn ℝ ∞ u U ∧ (∀ z ∈ U, u z ≠ 0) ∧
    JHolomorphic.IsJHolomorphicOn (Jtilde H J) U u ∧ energy H U u < ⊤

/-- The `ℝ`-invariant size of the derivative: `‖D(aCoord ∘ u)(z)‖ + ‖D(proj ∘ u)(z)‖`. -/
def gradNorm (H : V n → ℝ) (u : ℂ → V n) (z : ℂ) : ℝ :=
  ‖fderiv ℝ (fun z => aCoord H (u z)) z‖ + ‖fderiv ℝ (fun z => proj H (u z)) z‖

/-- A periodic Reeb orbit `P = (x, T)` on `S`: `x' = R(x)`, `x(ℝ) ⊆ S`, `x(τ + T) = x(τ)`, `T > 0`.
`T` need not be the least period. -/
structure ReebOrbit (H : V n → ℝ) where
  x : ℝ → V n
  T : ℝ
  T_pos : 0 < T
  mem : ∀ τ, x τ ∈ energySurface H
  hasDerivAt : ∀ τ, HasDerivAt x (reeb H (x τ)) τ
  periodic : ∀ τ, x (τ + T) = x τ

/-- `P` is isolated among the `T`-periodic orbits: some open set containing `x(ℝ)` meets no other
`T`-periodic orbit, i.e. every periodic orbit of the same period `T` that passes through it has its
image in `x(ℝ)`. -/
def ReebOrbit.IsIsolated {H : V n → ℝ} (P : ReebOrbit H) : Prop :=
  ∃ W : Set (V n), IsOpen W ∧ Set.range P.x ⊆ W ∧
    ∀ Q : ReebOrbit H, Q.T = P.T → (∃ τ, Q.x τ ∈ W) → Set.range Q.x ⊆ Set.range P.x

/-- The trivial cylinder over `P`, `F_P : ℂ \ {0} → V n \ {0}`, `F_P(e^{2π(s+it)}) = e^{2Ts} x(Tt)`,
i.e. `F_P(w) = |w|^{T/π} • x(T arg(w) / 2π)` (`a = Ts` in the coordinate `y = e^{2a} x`). -/
def trivialCylinder {H : V n → ℝ} (P : ReebOrbit H) (w : ℂ) : V n :=
  (‖w‖ ^ (P.T / π)) • P.x (P.T * Complex.arg w / (2 * π))

/-- The clockwise circle `t ↦ z₀ + ρ e^{-2π i t}` of radius `ρ` about `z₀`. -/
def cwLoop (z₀ : ℂ) (ρ : ℝ) (t : ℝ) : ℂ := z₀ + ρ * Complex.exp (-(2 * π * t : ℝ) * Complex.I)

/-- The counterclockwise circle `t ↦ R e^{2π i t}` about `0`. -/
def ccwLoop (R : ℝ) (t : ℝ) : ℂ := R * Complex.exp ((2 * π * t : ℝ) * Complex.I)

/-- The loop `t ↦ proj(u(γ(t)))` in `S`. -/
def loopInS (H : V n → ℝ) (u : ℂ → V n) (γ : ℝ → ℂ) (t : ℝ) : V n := proj H (u (γ t))

/-- The action `∫₀¹ λ₀(w(t)) w'(t) dt` of `w = proj ∘ u ∘ γ`, i.e. `∫_γ u*λ`. -/
def loopAction (H : V n → ℝ) (u : ℂ → V n) (γ : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..1, liouville (loopInS H u γ t) (deriv (loopInS H u γ) t)

/-- `f k → g` in `C^∞` on `ℝ` (uniformly on `ℝ`, for every derivative). -/
def TendstoCInfty (f : ℕ → ℝ → V n) (g : ℝ → V n) : Prop :=
  ∀ m : ℕ, TendstoUniformly (fun k => iteratedDeriv m (f k)) (iteratedDeriv m g) atTop

/-- The puncture `z₀` of `u` (defined on the punctured ball `ball z₀ ε \ {z₀}`) is removable: `u`
agrees there with a smooth `J̃`-holomorphic map on `ball z₀ ε` that avoids `0`. -/
def IsRemovablePuncture (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (u : ℂ → V n) (z₀ : ℂ)
    (ε : ℝ) : Prop :=
  ∃ v : ℂ → V n, ContDiffOn ℝ ∞ v (ball z₀ ε) ∧ (∀ z ∈ ball z₀ ε, v z ≠ 0) ∧
    JHolomorphic.IsJHolomorphicOn (Jtilde H J) (ball z₀ ε) v ∧
    ∀ z ∈ ball z₀ ε, z ≠ z₀ → v z = u z

end

end FiniteEnergyPlane


