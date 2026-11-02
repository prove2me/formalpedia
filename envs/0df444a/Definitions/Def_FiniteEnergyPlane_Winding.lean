-- Prove2me | Definitions.Def_FiniteEnergyPlane_Winding
-- name    : FiniteEnergyPlane_Winding
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-01T15:36:17.791919+00:00
-- url     : https://prove2.me/theorems/109f26f5-763a-4c3c-81c5-d4e94f088d2b
-- title:
--   Winding numbers of finite-energy curves and of asymptotic eigenvectors in dimension three
-- statement:
--   Winding numbers for finite-energy pseudoholomorphic curves in the symplectization of a strictly star-shaped level $S=H^{-1}(1)\subset\mathbb{R}^4$, in the setting of `FiniteEnergyPlane_Setting` and `FiniteEnergyPlane_Asymptotics` with $n=1$ (U. Hryniewicz 2014, § 2.2.4; C. Wendl, *Lectures on Symplectic Field Theory*, § 3.7). Here $R$ is the Reeb field, $\xi$ the contact planes, $J$ a complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit.
--
--   1. **Winding of a loop.** A continuous $1$-periodic $f:\mathbb{R}\to\mathbb{C}\setminus\{0\}$ has winding number $k\in\mathbb{Z}$ if $f(t)=|f(t)|e^{i\theta(t)}$ for a continuous $\theta$ with $\theta(1)-\theta(0)=2\pi k$. A vector $(q,p)\in\mathbb{R}^2$ is read as $q+ip$.
--   2. **Global frame of $\xi$.** $\xi$ is trivialized by Hryniewicz's frame $Z_1,Z_2$ (`HryniewiczCriterion.xiFrame1/2`, built from quaternions), with $\omega_0(Z_1,Z_2)=1$. For $v=aZ_1+bZ_2\in\xi_x$, its coordinate is $a+ib\in\mathbb{C}$. A loop $\eta$ along $P$ with $\eta(t)\in\xi_{x(Tt)}$ has winding $k$ if its coordinate loop does.
--   3. **Windings of eigenvectors.** For an eigenvalue $\mu$ of $-J_0\partial_t-S_\infty$ (a loop of symmetric $2\times2$ matrices), "$\mu$ has winding $k$" means that $\mu$ is an eigenvalue and every eigenfunction for $\mu$ has winding $k$; the *span of winding $k$* is the linear span of all eigenfunctions of eigenvalues with winding $k$. The same notion is defined for eigenvalues of the asymptotic operator $A_P$, with windings in the global frame.
--   4. **$\alpha^\pm$.** $\alpha^-(P)=k$ means $k$ is the winding of some eigenvalue $\mu<0$ of $A_P$ and no eigenvalue $\mu<0$ has larger winding; $\alpha^+(P)=k$ means $k$ is the winding of some eigenvalue $\mu\ge0$ and no eigenvalue $\mu\ge0$ has smaller winding.
--   5. **Prime orbits.** $P$ is prime if $x(\tau)\neq x(0)$ for $0<\tau<T$.
--   6. **Punctures.** At $z_0\in\mathbb{C}$ the cylindrical coordinates are $(s,t)\mapsto z_0+e^{-2\pi(s+it)}$; at $\infty$ they are $(s,t)\mapsto e^{2\pi(s+it)}$. In both, $s\to+\infty$ approaches the puncture.
--   7. **The transverse derivative.** $\pi v=v-\lambda_0(v)R$ projects $TS$ onto $\xi$ along $R$. For a curve $u$ with $w=\mathrm{proj}\circ u$, $\pi\partial_su(z)$ is the global-frame coordinate of $\pi(\partial_sw(z))$.
--   8. **Local index of a zero.** An isolated zero $z_0$ of $f:\mathbb{C}\to\mathbb{C}$ has local index $k$ if $f$ has winding $k$ along every small counterclockwise circle $t\mapsto z_0+\rho e^{2\pi it}$.
--   9. **$\mathrm{wind}_\pi$** (Hryniewicz (14)). $\mathrm{wind}_\pi(u)=k$ on $\mathbb{C}\setminus\Gamma$ means: the zeros of $\pi\partial_su$ in $\mathbb{C}\setminus\Gamma$ are finitely many, each is isolated with some local index, and these indices sum to $k$.
--   10. **$\mathrm{wind}_\infty$** (Hryniewicz (16), one puncture). At a puncture with sign $\varepsilon=\pm1$ and cylindrical coordinates $(s,t)$, $\mathrm{wind}_\infty=k$ means that for all large $s$ the loop $t\mapsto\pi\,\partial_sw(s,\varepsilon t)$ has winding $k$.
--   11. **Fast planes** (Hryniewicz, Definition 2.14). A finite-energy plane whose puncture $\infty$ is nondegenerate (Definition 2.9) with a prime asymptotic limit, and with $\mathrm{wind}_\pi=0$.
--
--   **Formalization Note** Every invariant is a predicate `Has… k` ("the invariant is defined and equals $k$"), never a total function with a default value. `V 1` and `HryniewiczCriterion.R4` are identified coordinatewise (`toR4`, `ofR4`, by `Fin.cast`), and the global frame is `HryniewiczCriterion.xiCoords` of `H ∘ ofR4`. Winding numbers depend only on the orientation of the frame, and $(Z_1,Z_2)$ induces the orientation of $\xi$ given by $d\lambda_0$, as does Hryniewicz's $(Z,JZ)$ in Remark 2.13. The coordinates at $z_0=0$ are the `cylEnd` of the previous mission (`cylEndAt 0 = cylEnd`). $\partial_s$ of the end map is `fderiv ℝ (endW H u e) (s, t) (1, 0)`.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4 (formulas (14)–(16), Remark 2.13, Definition 2.14); U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Sections 3–4; C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Section 3.7

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Definitions.Def_HryniewiczCriterion_ConleyZehnder

/-!
# Winding numbers of finite-energy curves in the symplectization of a star-shaped level in `ℝ⁴`

U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 2.2.4 ((14)–(16), Remark 2.13, Definition 2.14);
U. Hryniewicz, Trans. AMS 364 (2012), §§ 3–4; H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), § 3;
C. Wendl, *Lectures on Symplectic Field Theory* (2026 notes), § 3.7.
Everything is in the setting of `FiniteEnergyPlane_Setting` and `FiniteEnergyPlane_Asymptotics`
for `n = 1`, so `S = H⁻¹(1) ⊂ V 1 = ℝ⁴` and `ξ` has real rank `2`.

Conventions.
* `V 1` and `HryniewiczCriterion.R4` have the same coordinates `(q₁, p₁, q₂, p₂)`; `toR4` and
  `ofR4` are the identity on coordinates (`Fin (2 * (1 + 1)) = Fin 4`).
* `ξ` is trivialized by Hryniewicz's global frame `Z₁, Z₂` (`HryniewiczCriterion.xiFrame1/2` of
  `H ∘ ofR4`), with `ω₀(Z₁, Z₂) = 1`. `xiCoordC H x v = a + i b` for `v = a Z₁ + b Z₂`. Winding
  numbers of nowhere-vanishing sections depend only on the orientation of the frame, and `(Z₁, Z₂)`
  induces the orientation of `ξ` given by `dλ₀`, as does `(Z, J Z)` in Hryniewicz's Remark 2.13.
* `π : TS → ξ` is the projection along the Reeb field, `π v = v - λ₀(v) R`.
* Cylindrical coordinates at a puncture `z₀` are `(s, t) ↦ z₀ + e^{-2π(s + it)}` (`cylEndAt z₀`,
  with `cylEndAt 0 = cylEnd`), and at `∞` they are `cylInf`. In both, `s → +∞` approaches the
  puncture; at a puncture of sign `ε` the loops are read as `t ↦ (s, εt)`.
* All invariants are predicates `Has… k` asserting that the invariant is defined and equals the integer `k`,
  never total functions with default values.
-/

namespace FiniteEnergyPlane

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-! ### Winding of a loop in `ℂ \ {0}` -/

/-- `f` is a continuous `1`-periodic loop in `ℂ \ {0}` with winding number `k`: some continuous
`θ : ℝ → ℝ` has `f(t) = |f(t)| e^{iθ(t)}` for all `t`, and `θ(1) - θ(0) = 2πk`. -/
def HasLoopWind (f : ℝ → ℂ) (k : ℤ) : Prop :=
  Continuous f ∧ Function.Periodic f 1 ∧ (∀ t, f t ≠ 0) ∧
    ∃ θ : ℝ → ℝ, Continuous θ ∧
      (∀ t, f t = (‖f t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) ∧ θ 1 - θ 0 = 2 * π * k

/-- `ℝ² = CauchyRiemannIndex.Vec 1` as `ℂ`: `(q, p) ↦ q + i p`. Under this map `J₀` is
multiplication by `i`. -/
def vecToC (a : CauchyRiemannIndex.Vec 1) : ℂ := ⟨a (Sum.inl 0), a (Sum.inr 0)⟩

/-! ### The global frame of `ξ` -/

/-- `V 1 → HryniewiczCriterion.R4`, the identity on coordinates. -/
def toR4 (y : V 1) : HryniewiczCriterion.R4 := fun k => y (Fin.cast (by norm_num) k)

/-- `HryniewiczCriterion.R4 → V 1`, the identity on coordinates. -/
def ofR4 (x : HryniewiczCriterion.R4) : V 1 := fun k => x (Fin.cast (by norm_num) k)

/-- The coordinates `a + i b` of `v = a Z₁ + b Z₂ ∈ ξ_x` in Hryniewicz's global frame `Z₁, Z₂` of
`ξ` (`HryniewiczCriterion.xiCoords` of `H ∘ ofR4`): `a = ω₀(v, Z₂)`, `b = ω₀(Z₁, v)`. -/
def xiCoordC (H : V 1 → ℝ) (x v : V 1) : ℂ :=
  let c := HryniewiczCriterion.xiCoords (fun z => H (ofR4 z)) (toR4 x) (toR4 v)
  ⟨c 0, c 1⟩

/-- The projection `π v = v - λ₀(x)(v) R(x)` of `T_x S` onto `ξ_x` along the Reeb field. -/
def piXi {n : ℕ} (H : V n → ℝ) (x v : V n) : V n := v - liouville x v • reeb H x

/-- The winding of a `ξ`-valued loop `η` along `P = (x, T)` (`η(t) ∈ ξ_{x(Tt)}`) in the global
frame: `k` is the winding number of `t ↦ xiCoordC H (x(Tt)) (η(t))`. -/
def HasXiLoopWind {H : V 1 → ℝ} (P : ReebOrbit H) (η : ℝ → V 1) (k : ℤ) : Prop :=
  HasLoopWind (fun t => xiCoordC H (P.x (P.T * t)) (η t)) k

/-! ### Windings of eigenvectors -/

/-- `μ` is an eigenvalue of `A = -J₀ ∂ₜ - S∞` (on `ℝ²`-valued loops) and every eigenfunction for
`μ` has winding number `k` (as a loop in `ℂ` under `vecToC`). -/
def HasLoopEigenWind (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (μ : ℝ) (k : ℤ) : Prop :=
  (∃ e, IsLoopEigen Sinf μ e) ∧
    ∀ e, IsLoopEigen Sinf μ e → HasLoopWind (fun t => vecToC (e t)) k

/-- The linear span of all eigenfunctions of `A = -J₀ ∂ₜ - S∞` whose eigenvalue `μ` satisfies
`HasLoopEigenWind Sinf μ k`. -/
def loopEigenSpan (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (k : ℤ) :
    Submodule ℝ (ℝ → CauchyRiemannIndex.Vec 1) :=
  Submodule.span ℝ {e | ∃ μ : ℝ, IsLoopEigen Sinf μ e ∧ HasLoopEigenWind Sinf μ k}

/-- `μ` is an eigenvalue of the asymptotic operator `A_P` and every eigenvector for `μ` has
winding number `k` in the global frame. -/
def HasEigenWind {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (μ : ℝ) (k : ℤ) :
    Prop :=
  (∃ v, IsAsymptoticEigen J P μ v) ∧ ∀ v, IsAsymptoticEigen J P μ v → HasXiLoopWind P v k

/-- `k = α⁻(P)`: the largest winding number of an eigenvalue `μ < 0` of `A_P` (attained, and an
upper bound for all of them). -/
def IsAlphaMinus {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (k : ℤ) : Prop :=
  (∃ μ < 0, HasEigenWind J P μ k) ∧ ∀ μ < 0, ∀ k' : ℤ, HasEigenWind J P μ k' → k' ≤ k

/-- `k = α⁺(P)`: the smallest winding number of an eigenvalue `μ ≥ 0` of `A_P` (attained, and a
lower bound for all of them). -/
def IsAlphaPlus {H : V 1 → ℝ} (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (k : ℤ) : Prop :=
  (∃ μ, 0 ≤ μ ∧ HasEigenWind J P μ k) ∧ ∀ μ, 0 ≤ μ → ∀ k' : ℤ, HasEigenWind J P μ k' → k ≤ k'

/-! ### Winding numbers of a finite-energy curve -/

/-- `P` is prime (simply covered): `T` is the least positive period. -/
def ReebOrbit.IsPrime {n : ℕ} {H : V n → ℝ} (P : ReebOrbit H) : Prop :=
  ∀ τ : ℝ, 0 < τ → τ < P.T → P.x τ ≠ P.x 0

/-- Positive cylindrical coordinates at the puncture `z₀`: `(s, t) ↦ z₀ + e^{-2π(s + it)}`. -/
def cylEndAt (z₀ : ℂ) (s t : ℝ) : ℂ := cwLoop z₀ (Real.exp (-(2 * π * s))) t

/-- The `ξ`-component `π ∂ₛu(z)` of the derivative of `w = proj ∘ u`, in the global frame. -/
def piDs (H : V 1 → ℝ) (u : ℂ → V 1) (z : ℂ) : ℂ :=
  xiCoordC H (proj H (u z)) (piXi H (proj H (u z)) (ds (fun z => proj H (u z)) z))

/-- `z₀` is an isolated zero of `f : ℂ → ℂ` of local index `k`: `f(z₀) = 0`, `f` has no other zero
in some `closedBall z₀ r`, and `f` has winding number `k` along every counterclockwise circle
`t ↦ z₀ + ρ e^{2πit}`, `0 < ρ < r`. -/
def HasZeroIndex (f : ℂ → ℂ) (z₀ : ℂ) (k : ℤ) : Prop :=
  f z₀ = 0 ∧ ∃ r > 0, (∀ z ∈ closedBall z₀ r, z ≠ z₀ → f z ≠ 0) ∧
    ∀ ρ ∈ Set.Ioo 0 r, HasLoopWind (fun t => f (z₀ + ccwLoop ρ t)) k

/-- Hryniewicz (14): `wind_π(u) = k` on `ℂ \ Γ`. The zeros of `π ∂ₛu` in `ℂ \ Γ` form a finite set
`Z`, each `z ∈ Z` is an isolated zero of `piDs H u` of some local index, and these indices sum
to `k`. -/
def HasWindPi (H : V 1 → ℝ) (u : ℂ → V 1) (Γ : Finset ℂ) (k : ℤ) : Prop :=
  ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ z ∉ Γ ∧ piDs H u z = 0) ∧
    ∃ idx : ℂ → ℤ, (∀ z ∈ Z, HasZeroIndex (piDs H u) z (idx z)) ∧ ∑ z ∈ Z, idx z = k

/-- Hryniewicz (16) at one puncture: along the end `e` with sign `ε`, for all large `s` the loop
`t ↦ π ∂ₛw(s, εt)` (in the global frame) has winding number `k`. -/
def HasWindInfAt (H : V 1 → ℝ) (u : ℂ → V 1) (e : ℝ → ℝ → ℂ) (ε : ℝ) (k : ℤ) : Prop :=
  ∃ s₀ : ℝ, ∀ s ≥ s₀, HasLoopWind (fun t =>
    xiCoordC H (endW H u e (s, ε * t))
      (piXi H (endW H u e (s, ε * t)) (fderiv ℝ (endW H u e) (s, ε * t) (1, 0)))) k

/-- Hryniewicz, Definition 2.14: `u` is a fast finite-energy plane. It is a finite-energy
`J̃`-holomorphic plane, its puncture `∞` is nondegenerate (Definition 2.9) with a prime asymptotic
limit `P`, and `wind_π(u) = 0`. -/
def IsFastPlane (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (u : ℂ → V 1) : Prop :=
  IsFiniteEnergyCurve H J Set.univ u ∧
    (∃ P : ReebOrbit H, P.IsPrime ∧ IsNondegenerateEnd H u cylInf P 1) ∧ HasWindPi H u ∅ 0

end

end FiniteEnergyPlane


