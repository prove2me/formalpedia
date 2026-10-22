-- Prove2me | Definitions.Def_FiniteEnergyPlane_Asymptotics
-- name    : FiniteEnergyPlane_Asymptotics
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-21T12:40:27.152334+00:00
-- url     : https://prove2.me/theorems/98ce7492-504b-427c-ac36-093203afd80d
-- title:
--   Asymptotic operators and asymptotic behaviour of finite-energy curves at a puncture
-- statement:
--   Objects for the asymptotic analysis of finite-energy pseudoholomorphic curves near a puncture, in the setting of `FiniteEnergyPlane_Setting` (U. Hryniewicz 2014, § 2.2.3; C. Wendl, *Lectures on Symplectic Field Theory*, §§ 3.1, 4.6, 4.8, 6.4). Throughout, $S=H^{-1}(1)\subset V=\mathbb{R}^{2n+2}$ is a strictly star-shaped level with Reeb field $R$ (its defining formula makes sense on all of $V$), $\xi$ its contact planes, $J$ a complex structure on $\xi$, and $P=(x,T)$ a periodic Reeb orbit.
--
--   1. **Linearized Reeb flow.** $\Phi:\mathbb{R}\to\operatorname{End}(V)$ with $\Phi(0)=\mathrm{id}$ and $\Phi'(\tau)=DR(x(\tau))\circ\Phi(\tau)$ for all $\tau$.
--   2. **Nondegenerate orbit.** For every such $\Phi$, the only $v\in\xi_{x(0)}$ with $\Phi(T)v=v$ is $v=0$.
--   3. **$\xi$-loops.** $\eta:\mathbb{R}\to V$ is $C^\infty$, $1$-periodic, and $\eta(t)\in\xi_{x(Tt)}$ for all $t$.
--   4. **Asymptotic operator.** $A_P\eta(t)=J(x(Tt))\big(-\eta'(t)+T\,DR(x(Tt))\,\eta(t)\big)$. An **eigenvector** with eigenvalue $\mu\in\mathbb{R}$ is a $\xi$-loop $v$, not identically zero, with $A_Pv=\mu v$.
--   5. **Unitary frames.** $Z:\mathbb{R}\to\operatorname{Hom}(\mathbb{R}^{2n},V)$, $C^\infty$ and $1$-periodic, with $Z(t)$ mapping $\mathbb{R}^{2n}$ into and onto $\xi_{x(Tt)}$, $J(x(Tt))Z(t)=Z(t)J_0$, and $\omega_0(Z(t)a,Z(t)b)=\langle J_0a,b\rangle$.
--   6. **Decay on an end.** For $f:\mathbb{R}\times\mathbb{R}\to F$: $f\to0$ *uniformly* if $\sup_t\|f(s,t)\|\to0$ as $s\to+\infty$; $f\to0$ *in $C^\infty$* if $f$ is $C^\infty$ on some $(s_0,\infty)\times\mathbb{R}$ and $\sup_t\|D^mf(s,t)\|\to0$ as $s\to+\infty$ for every $m\ge0$; $f$ *decays like $e^{-bs}$ in $C^\infty$* if $f$ is $C^\infty$ on some $(s_0,\infty)\times\mathbb{R}$ and for every $m$ there are $C,s_1$ with $\|D^mf(s,t)\|\le Ce^{-bs}$ for $s\ge s_1$.
--   7. **Cylindrical ends.** At the puncture $0$: $e(s,t)=e^{-2\pi(s+it)}$; at $\infty$: $e(s,t)=e^{2\pi(s+it)}$. For $u:\mathbb{C}\to V$, $a(s,t)=a(u(e(s,t)))$ and $w(s,t)=\mathrm{proj}(u(e(s,t)))\in S$.
--   8. **Nondegenerate puncture** with sign $\varepsilon$ (Hryniewicz, Definition 2.9 (1), (2), (4)): there are $d,c\in\mathbb{R}$ and $b>0$ with $a(s,t)-\varepsilon Ts-d\to0$ and $e^{bs}\big(w(s,t)-x(\varepsilon Tt+c)\big)\to0$ uniformly.
--   9. **Asymptotically cylindrical end:** for some $d,c$, $a(s,t)-\varepsilon Ts-d\to0$ and $w(s,t)-x(\varepsilon Tt+c)\to0$ in $C^\infty$.
--   10. **Exponential asymptotics with rate $b$:** for some $d,c$, both $a(s,t)-\varepsilon Ts-d$ and $w(s,t)-x(\varepsilon Tt+c)$ decay like $e^{-bs}$ in $C^\infty$.
--   11. **Asymptotic eigenvalue $\mu$ and eigenvector $v$:** $v$ is an eigenvector of $A_P$ with eigenvalue $\mu$, $\varepsilon\mu<0$, and there are $c$, $s_0$, $\tau:\mathbb{R}^2\to\mathbb{R}$ and $r:\mathbb{R}^2\to V$ with $\tau(s,t)-\varepsilon Tt-c\to0$ and $r\to0$ in $C^\infty$, such that for $s\ge s_0$ and all $t$, with $h(s,t)=e^{\varepsilon\mu s}\big(v(\tau(s,t)/T)+r(s,t)\big)$: $h(s,t)\in\xi_{x(\tau(s,t))}$ and $w(s,t)=\mathrm{proj}\big(x(\tau(s,t))+h(s,t)\big)$.
--   12. **Half-cylinder equations.** For $S:\mathbb{R}^2\to\mathbb{R}^{2n\times2n}$ and $S_\infty:\mathbb{R}\to\mathbb{R}^{2n\times2n}$: $S\to S_\infty$ in $C^\infty$, or exponentially with rate $d$, means that every entry of $S(s,t)-S_\infty(t)$ does. $\zeta:\mathbb{R}^2\to\mathbb{R}^{2n}$ is a *solution* if it is $C^\infty$ on $(0,\infty)\times\mathbb{R}$, $1$-periodic in $t$, and $\partial_s\zeta+J_0\partial_t\zeta+S\zeta=0$ there. An *eigenfunction* of $-J_0\partial_t-S_\infty$ with eigenvalue $\mu$ is a $C^\infty$ $1$-periodic $e\neq0$ with $-J_0e'-S_\infty e=\mu e$.
--
--   **Formalization Note** Matrices, $J_0$, $\mathbb{R}^{2n}$ and the operator $\partial_s+J_0\partial_t+S$ are `CauchyRiemannIndex.Mat n`, `CauchyRiemannIndex.J₀ n`, `CauchyRiemannIndex.Vec n` (Euclidean, indexed by `Fin n ⊕ Fin n`) and `CauchyRiemannIndex.crOp`. Derivatives of maps on $\mathbb{R}^2$ are `iteratedFDeriv ℝ m f (s, t)` with operator norms, on maps `ℝ × ℝ → F`; derivatives of loops are `deriv`. The cylindrical coordinates are `cylEnd s t = cwLoop 0 (Real.exp (-(2 * π * s))) t` and `cylInf s t = ccwLoop (Real.exp (2 * π * s)) t`, so `t ↦ endW H u cylEnd (s, t)` is the loop `loopInS H u (cwLoop 0 (e^{-2πs}))` of the previous mission. The phase $\tau$ in item 11 is real-valued, so $v(\tau/T)$ is defined also for multiply covered orbits.
-- source:
--   U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.3 (Definitions 2.5, 2.9, Theorem 2.11); C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Sections 3.1, 4.6, 4.8, 6.4

import Definitions.Def_FiniteEnergyPlane_Setting
import Definitions.Def_CauchyRiemannIndex_Setting

/-!
# Asymptotic operators and asymptotic behaviour of finite-energy curves at a puncture

U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 2.2.3 (Definitions 2.5 and 2.9, Theorem 2.11);
C. Wendl, *Lectures on Symplectic Field Theory* (2026 notes), §§ 3.1, 4.6, 4.8, 6.4 and 6.7.
Everything is in the setting of `FiniteEnergyPlane_Setting`: `V n = ℝ^{2n+2}`, a strictly
star-shaped level `S = H⁻¹(1)`, its Reeb field `R = reeb H`, the contact planes `ξ` and a
compatible `J` on `ξ`.

Conventions.
* The formula for `reeb H` makes sense on all of `V n`. Its derivative along a
  periodic orbit `P = (x, T)` gives the linearized Reeb flow `Φ(τ)`, with `Φ(0) = id` and
  `Φ'(τ) = DR(x(τ)) Φ(τ)`. `P` is nondegenerate if `Φ(T)` has no nonzero fixed vector in `ξ_{x(0)}`.
* A `ξ`-loop along `P` is a smooth `1`-periodic `η : ℝ → V n` with `η(t) ∈ ξ_{x(Tt)}`. The
  asymptotic operator (Hryniewicz (13), for the flat connection of `V n`) is
  `A_P η (t) = J(x(Tt)) (-η'(t) + T DR(x(Tt)) η(t))`.
* Cylindrical coordinates at the puncture `0` of a map on a punctured disk are
  `(s, t) ↦ e^{-2π(s + it)}`, written as `cwLoop 0 (e^{-2πs}) t`, and at `∞` for a plane
  `(s, t) ↦ e^{2π(s + it)} = ccwLoop (e^{2πs}) t`. In both cases `s → +∞` approaches the puncture.
  Along an end `e`, `a(s, t) = aCoord H (u (e s t))` and `w(s, t) = proj H (u (e s t)) ∈ S`.
* Decay on an end is stated for maps `f : ℝ × ℝ → F`: uniformly in `t` as `s → +∞`, for `f`
  itself or for every derivative `D^m f` (with `f` smooth on some `(s₀, ∞) × ℝ`).
* Matrix coefficients on the half-cylinder use `CauchyRiemannIndex.Mat n`, `J₀ n` and
  `crOp S ζ = ∂ₛζ + J₀ ∂ₜζ + S ζ` on `CauchyRiemannIndex.Vec n = ℝ^{2n}`; matrix-valued
  convergence is entrywise.
-/

namespace FiniteEnergyPlane

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

variable {n : ℕ}

/-! ### Linearized Reeb flow and nondegeneracy -/

/-- `Φ` is the linearized Reeb flow along `P`: `Φ(0) = id` and `Φ'(τ) = DR(x(τ)) ∘ Φ(τ)`. -/
def IsLinReebFlow {H : V n → ℝ} (P : ReebOrbit H) (Φ : ℝ → V n →L[ℝ] V n) : Prop :=
  Φ 0 = ContinuousLinearMap.id ℝ (V n) ∧
    ∀ τ : ℝ, HasDerivAt Φ ((fderiv ℝ (reeb H) (P.x τ)).comp (Φ τ)) τ

/-- `P = (x, T)` is nondegenerate: the linearized Reeb flow `Φ(T)` fixes no nonzero vector of
`ξ_{x(0)}`. -/
def ReebOrbit.IsNondegenerate {H : V n → ℝ} (P : ReebOrbit H) : Prop :=
  ∀ Φ : ℝ → V n →L[ℝ] V n, IsLinReebFlow P Φ →
    ∀ v : V n, IsInXi H (P.x 0) v → Φ P.T v = v → v = 0

/-! ### The asymptotic operator -/

/-- `η` is a `ξ`-loop along `P`: smooth, `1`-periodic, and `η(t) ∈ ξ_{x(Tt)}` for all `t`. -/
def IsXiLoop {H : V n → ℝ} (P : ReebOrbit H) (η : ℝ → V n) : Prop :=
  ContDiff ℝ ∞ η ∧ Function.Periodic η 1 ∧ ∀ t : ℝ, IsInXi H (P.x (P.T * t)) (η t)

/-- Hryniewicz, Definition 2.5: the asymptotic operator at `P`,
`A_P η (t) = J(x(Tt)) (-η'(t) + T DR(x(Tt)) η(t))`. -/
def asympOp {H : V n → ℝ} (J : V n → V n →L[ℝ] V n) (P : ReebOrbit H) (η : ℝ → V n)
    (t : ℝ) : V n :=
  J (P.x (P.T * t)) (-(deriv η t) + P.T • fderiv ℝ (reeb H) (P.x (P.T * t)) (η t))

/-- `v` is an eigenvector of `A_P` with eigenvalue `μ`: a `ξ`-loop, not identically zero, with
`A_P v = μ v`. -/
def IsAsymptoticEigen {H : V n → ℝ} (J : V n → V n →L[ℝ] V n) (P : ReebOrbit H) (μ : ℝ)
    (v : ℝ → V n) : Prop :=
  IsXiLoop P v ∧ (∃ t : ℝ, v t ≠ 0) ∧ ∀ t : ℝ, asympOp J P v t = μ • v t

/-- `Z` is a unitary frame of `ξ` along `P`: a smooth `1`-periodic family of linear maps
`Z(t) : ℝ^{2n} → V n` onto `ξ_{x(Tt)}` with `J Z = Z J₀` and `ω₀(Z a, Z b) = ⟨J₀ a, b⟩`. -/
def IsUnitaryXiFrame {H : V n → ℝ} (J : V n → V n →L[ℝ] V n) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n) : Prop :=
  ContDiff ℝ ∞ Z ∧ Function.Periodic Z 1 ∧ ∀ t : ℝ,
    (∀ a, IsInXi H (P.x (P.T * t)) (Z t a)) ∧
    (∀ w, IsInXi H (P.x (P.T * t)) w → ∃ a, Z t a = w) ∧
    (∀ a, J (P.x (P.T * t)) (Z t a) = Z t (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) a)) ∧
    ∀ a b, omega0 (Z t a) (Z t b) = inner ℝ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) a) b

/-! ### Decay on a cylindrical end -/

/-- `f(s, t) → 0` uniformly in `t` as `s → +∞`. -/
def TendstoZeroUnif {F : Type*} [NormedAddCommGroup F] (f : ℝ × ℝ → F) : Prop :=
  ∀ ε > 0, ∃ s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ, ‖f (s, t)‖ ≤ ε

/-- `f → 0` in `C^∞` on the end: `f` is smooth on some `(s₀, ∞) × ℝ`, and every derivative
`D^m f(s, t)` tends to `0` uniformly in `t` as `s → +∞`. -/
def TendstoZeroCInfty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × ℝ → F) :
    Prop :=
  (∃ s₀ : ℝ, ContDiffOn ℝ ∞ f (Set.Ioi s₀ ×ˢ Set.univ)) ∧
    ∀ m : ℕ, ∀ ε > 0, ∃ s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ‖iteratedFDeriv ℝ m f (s, t)‖ ≤ ε

/-- `f` decays like `e^{-bs}` in `C^∞` on the end: `f` is smooth on some `(s₀, ∞) × ℝ`, and for
every `m` there are `C, s₁` with `‖D^m f(s, t)‖ ≤ C e^{-bs}` for `s ≥ s₁` and all `t`. -/
def ExpDecayCInfty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × ℝ → F)
    (b : ℝ) : Prop :=
  (∃ s₀ : ℝ, ContDiffOn ℝ ∞ f (Set.Ioi s₀ ×ˢ Set.univ)) ∧
    ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ,
      ‖iteratedFDeriv ℝ m f (s, t)‖ ≤ C * Real.exp (-(b * s))

/-! ### Cylindrical ends of a finite-energy curve -/

/-- Positive cylindrical coordinates at the puncture `0`: `(s, t) ↦ e^{-2π(s + it)}`. -/
def cylEnd (s t : ℝ) : ℂ := cwLoop 0 (Real.exp (-(2 * π * s))) t

/-- Positive cylindrical coordinates at `∞`: `(s, t) ↦ e^{2π(s + it)}`. -/
def cylInf (s t : ℝ) : ℂ := ccwLoop (Real.exp (2 * π * s)) t

/-- The coordinate `a(s, t) = aCoord H (u (e s t))` along the end `e`. -/
def endA (H : V n → ℝ) (u : ℂ → V n) (e : ℝ → ℝ → ℂ) (p : ℝ × ℝ) : ℝ :=
  aCoord H (u (e p.1 p.2))

/-- The coordinate `w(s, t) = proj H (u (e s t)) ∈ S` along the end `e`. -/
def endW (H : V n → ℝ) (u : ℂ → V n) (e : ℝ → ℝ → ℂ) (p : ℝ × ℝ) : V n :=
  proj H (u (e p.1 p.2))

/-- Hryniewicz, Definition 2.9 (1), (2), (4): along the end `e`, `u` is asymptotic to `P` with
sign `ε` and exponential `C⁰` decay. There are `d, c` and `b > 0` with
`a(s, t) - εTs - d → 0` and `e^{bs} (w(s, t) - x(εTt + c)) → 0`, uniformly in `t`. -/
def IsNondegenerateEnd (H : V n → ℝ) (u : ℂ → V n) (e : ℝ → ℝ → ℂ) (P : ReebOrbit H)
    (ε : ℝ) : Prop :=
  ∃ d c b : ℝ, 0 < b ∧
    TendstoZeroUnif (fun p : ℝ × ℝ => endA H u e p - ε * P.T * p.1 - d) ∧
    TendstoZeroUnif (fun p : ℝ × ℝ =>
      Real.exp (b * p.1) • (endW H u e p - P.x (ε * P.T * p.2 + c)))

/-- Along the end `e`, `u` is asymptotically cylindrical over `P` with sign `ε`: for some `d, c`,
`a(s, t) - εTs - d → 0` and `w(s, t) - x(εTt + c) → 0` in `C^∞`. -/
def IsAsymptoticallyCylindricalEnd (H : V n → ℝ) (u : ℂ → V n) (e : ℝ → ℝ → ℂ)
    (P : ReebOrbit H) (ε : ℝ) : Prop :=
  ∃ d c : ℝ,
    TendstoZeroCInfty (fun p : ℝ × ℝ => endA H u e p - ε * P.T * p.1 - d) ∧
    TendstoZeroCInfty (fun p : ℝ × ℝ => endW H u e p - P.x (ε * P.T * p.2 + c))

/-- Along the end `e`, `u` converges to the trivial cylinder over `P` (sign `ε`) exponentially
fast with rate `b` in `C^∞`: for some `d, c`, both `a(s, t) - εTs - d` and `w(s, t) - x(εTt + c)`
decay like `e^{-bs}` together with all derivatives. -/
def HasExpAsymptoticsEnd (H : V n → ℝ) (u : ℂ → V n) (e : ℝ → ℝ → ℂ) (P : ReebOrbit H)
    (ε b : ℝ) : Prop :=
  ∃ d c : ℝ,
    ExpDecayCInfty (fun p : ℝ × ℝ => endA H u e p - ε * P.T * p.1 - d) b ∧
    ExpDecayCInfty (fun p : ℝ × ℝ => endW H u e p - P.x (ε * P.T * p.2 + c)) b

/-- Hryniewicz, Theorem 2.11 (asymptotic eigenvalue `μ` and eigenvector `v` of `u` along the end
`e`): `v` is an eigenvector of `A_P` with eigenvalue `μ`, `εμ < 0`, and the end is written in the
tube `(τ, h) ↦ proj H (x(τ) + h)`, `h ∈ ξ_{x(τ)}`, as
`w(s, t) = proj H (x(τ(s, t)) + h(s, t))` with `h(s, t) = e^{εμs} (v(τ(s, t) / T) + r(s, t))`,
for `s ≥ s₀`, where `τ(s, t) - εTt - c → 0` and `r → 0` in `C^∞`. -/
def HasAsymptoticEigenvector (H : V n → ℝ) (J : V n → V n →L[ℝ] V n) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) (ε μ : ℝ) (v : ℝ → V n) : Prop :=
  IsAsymptoticEigen J P μ v ∧ ε * μ < 0 ∧
    ∃ (c : ℝ) (τ : ℝ × ℝ → ℝ) (r : ℝ × ℝ → V n) (s₀ : ℝ),
      TendstoZeroCInfty (fun p : ℝ × ℝ => τ p - ε * P.T * p.2 - c) ∧ TendstoZeroCInfty r ∧
      ∀ s ≥ s₀, ∀ t : ℝ,
        let h := Real.exp (ε * μ * s) • (v (τ (s, t) / P.T) + r (s, t))
        IsInXi H (P.x (τ (s, t))) h ∧ endW H u e (s, t) = proj H (P.x (τ (s, t)) + h)

/-! ### Linear Cauchy–Riemann equations on a half-cylinder -/

/-- `S(s, t) → S∞(t)` in `C^∞` as `s → +∞`, entrywise. -/
def IsCInftyAsymptoticTo (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) : Prop :=
  ∀ i j, TendstoZeroCInfty (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j)

/-- `S(s, t) - S∞(t)` decays like `e^{-ds}` in `C^∞` as `s → +∞`, entrywise. -/
def IsExpAsymptoticTo (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (Sinf : ℝ → CauchyRiemannIndex.Mat n) (d : ℝ) : Prop :=
  ∀ i j, ExpDecayCInfty (fun p : ℝ × ℝ => S p i j - Sinf p.2 i j) d

/-- `ζ` solves `∂ₛζ + J₀ ∂ₜζ + S ζ = 0` on the half-cylinder `(0, ∞) × ℝ/ℤ`: it is smooth on
`(0, ∞) × ℝ`, `1`-periodic in `t`, and satisfies the equation there. -/
def IsHalfCylSolution (S : ℝ × ℝ → CauchyRiemannIndex.Mat n)
    (ζ : ℝ × ℝ → CauchyRiemannIndex.Vec n) : Prop :=
  ContDiffOn ℝ ∞ ζ (Set.Ioi 0 ×ˢ Set.univ) ∧ (∀ s t : ℝ, ζ (s, t + 1) = ζ (s, t)) ∧
    ∀ s > 0, ∀ t : ℝ, CauchyRiemannIndex.crOp S ζ (s, t) = 0

/-- `e` is an eigenfunction of `A = -J₀ ∂ₜ - S∞` with eigenvalue `μ`: smooth, `1`-periodic, not
identically zero, with `-J₀ e' - S∞ e = μ e`. -/
def IsLoopEigen (Sinf : ℝ → CauchyRiemannIndex.Mat n) (μ : ℝ)
    (e : ℝ → CauchyRiemannIndex.Vec n) : Prop :=
  ContDiff ℝ ∞ e ∧ Function.Periodic e 1 ∧ (∃ t : ℝ, e t ≠ 0) ∧ ∀ t : ℝ,
    -(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv e t)) -
      Matrix.toEuclideanLin (Sinf t) (e t) = μ • e t

end

end FiniteEnergyPlane


