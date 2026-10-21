-- Prove2me | Definitions.Def_NewtonCartan_defs
-- name    : NewtonCartan_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-20T23:16:38.171985+00:00
-- url     : https://prove2.me/theorems/aba6278e-7111-440c-8bd7-8f7c9aa3f931
-- title:
--   Classical spacetimes on R^4, Trautman geometrization, and the categories NG1, NG2, GNG
-- statement:
--   On $\mathbb R^4$ (global chart, index 0 = time) with $t_a=dx^0$ and $h^{ab}=\mathrm{diag}(0,1,1,1)$: derivative operators as smooth symmetric Christoffel fields; compatibility $\nabla_at_b=0$, $\nabla_ah^{bc}=0$; Riemann tensor in Malament's convention, Ricci $R_{bc}=R^n{}_{bcn}$, raised forms $R^a{}_b{}^c{}_d$, $R^{ab}{}_{cd}$; Poisson's equation $h^{ab}\nabla_a\nabla_b\varphi=4\pi\rho$; NG objects (flat compatible $\nabla$, smooth $\varphi$); geometrization $\tilde\Gamma=\Gamma+t_bt_c\nabla^a\varphi$; GNG objects (compatible, curvature conditions (1)-(3) for some smooth $\rho$); unit-timelike curves, geodesics and Newtonian trajectories on open intervals; diffeomorphisms preserving $t,h$ and carrying one Christoffel field to another (transformation law); arrows of GNG, NG$_1$ and NG$_2$ (gauge $\psi$ with $\nabla^a\nabla^b\psi=0$, gauge-transformed $\Gamma-t_bt_c\nabla^a\psi$).
-- source:
--   J. O. Weatherall, Are Newtonian Gravitation and Geometrized Newtonian Gravitation Theoretically Equivalent?, Erkenntnis 81 (2016) 1073-1091, https://arxiv.org/abs/1411.5757, Sections 2 and 6; D. B. Malament, Topics in the Foundations of General Relativity and Newtonian Gravitation Theory (2012), Ch. 4

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Newtonian gravitation and geometrized Newtonian gravitation on `ℝ⁴`

Setting of J. O. Weatherall, "Are Newtonian Gravitation and Geometrized Newtonian Gravitation
Theoretically Equivalent?", Erkenntnis 81 (2016) 1073–1091, arXiv:1411.5757, §2 and §6, with the
conventions of D. Malament, *Topics in the Foundations of General Relativity and Newtonian
Gravitation Theory* (2012), Ch. 4. Spacetime is `ℝ⁴` (Weatherall, p. 3), written in one global
chart `E = Fin 4 → ℝ`; index `0` is time and `1, 2, 3` are space.

The classical metrics are the standard ones: the temporal 1-form `t_a = dx⁰` (`tt`) and the spatial
metric `h^{ab} = diag(0,1,1,1)` (`hh`). A derivative operator is a smooth field of Christoffel
symbols `Γ x a b c = Γ^a_{bc}(x)`, symmetric in `b c` (torsion-free), acting by
`∇_b ξ^a = ∂_b ξ^a + Γ^a_{bn} ξ^n` and `∇_b α_c = ∂_b α_c - Γ^n_{bc} α_n`.

* `riem Γ x a b c d` — Riemann tensor `R^a_{bcd}` in Malament's sign convention
  `ξ^b R^a_{bcd} = -2 ∇_{[c} ∇_{d]} ξ^a`; `ricci Γ x b c = R^n_{bcn}`.
* `IsNG Γ φ` — objects of NG: flat, compatible derivative operator with a smooth potential.
* `geomΓ Γ φ` — Trautman geometrization `∇̃ = (∇, C^a_{bc} = -t_b t_c ∇^a φ)`, i.e.
  `Γ̃^a_{bc} = Γ^a_{bc} + t_b t_c h^{an} ∂_n φ`.
* `IsGNG Γ` — objects of GNG: compatible derivative operators obeying conditions (1)–(3).
* `IsGNGArrow`, `IsNG1Arrow`, `IsNG2Arrow` — arrows of Weatherall's categories GNG, NG₁, NG₂ (§6),
  on the diffeomorphism level (`f : E ≃ E`, smooth with smooth inverse).
-/

open scoped ContDiff

namespace NewtonCartan

/-- Spacetime `ℝ⁴` in a global chart; coordinate `0` is time. -/
abbrev E := Fin 4 → ℝ

/-- Partial derivative `∂_b f (x)` of a scalar field. -/
noncomputable def pd (f : E → ℝ) (b : Fin 4) (x : E) : ℝ := fderiv ℝ f x (Pi.single b 1)

/-- Second partial derivative `∂_b ∂_c f (x)`. -/
noncomputable def pd2 (f : E → ℝ) (b c : Fin 4) (x : E) : ℝ := pd (fun y => pd f c y) b x

/-- The temporal metric 1-form `t_a = dx⁰` (components). -/
def tt (a : Fin 4) : ℝ := if a = 0 then 1 else 0

/-- The spatial metric `h^{ab} = diag(0,1,1,1)`. -/
def hh (a b : Fin 4) : ℝ := if a = b ∧ a ≠ 0 then 1 else 0

/-- A field of Christoffel symbols `Γ x a b c = Γ^a_{bc}(x)`. -/
abbrev Conn := E → Fin 4 → Fin 4 → Fin 4 → ℝ

/-- A (Malament) derivative operator: smooth and torsion-free. -/
def IsDerivOp (Γ : Conn) : Prop :=
  ContDiff ℝ ∞ Γ ∧ ∀ x a b c, Γ x a b c = Γ x a c b

/-- Compatibility with the classical metrics: `∇_b t_c = 0` and `∇_a h^{bc} = 0`. -/
def Compatible (Γ : Conn) : Prop :=
  (∀ x b c, ∑ n, Γ x n b c * tt n = 0) ∧
  (∀ x a b c, ∑ n, (Γ x b a n * hh n c + Γ x c a n * hh b n) = 0)

/-- A classical spacetime `(ℝ⁴, t_a, h^{ab}, ∇)`. -/
def IsClassical (Γ : Conn) : Prop := IsDerivOp Γ ∧ Compatible Γ

/-- Riemann tensor `R^a_{bcd}` (Malament's convention `ξ^b R^a_{bcd} = -2∇_{[c}∇_{d]}ξ^a`). -/
noncomputable def riem (Γ : Conn) (x : E) (a b c d : Fin 4) : ℝ :=
  pd (fun y => Γ y a c b) d x - pd (fun y => Γ y a d b) c x
    + ∑ e, (Γ x a d e * Γ x e c b - Γ x a c e * Γ x e d b)

/-- Ricci tensor `R_{bc} = R^n_{bcn}`. -/
noncomputable def ricci (Γ : Conn) (x : E) (b c : Fin 4) : ℝ := ∑ n, riem Γ x n b c n

/-- `R^a{}_b{}^c{}_d = R^a_{bnd} h^{nc}`. -/
noncomputable def riemUp3 (Γ : Conn) (x : E) (a b c d : Fin 4) : ℝ :=
  ∑ n, riem Γ x a b n d * hh n c

/-- `R^{ab}{}_{cd} = R^a_{ncd} h^{nb}`. -/
noncomputable def riemUp2 (Γ : Conn) (x : E) (a b c d : Fin 4) : ℝ :=
  ∑ n, riem Γ x a n c d * hh n b

/-- Flatness `R^a_{bcd} = 0`. -/
def IsFlat (Γ : Conn) : Prop := ∀ x a b c d, riem Γ x a b c d = 0

/-- Second covariant derivative of a scalar, `∇_a ∇_b φ = ∂_a∂_b φ - Γ^n_{ab} ∂_n φ`. -/
noncomputable def hess (Γ : Conn) (φ : E → ℝ) (x : E) (a b : Fin 4) : ℝ :=
  pd2 φ a b x - ∑ n, Γ x n a b * pd φ n x

/-- `∇^a ∇_a φ = h^{ab} ∇_a ∇_b φ`. -/
noncomputable def lap (Γ : Conn) (φ : E → ℝ) (x : E) : ℝ :=
  ∑ a, ∑ b, hh a b * hess Γ φ x a b

/-- Poisson's equation `∇^a ∇_a φ = 4πρ`. -/
def Poisson (Γ : Conn) (φ ρ : E → ℝ) : Prop := ∀ x, lap Γ φ x = 4 * Real.pi * ρ x

/-- `∇^a φ = h^{an} ∂_n φ`. -/
noncomputable def gradUp (φ : E → ℝ) (x : E) (a : Fin 4) : ℝ := ∑ n, hh a n * pd φ n x

/-- Objects of NG (both NG₁ and NG₂): a flat classical spacetime with a smooth gravitational
potential `φ`. The mass density is `ρ = ∇^a∇_a φ / 4π`. -/
def IsNG (Γ : Conn) (φ : E → ℝ) : Prop := IsClassical Γ ∧ IsFlat Γ ∧ ContDiff ℝ ∞ φ

/-- Trautman geometrization `∇̃ = (∇, -t_b t_c ∇^a φ)`: `Γ̃^a_{bc} = Γ^a_{bc} + t_b t_c ∇^a φ`. -/
noncomputable def geomΓ (Γ : Conn) (φ : E → ℝ) : Conn :=
  fun x a b c => Γ x a b c + tt b * tt c * gradUp φ x a

/-- The curvature conditions of Prop. 2.1: (1) `R_{ab} = 4πρ t_a t_b`,
(2) `R^a{}_b{}^c{}_d = R^c{}_d{}^a{}_b`, (3) `R^{ab}{}_{cd} = 0`. -/
def CurvConds (Γ : Conn) (ρ : E → ℝ) : Prop :=
  (∀ x a b, ricci Γ x a b = 4 * Real.pi * ρ x * tt a * tt b) ∧
  (∀ x a b c d, riemUp3 Γ x a b c d = riemUp3 Γ x c d a b) ∧
  (∀ x a b c d, riemUp2 Γ x a b c d = 0)

/-- Objects of GNG: classical spacetimes satisfying (1)–(3) for some smooth mass density. -/
def IsGNG (Γ : Conn) : Prop := IsClassical Γ ∧ ∃ ρ : E → ℝ, ContDiff ℝ ∞ ρ ∧ CurvConds Γ ρ

/-! ### Curves -/

/-- Acceleration `ξ^n ∇_n ξ^a` of a curve `γ` at parameter `s` (with `ξ = γ'`). -/
noncomputable def accel (Γ : Conn) (γ : ℝ → E) (s : ℝ) (a : Fin 4) : ℝ :=
  deriv (deriv γ) s a + ∑ b, ∑ c, Γ (γ s) a b c * deriv γ s b * deriv γ s c

/-- A smooth timelike curve on the open interval `(s₀, s₁)`, parametrized by elapsed time:
its tangent `ξ^a` has unit temporal length, `t_a ξ^a = 1` (the unit tangent of a massive body). -/
def IsTimelikeOn (γ : ℝ → E) (s₀ s₁ : ℝ) : Prop :=
  s₀ < s₁ ∧ ContDiffOn ℝ ∞ γ (Set.Ioo s₀ s₁) ∧ ∀ s ∈ Set.Ioo s₀ s₁, deriv γ s 0 = 1

/-- `ξ^n ∇_n ξ^a = 0` along `γ` on `(s₀, s₁)`. -/
def IsGeodesicOn (Γ : Conn) (γ : ℝ → E) (s₀ s₁ : ℝ) : Prop :=
  ∀ s ∈ Set.Ioo s₀ s₁, ∀ a, accel Γ γ s a = 0

/-- Newton's law `ξ^n ∇_n ξ^a = -∇^a φ` along `γ` on `(s₀, s₁)`. -/
def IsNewtonianOn (Γ : Conn) (φ : E → ℝ) (γ : ℝ → E) (s₀ s₁ : ℝ) : Prop :=
  ∀ s ∈ Set.Ioo s₀ s₁, ∀ a, accel Γ γ s a = -gradUp φ (γ s) a

/-- Empirical agreement: the timelike geodesics of `Γ'` are exactly the Newtonian trajectories
of `(Γ, φ)`. -/
def SameTrajectories (Γ : Conn) (φ : E → ℝ) (Γ' : Conn) : Prop :=
  ∀ γ s₀ s₁, IsTimelikeOn γ s₀ s₁ → (IsGeodesicOn Γ' γ s₀ s₁ ↔ IsNewtonianOn Γ φ γ s₀ s₁)

/-! ### Diffeomorphisms and arrows -/

/-- A diffeomorphism of `ℝ⁴`: a bijection, smooth with smooth inverse. -/
def IsDiffeo (f : E ≃ E) : Prop := ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ f.symm

/-- `f` preserves the classical metrics: `f*(t_a) = t_a` and `f_*(h^{ab}) = h^{ab}`. -/
def PreservesMetrics (f : E ≃ E) : Prop :=
  (∀ x b, ∑ a, tt a * pd (fun y => f y a) b x = tt b) ∧
  (∀ x a b, ∑ c, ∑ d, pd (fun y => f y a) c x * pd (fun y => f y b) d x * hh c d = hh a b)

/-- `f` maps the derivative operator `Γ` to `Γ'` (`f_* ∇ = ∇'`), via the transformation law
`∂_b∂_c f^a + Γ'^a_{de}(f x) ∂_b f^d ∂_c f^e = ∂_n f^a Γ^n_{bc}(x)`. -/
def MapsConn (f : E ≃ E) (Γ Γ' : Conn) : Prop :=
  ∀ x a b c, pd2 (fun y => f y a) b c x
      + ∑ d, ∑ e, Γ' (f x) a d e * pd (fun y => f y d) b x * pd (fun y => f y e) c x
    = ∑ n, pd (fun y => f y a) n x * Γ x n b c

/-- Arrows of GNG: diffeomorphisms preserving `t_a`, `h^{ab}` and the derivative operator. -/
def IsGNGArrow (Γ Γ' : Conn) (f : E ≃ E) : Prop :=
  IsDiffeo f ∧ PreservesMetrics f ∧ MapsConn f Γ Γ'

/-- Arrows of NG₁ (Option 1): diffeomorphisms preserving the metrics, `∇` and `φ`. -/
def IsNG1Arrow (Γ : Conn) (φ : E → ℝ) (Γ' : Conn) (φ' : E → ℝ) (f : E ≃ E) : Prop :=
  IsGNGArrow Γ Γ' f ∧ ∀ x, φ' (f x) = φ x

/-- Gauge functions: smooth `ψ` with `∇^a ∇^b ψ = 0`. -/
def IsGauge (Γ : Conn) (ψ : E → ℝ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ ∀ x a b, ∑ m, ∑ n, hh a m * hh b n * hess Γ ψ x m n = 0

/-- Gauge-transformed derivative operator `(∇, t_b t_c ∇^a ψ)`: `Γ^a_{bc} - t_b t_c ∇^a ψ`. -/
noncomputable def gaugeΓ (Γ : Conn) (ψ : E → ℝ) : Conn :=
  fun x a b c => Γ x a b c - tt b * tt c * gradUp ψ x a

/-- Arrows `(f, ψ)` of NG₂ (Option 2): `ψ` a gauge function and `f` a diffeomorphism preserving
the metrics and carrying `(∇, φ)` gauge transformed by `ψ` to `(∇', φ')`. -/
def IsNG2Arrow (Γ : Conn) (φ : E → ℝ) (Γ' : Conn) (φ' : E → ℝ) (f : E ≃ E) (ψ : E → ℝ) :
    Prop :=
  IsGauge Γ ψ ∧ IsGNGArrow (gaugeΓ Γ ψ) Γ' f ∧ ∀ x, φ' (f x) = φ x + ψ x

end NewtonCartan


