-- Prove2me | Definitions.Def_ViterboCap
-- name    : ViterboCap
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-04T17:47:23.178118+00:00
-- url     : https://prove2.me/theorems/d427b47f-5b58-4cef-8974-23d2d050fe04
-- title:
--   Notation for the Hofer–Zehnder proof that c_EHZ extends to a symplectic capacity — ℝ²ⁿ ≅ ℂⁿ, support functions, trigonometric loops, mollified gauges, cone and engine hypotheses
-- statement:
--   Definitions used by the standalone steps `Viterbo.Cap.*` of the proof of the Viterbo mission's capacity statement (Haim-Kislev–Ostrover, p. 2). Phase space is `OAI.SymmetricPolar.Phase n` $=\mathbb R^n\times\mathbb R^n$; `OAI.FourierPolynomial.Vector κ` is $\mathbb C^\kappa$ with its real inner product $\langle x,y\rangle=\operatorname{Re}\sum_j \overline{x_j}y_j$.
--
--   - `Viterbo.Capacities.Φ n` and `Viterbo.Capacities.Ψ n`: the mutually inverse real-linear maps $\mathbb R^n\times\mathbb R^n\to\mathbb C^n$, $(q,p)\mapsto q+ip$, and $\mathbb C^n\to\mathbb R^n\times\mathbb R^n$, $w\mapsto(\operatorname{Re}w,\operatorname{Im}w)$ (`phiL`, `psiL` are their linear-map versions).
--   - `supportFn L u` $=\sup\{\langle x,u\rangle : x\in L\}$ for $L\subseteq\mathbb C^\kappa$ (the real `sSup`, so $0$ when the set of values is empty or unbounded above).
--   - `trigLoop D b t` $=\sum_{m=-D}^{D}e^{2\pi i m t}\,b_m$, `trigVel D b t` $=\sum_{m=-D}^{D}2\pi i m\,e^{2\pi i m t}\,b_m$ (its derivative in $t$), and `trigAction D b` $=\pi\sum_{m=-D}^{D}m\,\|b_m\|^2$, for $b:\mathbb Z\to\mathbb C^\kappa$.
--   - `posCoeff b N`: the coefficient vector indexed by $\{0,\dots,N\}\times\kappa$ whose entry at $(i,j)$ is $b(i+1)_j$; with the frequencies `OAI.HamiltonianPeriodic.frequency N`, which send the right-hand copy of $\{0,\dots,N\}$ to $1,\dots,N+1$, it is the Galerkin vector of the loop $\sum_{m=1}^{N+1}e^{2\pi imt}b_m$.
--   - `ConeHyp H`: there are $b:\mathbb N\to\mathbb C^\kappa$ with $b_0=0$, some $b_m\neq0$ and $b_m=0$ for $m>D$, and constants $C_0$ and $c>0$, such that for every $N\ge D$, every coefficient vector $a$ on the nonpositive frequencies $0,-1,\dots,-N$ and every $s\ge0$, the Galerkin action functional `OAI.FourierPolynomial.action (frequency N) H` at `joinCoeff a (s • posCoeff b N)` is at most $C_0-c(\|a\|^2+s^2)$.
--   - `mollQ L φ z` $=\int \operatorname{gauge}_L(z-u)^2\,\rho(u)\,du$, where $\rho$ = `φ.normed volume` is the normalized smooth bump of `φ : ContDiffBump 0` (Lebesgue measure), and `homQ L φ z` $=\|z\|^2\,$`mollQ L φ`$(z/\|z\|)$ (which is $0$ at $z=0$).
--   - `Body L r`: $L$ is convex and bounded, $r>0$, and the open ball of radius $r$ about $0$ lies in $L$.
--   - `EngineHyp H V C R γ₀`: $H$ is $C^\infty$; $\|\nabla H(z)\|\le C(1+\|z\|)$; $V$ is continuous with $\|V(z)\|\le C\|z\|$; for every $B$ and $\varepsilon>0$ there is $r_0>0$ with $\|r^{-1}\nabla H(rz)-V(z)\|\le\varepsilon$ whenever $r\ge r_0$ and $\|z\|\le B$; $\gamma_0>0$; and $\tfrac12\langle\nabla H(z),z\rangle-H(z)\le-\gamma_0$ whenever $\|z\|\ge R$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, notation for the proof of the capacity statement, with the Hofer–Zehnder argument of Hofer, H. and Zehnder, E., Symplectic Invariants and Hamiltonian Dynamics, Birkhäuser (1994), https://doi.org/10.1007/978-3-0348-8540-9, ch. 3

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_OAIQWSP000

/-!
# Definitions for the capacity statement of the Viterbo mission

The real-linear identification `ℝ²ⁿ ≅ ℂⁿ`, `(q, p) ↦ q + i p`, and the objects used to state the
steps of a Hofer–Zehnder argument on the Galerkin action functional of `OAI.FourierPolynomial`:
support functions, trigonometric loops, the cone hypothesis, mollified gauges and the standing
hypotheses on a Hamiltonian.
-/

open MeasureTheory
open scoped ENNReal ContDiff Pointwise

namespace Viterbo.Capacities

open OAI.SymmetricPolar

noncomputable def phiL (n : ℕ) : Phase n →ₗ[ℝ] (OAI.FourierPolynomial.Vector (Fin n)) where
  toFun z := WithLp.toLp 2 (fun j => ((z.1 j : ℂ) + Complex.I * (z.2 j : ℂ)))
  map_add' x y := by
    ext j; simp; ring
  map_smul' r x := by
    ext j; simp; ring

noncomputable def psiL (n : ℕ) : (OAI.FourierPolynomial.Vector (Fin n)) →ₗ[ℝ] Phase n where
  toFun w := (WithLp.toLp 2 (fun j => (w j).re), WithLp.toLp 2 (fun j => (w j).im))
  map_add' x y := by
    ext j <;> simp
  map_smul' r x := by
    ext j <;> simp

noncomputable def Φ (n : ℕ) : Phase n →L[ℝ] (OAI.FourierPolynomial.Vector (Fin n)) := LinearMap.toContinuousLinearMap (phiL n)
noncomputable def Ψ (n : ℕ) : (OAI.FourierPolynomial.Vector (Fin n)) →L[ℝ] Phase n := LinearMap.toContinuousLinearMap (psiL n)

end Viterbo.Capacities

noncomputable section

namespace Viterbo.Cap

open OAI OAI.FourierPolynomial OAI.HamiltonianPeriodic

section Defs

variable {κ : Type} [Fintype κ]

/-- The support function of `L ⊆ ℂ^κ` for the real inner product. -/
def supportFn (L : Set (Vector κ)) (u : Vector κ) : ℝ :=
  sSup ((fun x => inner (𝕜 := ℝ) x u) '' L)

/-- The trigonometric loop `t ↦ ∑_{|m| ≤ D} e^{2π i m t} b m`. -/
def trigLoop (D : ℕ) (b : ℤ → Vector κ) (t : ℝ) : Vector κ :=
  ∑ m ∈ Finset.Icc (-(D : ℤ)) D, Complex.exp (2 * Real.pi * Complex.I * m * t) • b m

/-- Its velocity. -/
def trigVel (D : ℕ) (b : ℤ → Vector κ) (t : ℝ) : Vector κ :=
  ∑ m ∈ Finset.Icc (-(D : ℤ)) D,
    (2 * Real.pi * Complex.I * m * Complex.exp (2 * Real.pi * Complex.I * m * t)) • b m

/-- Its action `π ∑ m ‖b m‖²`. -/
def trigAction (D : ℕ) (b : ℤ → Vector κ) : ℝ :=
  Real.pi * ∑ m ∈ Finset.Icc (-(D : ℤ)) D, (m : ℝ) * ‖b m‖ ^ 2

/-- Galerkin coefficients (modes `1, …, N+1`) of the positive-frequency loop
`t ↦ ∑_{m ≥ 1} e^{2π i m t} b m`. -/
def posCoeff (b : ℕ → Vector κ) (N : ℕ) : Coeff (Fin (N + 1)) κ :=
  (EuclideanSpace.equiv (Fin (N + 1) × κ) ℂ).symm (fun p => b (p.1.val + 1) p.2)

/-- The cone hypothesis of the linking argument: along `E_N^{≤0} ⊕ ℝ₊ e` the Galerkin action
functional is bounded above by `C₀ - c (‖a‖² + s²)`. -/
def ConeHyp [DecidableEq κ] (H : Vector κ → ℝ) : Prop :=
  ∃ (b : ℕ → Vector κ) (D : ℕ) (C₀ c : ℝ), 0 < c ∧ (∃ m, b m ≠ 0) ∧ (∀ m, D < m → b m = 0) ∧
    b 0 = 0 ∧ ∀ N, D ≤ N → ∀ (a : Coeff (Fin (N + 1)) κ) (s : ℝ), 0 ≤ s →
      FourierPolynomial.action (frequency N) H (joinCoeff a (s • posCoeff b N)) ≤ C₀ - c * (‖a‖ ^ 2 + s ^ 2)

/-- Mollified squared gauge `Q(z) = ∫ gauge_L(z - u)² ρ(u) du`. -/
def mollQ (L : Set (Vector κ)) (φ : ContDiffBump (0 : Vector κ)) (z : Vector κ) : ℝ :=
  ∫ u, gauge L (z - u) ^ 2 * φ.normed volume u

/-- Its 2-homogenization `q̂(z) = ‖z‖² Q(z / ‖z‖)`. -/
def homQ (L : Set (Vector κ)) (φ : ContDiffBump (0 : Vector κ)) (z : Vector κ) : ℝ :=
  ‖z‖ ^ 2 * mollQ L φ (‖z‖⁻¹ • z)

end Defs

section Engine

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Hypotheses on the Hamiltonian shared by E2a and E2b. -/
structure EngineHyp (H : Vector κ → ℝ) (V : Vector κ → Vector κ) (C R γ₀ : ℝ) : Prop where
  smooth : ContDiff ℝ ∞ H
  grow : ∀ z, ‖gradient H z‖ ≤ C * (1 + ‖z‖)
  contV : Continuous V
  linV : ∀ z, ‖V z‖ ≤ C * ‖z‖
  asym : ∀ B ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r, r₀ ≤ r → ∀ z : Vector κ, ‖z‖ ≤ B →
    ‖r⁻¹ • gradient H (r • z) - V z‖ ≤ ε
  γpos : 0 < γ₀
  outer : ∀ z, R ≤ ‖z‖ → inner (𝕜 := ℝ) (gradient H z) z / 2 - H z ≤ -γ₀

end Engine

section Body

variable {κ : Type} [Fintype κ]

/-- The standing hypotheses on `L`: convex, bounded, containing the ball of radius `r` about `0`. -/
structure Body (L : Set (Vector κ)) (r : ℝ) : Prop where
  convex : Convex ℝ L
  bounded : Bornology.IsBounded L
  rpos : 0 < r
  ball : Metric.ball (0 : Vector κ) r ⊆ L

end Body

end Viterbo.Cap

end


