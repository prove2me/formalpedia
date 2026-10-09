-- Prove2me | Definitions.Def_AffineVolterra_RiccatiSqrt_Setting
-- name    : AffineVolterra_RiccatiSqrt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:40.959723+00:00
-- url     : https://prove2.me/theorems/8e26309e-454f-42da-a516-edab8b6a7516
-- title:
--   §2, §3, §6 and Appendix B — kernels, resolvents and Volterra equation solutions
-- statement:
--   This setting fixes the deterministic objects used in the square-root Riccati–Volterra equation. A diagonal kernel has scalar entries $K_i$. Condition (2.5) says that each entry is locally square integrable and has a positive-time $L^2$ regularity exponent $\gamma_i\in(0,2]$. Condition (3.4) requires $K_i$ to be nonnegative, nonzero, nonincreasing and continuous on positive times, and to have a nonnegative resolvent measure $L_i$ whose interval masses $L_i([s,s+t])$ decrease with $s$.
--
--   For a complex matrix kernel $K$ and a vector-valued function $q$, convolution is
--   $$
--   (K*q)(t)=\int_0^t K(t-s)q(s)\,ds.
--   $$
--   A solution of equation (B.1), $\psi=g+K*p(\cdot,\psi)$, is locally square integrable and satisfies the equation almost everywhere on each stated time interval. The integrand must actually be integrable at the times where the equation is asserted. A non-continuable solution has a maximal lifetime $T_{\max}>0$ and infinite $L^2$ norm on $(0,T_{\max})$ if that lifetime is finite.
--
--   The square-root drift encodes (6.3) with coupling $\sum_j\psi_j B_{ji}$ and quadratic coefficient $\sigma_i^2/2$. These definitions are shared by the appendix results and the mission goal.
--
--   **Formalization Note** Time is represented by real numbers, constrained to positive intervals. Matrix $L^p$ membership is componentwise. Finite-dimensional vectors use the sup norm, equivalent to the paper's Euclidean norm. Equality of $L^2$ solutions and sign conditions on $L^1$ data are almost everywhere. The resolvent convolution is required to be integrable, excluding default zero values of undefined integrals.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, (2.1)–(2.2), pp. 4–5; (2.5), p. 6; (2.13), p. 10; (3.4), p. 14; (6.3), p. 27; (B.1) and solution notions, pp. 39–40

import Mathlib
import Definitions.Def_AffineVolterra_Transform_Core

namespace AffineVolterra.RiccatiSqrt

open MeasureTheory Filter Asymptotics

abbrev CMat (d : ℕ) := Fin d → Fin d → ℂ
abbrev RMat (d : ℕ) := Fin d → Fin d → ℝ

/-- Local Lebesgue membership on the positive time axis. -/
def VecLpLoc {d : ℕ} (p : ENNReal) (f : ℝ → AffineVolterra.Transform.CVec d) : Prop :=
  ∀ T : ℝ, 0 < T → MemLp f p (volume.restrict (Set.Ioc 0 T))

def RealVecLpLoc {d : ℕ} (p : ENNReal) (f : ℝ → AffineVolterra.Transform.RVec d) : Prop :=
  ∀ T : ℝ, 0 < T → MemLp f p (volume.restrict (Set.Ioc 0 T))

def RealMatLpLoc {d : ℕ} (p : ENNReal) (K : ℝ → RMat d) : Prop :=
  ∀ i j T, 0 < T → MemLp (fun t => K t i j) p (volume.restrict (Set.Ioc 0 T))

def ComplexMatLpLoc {d : ℕ} (p : ENNReal) (K : ℝ → CMat d) : Prop :=
  ∀ i j T, 0 < T → MemLp (fun t => K t i j) p (volume.restrict (Set.Ioc 0 T))

/-- Condition (2.5); the Big-O limits are taken through positive `h`. -/
def Cond25 (k : ℝ → ℝ) (γ : ℝ) : Prop :=
  0 < γ ∧ γ ≤ 2 ∧
  (∀ T : ℝ, 0 < T → MemLp k 2 (volume.restrict (Set.Ioc 0 T))) ∧
  IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun h : ℝ => ∫ t in (0 : ℝ)..h, k t ^ 2) (fun h : ℝ => h ^ γ) ∧
  ∀ T : ℝ, 0 < T →
    IsBigO (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (fun h : ℝ => ∫ t in (0 : ℝ)..T, (k (t + h) - k t) ^ 2)
      (fun h : ℝ => h ^ γ)

def shift (h : ℝ) (k : ℝ → ℝ) : ℝ → ℝ := fun t => k (t + h)

/-- The scalar resolvent identity (2.13), with an actual integrable convolution. -/
def ResolventFirstKindNonneg (k : ℝ → ℝ) (L : Measure ℝ) : Prop :=
  L (Set.Iio 0) = 0 ∧
  (∀ T : ℝ, 0 < T → L (Set.Icc 0 T) < ⊤) ∧
  ∀ t : ℝ, 0 < t →
    IntegrableOn (fun s => k (t - s)) (Set.Icc 0 t) L ∧
      (∫ s in Set.Icc 0 t, k (t - s) ∂L) = 1

/-- Condition (3.4) with a named resolvent, needed in (3.9)–(3.10). -/
def Cond34With (k : ℝ → ℝ) (L : Measure ℝ) : Prop :=
  (∀ t : ℝ, 0 < t → 0 ≤ k t) ∧
  (∃ t : ℝ, 0 < t ∧ k t ≠ 0) ∧
  AntitoneOn k (Set.Ioi 0) ∧ ContinuousOn k (Set.Ioi 0) ∧
  ResolventFirstKindNonneg k L ∧
  ∀ t s r : ℝ, 0 ≤ t → 0 ≤ s → s ≤ r →
    L (Set.Icc r (r + t)) ≤ L (Set.Icc s (s + t))

def Cond34 (k : ℝ → ℝ) : Prop := ∃ L : Measure ℝ, Cond34With k L

/-- Matrix times column vector, with ordinary complex multiplication. -/
def mulVec {d : ℕ} (A : CMat d) (x : AffineVolterra.Transform.CVec d) : AffineVolterra.Transform.CVec d :=
  fun i => ∑ j : Fin d, A i j * x j

def realMatToComplex {d : ℕ} (A : RMat d) : CMat d :=
  fun i j => (A i j : ℂ)

def realVecToComplex {d : ℕ} (x : AffineVolterra.Transform.RVec d) : AffineVolterra.Transform.CVec d :=
  fun i => (x i : ℂ)

/-- The convolution in (B.1). -/
noncomputable def convolution {d : ℕ} (K : ℝ → CMat d)
    (q : ℝ → AffineVolterra.Transform.CVec d) (t : ℝ) : AffineVolterra.Transform.CVec d :=
  ∫ s in (0 : ℝ)..t, mulVec (K (t - s)) (q s)

/-- An `L²` solution of (B.1) on `[0,T]`, with integrability preventing junk-zero integrals. -/
def SolvesOn {d : ℕ} (K : ℝ → CMat d) (g : ℝ → AffineVolterra.Transform.CVec d)
    (p : ℝ → AffineVolterra.Transform.CVec d → AffineVolterra.Transform.CVec d) (ψ : ℝ → AffineVolterra.Transform.CVec d) (T : ℝ) : Prop :=
  MemLp ψ 2 (volume.restrict (Set.Ioc 0 T)) ∧
  ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
    IntegrableOn (fun s => mulVec (K (t - s)) (p s (ψ s))) (Set.Ioc 0 t) ∧
      ψ t = g t + convolution K (fun s => p s (ψ s)) t

/-- Local solutions on `[0,Tmax)`, using positive finite horizons. -/
def SolvesOnIco {d : ℕ} (K : ℝ → CMat d) (g : ℝ → AffineVolterra.Transform.CVec d)
    (p : ℝ → AffineVolterra.Transform.CVec d → AffineVolterra.Transform.CVec d) (ψ : ℝ → AffineVolterra.Transform.CVec d) (Tmax : ENNReal) : Prop :=
  ∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tmax → SolvesOn K g p ψ T

def IsNonContinuable {d : ℕ} (K : ℝ → CMat d) (g : ℝ → AffineVolterra.Transform.CVec d)
    (p : ℝ → AffineVolterra.Transform.CVec d → AffineVolterra.Transform.CVec d) (ψ : ℝ → AffineVolterra.Transform.CVec d) (Tmax : ENNReal) : Prop :=
  0 < Tmax ∧ SolvesOnIco K g p ψ Tmax ∧
  (Tmax = ⊤ ∨
    eLpNorm ψ 2 (volume.restrict (Set.Ioo (0 : ℝ) Tmax.toReal)) = ⊤)

def IsUniqueNonContinuable {d : ℕ} (K : ℝ → CMat d) (g : ℝ → AffineVolterra.Transform.CVec d)
    (p : ℝ → AffineVolterra.Transform.CVec d → AffineVolterra.Transform.CVec d) (ψ : ℝ → AffineVolterra.Transform.CVec d) (Tmax : ENNReal) : Prop :=
  IsNonContinuable K g p ψ Tmax ∧
  ∀ (T : ℝ) (φ : ℝ → AffineVolterra.Transform.CVec d), 0 ≤ T → SolvesOn K g p φ T →
    ENNReal.ofReal T < Tmax ∧
      φ =ᵐ[volume.restrict (Set.Ioc 0 T)] ψ

def IsGlobal {d : ℕ} (K : ℝ → CMat d) (g : ℝ → AffineVolterra.Transform.CVec d)
    (p : ℝ → AffineVolterra.Transform.CVec d → AffineVolterra.Transform.CVec d) (ψ : ℝ → AffineVolterra.Transform.CVec d) : Prop :=
  VecLpLoc 2 ψ ∧ ∀ T : ℝ, 0 < T → SolvesOn K g p ψ T

/-- Diagonal kernel and the two pieces of the square-root equation (6.3). -/
def diagonalKernel {d : ℕ} (Kd : Fin d → ℝ → ℝ) : ℝ → CMat d :=
  fun t i j => if i = j then (Kd i t : ℂ) else 0

def squareRootSource {d : ℕ} (Kd : Fin d → ℝ → ℝ) (u : AffineVolterra.Transform.CVec d) : ℝ → AffineVolterra.Transform.CVec d :=
  fun t i => u i * (Kd i t : ℂ)

noncomputable def squareRootDrift {d : ℕ} (B : RMat d) (σ : AffineVolterra.Transform.RVec d)
    (f : ℝ → AffineVolterra.Transform.CVec d) : ℝ → AffineVolterra.Transform.CVec d → AffineVolterra.Transform.CVec d :=
  fun t x i => f t i + (∑ j : Fin d, x j * (B j i : ℂ)) +
    (((σ i ^ 2 / 2 : ℝ) : ℂ) * x i ^ 2)

def SolvesSquareRoot {d : ℕ} (Kd : Fin d → ℝ → ℝ) (B : RMat d)
    (σ : AffineVolterra.Transform.RVec d) (u : AffineVolterra.Transform.CVec d) (f ψ : ℝ → AffineVolterra.Transform.CVec d) (T : ℝ) : Prop :=
  SolvesOn (diagonalKernel Kd) (squareRootSource Kd u)
    (squareRootDrift B σ f) ψ T

end AffineVolterra.RiccatiSqrt


