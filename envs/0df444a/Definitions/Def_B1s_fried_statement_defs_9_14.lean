-- Prove2me | Definitions.Def_B1s_fried_statement_defs_9_14
-- name    : B1s_fried_statement_defs_9_14
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:36:55.293076+00:00
-- url     : https://prove2.me/theorems/b2f7a023-b2b8-41a1-bad6-3bcb90f43627
-- title:
--   fried statement defs 9 14
-- statement:
--   Definitions and structural lemmas for fried statement defs 9 14, from Ben Lawton (blawton/fried-conj-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Resonance-cluster conditional reduction for a proposed counterexample to Fried's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_statement_defs_9_14.lean

import Mathlib
set_option autoImplicit true
set_option linter.style.header false
namespace FriedCrossing
open Filter Topology Matrix
namespace TorsionCore
variable {K : Type*} [Field K]
def d₁ : Matrix (Fin 3) (Fin 1) K := !![0; 1; 0]
def d₂ (x l : K) : Matrix (Fin 3) (Fin 3) K := !![-1, 0, x; 0, 0, 0; 1, 0, l]
def d₃ (l : K) : Matrix (Fin 1) (Fin 3) K := !![0, -l, 0]
def D₂mat : Matrix (Fin 3) (Fin 3) K :=
  (Matrix.of ![d₁ *ᵥ ![1], ![1, 0, 0], ![0, 0, 1]])ᵀ
def D₃mat (x l : K) : Matrix (Fin 3) (Fin 3) K :=
  (Matrix.of ![d₂ x l *ᵥ ![1, 0, 0], d₂ x l *ᵥ ![0, 0, 1], ![0, -1, 0]])ᵀ
def D₄mat (l : K) : Matrix (Fin 1) (Fin 1) K :=
  (Matrix.of ![d₃ l *ᵥ ![0, -1, 0]])ᵀ
def N_C : ℕ := 3
def m_C : ℕ := 6
def refinedTorsion (x l : K) : K :=
  (-1) ^ (N_C + m_C) *
    ((!![(1 : K)]).det * (D₂mat : Matrix (Fin 3) (Fin 3) K).det⁻¹ * (D₃mat x l).det *
      (D₄mat l).det⁻¹)
end TorsionCore
namespace OrderCount
def zetaOrder (c : Fin 5 → ℕ) : ℤ := ∑ k : Fin 5, (-1 : ℤ) ^ (k : ℕ) * (c k : ℤ)
end OrderCount
namespace TwinRate
def disc (a b : ℝ) : ℝ := a ^ 2 - 4 * b
noncomputable def wPlus (a b : ℝ) : ℝ := (a + Real.sqrt (disc a b)) / 2
noncomputable def wMinus (a b : ℝ) : ℝ := (a - Real.sqrt (disc a b)) / 2
noncomputable def twin (sStar : ℝ → ℝ) (a b : ℝ → ℝ → ℝ) (θ τ : ℝ) : ℝ :=
  sStar θ + τ * wPlus (a θ τ) (b θ τ)
noncomputable def dwPlus (a b a' b' : ℝ) : ℝ :=
  (a' + (2 * a * a' - 4 * b') / (2 * Real.sqrt (disc a b))) / 2
noncomputable def dtwin (a b a' b' τ : ℝ) : ℝ := wPlus a b + τ * dwPlus a b a' b'
end TwinRate
namespace FirstVariation
variable {K : Type*} [Field K]
def Bmat (Bcc Bcψ Bψc Bψψ : K) : Matrix (Fin 2) (Fin 2) K := !![Bcc, Bcψ; Bψc, Bψψ]
def Pmat (p : K) : Matrix (Fin 2) (Fin 2) K := !![0, 0; 0, p]
end FirstVariation
namespace Hadamard
noncomputable def Ndiv (M M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ)
    (θ τ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if τ = 0 then M' θ 0 else (1 / τ) • (M θ τ - sStar θ • (1 : Matrix (Fin 2) (Fin 2) ℝ))
end Hadamard
namespace ClusterMatrix
noncomputable def c₁ (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := -A.charpoly.coeff 3
noncomputable def c₂ (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := A.charpoly.coeff 2
noncomputable def c₃ (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := -A.charpoly.coeff 1
noncomputable def c₄ (A : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := A.charpoly.coeff 0
noncomputable def E₁ (A : Matrix (Fin 4) (Fin 4) ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  c₁ A - M.trace
noncomputable def E₂ (A : Matrix (Fin 4) (Fin 4) ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  c₂ A - M.det - M.trace * E₁ A M
end ClusterMatrix
namespace Regularity
noncomputable def pτ (f : ℝ → ℝ → ℝ) (θ τ : ℝ) : ℝ := deriv (fun t => f θ t) τ
noncomputable def pθ (f : ℝ → ℝ → ℝ) (θ τ : ℝ) : ℝ := deriv (fun s => f s τ) θ
end Regularity
namespace HQuot
noncomputable def hq (f f' : ℝ → ℝ) (τ : ℝ) : ℝ := if τ = 0 then f' 0 else (f τ - f 0) / τ
noncomputable def hq' (f f' f'' : ℝ → ℝ) (τ : ℝ) : ℝ :=
  if τ = 0 then f'' 0 / 2 else (τ * f' τ - (f τ - f 0)) / τ ^ 2
end HQuot
namespace Ledger
structure Pinned (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  deg1 : ∀ τ, (M 0 τ).det = 0
  deg2 : ∀ τ z, (A 0 τ).charpoly.eval z = z ^ 3 * (z - (M 0 τ).trace)
structure ZetaFactorization (ζ₀ F s z : ℝ → ℝ) (δ : ℝ) : Prop where
  off : ∀ τ, |τ| < δ → s τ ≠ 0 → ζ₀ τ = F τ * z τ / s τ
  cont : ∀ τ₀, s τ₀ = 0 → ContinuousAt F τ₀
  at_crossing : ∀ τ₀, s τ₀ = 0 → ζ₀ τ₀ = F τ₀
end Ledger
namespace Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
noncomputable def Mτ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => pτ (fun θ τ => M θ τ i j) θ τ
noncomputable def Mττ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => pτ (fun θ τ => Mτ M θ τ i j) θ τ
noncomputable def Nτ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j =>
    hq' (fun t => M θ t i j) (fun t => Mτ M θ t i j) (fun t => Mττ M θ t i j) τ
noncomputable def aτ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) : ℝ := (Nτ M θ τ).trace
noncomputable def bτ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (sStar : ℝ → ℝ) (θ τ : ℝ) : ℝ :=
  Nτ M θ τ 0 0 * Ndiv M (Mτ M) sStar θ τ 1 1 + Ndiv M (Mτ M) sStar θ τ 0 0 * Nτ M θ τ 1 1 -
    (Nτ M θ τ 0 1 * Ndiv M (Mτ M) sStar θ τ 1 0 + Ndiv M (Mτ M) sStar θ τ 0 1 * Nτ M θ τ 1 0)
noncomputable def E₁f (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (θ τ : ℝ) : ℝ := E₁ (A θ τ) (M θ τ)
noncomputable def E₂f (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ)
    (θ τ : ℝ) : ℝ := E₂ (A θ τ) (M θ τ)
noncomputable def resZero₁ (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Submodule ℝ (Fin 2 → ℝ) := Module.End.maxGenEigenspace (Matrix.toLin' (M θ τ)) 0
noncomputable def resZero₂ (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) (θ τ : ℝ) :
    Submodule ℝ (Fin 4 → ℝ) := Module.End.maxGenEigenspace (Matrix.toLin' (A θ τ)) 0
end Derived
namespace Branch
open TwinRate
noncomputable def zBranch (e₁ e₂ : ℝ → ℝ) (τ : ℝ) : ℝ :=
  if |wPlus (e₁ τ) (e₂ τ)| ≤ |wMinus (e₁ τ) (e₂ τ)| then wPlus (e₁ τ) (e₂ τ)
  else wMinus (e₁ τ) (e₂ τ)
end Branch
end FriedCrossing
namespace FriedCrossing
open Filter Topology ContinuousLinearMap Asymptotics
namespace Scale
universe u
structure BanachScale where
  H : ℕ → Type u
  [normed : ∀ n, NormedAddCommGroup (H n)]
  [space : ∀ n, NormedSpace ℝ (H n)]
  [complete : ∀ n, CompleteSpace (H n)]
  incl : ∀ (a b : ℕ), b ≤ a → (H a →L[ℝ] H b)
  incl_refl : ∀ a, incl a a le_rfl = ContinuousLinearMap.id ℝ (H a)
  incl_trans : ∀ a b c (hab : b ≤ a) (hbc : c ≤ b),
    (incl b c hbc).comp (incl a b hab) = incl a c (le_trans hbc hab)
attribute [instance] BanachScale.normed BanachScale.space BanachScale.complete
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
structure ResolventFamily (S : BanachScale.{u}) (X : Type*) [NormedAddCommGroup X]
    [NormedSpace ℝ X] where
  R : ∀ n, X → (S.H n →L[ℝ] S.H n)
  B : ∀ n, X → (S.H (n + 1) →L[ℝ] S.H n)
  /-- CDDP Lemma 4.3: the resolvent is bounded locally uniformly in the parameter, on each level. -/
  bdd : ∀ n (x₀ : X), ∃ C, ∀ᶠ x in 𝓝 x₀, ‖R n x‖ ≤ C
  /-- the generator family is smooth in the parameter (affine in θ and λ, smooth in τ). -/
  smooth : ∀ n, ContDiff ℝ ⊤ (B n)
  /-- the resolvent is a two-sided inverse of the generator, modulo the inclusion. -/
  inv_left : ∀ n x, (R n x).comp (B n x) = S.incl (n + 1) n (Nat.le_succ n)
  inv_right : ∀ n x, (B n x).comp (R (n + 1) x) = S.incl (n + 1) n (Nat.le_succ n)
  /-- the resolvent commutes with the inclusion. -/
  R_incl : ∀ n x, (S.incl (n + 1) n (Nat.le_succ n)).comp (R (n + 1) x) =
    (R n x).comp (S.incl (n + 1) n (Nat.le_succ n))
  /-- so does the generator. -/
  B_incl : ∀ n x, (S.incl (n + 1) n (Nat.le_succ n)).comp (B (n + 1) x) =
    (B n x).comp (S.incl (n + 2) (n + 1) (Nat.le_succ _))
end Scale
end FriedCrossing
namespace FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
namespace ClusterFrame
abbrev Param : Type := (ℝ × ℝ) × ℂ
structure ComplexStructure (S : BanachScale.{0}) where
  J : ∀ n, S.H n →L[ℝ] S.H n
  J_sq : ∀ n, (J n).comp (J n) = -ContinuousLinearMap.id ℝ (S.H n)
  J_incl : ∀ n, (S.incl (n + 1) n (Nat.le_succ n)).comp (J (n + 1)) =
    (J n).comp (S.incl (n + 1) n (Nat.le_succ n))
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
noncomputable def melem (a b : ℕ) (hab : b ≤ a) (φ : S.H a) (ℓ : S.H b →L[ℝ] ℝ) (x : Param) : ℂ :=
  (ℓ (((S.incl a b hab).comp (F.R a x)) φ) : ℂ) -
    Complex.I * (ℓ (Jc.J b (((S.incl a b hab).comp (F.R a x)) φ)) : ℂ)
noncomputable def contour (c : ℂ) (r t : ℝ) : ℂ := c + r * Complex.exp (Complex.I * t)
noncomputable def riesz (c : ℂ) (r : ℝ) (g : Param → ℂ) (p : ℝ × ℝ) : ℂ :=
  -((r : ℂ) / (2 * Real.pi)) *
    ∫ t in (0 : ℝ)..(2 * Real.pi), g (p, contour c r t) * Complex.exp (Complex.I * t)
structure FrameData (S : BanachScale.{0}) (k : ℕ) where
  a : ℕ
  b : ℕ
  hab : b + 15 ≤ a
  φ : Fin k → S.H a
  ℓ : Fin k → (S.H b →L[ℝ] ℝ)
  c : ℂ
  r : ℝ
variable {k : ℕ}
noncomputable def Amat (D : FrameData S k) (p : ℝ × ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun l j =>
    riesz D.c D.r (melem F Jc D.a D.b (by have := D.hab; omega) (D.φ j) (D.ℓ l)) p
noncomputable def Bmat (D : FrameData S k) (p : ℝ × ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun l j => riesz D.c D.r
    (fun x => x.2 * melem F Jc D.a D.b (by have := D.hab; omega) (D.φ j) (D.ℓ l) x) p
noncomputable def Mframe (D : FrameData S k) (p : ℝ × ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  (Amat F Jc D p)⁻¹ * Bmat F Jc D p
noncomputable def Mreal (D : FrameData S k) (θ τ : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (Mframe F Jc D (θ, τ)).map Complex.re
end ClusterFrame
end FriedCrossing
namespace FriedCrossing
open FirstVariation
namespace Ledger
structure FirstVariation422 (M' : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (Bcc Bcψ Bψc Bψψ p : ℝ) : Prop where
  det_ne : Bcc * Bψψ - Bcψ * Bψc ≠ 0
  eq422 : Bmat Bcc Bcψ Bψc Bψψ * M' 0 0 = Pmat p
structure DoublePoint (sStar : ℝ → ℝ) : Prop where
  zero : sStar 0 = 0
  cont : ContinuousAt sStar 0
  neg : ∀ θ, θ ≠ 0 → sStar θ < 0
end Ledger
end FriedCrossing


