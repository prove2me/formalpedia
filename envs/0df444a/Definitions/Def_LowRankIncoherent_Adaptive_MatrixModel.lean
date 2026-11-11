-- Prove2me | Definitions.Def_LowRankIncoherent_Adaptive_MatrixModel
-- name    : LowRankIncoherent_Adaptive_MatrixModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T13:16:13.834497+00:00
-- url     : https://prove2.me/theorems/02188559-0f6c-449c-b385-de7014072079
-- title:
--   Finite matrices, weighted Choi reconstruction and regularization
-- statement:
--   The input and output registers are finite complex Hilbert spaces of dimensions $a$ and $b$. States are positive semidefinite matrices of trace one, and the joint register has order $B⊗A$. The unnormalized Choi operator, its inverse reshaping, partial trace, and weighted reconstruction are defined in the computational basis. The Euclidean spectral norm is used for square and rectangular matrices; trace norm is the published unhalved Schatten norm.
--
--   For a positive definite input state $σ$, reconstruction has Choi operator $(I_b⊗(σ^T)^{-1/2})M(I_b⊗(σ^T)^{-1/2})$. For $s>0$ define
--   $$f_s(X)=X(X+sI)^{-1},\qquad X_s=Xf_s(X),\qquad H_s(σ)=Φ_σ(f_s(X))^†(I_b).$$
--   Here $X$ is the actual purified-input output state of the unknown channel. The complementary channel and its adjoint are computed from a Kraus list. The support projection and Moore–Penrose inverse use their spectral functions, including value zero at a zero eigenvalue. Rank truncation retains precisely the largest positive eigenvalues up to the rank budget and permits a split of tied eigenspaces.
--
--   This layer supplies the shared matrix conventions for every theorem in this mission; it imposes no estimation guarantee.
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), §§2.1, 2.5, equations (2)–(5), (26)–(35), Definition 3.3, printed pp. 7–8, 13–16, 19 = PDF pp. 7–8, 13–16, 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Mathlib
import Definitions.Def_ChanTomoNB_QChan
import Definitions.Def_ChanTomoNB_diamondDist
import Definitions.Def_WildeQIT_traceNorm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder
noncomputable section

namespace LowRankIncoherent.Adaptive

abbrev Mat (ι : Type) := Matrix ι ι ℂ
abbrev Input (a : ℕ) := Mat (Fin a)
abbrev Joint (a b : ℕ) := Mat (Fin b × Fin a)
abbrev Map (a b : ℕ) := ChanTomoNB.Superop (Fin a) (Fin b)

def State {ι : Type} [Fintype ι] (X : Mat ι) : Prop := X.PosSemidef ∧ X.trace = 1

def LE {ι : Type} [Fintype ι] (X Y : Mat ι) : Prop := (Y - X).PosSemidef

/-- Euclidean spectral norm, including rectangular matrices (not the entrywise matrix norm). -/
def opNorm {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι κ ℂ) : ℝ :=
  by
    classical
    exact ‖LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 M)‖

def rt {ι : Type} [Fintype ι] (M : Mat ι) : ℝ := M.trace.re

def sqrtM {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) : Mat ι := CFC.sqrt X

def logM {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) : Mat ι := cfc Real.log X

def expM {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) : Mat ι := cfc Real.exp X

def fs {ι : Type} [Fintype ι] [DecidableEq ι] (s : ℝ) (X : Mat ι) : Mat ι :=
  X * (X + (s : ℂ) • 1)⁻¹

def regularized {ι : Type} [Fintype ι] [DecidableEq ι] (s : ℝ) (X : Mat ι) : Mat ι :=
  X * fs s X

/-- Support projection and Moore--Penrose inverse by functional calculus. -/
def support {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) : Mat ι :=
  cfc (fun x : ℝ => if x = 0 then 0 else 1) X

def pinv {ι : Type} [Fintype ι] [DecidableEq ι] (X : Mat ι) : Mat ι :=
  cfc (fun x : ℝ => x⁻¹) X

def resolvent {ι : Type} [Fintype ι] [DecidableEq ι] (s : ℝ) (S : Mat ι) : Mat ι :=
  (S + (s : ℂ) • 1)⁻¹ * support S

def choi {a b : ℕ} (E : Map a b) : Joint a b :=
  fun p q => E (Matrix.single p.2 q.2 1) p.1 q.1

/-- Inverse of the unnormalized Choi map, in B ⊗ A order. -/
def unchoi {a b : ℕ} (C : Joint a b) : Map a b where
  toFun ρ := fun i j => ∑ x, ∑ y, C (i,x) (j,y) * ρ x y
  map_add' ρ τ := by
    ext i j
    change (∑ x, ∑ y, C (i,x) (j,y) * (ρ x y + τ x y)) = _ + _
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' z ρ := by
    ext i j
    change (∑ x, ∑ y, C (i,x) (j,y) * (z * ρ x y)) = z * (∑ x, ∑ y, C (i,x) (j,y) * ρ x y)
    simp [Finset.mul_sum, mul_left_comm]

def ptrB {a b : ℕ} (C : Joint a b) : Input a := fun x y => ∑ i, C (i,x) (i,y)

def liftA {a b : ℕ} (M : Input a) : Joint a b := Matrix.kronecker (1 : Input b) M

def whiten {a b : ℕ} (σ : Input a) (M : Joint a b) : Joint a b :=
  let L : Joint a b := liftA ((sqrtM σ.transpose)⁻¹)
  L * M * L

def reconstruct {a b : ℕ} (σ : Input a) (M : Joint a b) : Map a b := unchoi (whiten σ M)

/-- Hilbert--Schmidt adjoint of the reconstructed Hermiticity-preserving map at I_B. -/
def adjointI {a b : ℕ} (σ : Input a) (M : Joint a b) : Input a := (ptrB (whiten σ M)).transpose

def outputState {a b : ℕ} (E : Map a b) (σ : Input a) : Joint a b :=
  let L : Joint a b := liftA (sqrtM σ.transpose)
  L * choi E * L

def sensitivity {a b : ℕ} (E : Map a b) (s : ℝ) (σ : Input a) : Input a :=
  adjointI σ (fs s (outputState E σ))

def mixture {a : ℕ} (ρ : Input a) : Input a :=
  (1/2 : ℂ) • ρ + (1 / (2 * (a : ℂ))) • 1

def Amap {a b : ℕ} (E : Map a b) (r : ℕ) (s : ℝ) (ρ : Input a) : Input a :=
  sensitivity E s (mixture ρ) + (r : ℂ) • 1

def weightedL {a b : ℕ} (ρ σ : Input a) : Joint a b :=
  liftA (sqrtM ρ.transpose * (sqrtM σ.transpose)⁻¹)

def complement {a b r : ℕ} (K : Fin r → Matrix (Fin b) (Fin a) ℂ) (ρ : Input a) : Input r :=
  fun i j => Matrix.trace (ρ * (K j)ᴴ * K i)

def complementAdj {a b r : ℕ} (K : Fin r → Matrix (Fin b) (Fin a) ℂ) (Q : Input r) : Input a :=
  ∑ i, ∑ j, Q i j • ((K i)ᴴ * K j)

def CP {a b : ℕ} (E : Map a b) : Prop := (choi E).PosSemidef

def TNI {a b : ℕ} (E : Map a b) : Prop :=
  ∀ ρ, ρ.PosSemidef → rt (E ρ) ≤ rt ρ

def convexOp {ι κ : Type} [Fintype ι] [Fintype κ]
    (domain : Set (Mat ι)) (f : Mat ι → Mat κ) : Prop :=
  ∀ X ∈ domain, ∀ Y ∈ domain, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    LE (f ((t : ℂ) • X + ((1-t : ℝ) : ℂ) • Y))
      ((t : ℂ) • f X + ((1-t : ℝ) : ℂ) • f Y)

def concaveOp {ι κ : Type} [Fintype ι] [Fintype κ]
    (domain : Set (Mat ι)) (f : Mat ι → Mat κ) : Prop :=
  ∀ X ∈ domain, ∀ Y ∈ domain, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    LE ((t : ℂ) • f X + ((1-t : ℝ) : ℂ) • f Y)
      (f ((t : ℂ) • X + ((1-t : ℝ) : ℂ) • Y))

/-- Structural admissibility of one tie-breaking rank truncation, with exactly the r largest
positive eigenvalues retained. No approximation or statistical guarantee is assumed. -/
def IsTruncation {ι : Type} [Fintype ι] [DecidableEq ι] (r : ℕ) (X S : Mat ι) : Prop := by
  classical
  exact ∃ U : Matrix.unitaryGroup ι ℂ, ∃ eig : ι → ℝ, ∃ J : Finset ι,
    X = (U : Mat ι) * Matrix.diagonal (fun i => (eig i : ℂ)) * (U : Mat ι)ᴴ ∧
    J.card = min r (Finset.univ.filter (fun i => 0 < eig i)).card ∧
    (∀ i ∈ J, 0 < eig i) ∧ (∀ i ∈ J, ∀ j ∉ J, eig j ≤ eig i) ∧
    S = (U : Mat ι) * Matrix.diagonal (fun i => if i ∈ J then (eig i : ℂ) else 0) * (U : Mat ι)ᴴ

end LowRankIncoherent.Adaptive


