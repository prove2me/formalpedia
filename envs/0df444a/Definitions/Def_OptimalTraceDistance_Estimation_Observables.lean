-- Prove2me | Definitions.Def_OptimalTraceDistance_Estimation_Observables
-- name    : OptimalTraceDistance_Estimation_Observables
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:40:54.276919+00:00
-- url     : https://prove2.me/theorems/e0c9d5b4-2421-455b-bc84-531471b71599
-- title:
--   Signed kernels, U-statistics and spectral outcome measures
-- statement:
--   Permutation operators use $U_\pi|x\rangle=|x\circ\pi^{-1}\rangle$. The quantum shift is the left cyclic shift. A word kernel is the signed diagonal bit tensor times this shift and the ordered matrix coefficients, with the trailing coefficient moved to the first factor by trace cyclicity. Bit and quantum coordinates are explicitly projected from each register pair. Symmetrization permutes whole pairs, and kernels are the Hermitian parts of the degree components.
--
--   The quantum U-statistic averages embeddings over ordered injections. For symmetric kernels each subset occurs $k!$ times, giving exactly the subset normalization (20). The observable is the scalar constant plus these degree components. The labelled state is $\tau=\tfrac12\operatorname{diag}(\rho,\sigma)$. Spectral outcome measures sum Born weights at the actual eigenvalues of a Hermitian observable. The physical realization, integrability and unbiasedness are open theorem obligations; the definitions contain no accuracy certificate. Each label history consumes at most $n$ copies of either input.
--
--   Permutation operators alias the published tensor-factor permutation definition; its inverse-permutation orientation agrees exactly with this source.
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), §2.4, Algorithm 1, §4.1, pp.9–10,15.

import Definitions.Def_OptimalTraceDistance_Estimation_Expressions
import Definitions.Def_OptimalSpectrum_Entangled_permOp

open scoped BigOperators Matrix Classical
noncomputable section

namespace OptimalTraceDistance.Estimation

abbrev permutationOp {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (π : Equiv.Perm (Fin k)) : Matrix (Fin k → ι) (Fin k → ι) ℂ :=
  OptimalSpectrum.Entangled.permOp π

def symmetrize {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (H : Matrix (Fin k → ι) (Fin k → ι) ℂ) :=
  ((k.factorial : ℂ)⁻¹) • ∑ π : Equiv.Perm (Fin k),
    permutationOp π * H * (permutationOp π)ᴴ

def cycleAverage (d j : ℕ) : Op d j :=
  (((j-1).factorial : ℂ)⁻¹) •
    ∑ π : Equiv.Perm (Fin j), if
      (j = 1 ∧ π = 1) ∨ (π.IsCycle ∧ π.support = Finset.univ)
      then permutationOp π else 0

/-- V is the left shift; bits and quantum coordinates are explicitly projected from pairs. -/
def leftShift (d k : ℕ) : Op d k := fun x y =>
  if ∀ i : Fin k, x i = y ⟨(i.val+1)%k, Nat.mod_lt _ (by have hi := i.isLt; omega)⟩
  then 1 else 0

def wordKernel {d : ℕ} (w : Word d) (k : ℕ) :
    Matrix (Fin k → Bool × Fin d) (Fin k → Bool × Fin d) ℂ :=
  if w.factors.length = k then
    let factors := fun i : Fin k => w.factors[i.val]?.getD (1,false)
    let known := tensor k (fun i => if i.val = 0 then w.tail * (factors i).1 else (factors i).1)
    let V := leftShift d k * known
    fun x y => if (fun i => (x i).1) = (fun i => (y i).1) then
      (∏ i, if (factors i).2 && (x i).1 then (-1 : ℂ) else 1) *
        V (fun i => (x i).2) (fun i => (y i).2)
      else 0
  else 0

def expressionKernel {d : ℕ} (f : TraceExpression d) (k : ℕ) :=
  hermPart (symmetrize ((f.words.map (fun w => wordKernel w k)).sum))

def embed {ι : Type*} [Fintype ι] [DecidableEq ι] {k n : ℕ}
    (e : Fin k ↪ Fin n) (H : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    Matrix (Fin n → ι) (Fin n → ι) ℂ := fun x y =>
  if ∀ i, i ∉ Set.range e → x i = y i then H (x ∘ e) (y ∘ e) else 0

/-- Averaging over ordered injections equals the subset average for symmetric kernels. -/
def uStatistic {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ)
    (H : Matrix (Fin k → ι) (Fin k → ι) ℂ) : Matrix (Fin n → ι) (Fin n → ι) ℂ :=
  ((Fintype.card (Fin k ↪ Fin n) : ℂ)⁻¹) • ∑ e : Fin k ↪ Fin n, embed e H

def observable {d : ℕ} (f : TraceExpression d) (n : ℕ) :=
  (evaluate f 0 0).re • (1 : Matrix (Fin n → Bool × Fin d) (Fin n → Bool × Fin d) ℂ) +
    ∑ k ∈ Finset.Icc 1 (expressionDegree f), uStatistic n k (expressionKernel f k)

def labelledState {d : ℕ} (ρ σ : Mat d) : Matrix (Bool × Fin d) (Bool × Fin d) ℂ :=
  fun x y => if x.1 = y.1 then (2 : ℂ)⁻¹ * (if x.1 then σ x.2 y.2 else ρ x.2 y.2) else 0

def polynomialVariance {d : ℕ} (f : TraceExpression d) (n : ℕ) (ρ σ : Mat d) : ℝ :=
  variance (labelledState ρ σ) n (observable f n)

def univariate (d K : ℕ) : TraceExpression d :=
  traceExpr (exprPoly (q K) (exprVar d true))

/-- Direct finite spectral outcome measure. Off the Hermitian domain the measure is zero.
All theorems using this definition establish the actual observable is Hermitian. -/
def spectralLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G R : Matrix ι ι ℂ) : MeasureTheory.Measure ℝ := by
  classical
  exact if h : G.IsHermitian then
    ∑ i, ENNReal.ofReal (tr (R * QAlgorithms.pureDensity (h.eigenvectorBasis i))) •
      MeasureTheory.Measure.dirac (h.eigenvalues i)
  else 0

/-- Worst-case per-input cost of n independent uniform labels. -/
def inputCost (n : ℕ) : ℕ := n

end OptimalTraceDistance.Estimation


