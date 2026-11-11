-- Prove2me | Definitions.Def_JainCRERepetition_Cubic_quantum
-- name    : JainCRERepetition_Cubic_quantum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:46.184804+00:00
-- url     : https://prove2.me/theorems/d0356241-35e8-4372-ade9-63a514f56ac3
-- title:
--   Definitions 2.2, 2.4 and 2.9 — quantum information and finite local preparation
-- statement:
--   All registers have finite distinguished orthonormal bases and all operators are complex matrices. A state is positive semidefinite with trace one. The published support-aware binary relative entropy is $D(\rho\|\nu)$, with value $+\infty$ outside support containment; $\nu$ may be unnormalized. The real expression $d$ is used for subtraction only where the full divergence is finite. Entropy, root fidelity, purified distance, measured relative entropy, classical blocks and their separately normalized conditionals are defined by
--
--   $$H(\rho)=-\operatorname{Tr}\rho\log_2\rho,\qquad F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1,\qquad P^2=1-F^2.$$
--
--   Finite probability laws and Kraus channels reuse published definitions. Measured divergence takes an extended-real supremum over all finite POVMs. A preparation consists of an arbitrary finite shared mixed state and two channel families indexed separately by the players' questions. Its designated output is the entire original workspace, and $d_{\rm prep}$ is the infimum of its mean infidelity. Resources can depend on the family but cannot depend on the questions received.
--
--   The module also computes the exact supported-power, real-integral replacement of Eq. (39), with $\beta_0(s)=\pi/[2(\cosh(\pi s)+1)]$. No budget, preparation estimate or repetition rate is assumed by these definitions.
-- source:
--   Rahul Jain, Parallel Repetition for Entangled Games via Conditional Relative Entropy, STOC 2027 submission #1639 (October 2026), pp. 10–14, Definitions 2.2, 2.4, 2.9; p. 27, Eq. (39); pinned PDF sha256 feaaea94c75228982a63b6750208082f2569d2e250a47abe4bf95fa37cc76a35

import Mathlib
import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_WildeQIT_Recover_qRelEntropy
import Definitions.Def_WildeQIT_QChannel
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_WildeQIT_partialTrace

open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

noncomputable section

namespace JainCRERepetition.Cubic

abbrev Op (I : Type) := Matrix I I ℂ

def IsState {I : Type} [Fintype I] (ρ : Op I) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

def ket {I : Type} (u : I → ℂ) : Op I := fun i j => u i * star (u j)

def sqnorm {I : Type} [Fintype I] (u : I → ℂ) : ℝ := ∑ i, Complex.normSq (u i)

def IsUnit {I : Type} [Fintype I] (u : I → ℂ) : Prop := sqnorm u = 1

abbrev D {I : Type} [Fintype I] [DecidableEq I] := @WildeQIT.Recover.qRelEntropy I _ _
abbrev trR {I J : Type} [Fintype J] := @WildeQIT.partialTraceRight I J _
abbrev trL {I J : Type} [Fintype I] := @WildeQIT.partialTraceLeft I J _

/-- This predicate is exactly the finite-support domain of relative entropy. -/
def FiniteD {I : Type} [Fintype I] [DecidableEq I] (ρ ν : Op I) : Prop :=
  WildeQIT.Recover.SuppSubset ρ ν

/-- Real value, used only with FiniteD at every statement that subtracts it. -/
def d {I : Type} [Fintype I] [DecidableEq I] (ρ ν : Op I) : ℝ :=
  (ρ * (WildeQIT.Recover.log2Op ρ - WildeQIT.Recover.log2Op ν)).trace.re

def entropy {I : Type} [Fintype I] [DecidableEq I] (ρ : Op I) : ℝ :=
  -(ρ * WildeQIT.Recover.log2Op ρ).trace.re

def rootF {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Op I) : ℝ :=
  WildeQIT.traceNorm (CFC.sqrt ρ * CFC.sqrt σ)

def infidelity {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Op I) : ℝ :=
  1 - (rootF ρ σ)^2

def purified {I : Type} [Fintype I] [DecidableEq I] (ρ σ : Op I) : ℝ :=
  Real.sqrt (infidelity ρ σ)

/-- The published, nonnegative normalized finite distribution; no local redefinition. -/
abbrev Law (Z : Type) [Fintype Z] := Arlib.Probability.FinDist Z

def diagonal {Z : Type} [DecidableEq Z] (p : Z → ℝ) : Op Z :=
  Matrix.diagonal fun z => (p z : ℂ)

def mean {Z : Type} [Fintype Z] (p f : Z → ℝ) : ℝ := ∑ z, p z * f z

def cq {Z I : Type} [DecidableEq Z] (p : Z → ℝ) (ρ : Z → Op I) : Op (Z × I) :=
  fun a b => if a.1 = b.1 then (p a.1 : ℂ) * ρ a.1 a.2 b.2 else 0

def block {Z I : Type} (ρ : Op (Z × I)) (z : Z) : Op I :=
  fun a b => ρ (z,a) (z,b)

def blockProb {Z I : Type} [Fintype I] (ρ : Op (Z × I)) (z : Z) : ℝ :=
  (block ρ z).trace.re

/-- Arbitrary zero branches are set to zero; all uses condition on positive mass. -/
def conditional {Z I : Type} [Fintype I] (ρ : Op (Z × I)) (z : Z) : Op I :=
  (blockProb ρ z : ℂ)⁻¹ • block ρ z

def marginalX {X Y : Type} [Fintype Y] (p : X × Y → ℝ) (x : X) : ℝ :=
  ∑ y, p (x,y)

def kernel {X Y : Type} [Fintype Y] (p : X × Y → ℝ) (x : X) (y : Y) : ℝ :=
  p (x,y) / marginalX p x

def swapLaw {X Y : Type} [Fintype X] [Fintype Y] (p : Law (X × Y)) : Law (Y × X) where
  p z := p.p (z.2,z.1)
  p_nonneg z := p.p_nonneg _
  p_sum := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using p.p_sum

def classicalD {Z : Type} [Fintype Z] [DecidableEq Z] (p q : Z → ℝ) : EReal :=
  D (diagonal p) (diagonal q)

def classicald {Z : Type} [Fintype Z] (p q : Z → ℝ) : ℝ :=
  ∑ z, if p z = 0 then 0 else p z * Real.logb 2 (p z / q z)

def MeasuredD {I : Type} [Fintype I] [DecidableEq I] (ρ ν : Op I) : EReal :=
  ⨆ (k : ℕ) (M : QuantumParallelRepetition.POVM (Fin k) I),
    classicalD (fun j => (ρ * M.operator j).trace.re)
      (fun j => (ν * M.operator j).trace.re)

def charge {R K : Type} [Fintype R] [Fintype K] [DecidableEq R] [DecidableEq K]
    (ρ ν : Op (R × K)) : ℝ := d ρ ν - d (trL ρ) (trL ν)

def localOutput {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B]
    [DecidableEq I] [DecidableEq J]
    (η : Op (I × J)) (N : WildeQIT.QChannel I A) (M : WildeQIT.QChannel J B) : Op (A × B) :=
  ∑ i, ∑ j, (N.K i ⊗ₖ M.K j) * η * (N.K i ⊗ₖ M.K j)ᴴ

/-- The unbounded finite resource quantifier is inside the preparation witness. -/
structure Preparation {X Y A B : Type} [Fintype A] [Fintype B] where
  da : ℕ
  db : ℕ
  resource : QuantumParallelRepetition.DensityMatrix (Fin da × Fin db)
  alice : X → WildeQIT.QChannel (Fin da) A
  bob : Y → WildeQIT.QChannel (Fin db) B

def Preparation.output {X Y A B : Type} [Fintype A] [Fintype B]
    (P : Preparation (X := X) (Y := Y) (A := A) (B := B)) (x : X) (y : Y) : Op (A × B) :=
  localOutput P.resource.matrix (P.alice x) (P.bob y)

def preparationError {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (q : X × Y → ℝ) (ψ : X → Y → A × B → ℂ)
    (P : Preparation (X := X) (Y := Y) (A := A) (B := B)) : ℝ :=
  ∑ x, ∑ y, q (x,y) * infidelity (P.output x y) (ket (ψ x y))

def dprep {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (q : X × Y → ℝ) (ψ : X → Y → A × B → ℂ) : ℝ :=
  sInf (Set.range (preparationError q ψ))

def beta0 (s : ℝ) : ℝ := Real.pi / (2 * (Real.cosh (Real.pi * s) + 1))

def replacementL {K : Type} [Fintype K] [DecidableEq K] (ρ ν : Op K) (s : ℝ) : Op K :=
  WildeQIT.Recover.supportPow ρ ((1 + Complex.I * (s : ℂ))/2) *
    WildeQIT.Recover.supportPow ν (-((1 + Complex.I * (s : ℂ))/2))

def replacementKernel {R K : Type} [Fintype R] [Fintype K] [DecidableEq R] [DecidableEq K]
    (ρ ν : Op (R × K)) (s : ℝ) : Op (R × K) :=
  (beta0 s : ℂ) •
    (((1 : Op R) ⊗ₖ replacementL (trL ρ) (trL ν) s) * ν *
      ((1 : Op R) ⊗ₖ replacementL (trL ρ) (trL ν) s)ᴴ)

/-- The real integral in (39), with kernel-zero supported complex powers. -/
def replacement {R K : Type} [Fintype R] [Fintype K] [DecidableEq R] [DecidableEq K]
    (ρ ν : Op (R × K)) : Op (R × K) :=
  fun a b => ∫ s : ℝ, replacementKernel ρ ν s a b

end JainCRERepetition.Cubic


