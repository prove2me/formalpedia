-- Prove2me | Definitions.Def_OAICatalanIrrationality
-- name    : OAICatalanIrrationality
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-07T18:58:42.398216+00:00
-- url     : https://prove2.me/theorems/86781a1b-013a-4806-99ec-e35fe8bb22dd
-- title:
--   OpenAI's Catalan determinants — the moment determinants Δ_N, the fixed matrices modulo 101 and the barrier functions
-- statement:
--   The definitions behind OpenAI's proof that Catalan's constant $G=\sum_{j\ge0}(-1)^j/(2j+1)^2$ is irrational, as they appear in OpenAI's Lean development `lean/OAI/NumberTheory/Catalan` (github.com/openai/math, Apache License 2.0), carved out of that development without change. They are published so that the paper's intermediate propositions can be stated, and proved one at a time.
--
--   **Scale parameters** (paper, Eq. (2)). For $N\ge1$: `n N` $=48N$, `b N` $=7N$, `q N` $=$ `g N` $=4N$, `h N` $=2N$, `Cdegree N` $=63N$, `H N` $=65N$.
--
--   **Rows** (Eq. (3)). For $0\le r$, with $d=|r-g|$, `rowP N r` is the integer polynomial $P_r(t)=(1-t)^h\,t^{C-1}T_d(1/t)$ and `rowD N r` is $D_r(t)=\operatorname{sgn}(r-g)(1-t)^h\,t^{C-1}U_{d-1}(1/t)$, with $T_d,U_d$ the Chebyshev polynomials (the factor $t^{C-1}F(1/t)$ is written `reversedRow`).
--
--   **The real determinant** (Eq. (6), (7)). For real polynomials,
--   $$M(P,Q)=\int_{-1}^{1}\!\int_0^1\frac{|t|}{\sqrt{1-t^2}}\,\frac{P(t)Q(s)}{1-ts}\,ds\,dt,\qquad Z(P,Q)=\int_0^1\!\int_0^1\frac{P(t)Q(s)}{1-ts}\,ds\,dt$$
--   (`mixedMoment`, `zetaMoment`), and `determinant N` is
--   $$\Delta_N=\det_{0\le r,k<n}\Big(M\big(P_r,\,s^{b+k}(1-s)^q\big)-\tfrac32\,Z\big(D_r,\,s^{b+k}(1-s)^q\big)\Big).$$
--
--   **The rational model** (Eq. (13)–(17)). `momentRat i j` is the rational array $M^0(i,j)$ of Eq. (14), `zetaRat i j` is $Z^0(i,j)$ of Eq. (16), and `centralCoeffKernel d` is $c_{d/2}$ for even $d\ge0$ and $0$ otherwise, where $c_l=4^{-l}\binom{2l}{l}$. For a rational number $z$, `rawEntryRat z N r j` is
--   $$\sum_{i<H}[t^i]P_r\,\big(M^0(i,j)+4z\,c_{(i-j)/2}\big)-\tfrac32\sum_{i<H}[t^i]D_r\,Z^0(i,j),$$
--   `filteredEntryRat z N r k` $=\sum_{v=0}^{q}(-1)^v\binom{q}{v}\,$`rawEntryRat z N r (b+k+v)`, and `determinantRat z N` is the $n\times n$ determinant of these entries. By Eq. (17), with $z=G$ this is $\Delta_N$ (the $\zeta(2)$ terms cancel, Proposition 2.1); for general rational $z$ it is the same construction with $G$ replaced by $z$.
--
--   **The fixed matrices** (Eq. (47), (48)). `fixedBaseEntryRat r k` $=$ `filteredEntryRat 0 1 r k` for $0\le r\le48$, $0\le k<48$: the rational $49\times48$ matrix $\mathcal B(r,k)$ of Eq. (47). `fixedB0`, `fixedB1` are $\mathcal B_0=(\mathcal B(r,k))_{r,k<48}$ and $\mathcal B_1=(\mathcal B(r+1,k))_{r,k<48}$, and `fixedMatrix σ` $=\mathcal B_0+\sigma\mathcal B_1$. `fixedIntegerBaseCanonical r k` is OpenAI's explicit integer table $A(r,k)=2\sum_{i<65}[t^i]P_r\,c_M(i,k)-3\sum_{i<65}[t^i]D_r\,c_Z(i,k)$ (rows at $N=1$), where `fixedClearedMoment`, `fixedClearedZeta` are explicit integer tables $c_M,c_Z$ (given column by column) of the filtered moments $\sum_{v=0}^4(-1)^v\binom4vM^0(i,7+k+v)$ and $\sum_{v=0}^4(-1)^v\binom4vZ^0(i,7+k+v)$ cleared of a common denominator; it is certificate data, about $370$ KB of the bundle. `fixedLiteralBaseMod` is an explicit $49\times48$ table of residues modulo $101$ (given row by row as `fixedLiteralModZeroRow_r`, the last row as a difference of two such rows), the reduction of $\mathcal B$ modulo $101$ after clearing a common denominator. `palindromicPrimeCutoff z` is the maximum of the denominator of $z$ and $260+\sum_{\sigma\in\{0,1,-1\}}\big(|\operatorname{num}\det(\mathcal B_0+\sigma\mathcal B_1)|+\operatorname{den}\det(\mathcal B_0+\sigma\mathcal B_1)\big)$.
--
--   **The barrier functions** (§7.1, Eq. (89)–(91)). `barrierP2`, `barrierV2` (and `barrierP1`, `barrierV1`) are the trial sequences $p,v$ of §7.1: $u_k=l_k+\sum_z r_z z^k$ with the finite parts and exponential tails of the paper's tables (all integer coefficients times $10^{-8}$). For a sequence $u$,
--   $$\|u\|_*^2=\sum_{k\ge1}\frac{u_k^2}{k},\qquad T(u,x)=\sum_{k\ge1}\frac{u_kT_k(x)}{k},\qquad S(u,x)=\sum_{k\ge1}\frac{u_kx^k}{k}$$
--   (`barrierTrialNormSq`, `barrierTrialT`, `barrierTrialS`). In case $\kappa=2$ (with $\lambda_2=0$),
--   $$X_2(x)=\tfrac{19}{48}\log|x|+\tfrac1{12}\log(1-x)-\big(1+\tfrac{17}{48}\big)\log(1+x^2)-4T(p,x)-S(v,x),\qquad Y_2(s)=\tfrac{7}{48}\log s+\tfrac1{12}\log(1-s)+2T(v,s)$$
--   (`barrierCase2X`, `barrierCase2Y`). `barrierBracketLeft m` $=m/10^{10}$, and `barrierCase2YBrackets` is the list of fifteen integers $m$ of the root table on p. 38 for $Y_2$. `realDeterminantCertificateSupBound` is the larger of the two right-hand sides of Eq. (78) (cases $\kappa=1,2$), built from `realEnergyDualConstant`, `realEnergyRowTrialSup` and `realEnergyColumnTrialSup`.
--
--   **Source and credit.** OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math), [paper](https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf); Lean in `lean/OAI/NumberTheory/Catalan`, Apache License 2.0. The code of this bundle is OpenAI's, with comments removed; only declarations needed to state the published lemmas are kept.
--
--   **Formalization note.** The definitions live in OpenAI's namespace `OAI.InternalCatalan`, under their own names, so that the published lemmas and their proofs use OpenAI's code verbatim. $\log$ is `Real.log` (so $\log 0=0$ in Lean; the statements that use it carry the hypothesis $\Delta_N\ne0$).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), §2 Eq. (2)-(7) pp. 4-5 (the determinant Δ_N), §4 Eq. (47) p. 19 (the fixed matrices), §4.4 p. 24 (their reduction mod 101), §7.1 Eq. (89)-(91) pp. 34-36 (the trial sequences and the barrier functions X_2, Y_2); the definitions are OpenAI's Lean definitions, carved from the development

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue

/-!
# Catalan's constant is irrational: definitions

OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026,
https://github.com/openai/math (paper:
`preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf`).

The definitions below are taken from OpenAI's Lean development `lean/OAI/NumberTheory/Catalan`
in that repository (Apache License, Version 2.0), with comments removed and line-level edits for
this Lean and Mathlib version. They are the declarations needed to state the published lemmas
of the proof.
-/

section

namespace OAI

namespace InternalCatalan

section

def n (N : ℕ) : ℕ := 48 * N
def a (N : ℕ) : ℕ := 11 * N
def b (N : ℕ) : ℕ := 7 * N
def q (N : ℕ) : ℕ := 4 * N
def g (N : ℕ) : ℕ := 4 * N
def h (N : ℕ) : ℕ := 2 * N
def Cdegree (N : ℕ) : ℕ := 63 * N
def H (N : ℕ) : ℕ := 65 * N

def rowOffset (N r : ℕ) : ℤ := (r : ℤ) - (g N : ℤ)
def rowDistance (N r : ℕ) : ℕ := (rowOffset N r).natAbs

end

noncomputable section
open Set
open scoped BigOperators

end

end InternalCatalan

end OAI

end

section

namespace OAI

namespace InternalCatalan

section

open scoped BigOperators

def centralCoeff (l : ℕ) : ℚ :=
  ((2 * l).choose l : ℚ) / 4 ^ l

def centralCoeffKernel (d : ℤ) : ℚ :=
  if 0 ≤ d ∧ d % 2 = 0 then centralCoeff (d.toNat / 2) else 0

def momentScalar (i : ℕ) : ℚ :=
  if i % 2 = 0 then 2 / (((i + 1 : ℕ) : ℚ) * centralCoeff (i / 2)) else 0

def boundaryMinus : ℕ → ℚ
  | 0 => 0
  | 1 => 2
  | d + 2 =>
      (((d + 1 : ℕ) : ℚ) * boundaryMinus d + momentScalar d + momentScalar (d + 1)) /
        ((d + 2 : ℕ) : ℚ)

def boundaryPlus : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | d + 2 =>
      ((d : ℚ) * boundaryPlus d + 2 / ((d + 1 : ℕ) : ℚ)) /
        ((d + 1 : ℕ) : ℚ)

def momentRat (i j : ℕ) : ℚ :=
  if j ≤ i then
    boundaryMinus (i - j) -
      ∑ k ∈ Finset.range j, momentScalar (i - j + k) / ((k + 1 : ℕ) : ℚ)
  else
    boundaryPlus (j - i) -
      ∑ k ∈ Finset.range i, momentScalar k / ((j - i + k + 1 : ℕ) : ℚ)

def harmonicRat (d n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, 1 / (((k + 1 : ℕ) : ℚ) ^ d)

def zetaRat (i j : ℕ) : ℚ :=
  if i = j then -harmonicRat 2 i
  else (harmonicRat 1 i - harmonicRat 1 j) / ((i : ℚ) - (j : ℚ))

end

end InternalCatalan

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial

def reversedRow (C : ℕ) (F : ℤ[X]) : ℤ[X] :=
  ∑ u ∈ Finset.range C, Polynomial.C (F.coeff u) * X ^ (C - 1 - u)

def rowP (N r : ℕ) : ℤ[X] :=
  (1 - X) ^ h N *
    reversedRow (Cdegree N) (Polynomial.Chebyshev.T ℤ (rowDistance N r : ℤ))

def rowD (N r : ℕ) : ℤ[X] :=
  Polynomial.C (Int.sign (rowOffset N r)) * (1 - X) ^ h N *
    reversedRow (Cdegree N)
      (Polynomial.Chebyshev.U ℤ ((rowDistance N r : ℤ) - 1))

def realPoly (F : ℤ[X]) : ℝ[X] := F.map (Int.castRingHom ℝ)

def filteredColumn (N k : ℕ) : ℝ[X] := X ^ (b N + k) * (1 - X) ^ q N

def mixedMoment (P Q : ℝ[X]) : ℝ :=
  ∫ t in (-1 : ℝ)..1, ∫ s in (0 : ℝ)..1,
    (|t| / Real.sqrt (1 - t ^ 2)) * (P.eval t * Q.eval s) / (1 - t * s)

def zetaMoment (P Q : ℝ[X]) : ℝ :=
  ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1,
    (P.eval t * Q.eval s) / (1 - t * s)

def determinantEntry (N r k : ℕ) : ℝ :=
  mixedMoment (realPoly (rowP N r)) (filteredColumn N k) -
    (3 / 2 : ℝ) * zetaMoment (realPoly (rowD N r)) (filteredColumn N k)

def determinant (N : ℕ) : ℝ :=
  Matrix.det (fun r k : Fin (n N) => determinantEntry N r.val k.val)

end

section

open scoped BigOperators

def rawEntryRat (z : ℚ) (N r j : ℕ) : ℚ :=
  (∑ i ∈ Finset.range (H N), ((rowP N r).coeff i : ℚ) *
    (momentRat i j + 4 * z * centralCoeffKernel ((i : ℤ) - (j : ℤ)))) -
  (3 / 2 : ℚ) *
    ∑ i ∈ Finset.range (H N), ((rowD N r).coeff i : ℚ) * zetaRat i j

def filterCoeffRat (N v : ℕ) : ℚ := (-1 : ℚ) ^ v * ((q N).choose v : ℚ)

def filteredEntryRat (z : ℚ) (N r k : ℕ) : ℚ :=
  ∑ v ∈ Finset.range (q N + 1),
    filterCoeffRat N v * rawEntryRat z N r (b N + k + v)

def determinantRat (z : ℚ) (N : ℕ) : ℚ :=
  Matrix.det (fun r k : Fin (n N) => filteredEntryRat z N r.val k.val)

def fixedBaseEntryRat (r : Fin 49) (k : Fin 48) : ℚ :=
  filteredEntryRat 0 1 r.val k.val

end

section

open Polynomial

variable {K : Type*} [Field K]

end

open Polynomial

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section

open Polynomial
open scoped BigOperators

namespace InternalCatalan

def fixedB0 : Matrix (Fin 48) (Fin 48) ℚ :=
  fun r k => fixedBaseEntryRat r.castSucc k

def fixedB1 : Matrix (Fin 48) (Fin 48) ℚ :=
  fun r k => fixedBaseEntryRat r.succ k

def fixedMatrix (sigma : ℚ) : Matrix (Fin 48) (Fin 48) ℚ :=
  fixedB0 + sigma • fixedB1

end InternalCatalan

end

noncomputable section
open scoped BigOperators
namespace InternalCatalan

end InternalCatalan

end

noncomputable section

namespace InternalCatalan

open scoped BigOperators

end InternalCatalan

end

noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker

end InternalCatalan

end

noncomputable section

namespace InternalCatalan

open Matrix
open scoped Kronecker

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace InternalCatalan

def fixedClearedMoment47 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1098499161679083876906851672851809063872171696266173045255700480 : ℤ)
  | 19 => (-1113459562072658407803054166731097589737492378529792550108135424 : ℤ)
  | 20 => (1129047896646103068279984893916747415708396922444516971759271936 : ℤ)
  | 21 => (-1145311282309136243324716793051867407865221070886572957940842496 : ℤ)
  | 22 => (1162297703207636867085657452878602469918394662562436797761060864 : ℤ)
  | 23 => (-1180065028086128711697075453036811657996993739026930032076390400 : ℤ)
  | 24 => (1198671965985038090998251491093849840690780407513653869792985088 : ℤ)
  | 25 => (-1218190468639482458417904730083896821372061878093180663551229952 : ℤ)
  | 26 => (1238693303692555703887821519721594523094727748847736479192973312 : ℤ)
  | 27 => (-1260271194916588178359243599087835015429717721482612658403278848 : ℤ)
  | 28 => (1283015659759546505584906954747879420351629998150372067744153600 : ℤ)
  | 29 => (-1307042946917041295803136906785810699262308966130678115631890432 : ℤ)
  | 30 => (1332470078370504600504542147689313570544805065852000670515724288 : ℤ)
  | 31 => (-1359448810855605142067015265437111984872804669673888307874889728 : ℤ)
  | 32 => (1388131655595337420831040482729767641377701885684546288496934912 : ℤ)
  | 33 => (-1418721090272735418080946198860855592663925265982375680939130880 : ℤ)
  | 34 => (1451420329646471703958529603358432112951326468066858801985224704 : ℤ)
  | 35 => (-1486506593229978563593047006863805262836635016945312190940839936 : ℤ)
  | 36 => (1524257821418839191473038337700179073598155771505841843812171776 : ℤ)
  | 37 => (-1565065539844146601069102526820649877647236538623319790619459584 : ℤ)
  | 38 => (1609321979903294751977345801792069537686415698581653996406046720 : ℤ)
  | 39 => (-1657601551911522307275536389331572473677557706326022165157117952 : ℤ)
  | 40 => (1710479357793816390200503297571011687026240702214056044321046528 : ℤ)
  | 41 => (-1768839299603453730962248508356865435310142620591972368932405248 : ℤ)
  | 42 => (1833565957705691764767331102860395338105395274382299773095903232 : ℤ)
  | 43 => (-1906105940485271056492204552384027742788082068934940805237309440 : ℤ)
  | 44 => (1987906522113880326045354997941377954230039891365274332841377792 : ℤ)
  | 45 => (-2081539716927071166038961224559395522846235574672372566566371328 : ℤ)
  | 46 => (2189578193220849070849070349447081023762805689579474612941488128 : ℤ)
  | 47 => (-2317166313755609102364268814008927860483323434667926266075676672 : ℤ)
  | 48 => (2469449084059849560400678364457351162529651490296267360425738240 : ℤ)
  | 49 => (-2658773431978827080322175194634127837985471291124943757051428864 : ℤ)
  | 50 => (2897486917511473775686625802667220968903062544509026412355649536 : ℤ)
  | 51 => (-3226746712443744637319744315112087202630613929448770869716320256 : ℤ)
  | 52 => (3687710610629412754199534379645037596089330228192616602732068864 : ℤ)
  | 53 => (-4609638177058376115623600054063512162374602760977048364205998080 : ℤ)
  | 54 => (4757244146137854814882390605272450938236440253337789685737455616 : ℤ)
  | 55 => (-590423537675511112322859098900454669425441510516346448504684544 : ℤ)
  | 56 => (-5955018974534558155321716157140116851492823129510682212786241536 : ℤ)
  | 57 => (8333641102063521243052901725350732741287081166240875406734393344 : ℤ)
  | 58 => (-6844886275254554483415942098642998158654108393951403735525621760 : ℤ)
  | 59 => (5475909085616104316316194683260390546530967873329047935467388928 : ℤ)
  | 60 => (-4791420381776111350127252634992433374456595682737995123693453312 : ℤ)
  | 61 => (4302500002862468653153765095081309123949629448675859818319183872 : ℤ)
  | 62 => (-3948032604384697765507732815777985917801152147474560285228924928 : ℤ)
  | 63 => (3666903416175881451352142382009556623774709695491012861676748800 : ℤ)
  | 64 => (-3440777637003274724542394381227932663713533864451941753195331584 : ℤ)
  | _ => 0

def fixedClearedZeta47 (i : ℕ) : ℤ :=
  match i with
  | 19 => (8124177052172180195519299995398577440872481188730634240 : ℤ)
  | 20 => (7838786020072029603590932957237915863150748995566960640 : ℤ)
  | 21 => (7574123574274400002312186023646102802101402147529687040 : ℤ)
  | 22 => (7327916168201763039515482724089233045415504741285232640 : ℤ)
  | 23 => (7098220168619550315084993141734610581579259348611235840 : ℤ)
  | 24 => (6883362964715419225844687018844396210539655336957050880 : ℤ)
  | 25 => (6681896431672808165385881904177419533821629001640181760 : ℤ)
  | 26 => (6492559795782896955821246000405382339396884166460047360 : ℤ)
  | 27 => (6314249734583131066894838077998824038821511535798517760 : ℤ)
  | 28 => (6145996102435216131870192123920153363680008245671362560 : ℤ)
  | 29 => (5986942071825265672639789741133001116501491260013412352 : ℤ)
  | 30 => (5836327771448139879351940957356393547803154702760148992 : ℤ)
  | 31 => (5693476716089291715588029685127969119993144841194176512 : ℤ)
  | 32 => (5557784482465664233245508611450934236840981722396884992 : ℤ)
  | 33 => (5428709204776651500810139687064637746423573315428810752 : ℤ)
  | 34 => (5305763554433578461213822277229168334591193099838423040 : ℤ)
  | 35 => (5188507937862985692265249815614125991155753674646487040 : ℤ)
  | 36 => (5076544699853752671500628490492883802066262395652669440 : ℤ)
  | 37 => (4969513161582884344258015907427821618352800603874263040 : ℤ)
  | 38 => (4867085355095100797129403139207720451492613275768586240 : ℤ)
  | 39 => (4768962341758731965295239082210109974745662127991685120 : ℤ)
  | 40 => (4674871022663064056359218066054599935479780726873784320 : ℤ)
  | 41 => (4584561365253322423132989394482527458622987178627563520 : ℤ)
  | 42 => (4497803983622126563598680242403605135949973879594680320 : ℤ)
  | 43 => (4414388020479286794276263047113261557284473612974161920 : ℤ)
  | 44 => (4334119287434111050361622785467375024703924032587694080 : ℤ)
  | 45 => (4256818627254739604110130294704539873149249704458977280 : ℤ)
  | 46 => (4182320467535363753246299811804910943492460089788334080 : ℤ)
  | 47 => (4110471539953266671026424037595325699670885958712033280 : ℤ)
  | 48 => (4041129743229181875828931619309806779472922833248583680 : ℤ)
  | 49 => (3974163131171341620787579216215092673484515012520181760 : ℤ)
  | 50 => (3909449009908916536455955309038420430650028727048601600 : ℤ)
  | 51 => (3846873130702728920332092683650770710896638630140313600 : ℤ)
  | 52 => (3786328966639162547477520686151662709887985107179929600 : ℤ)
  | 53 => (3727717063130816378011924390700398581251948186016153600 : ℤ)
  | 54 => (-702421057437880508619946662035991106879640301942565585687674880 : ℤ)
  | 55 => (2809684248051223980758339776566138709138699697552553437739089920 : ℤ)
  | 56 => (-4214526363090375193947148753570461764698160109382169351033978880 : ℤ)
  | 57 => (2809684247946119176346756608013170916167823797705224071592017920 : ℤ)
  | 58 => (-702421057648238384408583884489415205382009324693435284172308480 : ℤ)
  | 59 => (3411808837441764142587185035556297006569579695675801600 : ℤ)
  | 60 => (3364422603588406307273474132284681770367224422124748800 : ℤ)
  | 61 => (3318368067173550331500195385545289913168214027455692800 : ℤ)
  | 62 => (3273588845845969322020677272581716816103455280909516800 : ℤ)
  | 63 => (3230031739327168767570423735766667115689764975332556800 : ℤ)
  | 64 => (3187646505671897543258992470210064209310548128641843200 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment0 (i : ℕ) : ℤ :=
  match i with
  | 18 => (3251427179346744574627321205113340229657965237132715044005478400 : ℤ)
  | 19 => (-3090827769323048355141178329023161479432117598187690114678784000 : ℤ)
  | 20 => (2951958686035753392972316191714787242842861867417418546020352000 : ℤ)
  | 21 => (-2830327516670362388810274535998511292422348242136929876836352000 : ℤ)
  | 22 => (2722773090780290587318685752348690786031042807077584793868697600 : ℤ)
  | 23 => (-2626501626377038481674907526885209611592560253576249965176422400 : ℤ)
  | 24 => (2539997212902010229053711859467068320825399560813681515587174400 : ℤ)
  | 25 => (-2461325985056972754187498472842753666762633623251848331494686720 : ℤ)
  | 26 => (2389784588649477148742928036848231757414926561347981062470369280 : ℤ)
  | 27 => (-2323920482725245696004106698702883382963822780909352189427712000 : ℤ)
  | 28 => (2263469229773343007219301459540943143919851003866081485284966400 : ℤ)
  | 29 => (-2207269453465080735598442044388600486026379636534895187360481280 : ℤ)
  | 30 => (2155309612998750858700977790819780779484646778386289848871813120 : ℤ)
  | 31 => (-2106615840896578601361511784972622474625151381484253542245990400 : ℤ)
  | 32 => (2061329340394999302318545204944227937985188325829955763514114048 : ℤ)
  | 33 => (-2018603447915421966593984574224287282008528462367584162511060992 : ℤ)
  | 34 => (1978674802035512934215046747408914005576127752246715654195904512 : ℤ)
  | 35 => (-1940786933796165801918270334856328299637468122000774315374542848 : ℤ)
  | 36 => (1905237494756589246332567796484700705207879198942892775387955200 : ℤ)
  | 37 => (-1871336455752144551980586155020202541679250484781223551002738688 : ℤ)
  | 38 => (1839420978646647228594792007594321373016534400451429961933258752 : ℤ)
  | 39 => (-1808851629666643343661302778817974291863768690268903060854013952 : ℤ)
  | 40 => (1779991211858624260484627049141226436051010320485136635000782848 : ℤ)
  | 41 => (-1752239959538003673963440192484813125844888494402821977328844800 : ℤ)
  | 42 => (1725977133639593474392911270913673128983913945205947858140790784 : ℤ)
  | 43 => (-1700634875157763406374518721700065949545433031674798209434648576 : ℤ)
  | 44 => (1676602690585271620730455476365387274571853738927244905090646016 : ℤ)
  | 45 => (-1653338968324046387786897740592503236388462506722318004422180864 : ℤ)
  | 46 => (1631239184600741969573382121483122634141589920408841927036764160 : ℤ)
  | 47 => (-1609783750357050029228625875253861258698661574628048152568561664 : ℤ)
  | 48 => (1589371128354085397640150591973744227466047996707928627897040896 : ℤ)
  | 49 => (-1569500530132423764532484128682873160552792414688661743044673536 : ℤ)
  | 50 => (1550571302536054296049095008310254512195776334065154367000346624 : ℤ)
  | 51 => (-1532098952583545550787145720260770097995799038951762277338009600 : ℤ)
  | 52 => (1514482219631313195809805168307832175074246695858980200738603008 : ℤ)
  | 53 => (-1497250923708359479705925422094813831065305708700474650750932992 : ℤ)
  | 54 => (1480802135387546307273939245635524960989367422151391644112658432 : ℤ)
  | 55 => (-1464678393328318865513878963926413261922193884779229673412942208 : ℤ)
  | 56 => (1449274345135013271303942908731020598749413281777573536112821760 : ℤ)
  | 57 => (-1434143946746632289979113815182263952605360089781728264344711104 : ℤ)
  | 58 => (1419678890317253474005538496369715390276918132823225724497387776 : ℤ)
  | 59 => (-1405443472408827080502959878747946819657356762722242244661986896 : ℤ)
  | 60 => (1391826058829532045531401451790380353269783821054364874609249344 : ℤ)
  | 61 => (-1378400384881082745112268869327669668327578600712020346907491320 : ℤ)
  | 62 => (1365551237832238548140495799799026360425452321358628288581131936 : ℤ)
  | 63 => (-1352861027599423862515085408596348801302296188061872277946793019 : ℤ)
  | 64 => (1340710798462641014838755015393798098259867313213664270168284364 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment1 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-3440708417269749436320240380445349033788366030905054498232729600 : ℤ)
  | 19 => (3251365978813524233705918910505601362827547571581551686713344000 : ℤ)
  | 20 => (-3090827769323048355141178329023161479432117598187690114678784000 : ℤ)
  | 21 => (2951900399813638782570980673040750226813892662130596300980224000 : ℤ)
  | 22 => (-2830327516670362388810274535998511292422348242136929876836352000 : ℤ)
  | 23 => (2722717338741746177369582212747437988090289654194537429047705600 : ℤ)
  | 24 => (-2626501626377038481674907526885209611592560253576249965176422400 : ℤ)
  | 25 => (2539943690945007595502572461449865634802276534045956045359022080 : ℤ)
  | 26 => (-2461325985056972754187498472842753666762633623251848331494686720 : ℤ)
  | 27 => (2389733048987178316434423431350184726429696980016097276324741120 : ℤ)
  | 28 => (-2323920482725245696004106698702883382963822780909352189427712000 : ℤ)
  | 29 => (2263419467340778617404193564577311527796181063269779898661601280 : ℤ)
  | 30 => (-2207269453465080735598442044388600486026379636534895187360481280 : ℤ)
  | 31 => (2155261455805946610492808860209814699364966190712449603752427520 : ℤ)
  | 32 => (-2106615840896578601361511784972622474625151381484253542245990400 : ℤ)
  | 33 => (2061282642511067910116684423746685072414588968085625828852891648 : ℤ)
  | 34 => (-2018603447915421966593984574224287282008528462367584162511060992 : ℤ)
  | 35 => (1978629438376836724647524845674158079021831233295080860525002752 : ℤ)
  | 36 => (-1940786933796165801918270334856328299637468122000774315374542848 : ℤ)
  | 37 => (1905193357142742123510114054256289533425320423746707570735185920 : ℤ)
  | 38 => (-1871336455752144551980586155020202541679250484781223551002738688 : ℤ)
  | 39 => (1839377972766488493537016566448689974869425850260275147143380992 : ℤ)
  | 40 => (-1808851629666643343661302778817974291863768690268903060854013952 : ℤ)
  | 41 => (1779949254902371836038016862657683608590416612981570962035048448 : ℤ)
  | 42 => (-1752239959538003673963440192484813125844888494402821977328844800 : ℤ)
  | 43 => (1725936152426509710979943181790212692859613114621069758964957184 : ℤ)
  | 44 => (-1700634875157763406374518721700065949545433031674798209434648576 : ℤ)
  | 45 => (1676562620065811940948886678111337070361426260133141874785386496 : ℤ)
  | 46 => (-1653338968324046387786897740592503236388462506722318004422180864 : ℤ)
  | 47 => (1631199966645526112765889255106818178956916217759294280355020800 : ℤ)
  | 48 => (-1609783750357050029228625875253861258698661574628048152568561664 : ℤ)
  | 49 => (1589332710765302517502198396339813332591265594112453382167986176 : ℤ)
  | 50 => (-1569500530132423764532484128682873160552792414688661743044673536 : ℤ)
  | 51 => (1550533638233325982188357561610322262318538684461747263344410624 : ℤ)
  | 52 => (-1532098952583545550787145720260770097995799038951762277338009600 : ℤ)
  | 53 => (1514445265975806170889836352677709967647522964172618514132779008 : ℤ)
  | 54 => (-1497250923708359479705925422094813831065305708700474650750932992 : ℤ)
  | 55 => (1480765853616684864625242590289586793697675031041145624536031232 : ℤ)
  | 56 => (-1464678393328318865513878963926413261922193884779229673412942208 : ℤ)
  | 57 => (1449238699886447643438556721022730469480382160686805516879644160 : ℤ)
  | 58 => (-1434143946746632289979113815182263952605360089781728264344711104 : ℤ)
  | 59 => (1419643849225443195764989362690379330995497708700097841183416576 : ℤ)
  | 60 => (-1405443472408827080502959878747946819657356762722242244661986896 : ℤ)
  | 61 => (1391791592181849804639058041613984229386419469457845645120097344 : ℤ)
  | 62 => (-1378400384881082745112268869327669668327578600712020346907491320 : ℤ)
  | 63 => (1365517318274202057103586412006382555968808038835069681782283936 : ℤ)
  | 64 => (-1352861027599423862515085408596348801302296188061872277946793019 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment10 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-590418503790983206547034926076470168381739935373893445668044800 : ℤ)
  | 19 => (-5955015070891881819400937922418421389940369243628887095640064000 : ℤ)
  | 20 => (8333645928245127947027302423529880362202746904733147786641408000 : ℤ)
  | 21 => (-6844882519192183646847523721791223778983539386936376468439040000 : ℤ)
  | 22 => (5475913728417725993741654354340220011774123675060740810185113600 : ℤ)
  | 23 => (-4791416757382705195019748947396390429385787288397423575459430400 : ℤ)
  | 24 => (4302504482133304174179707421862823284408100980072282025518694400 : ℤ)
  | 25 => (-3948029098457143761018781871632206703251883480369799062785884160 : ℤ)
  | 26 => (3666907748376219326046864303395881194490515087143481186598256640 : ℤ)
  | 27 => (-3440774238435990214504716803577592567221621306503039544994037760 : ℤ)
  | 28 => (3251325231402906434412204688241299096166803675842324537267978240 : ℤ)
  | 29 => (-3090890639095355542924470390675632968060893506973666623178670080 : ℤ)
  | 30 => (2951861333317228028544900827579513336928141938449218328980357120 : ℤ)
  | 31 => (-2830387801551524770260021177238107810399639713956587087750758400 : ℤ)
  | 32 => (2722679760185609638889908888654187021703042104099079022455029760 : ℤ)
  | 33 => (-2626559622497574767042330245450185831762442931117338305956413440 : ℤ)
  | 34 => (2539907441768566440622988954275526369440905608570568391356579840 : ℤ)
  | 35 => (-2461381935805021141263858475649662827954489355887082896139223040 : ℤ)
  | 36 => (2389697997001703785530003984669295309025537267177708867152773120 : ℤ)
  | 37 => (-2323974591062370317261272123853023407163130420645115487636684800 : ℤ)
  | 38 => (2263385500957688940637028706975355908819904711978027284902707200 : ℤ)
  | 39 => (-2207321890766936375619122113917211108698250729813429599936184320 : ℤ)
  | 40 => (2155228479796721622883133026454322954749678594688775250383994880 : ℤ)
  | 41 => (-2106666753448544458399763989828302166287837205624264177011916800 : ℤ)
  | 42 => (2061250574828888836718529320110588746140092241060019394710601728 : ℤ)
  | 43 => (-2018652961782533881510832050331525923947229587756226400130957312 : ℤ)
  | 44 => (1978598207731659184734759296369484539438812172408632265809068032 : ℤ)
  | 45 => (-1940835158539286084317870336569910622547128293913482238653104128 : ℤ)
  | 46 => (1905162901122133462885983082010096841860066975583149548896256000 : ℤ)
  | 47 => (-1871383487308281262459449247238899636035715770034938298402603008 : ℤ)
  | 48 => (1839348236359059457115502272462557428469406664336230537895084032 : ℤ)
  | 49 => (-1808897552612604499817948698911932149013392580872635398049759232 : ℤ)
  | 50 => (1779920189323047597551473903779334173079101417735421821943021568 : ℤ)
  | 51 => (-1752284848891649001785817636710379044854829771228637619290112000 : ℤ)
  | 52 => (1725907714171419393082745597018057796012369711755761140308639744 : ℤ)
  | 53 => (-1700678797827439292667082188386601669833227265046227652998332416 : ℤ)
  | 54 => (1676534770144166482188988059521637232764371893238267090625888256 : ℤ)
  | 55 => (-1653381984286800913551104089201397542146223067485743888306274304 : ℤ)
  | 56 => (1631172669949553638986095370403398808117206343463188968982446080 : ℤ)
  | 57 => (-1609825913625253197982864339806162442337095378799354651479670784 : ℤ)
  | 58 => (1589305935549050302593886383052756545748064084481751887725592576 : ℤ)
  | 59 => (-1569541889553506345107134738311208429620847020174199962490126336 : ℤ)
  | 60 => (1550507355678168370238095083842275929355791483655583786385997824 : ℤ)
  | 61 => (-1532139552506805698537055408771156196165221889953494888516505600 : ℤ)
  | 62 => (1514419449825642840181604936274467151116866299322215324387524608 : ℤ)
  | 63 => (-1497290804544907854509305155933536875987404893804144004945467392 : ℤ)
  | 64 => (1480740479869627114871963452745411578780403015258322279644536832 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment11 (i : ℕ) : ℤ :=
  match i with
  | 18 => (4757248216844528871791367092635246214496994032563152019993395200 : ℤ)
  | 19 => (-590420344408523667928129731929334495203707383961898358669312000 : ℤ)
  | 20 => (-5955015070891881819400937922418421389940369243628887095640064000 : ℤ)
  | 21 => (8333644175276041793331021656050961955705635048935047869497344000 : ℤ)
  | 22 => (-6844882519192183646847523721791223778983539386936376468439040000 : ℤ)
  | 23 => (5475912051664687064119124924577776318602973204297340889438617600 : ℤ)
  | 24 => (-4791416757382705195019748947396390429385787288397423575459430400 : ℤ)
  | 25 => (4302502872450386801742079169290877338963796528139418101602058240 : ℤ)
  | 26 => (-3948029098457143761018781871632206703251883480369799062785884160 : ℤ)
  | 27 => (3666906198311187782218037097215488802581184874171093704308162560 : ℤ)
  | 28 => (-3440774238435990214504716803577592567221621306503039544994037760 : ℤ)
  | 29 => (3251323734788393219680923247791265062599174504696571106091335680 : ℤ)
  | 30 => (-3090890639095355542924470390675632968060893506973666623178670080 : ℤ)
  | 31 => (2951859884980602336869467175531093304443339514759779524615864320 : ℤ)
  | 32 => (-2830387801551524770260021177238107810399639713956587087750758400 : ℤ)
  | 33 => (2722678355737972604537973226061779717475354905369926242465218560 : ℤ)
  | 34 => (-2626559622497574767042330245450185831762442931117338305956413440 : ℤ)
  | 35 => (2539906077448004750109680024900044988191152329805105690795048960 : ℤ)
  | 36 => (-2461381935805021141263858475649662827954489355887082896139223040 : ℤ)
  | 37 => (2389696669554670789354892593925583694836588131081582996336148480 : ℤ)
  | 38 => (-2323974591062370317261272123853023407163130420645115487636684800 : ℤ)
  | 39 => (2263384207547759354620253505737893310379390169115135410773688320 : ℤ)
  | 40 => (-2207321890766936375619122113917211108698250729813429599936184320 : ℤ)
  | 41 => (2155227217933375685305791366710457005051615626042051470745927680 : ℤ)
  | 42 => (-2106666753448544458399763989828302166287837205624264177011916800 : ℤ)
  | 43 => (2061249342311202106991823512918905725504774922846940354133884928 : ℤ)
  | 44 => (-2018652961782533881510832050331525923947229587756226400130957312 : ℤ)
  | 45 => (1978597002603254382335313618226505585928724127933621648356278272 : ℤ)
  | 46 => (-1940835158539286084317870336569910622547128293913482238653104128 : ℤ)
  | 47 => (1905161721634758549899291567231862121403385059713990221176504320 : ℤ)
  | 48 => (-1871383487308281262459449247238899636035715770034938298402603008 : ℤ)
  | 49 => (1839347080942855460720375890638980559450616216137870380128796672 : ℤ)
  | 50 => (-1808897552612604499817948698911932149013392580872635398049759232 : ℤ)
  | 51 => (1779919056562063287360173529442494105413620586168402059427053568 : ℤ)
  | 52 => (-1752284848891649001785817636710379044854829771228637619290112000 : ℤ)
  | 53 => (1725906602783283843461092399555497729623596065690005901613727744 : ℤ)
  | 54 => (-1700678797827439292667082188386601669833227265046227652998332416 : ℤ)
  | 55 => (1676533678963087942560455829285669167582666858919161947179974656 : ℤ)
  | 56 => (-1653381984286800913551104089201397542146223067485743888306274304 : ℤ)
  | 57 => (1631171597912002793035256688066307375657987362377752336825057280 : ℤ)
  | 58 => (-1609825913625253197982864339806162442337095378799354651479670784 : ℤ)
  | 59 => (1589304881681627437082892424145107340957645425109627740859006976 : ℤ)
  | 60 => (-1569541889553506345107134738311208429620847020174199962490126336 : ℤ)
  | 61 => (1550506319087260633669904304588850482020953458043658396025421824 : ℤ)
  | 62 => (-1532139552506805698537055408771156196165221889953494888516505600 : ℤ)
  | 63 => (1514418429688559035939893375739350044215914591577145892604100608 : ℤ)
  | 64 => (-1497290804544907854509305155933536875987404893804144004945467392 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment12 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-4609634847963465878594408033315023119997213667926655321820364800 : ℤ)
  | 19 => (4757246776361236336797466809793874132636323855407322088079360000 : ℤ)
  | 20 => (-590420344408523667928129731929334495203707383961898358669312000 : ℤ)
  | 21 => (-5955016442780731852728462001314966229807674174253487030796288000 : ℤ)
  | 22 => (8333644175276041793331021656050961955705635048935047869497344000 : ℤ)
  | 23 => (-6844883831433692374378198927692266669291396277099037275979776000 : ℤ)
  | 24 => (5475912051664687064119124924577776318602973204297340889438617600 : ℤ)
  | 25 => (-4791418017134553573449197145061391604081329902953577950698536960 : ℤ)
  | 26 => (4302502872450386801742079169290877338963796528139418101602058240 : ℤ)
  | 27 => (-3948030311551516273580472728642948575180924516609058831534653440 : ℤ)
  | 28 => (3666906198311187782218037097215488802581184874171093704308162560 : ℤ)
  | 29 => (-3440775409699522295598763148277619202187591962182324838958366720 : ℤ)
  | 30 => (3251323734788393219680923247791265062599174504696571106091335680 : ℤ)
  | 31 => (-3090891772576193040757418466191787776092478012469749165724794880 : ℤ)
  | 32 => (2951859884980602336869467175531093304443339514759779524615864320 : ℤ)
  | 33 => (-2830388900684458101491970826223470048490873173831576219916697600 : ℤ)
  | 34 => (2722678355737972604537973226061779717475354905369926242465218560 : ℤ)
  | 35 => (-2626560690226710003096224190178823434479641149281613462917611520 : ℤ)
  | 36 => (2539906077448004750109680024900044988191152329805105690795048960 : ℤ)
  | 37 => (-2461382974676612181748728259709958873841493027614485751560929280 : ℤ)
  | 38 => (2389696669554670789354892593925583694836588131081582996336148480 : ℤ)
  | 39 => (-2323975603296228254143965759604081092899185280276943910868090880 : ℤ)
  | 40 => (2263384207547759354620253505737893310379390169115135410773688320 : ℤ)
  | 41 => (-2207322878312163631114432978064584460635865227015213427479019520 : ℤ)
  | 42 => (2155227217933375685305791366710457005051615626042051470745927680 : ℤ)
  | 43 => (-2106667718027603638185881578065271486785042063356239078332825600 : ℤ)
  | 44 => (2061249342311202106991823512918905725504774922846940354133884928 : ℤ)
  | 45 => (-2018653904926502857301702581052118148433385448649712970311401472 : ℤ)
  | 46 => (1978597002603254382335313618226505585928724127933621648356278272 : ℤ)
  | 47 => (-1940836081616362103177020217700703012469748923724128669042475008 : ℤ)
  | 48 => (1905161721634758549899291567231862121403385059713990221176504320 : ℤ)
  | 49 => (-1871384391547049607464330763448655446572160468624959291437088768 : ℤ)
  | 50 => (1839347080942855460720375890638980559450616216137870380128796672 : ℤ)
  | 51 => (-1808898439121200916489401165784241767186377579490303038279647232 : ℤ)
  | 52 => (1779919056562063287360173529442494105413620586168402059427053568 : ℤ)
  | 53 => (-1752285718673668127576676660811513009854739581193141719138304000 : ℤ)
  | 54 => (1725906602783283843461092399555497729623596065690005901613727744 : ℤ)
  | 55 => (-1700679651795239888898107412049533199105865987556831678303830016 : ℤ)
  | 56 => (1676533678963087942560455829285669167582666858919161947179974656 : ℤ)
  | 57 => (-1653382823272710271251760449291295184940394443987389948255535104 : ℤ)
  | 58 => (1631171597912002793035256688066307375657987362377752336825057280 : ℤ)
  | 59 => (-1609826738391062397078424829386061819999162155699277896853520384 : ℤ)
  | 60 => (1589304881681627437082892424145107340957645425109627740859006976 : ℤ)
  | 61 => (-1569542700798564573725718826422584866665502866305272007120142336 : ℤ)
  | 62 => (1550506319087260633669904304588850482020953458043658396025421824 : ℤ)
  | 63 => (-1532140350874958240987090543102986975479010182971375313390489600 : ℤ)
  | 64 => (1514418429688559035939893375739350044215914591577145892604100608 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment13 (i : ℕ) : ℤ :=
  match i with
  | 18 => (3687713352207284335852347501449232407068317607533477998729625600 : ℤ)
  | 19 => (-4609635988346072468797912423897776018136910891508354017918976000 : ℤ)
  | 20 => (4757246776361236336797466809793874132636323855407322088079360000 : ℤ)
  | 21 => (-590421430487196610979086294389099160098657120706373307334656000 : ℤ)
  | 22 => (-5955016442780731852728462001314966229807674174253487030796288000 : ℤ)
  | 23 => (8333643136418180717369237118045969667545248344222941396860928000 : ℤ)
  | 24 => (-6844883831433692374378198927692266669291396277099037275979776000 : ℤ)
  | 25 => (5475911054361140431195811768092983721969001967773718675707658240 : ℤ)
  | 26 => (-4791418017134553573449197145061391604081329902953577950698536960 : ℤ)
  | 27 => (4302501912084008562630740574157373357019972374450004118009282560 : ℤ)
  | 28 => (-3948030311551516273580472728642948575180924516609058831534653440 : ℤ)
  | 29 => (3666905271060891551351917074327967716566458105091659513253068800 : ℤ)
  | 30 => (-3440775409699522295598763148277619202187591962182324838958366720 : ℤ)
  | 31 => (3251322837449396867229839354674309172907503437845505759908986880 : ℤ)
  | 32 => (-3090891772576193040757418466191787776092478012469749165724794880 : ℤ)
  | 33 => (2951859014833696782977507036751014865954446359025413128317829120 : ℤ)
  | 34 => (-2830388900684458101491970826223470048490873173831576219916697600 : ℤ)
  | 35 => (2722677510452407209328640519818274948657572982656541743204270080 : ℤ)
  | 36 => (-2626560690226710003096224190178823434479641149281613462917611520 : ℤ)
  | 37 => (2539905255007995176392491445852310618530607756354245096919531520 : ℤ)
  | 38 => (-2461382974676612181748728259709958873841493027614485751560929280 : ℤ)
  | 39 => (2389695868202866589322760132289329693628878033873052161277952000 : ℤ)
  | 40 => (-2323975603296228254143965759604081092899185280276943910868090880 : ℤ)
  | 41 => (2263383425741121110686465738287889406762112025497056547302277120 : ℤ)
  | 42 => (-2207322878312163631114432978064584460635865227015213427479019520 : ℤ)
  | 43 => (2155226454308287167975114942689522959657995113670904673866874880 : ℤ)
  | 44 => (-2106667718027603638185881578065271486785042063356239078332825600 : ℤ)
  | 45 => (2061248595655560001157384342765103547786568199639596819407699968 : ℤ)
  | 46 => (-2018653904926502857301702581052118148433385448649712970311401472 : ℤ)
  | 47 => (1978596271833902534071819962331294943906649462666859890964692992 : ℤ)
  | 48 => (-1940836081616362103177020217700703012469748923724128669042475008 : ℤ)
  | 49 => (1905161005779066943437093700232472104728699673330223601690869760 : ℤ)
  | 50 => (-1871384391547049607464330763448655446572160468624959291437088768 : ℤ)
  | 51 => (1839346379123549964188809354365068778397003092232216831613468672 : ℤ)
  | 52 => (-1808898439121200916489401165784241767186377579490303038279647232 : ℤ)
  | 53 => (1779918367984631479442410135362429716455358653279836313713901568 : ℤ)
  | 54 => (-1752285718673668127576676660811513009854739581193141719138304000 : ℤ)
  | 55 => (1725905926725441704778197430822343602282757077035777714913542144 : ℤ)
  | 56 => (-1700679651795239888898107412049533199105865987556831678303830016 : ℤ)
  | 57 => (1676533014765909701047436210881166867037281185855358816386809856 : ℤ)
  | 58 => (-1653382823272710271251760449291295184940394443987389948255535104 : ℤ)
  | 59 => (1631170944972403843751271300482220368342184497331979767570759680 : ℤ)
  | 60 => (-1609826738391062397078424829386061819999162155699277896853520384 : ℤ)
  | 61 => (1589304239445956339426513354390267661630626213589195705526910976 : ℤ)
  | 62 => (-1569542700798564573725718826422584866665502866305272007120142336 : ℤ)
  | 63 => (1550505687045806537563626489909484448397537726071169726333517824 : ℤ)
  | 64 => (-1532140350874958240987090543102986975479010182971375313390489600 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment14 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-3226744431587179668022869103006607947269372808334715348477542400 : ℤ)
  | 19 => (3687712439901199063689543988983030088556559828668119041850736640 : ℤ)
  | 20 => (-4609635988346072468797912423897776018136910891508354017918976000 : ℤ)
  | 21 => (4757245907498297982356701559826062400720364066011742129147084800 : ℤ)
  | 22 => (-590421430487196610979086294389099160098657120706373307334656000 : ℤ)
  | 23 => (-5955017273867020713497889631718960060335983538023172208905420800 : ℤ)
  | 24 => (8333643136418180717369237118045969667545248344222941396860928000 : ℤ)
  | 25 => (-6844884629276529680716849452880100746598573266317935046964543488 : ℤ)
  | 26 => (5475911054361140431195811768092983721969001967773718675707658240 : ℤ)
  | 27 => (-4791418785427656164738268021168194789636389225905109137572757504 : ℤ)
  | 28 => (4302501912084008562630740574157373357019972374450004118009282560 : ℤ)
  | 29 => (-3948031053351753258273368746952965443992705931872606184378728448 : ℤ)
  | 30 => (3666905271060891551351917074327967716566458105091659513253068800 : ℤ)
  | 31 => (-3440776127570719377559630262771183913940928815663177115904245760 : ℤ)
  | 32 => (3251322837449396867229839354674309172907503437845505759908986880 : ℤ)
  | 33 => (-3090892468693717483870986577215850526883592537057242282763223040 : ℤ)
  | 34 => (2951859014833696782977507036751014865954446359025413128317829120 : ℤ)
  | 35 => (-2830389576912910417659436991218273863545098712002283819325456384 : ℤ)
  | 36 => (2722677510452407209328640519818274948657572982656541743204270080 : ℤ)
  | 37 => (-2626561348178717662069975053417010930208076808042301938018025472 : ℤ)
  | 38 => (2539905255007995176392491445852310618530607756354245096919531520 : ℤ)
  | 39 => (-2461383615758055541774434229018962074807661105381310419607486464 : ℤ)
  | 40 => (2389695868202866589322760132289329693628878033873052161277952000 : ℤ)
  | 41 => (-2323976228741538849290995973564084215793007795171407001645219840 : ℤ)
  | 42 => (2263383425741121110686465738287889406762112025497056547302277120 : ℤ)
  | 43 => (-2207323489212234444978974117281331696950761636912130864982261760 : ℤ)
  | 44 => (2155226454308287167975114942689522959657995113670904673866874880 : ℤ)
  | 45 => (-2106668315352117322853432914188313228959607441922113906113773568 : ℤ)
  | 46 => (2061248595655560001157384342765103547786568199639596819407699968 : ℤ)
  | 47 => (-2018654489541984335912497505768286662051045180863122376224669696 : ℤ)
  | 48 => (1978596271833902534071819962331294943906649462666859890964692992 : ℤ)
  | 49 => (-1940836654300915388346778511300215025809497232831141964630982656 : ℤ)
  | 50 => (1905161005779066943437093700232472104728699673330223601690869760 : ℤ)
  | 51 => (-1871384953002494004689583992467784871415050967749482130249351168 : ℤ)
  | 52 => (1839346379123549964188809354365068778397003092232216831613468672 : ℤ)
  | 53 => (-1808898989983146362823611881048293278352987125801155634850168832 : ℤ)
  | 54 => (1779918367984631479442410135362429716455358653279836313713901568 : ℤ)
  | 55 => (-1752286259519941838522992635798036311727410772116524268498452480 : ℤ)
  | 56 => (1725905926725441704778197430822343602282757077035777714913542144 : ℤ)
  | 57 => (-1700680183152982482108523106773135039542174526007874182938361856 : ℤ)
  | 58 => (1676533014765909701047436210881166867037281185855358816386809856 : ℤ)
  | 59 => (-1653383345624389430678948759358564790793036736024008003658973184 : ℤ)
  | 60 => (1631170944972403843751271300482220368342184497331979767570759680 : ℤ)
  | 61 => (-1609827252179599275203528085189933563460777524915623525119197184 : ℤ)
  | 62 => (1589304239445956339426513354390267661630626213589195705526910976 : ℤ)
  | 63 => (-1569543206431727850610741078166077693564235451883262942873665536 : ℤ)
  | 64 => (1550505687045806537563626489909484448397537726071169726333517824 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment15 (i : ℕ) : ℤ :=
  match i with
  | 18 => (2897488823511272502127062593111820093562503463835376796009758720 : ℤ)
  | 19 => (-3226745168449787003231287324613925204528869475879812967495106560 : ℤ)
  | 20 => (3687712439901199063689543988983030088556559828668119041850736640 : ℤ)
  | 21 => (-4609636690119984216615453587333316263145955336789399369364275200 : ℤ)
  | 22 => (4757245907498297982356701559826062400720364066011742129147084800 : ℤ)
  | 23 => (-590422101749199152369777842023094177063830068366503643499724800 : ℤ)
  | 24 => (-5955017273867020713497889631718960060335983538023172208905420800 : ℤ)
  | 25 => (8333642492006658277634173232317334451258682314469216274142461952 : ℤ)
  | 26 => (-6844884629276529680716849452880100746598573266317935046964543488 : ℤ)
  | 27 => (5475910433816711415154639137391334995174530976159020409386172416 : ℤ)
  | 28 => (-4791418785427656164738268021168194789636389225905109137572757504 : ℤ)
  | 29 => (4302501312937663305763401482445436655287379692890985102250606592 : ℤ)
  | 30 => (-3948031053351753258273368746952965443992705931872606184378728448 : ℤ)
  | 31 => (3666904691241847754383524404929319295534916800357124981873704960 : ℤ)
  | 32 => (-3440776127570719377559630262771183913940928815663177115904245760 : ℤ)
  | 33 => (3251322275200627124715034341924104643422372475678684396147179520 : ℤ)
  | 34 => (-3090892468693717483870986577215850526883592537057242282763223040 : ℤ)
  | 35 => (2951858468649177604534553595793673323026033424349072374949216256 : ℤ)
  | 36 => (-2830389576912910417659436991218273863545098712002283819325456384 : ℤ)
  | 37 => (2722676979029631792465226361048969663646144181349831821007781888 : ℤ)
  | 38 => (-2626561348178717662069975053417010930208076808042301938018025472 : ℤ)
  | 39 => (2539904737211444770217882778333500340827164308927194403497312256 : ℤ)
  | 40 => (-2461383615758055541774434229018962074807661105381310419607486464 : ℤ)
  | 41 => (2389695363035500339396312651783173325137713694919831972573347840 : ℤ)
  | 42 => (-2323976228741538849290995973564084215793007795171407001645219840 : ℤ)
  | 43 => (2263382932321833145642028664305132023584695694426469386241966080 : ℤ)
  | 44 => (-2207323489212234444978974117281331696950761636912130864982261760 : ℤ)
  | 45 => (2155225971853872268820554248128604629440076923290775005274570752 : ℤ)
  | 46 => (-2106668315352117322853432914188313228959607441922113906113773568 : ℤ)
  | 47 => (2061248123466132653048665365109736671403073800544150760785444864 : ℤ)
  | 48 => (-2018654489541984335912497505768286662051045180863122376224669696 : ℤ)
  | 49 => (1978595809280994111434707494423996779286083520695810690681667584 : ℤ)
  | 50 => (-1940836654300915388346778511300215025809497232831141964630982656 : ℤ)
  | 51 => (1905160552295823391832081476793944492355595808652724385727119360 : ℤ)
  | 52 => (-1871384953002494004689583992467784871415050967749482130249351168 : ℤ)
  | 53 => (1839345934196594026765023776651796403993203074058066657460355072 : ℤ)
  | 54 => (-1808898989983146362823611881048293278352987125801155634850168832 : ℤ)
  | 55 => (1779917931147256559062693386334853203404354999072488869999935488 : ℤ)
  | 56 => (-1752286259519941838522992635798036311727410772116524268498452480 : ℤ)
  | 57 => (1725905497551880379492861677391742115776507872902243384247189504 : ℤ)
  | 58 => (-1700680183152982482108523106773135039542174526007874182938361856 : ℤ)
  | 59 => (1676532592866476533817784114288372185387070103825782694714802176 : ℤ)
  | 60 => (-1653383345624389430678948759358564790793036736024008003658973184 : ℤ)
  | 61 => (1631170529989354826804072516948323960161649006811085221663866880 : ℤ)
  | 62 => (-1609827252179599275203528085189933563460777524915623525119197184 : ℤ)
  | 63 => (1589303831049939846557841535674369609135496048314664565110603776 : ℤ)
  | 64 => (-1569543206431727850610741078166077693564235451883262942873665536 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment16 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-2658771823552136205452113933866009541015961949623599808517242880 : ℤ)
  | 19 => (2897488223104703562327610708839191217276987660650482439773224960 : ℤ)
  | 20 => (-3226745168449787003231287324613925204528869475879812967495106560 : ℤ)
  | 21 => (3687711868085419121023399337294812111141782873253933940673085440 : ℤ)
  | 22 => (-4609636690119984216615453587333316263145955336789399369364275200 : ℤ)
  | 23 => (4757245360544073689371693632124288683193186108659043336716288000 : ℤ)
  | 24 => (-590422101749199152369777842023094177063830068366503643499724800 : ℤ)
  | 25 => (-5955017798943076034763497242312662829162074377081763049638985728 : ℤ)
  | 26 => (8333642492006658277634173232317334451258682314469216274142461952 : ℤ)
  | 27 => (-6844885134905323693787434559377740449912586666892874375078346752 : ℤ)
  | 28 => (5475910433816711415154639137391334995174530976159020409386172416 : ℤ)
  | 29 => (-4791419273620974522185729503303846916974057336805050557820567552 : ℤ)
  | 30 => (4302501312937663305763401482445436655287379692890985102250606592 : ℤ)
  | 31 => (-3948031525796900055803170181277790083351739587582226913650802688 : ℤ)
  | 32 => (3666904691241847754383524404929319295534916800357124981873704960 : ℤ)
  | 33 => (-3440776585699346575164286199086165382410294784836142671562014720 : ℤ)
  | 34 => (3251322275200627124715034341924104643422372475678684396147179520 : ℤ)
  | 35 => (-3090892913732955332972652343921832524825262335682408822545055744 : ℤ)
  | 36 => (2951858468649177604534553595793673323026033424349072374949216256 : ℤ)
  | 37 => (-2830390009924060757325922602067337429109966624178121533707780096 : ℤ)
  | 38 => (2722676979029631792465226361048969663646144181349831821007781888 : ℤ)
  | 39 => (-2626561770087017993027063597321226712040512209649528428954648576 : ℤ)
  | 40 => (2539904737211444770217882778333500340827164308927194403497312256 : ℤ)
  | 41 => (-2461384027375909523195984027949904300985646863046897240033460224 : ℤ)
  | 42 => (2389695363035500339396312651783173325137713694919831972573347840 : ℤ)
  | 43 => (-2323976630786884598586463219031516157641272953821515058805473280 : ℤ)
  | 44 => (2263382932321833145642028664305132023584695694426469386241966080 : ℤ)
  | 45 => (-2207323882323239177623430979516154040091287569814458743094509568 : ℤ)
  | 46 => (2155225971853872268820554248128604629440076923290775005274570752 : ℤ)
  | 47 => (-2106668700099058125016092821907501054160973248592477361287462912 : ℤ)
  | 48 => (2061248123466132653048665365109736671403073800544150760785444864 : ℤ)
  | 49 => (-2018654866436946754357552109248307388778913726172866169047875584 : ℤ)
  | 50 => (1978595809280994111434707494423996779286083520695810690681667584 : ℤ)
  | 51 => (-1940837023805780504469381063731607895150544826272067251712557056 : ℤ)
  | 52 => (1905160552295823391832081476793944492355595808652724385727119360 : ℤ)
  | 53 => (-1871385315535569212960816685419340139447776908483974864744480768 : ℤ)
  | 54 => (1839345934196594026765023776651796403993203074058066657460355072 : ℤ)
  | 55 => (-1808899345924711112762640343218911177876027140340475774172659712 : ℤ)
  | 56 => (1779917931147256559062693386334853203404354999072488869999935488 : ℤ)
  | 57 => (-1752286609216917733199932879334081967399169382891996686078443520 : ℤ)
  | 58 => (1725905497551880379492861677391742115776507872902243384247189504 : ℤ)
  | 59 => (-1700680526922890988740091481774671446812716889143084356152590336 : ℤ)
  | 60 => (1676532592866476533817784114288372185387070103825782694714802176 : ℤ)
  | 61 => (-1653383683758725666709999620015813715977176765337329485509033984 : ℤ)
  | 62 => (1631170529989354826804072516948323960161649006811085221663866880 : ℤ)
  | 63 => (-1609827584946723824948371789328813458086439141065241491384336384 : ℤ)
  | 64 => (1589303831049939846557841535674369609135496048314664565110603776 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment17 (i : ℕ) : ℤ :=
  match i with
  | 18 => (2469450443997604965167365767676807465304295768260988798511349760 : ℤ)
  | 19 => (-2658772316743246406001663695947097546536207073668334458282967040 : ℤ)
  | 20 => (2897488223104703562327610708839191217276987660650482439773224960 : ℤ)
  | 21 => (-3226745638155606241849906145643532828833864832112893586319605760 : ℤ)
  | 22 => (3687711868085419121023399337294812111141782873253933940673085440 : ℤ)
  | 23 => (-4609637139403811314424567242231201816828994373186259091718144000 : ℤ)
  | 24 => (4757245360544073689371693632124288683193186108659043336716288000 : ℤ)
  | 25 => (-590422533061673166266526950725064308599547543307488976959438848 : ℤ)
  | 26 => (-5955017798943076034763497242312662829162074377081763049638985728 : ℤ)
  | 27 => (8333642076668720338326192609122844694965028449711230397477552128 : ℤ)
  | 28 => (-6844885134905323693787434559377740449912586666892874375078346752 : ℤ)
  | 29 => (5475910032800771335822795777065620747718589313634068528468328448 : ℤ)
  | 30 => (-4791419273620974522185729503303846916974057336805050557820567552 : ℤ)
  | 31 => (4302500924857721293506778875678616415813887761415225217491402752 : ℤ)
  | 32 => (-3948031525796900055803170181277790083351739587582226913650802688 : ℤ)
  | 33 => (3666904314921903984922557028670584517863651897107903275440537600 : ℤ)
  | 34 => (-3440776585699346575164286199086165382410294784836142671562014720 : ℤ)
  | 35 => (3251321909632681748667237462129905145113143712522297595612102656 : ℤ)
  | 36 => (-3090892913732955332972652343921832524825262335682408822545055744 : ℤ)
  | 37 => (2951858112961446968379940415453371108454891925061777109563736064 : ℤ)
  | 38 => (-2830390009924060757325922602067337429109966624178121533707780096 : ℤ)
  | 39 => (2722676632462099377750475057127649557140929387172467203452698624 : ℤ)
  | 40 => (-2626561770087017993027063597321226712040512209649528428954648576 : ℤ)
  | 41 => (2539904399096778999764466872068797797895247436559033801004548096 : ℤ)
  | 42 => (-2461384027375909523195984027949904300985646863046897240033460224 : ℤ)
  | 43 => (2389695032783966331046464557292068515762353028885814639905996800 : ℤ)
  | 44 => (-2323976630786884598586463219031516157641272953821515058805473280 : ℤ)
  | 45 => (2263382609409222115255510527469385098862120820970985772078333952 : ℤ)
  | 46 => (-2207323882323239177623430979516154040091287569814458743094509568 : ℤ)
  | 47 => (2155225655811742324186940752502128915881812153525833595667611648 : ℤ)
  | 48 => (-2106668700099058125016092821907501054160973248592477361287462912 : ℤ)
  | 49 => (2061247813873842095040227655108291074448038924039718359537811456 : ℤ)
  | 50 => (-2018654866436946754357552109248307388778913726172866169047875584 : ℤ)
  | 51 => (1978595505759140623191141112069638350898794426083622062007517184 : ℤ)
  | 52 => (-1940837023805780504469381063731607895150544826272067251712557056 : ℤ)
  | 53 => (1905160254500797327894997479012309807900142357335105353820405760 : ℤ)
  | 54 => (-1871385315535569212960816685419340139447776908483974864744480768 : ℤ)
  | 55 => (1839345641816022982172250397011645986527848776400767971588308992 : ℤ)
  | 56 => (-1808899345924711112762640343218911177876027140340475774172659712 : ℤ)
  | 57 => (1779917643896169217006635329144529986245410425935493669844942848 : ℤ)
  | 58 => (-1752286609216917733199932879334081967399169382891996686078443520 : ℤ)
  | 59 => (1725905215169455534759787655069051495518562360326892170535501824 : ℤ)
  | 60 => (-1700680526922890988740091481774671446812716889143084356152590336 : ℤ)
  | 61 => (1676532315113271768506563764462774853985812222604125763195109376 : ℤ)
  | 62 => (-1653383683758725666709999620015813715977176765337329485509033984 : ℤ)
  | 63 => (1631170256644931089513665188548529761004855536402470463660359680 : ℤ)
  | 64 => (-1609827584946723824948371789328813458086439141065241491384336384 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment18 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-2317165152312000707748858726049660546141233546431199589108285440 : ℤ)
  | 19 => (2469450035839444799195324585264872564184092906982587709050060800 : ℤ)
  | 20 => (-2658772316743246406001663695947097546536207073668334458282967040 : ℤ)
  | 21 => (2897487834382646261401857201780205597162508745147243306952949760 : ℤ)
  | 22 => (-3226745638155606241849906145643532828833864832112893586319605760 : ℤ)
  | 23 => (3687711496264320833181374243586217170162716084511705204931952640 : ℤ)
  | 24 => (-4609637139403811314424567242231201816828994373186259091718144000 : ℤ)
  | 25 => (4757245003595819333043349542164037539853281991466503750404800512 : ℤ)
  | 26 => (-590422533061673166266526950725064308599547543307488976959438848 : ℤ)
  | 27 => (-5955018142671024674190791551163275041267167230674578947568566272 : ℤ)
  | 28 => (8333642076668720338326192609122844694965028449711230397477552128 : ℤ)
  | 29 => (-6844885466780584449096546305854193620220952180706627655837941760 : ℤ)
  | 30 => (5475910032800771335822795777065620747718589313634068528468328448 : ℤ)
  | 31 => (-4791419594790581704742934419248801597917636866302231152104046592 : ℤ)
  | 32 => (4302500924857721293506778875678616415813887761415225217491402752 : ℤ)
  | 33 => (-3948031837234094899495005251285018864872786404064341429319630848 : ℤ)
  | 34 => (3666904314921903984922557028670584517863651897107903275440537600 : ℤ)
  | 35 => (-3440776888238335851893497409950330484459311692275911058211733504 : ℤ)
  | 36 => (3251321909632681748667237462129905145113143712522297595612102656 : ℤ)
  | 37 => (-3090893208095215169790263251789668840332413921299480766312349696 : ℤ)
  | 38 => (2951858112961446968379940415453371108454891925061777109563736064 : ℤ)
  | 39 => (-2830390296738570341917440922553947172424627143497319837891297280 : ℤ)
  | 40 => (2722676632462099377750475057127649557140929387172467203452698624 : ℤ)
  | 41 => (-2626562049906051734091959519747187437225546862643868237914177536 : ℤ)
  | 42 => (2539904399096778999764466872068797797895247436559033801004548096 : ℤ)
  | 43 => (-2461384300687523874933789347528749660468703965971601239482302464 : ℤ)
  | 44 => (2389695032783966331046464557292068515762353028885814639905996800 : ℤ)
  | 45 => (-2323976898024907520285650642619720509135817676681225636044341248 : ℤ)
  | 46 => (2263382609409222115255510527469385098862120820970985772078333952 : ℤ)
  | 47 => (-2207324143875346718009869734517375320277437724102686116562337792 : ℤ)
  | 48 => (2155225655811742324186940752502128915881812153525833595667611648 : ℤ)
  | 49 => (-2106668956313367552333420581908697410261691767078904176113090560 : ℤ)
  | 50 => (2061247813873842095040227655108291074448038924039718359537811456 : ℤ)
  | 51 => (-2018655117627446192903951873955362639858049528610539516916137984 : ℤ)
  | 52 => (1978595505759140623191141112069638350898794426083622062007517184 : ℤ)
  | 53 => (-1940837270256836557382829889481926254699885613569407140187078656 : ℤ)
  | 54 => (1905160254500797327894997479012309807900142357335105353820405760 : ℤ)
  | 55 => (-1871385557505696974003111896156016347005311499648635846155829248 : ℤ)
  | 56 => (1839345641816022982172250397011645986527848776400767971588308992 : ℤ)
  | 57 => (-1808899583649748913084895287100557978283429545695230422576791552 : ℤ)
  | 58 => (1779917643896169217006635329144529986245410425935493669844942848 : ℤ)
  | 59 => (-1752286842912717604703166552980446618647124289850908035357081600 : ℤ)
  | 60 => (1725905215169455534759787655069051495518562360326892170535501824 : ℤ)
  | 61 => (-1700680756787612173825239357492407169351688928774800437410267136 : ℤ)
  | 62 => (1676532315113271768506563764462774853985812222604125763195109376 : ℤ)
  | 63 => (-1653383909974800483777922926277712363555212740847907216270557184 : ℤ)
  | 64 => (1631170256644931089513665188548529761004855536402470463660359680 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment19 (i : ℕ) : ℤ :=
  match i with
  | 18 => (2189579184385334161406219270553295463424960287234577440660520960 : ℤ)
  | 19 => (-2317165492443800846058893044726272963741402597496533830326026240 : ℤ)
  | 20 => (2469450035839444799195324585264872564184092906982587709050060800 : ℤ)
  | 21 => (-2658772640678294156773124951829585563298272836587700402299863040 : ℤ)
  | 22 => (2897487834382646261401857201780205597162508745147243306952949760 : ℤ)
  | 23 => (-3226745948006521481718260390400695279649753822731417532770549760 : ℤ)
  | 24 => (3687711496264320833181374243586217170162716084511705204931952640 : ℤ)
  | 25 => (-4609637436860689944698187317198077769612247804180042080311050240 : ℤ)
  | 26 => (4757245003595819333043349542164037539853281991466503750404800512 : ℤ)
  | 27 => (-590422819501630365789272208100574485353791587968168891900755968 : ℤ)
  | 28 => (-5955018142671024674190791551163275041267167230674578947568566272 : ℤ)
  | 29 => (8333641800106003042235266153725800386374723854866435996844556288 : ℤ)
  | 30 => (-6844885466780584449096546305854193620220952180706627655837941760 : ℤ)
  | 31 => (5475909765159432017025125013778158513598939705719751366565429248 : ℤ)
  | 32 => (-4791419594790581704742934419248801597917636866302231152104046592 : ℤ)
  | 33 => (4302500665326725590430249650672592431213015414346796454434045952 : ℤ)
  | 34 => (-3948031837234094899495005251285018864872786404064341429319630848 : ℤ)
  | 35 => (3666904062806079587648214352950446932822804474241429619899105280 : ℤ)
  | 36 => (-3440776888238335851893497409950330484459311692275911058211733504 : ℤ)
  | 37 => (3251321664330798551319228372240041548857184057841404309139357696 : ℤ)
  | 38 => (-3090893208095215169790263251789668840332413921299480766312349696 : ℤ)
  | 39 => (2951857873949355647887008481714529655692674825629111856077471744 : ℤ)
  | 40 => (-2830390296738570341917440922553947172424627143497319837891297280 : ℤ)
  | 41 => (2722676399279571260196395121772682286153400509677184029319757824 : ℤ)
  | 42 => (-2626562049906051734091959519747187437225546862643868237914177536 : ℤ)
  | 43 => (2539904171337100373316295772419759998326033184121780468130512896 : ℤ)
  | 44 => (-2461384300687523874933789347528749660468703965971601239482302464 : ℤ)
  | 45 => (2389694810085613896297141704301898222850232426502722492206940160 : ℤ)
  | 46 => (-2323976898024907520285650642619720509135817676681225636044341248 : ℤ)
  | 47 => (2263382391449132498266811564968367365373662359064129627521810432 : ℤ)
  | 48 => (-2207324143875346718009869734517375320277437724102686116562337792 : ℤ)
  | 49 => (2155225442299817801422500952501131952464546721453811249979588608 : ℤ)
  | 50 => (-2106668956313367552333420581908697410261691767078904176113090560 : ℤ)
  | 51 => (2061247604548425896251561184519078365215425755341657236314259456 : ℤ)
  | 52 => (-2018655117627446192903951873955362639858049528610539516916137984 : ℤ)
  | 53 => (1978595300383260579096600423944373051274343770002505488278749184 : ℤ)
  | 54 => (-1940837270256836557382829889481926254699885613569407140187078656 : ℤ)
  | 55 => (1905160052859024193693084803398412968268863531364554535977615360 : ℤ)
  | 56 => (-1871385557505696974003111896156016347005311499648635846155829248 : ℤ)
  | 57 => (1839345443711824815237037943776940319521680105271805764584865792 : ℤ)
  | 58 => (-1808899583649748913084895287100557978283429545695230422576791552 : ℤ)
  | 59 => (1779917449149669324087273934439226110205448003469734212112744448 : ℤ)
  | 60 => (-1752286842912717604703166552980446618647124289850908035357081600 : ℤ)
  | 61 => (1725905023615521213855497758637605060069418993967128769487437824 : ℤ)
  | 62 => (-1700680756787612173825239357492407169351688928774800437410267136 : ℤ)
  | 63 => (1676532126599876087616627675911192647670782243011977654227173376 : ℤ)
  | 64 => (-1653383909974800483777922926277712363555212740847907216270557184 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
namespace InternalCatalan

def fixedClearedMoment2 (i : ℕ) : ℤ :=
  match i with
  | 18 => (3666950415600667683018821356153051320217702973227923950429798400 : ℤ)
  | 19 => (-3440746079136346569194949484819342182607084594321155025797120000 : ℤ)
  | 20 => (3251365978813524233705918910505601362827547571581551686713344000 : ℤ)
  | 21 => (-3090863637767426576926615571284107335449944801441119188549632000 : ℤ)
  | 22 => (2951900399813638782570980673040750226813892662130596300980224000 : ℤ)
  | 23 => (-2830361825617158948778953637291589937308965566988035947495424000 : ℤ)
  | 24 => (2722717338741746177369582212747437988090289654194537429047705600 : ℤ)
  | 25 => (-2626534562965963179244839464126565110683712885433311793009131520 : ℤ)
  | 26 => (2539943690945007595502572461449865634802276534045956045359022080 : ℤ)
  | 27 => (-2461357701772233574069655153149244147368928750225315276815073280 : ℤ)
  | 28 => (2389733048987178316434423431350184726429696980016097276324741120 : ℤ)
  | 29 => (-2323951105760669935890326941757425915963004282814768550426705920 : ℤ)
  | 30 => (2263419467340778617404193564577311527796181063269779898661601280 : ℤ)
  | 31 => (-2207299088660652580649622924763964227638490767411104568972410880 : ℤ)
  | 32 => (2155261455805946610492808860209814699364966190712449603752427520 : ℤ)
  | 33 => (-2106644578055920996562656881094187314976289447788456578960588800 : ℤ)
  | 34 => (2061282642511067910116684423746685072414588968085625828852891648 : ℤ)
  | 35 => (-2018631364013068864789382667599521698349634012491667112462385152 : ℤ)
  | 36 => (1978629438376836724647524845674158079021831233295080860525002752 : ℤ)
  | 37 => (-1940814095404687108270549560843042866888273522121503672083939328 : ℤ)
  | 38 => (1905193357142742123510114054256289533425320423746707570735185920 : ℤ)
  | 39 => (-1871362920909165312016140272648283402077471131052703437027278848 : ℤ)
  | 40 => (1839377972766488493537016566448689974869425850260275147143380992 : ℤ)
  | 41 => (-1808877449332029451013062893577077570301057125655712705756004352 : ℤ)
  | 42 => (1779949254902371836038016862657683608590416612981570962035048448 : ℤ)
  | 43 => (-1752265178746055220679112862714634932690612082455054653744742400 : ℤ)
  | 44 => (1725936152426509710979943181790212692859613114621069758964957184 : ℤ)
  | 45 => (-1700659533938969363163176443702558382905696095548092381930192896 : ℤ)
  | 46 => (1676562620065811940948886678111337070361426260133141874785386496 : ℤ)
  | 47 => (-1653363102450333068899201042977921362655954016045116556226330624 : ℤ)
  | 48 => (1631199966645526112765889255106818178956916217759294280355020800 : ℤ)
  | 49 => (-1609807391950147186236596457182434117083143053148340611478749184 : ℤ)
  | 50 => (1589332710765302517502198396339813332591265594112453382167986176 : ℤ)
  | 51 => (-1569523708164871957677553326652062237400323275983066114525249536 : ℤ)
  | 52 => (1550533638233325982188357561610322262318538684461747263344410624 : ℤ)
  | 53 => (-1532121693294626796891741914494691456412244412297215622941593600 : ℤ)
  | 54 => (1514445265975806170889836352677709967647522964172618514132779008 : ℤ)
  | 55 => (-1497273250951966521335892594615391164783270257076010662798088192 : ℤ)
  | 56 => (1480765853616684864625242590289586793697675031041145624536031232 : ℤ)
  | 57 => (-1464700328865897713431039694823822572241597651604317685248743808 : ℤ)
  | 58 => (1449238699886447643438556721022730469480382160686805516879644160 : ℤ)
  | 59 => (-1434165510495438615050220974369547681393926504626730038691770304 : ℤ)
  | 60 => (1419643849225443195764989362690379330995497708700097841183416576 : ℤ)
  | 61 => (-1405464682653554613359786592702652126662504056012407924347618896 : ℤ)
  | 62 => (1391791592181849804639058041613984229386419469457845645120097344 : ℤ)
  | 63 => (-1378421258455259047288828492584681240300898159188056412629859320 : ℤ)
  | 64 => (1365517318274202057103586412006382555968808038835069681782283936 : ℤ)
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment20 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-2081538861768428247664686342475430811857105333642946358605250560 : ℤ)
  | 19 => (2189578899113501787339738874243878597050624954083006786735964160 : ℤ)
  | 20 => (-2317165492443800846058893044726272963741402597496533830326026240 : ℤ)
  | 21 => (2469449764151985395322486112589237453351392589695377562455244800 : ℤ)
  | 22 => (-2658772640678294156773124951829585563298272836587700402299863040 : ℤ)
  | 23 => (2897487574507685092480011706177424186800795398176868384123125760 : ℤ)
  | 24 => (-3226745948006521481718260390400695279649753822731417532770549760 : ℤ)
  | 25 => (3687711246784358111016402567807547016215471271420145279015321600 : ℤ)
  | 26 => (-4609637436860689944698187317198077769612247804180042080311050240 : ℤ)
  | 27 => (4757244763355855230217821261784577391607786986267223821744340992 : ℤ)
  | 28 => (-590422819501630365789272208100574485353791587968168891900755968 : ℤ)
  | 29 => (-5955018374626852083815439546012408977504196890866987154551078912 : ℤ)
  | 30 => (8333641800106003042235266153725800386374723854866435996844556288 : ℤ)
  | 31 => (-6844885691253965813249431462159807106901948626054119469046824960 : ℤ)
  | 32 => (5475909765159432017025125013778158513598939705719751366565429248 : ℤ)
  | 33 => (-4791419812461739391194216995060305585002239479972526243700539392 : ℤ)
  | 34 => (4302500665326725590430249650672592431213015414346796454434045952 : ℤ)
  | 35 => (-3948032048686076652047679753501908452326400371629770946870509568 : ℤ)
  | 36 => (3666904062806079587648214352950446932822804474241429619899105280 : ℤ)
  | 37 => (-3440777093975399178701505033728925758738503660717950588801777664 : ℤ)
  | 38 => (3251321664330798551319228372240041548857184057841404309139357696 : ℤ)
  | 39 => (-3090893408556969180526270680086761671681370198243006462784700416 : ℤ)
  | 40 => (2951857873949355647887008481714529655692674825629111856077471744 : ℤ)
  | 41 => (-2830390492311013279220862803819403593252877169783686371035054080 : ℤ)
  | 42 => (2722676399279571260196395121772682286153400509677184029319757824 : ℤ)
  | 43 => (-2626562240930298324016232054936703011057791074365435549356916736 : ℤ)
  | 44 => (2539904171337100373316295772419759998326033184121780468130512896 : ℤ)
  | 45 => (-2461384487466787207304189159714053777104676084099355944004091904 : ℤ)
  | 46 => (2389694810085613896297141704301898222850232426502722492206940160 : ℤ)
  | 47 => (-2323977080830143973243914288588316027545492515699879176640135168 : ℤ)
  | 48 => (2263382391449132498266811564968367365373662359064129627521810432 : ℤ)
  | 49 => (-2207324322949864059683270857098856644433853892937285503268421632 : ℤ)
  | 50 => (2155225442299817801422500952501131952464546721453811249979588608 : ℤ)
  | 51 => (-2106669131876619848091656976596424198650335069857923182687682560 : ℤ)
  | 52 => (2061247604548425896251561184519078365215425755341657236314259456 : ℤ)
  | 53 => (-2018655289878184294402598902705585149220492014355992127140265984 : ℤ)
  | 54 => (1978595300383260579096600423944373051274343770002505488278749184 : ℤ)
  | 55 => (-1940837439375743057036046972254871991164829145028578793861677056 : ℤ)
  | 56 => (1905160052859024193693084803398412968268863531364554535977615360 : ℤ)
  | 57 => (-1871385723657605114013290082739963035462098127047120277836136448 : ℤ)
  | 58 => (1839345443711824815237037943776940319521680105271805764584865792 : ℤ)
  | 59 => (-1808899746985523016823714521369522519478236738731028677448957952 : ℤ)
  | 60 => (1779917449149669324087273934439226110205448003469734212112744448 : ℤ)
  | 61 => (-1752287003570856067397087111277788790314147758410709597526425600 : ℤ)
  | 62 => (1725905023615521213855497758637605060069418993967128769487437824 : ℤ)
  | 63 => (-1700680914895621454571637367245347084325585040690795625576923136 : ℤ)
  | 64 => (1676532126599876087616627675911192647670782243011977654227173376 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment21 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1987907257101630876090125158785154416610805766332942106482442240 : ℤ)
  | 19 => (-2081539102466536813283279176861501292860450770989584097854095360 : ℤ)
  | 20 => (2189578899113501787339738874243878597050624954083006786735964160 : ℤ)
  | 21 => (-2317165721680094718076600506046340088506493490207617391515402240 : ℤ)
  | 22 => (2469449764151985395322486112589237453351392589695377562455244800 : ℤ)
  | 23 => (-2658772859947792643050932088744432378290968473093954243437527040 : ℤ)
  | 24 => (2897487574507685092480011706177424186800795398176868384123125760 : ℤ)
  | 25 => (-3226746158505240028544955241838948222042741633777421220262707200 : ℤ)
  | 26 => (3687711246784358111016402567807547016215471271420145279015321600 : ℤ)
  | 27 => (-4609637639563159656457226803768247269694384214816934520118312960 : ℤ)
  | 28 => (4757244763355855230217821261784577391607786986267223821744340992 : ℤ)
  | 29 => (-590423015214359742660068953754531244053785363755513316542251008 : ℤ)
  | 30 => (-5955018374626852083815439546012408977504196890866987154551078912 : ℤ)
  | 31 => (8333641610706587516231269303092939006987633104104489779449561088 : ℤ)
  | 32 => (-6844885691253965813249431462159807106901948626054119469046824960 : ℤ)
  | 33 => (5475909581499392719081855340437202024496306250435439883030888448 : ℤ)
  | 34 => (-4791419812461739391194216995060305585002239479972526243700539392 : ℤ)
  | 35 => (4302500486914115986713930539427091841799028629213465299000492032 : ℤ)
  | 36 => (-3948032048686076652047679753501908452326400371629770946870509568 : ℤ)
  | 37 => (3666903889215432405653957920387257170149736250868458765963755520 : ℤ)
  | 38 => (-3440777093975399178701505033728925758738503660717950588801777664 : ℤ)
  | 39 => (3251321495191193604760722104614369472406502199170304502740811776 : ℤ)
  | 40 => (-3090893408556969180526270680086761671681370198243006462784700416 : ℤ)
  | 41 => (2951857708935106919537246269396800800618838865949990093737426944 : ℤ)
  | 42 => (-2830390492311013279220862803819403593252877169783686371035054080 : ℤ)
  | 43 => (2722676238102863199947790170206528520732444456037111610289946624 : ℤ)
  | 44 => (-2626562240930298324016232054936703011057791074365435549356916736 : ℤ)
  | 45 => (2539904013742096936628770930888409649914431709451487436190253056 : ℤ)
  | 46 => (-2461384487466787207304189159714053777104676084099355944004091904 : ℤ)
  | 47 => (2389694655843695639113606753015895754192069281080733567329239040 : ℤ)
  | 48 => (-2323977080830143973243914288588316027545492515699879176640135168 : ℤ)
  | 49 => (2263382240355008491229879367790242498116686216609936394988552192 : ℤ)
  | 50 => (-2207324322949864059683270857098856644433853892937285503268421632 : ℤ)
  | 51 => (2155225294168323676876488994483362474761628934734013963182276608 : ℤ)
  | 52 => (-2106669131876619848091656976596424198650335069857923182687682560 : ℤ)
  | 53 => (2061247459211865623112077754011078122940864907993931596437651456 : ℤ)
  | 54 => (-2018655289878184294402598902705585149220492014355992127140265984 : ℤ)
  | 55 => (1978595157689183220014198510354700086132047665333829405490806784 : ℤ)
  | 56 => (-1940837439375743057036046972254871991164829145028578793861677056 : ℤ)
  | 57 => (1905159912668351700559496958468207949883449814497083296747356160 : ℤ)
  | 58 => (-1871385723657605114013290082739963035462098127047120277836136448 : ℤ)
  | 59 => (1839345305897265415207409214862501487888561536147850987036475392 : ℤ)
  | 60 => (-1808899746985523016823714521369522519478236738731028677448957952 : ℤ)
  | 61 => (1779917313594364996189278463375843652861396951872401644032360448 : ℤ)
  | 62 => (-1752287003570856067397087111277788790314147758410709597526425600 : ℤ)
  | 63 => (1725904890211888383225724437908562006810194149538007829471821824 : ℤ)
  | 64 => (-1700680914895621454571637367245347084325585040690795625576923136 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment22 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1906105300789879641899243847434582559578114839895154900546355200 : ℤ)
  | 19 => (1987907052872932699201622147790912796365542971008522206513725440 : ℤ)
  | 20 => (-2081539102466536813283279176861501292860450770989584097854095360 : ℤ)
  | 21 => (2189578704609979714112593149487458006340850863297844977241948160 : ℤ)
  | 22 => (-2317165721680094718076600506046340088506493490207617391515402240 : ℤ)
  | 23 => (2469449578105138194844346723691791670933347807205222788156620800 : ℤ)
  | 24 => (-2658772859947792643050932088744432378290968473093954243437527040 : ℤ)
  | 25 => (2897487395902711780020997892835876235679472406986319800796446720 : ℤ)
  | 26 => (-3226746158505240028544955241838948222042741633777421220262707200 : ℤ)
  | 27 => (3687711074794383810129944821626797137357900983607024420997038080 : ℤ)
  | 28 => (-4609637639563159656457226803768247269694384214816934520118312960 : ℤ)
  | 29 => (4757244597296569698327448265472129232710822570447658855381860352 : ℤ)
  | 30 => (-590423015214359742660068953754531244053785363755513316542251008 : ℤ)
  | 31 => (-5955018535329386469515800510185745905469001164240759702643802112 : ℤ)
  | 32 => (8333641610706587516231269303092939006987633104104489779449561088 : ℤ)
  | 33 => (-6844885847086726429686145124388497461292061860840808000530677760 : ℤ)
  | 34 => (5475909581499392719081855340437202024496306250435439883030888448 : ℤ)
  | 35 => (-4791419963842135418589881695511033357838349479479595102856282112 : ℤ)
  | 36 => (4302500486914115986713930539427091841799028629213465299000492032 : ℤ)
  | 37 => (-3948032195975110624648867029616130069139912803582594701724745728 : ℤ)
  | 38 => (3666903889215432405653957920387257170149736250868458765963755520 : ℤ)
  | 39 => (-3440777237487791254569328533532526308454233722620701939685392384 : ℤ)
  | 40 => (3251321495191193604760722104614369472406502199170304502740811776 : ℤ)
  | 41 => (-3090893548569059010641220435992713427501594648879837049012617216 : ℤ)
  | 42 => (2951857708935106919537246269396800800618838865949990093737426944 : ℤ)
  | 43 => (-2830390629067007997007557914239170424519142912266172059908833280 : ℤ)
  | 44 => (2722676238102863199947790170206528520732444456037111610289946624 : ℤ)
  | 45 => (-2626562374647270936963222829569363912740362022570532667366834176 : ℤ)
  | 46 => (2539904013742096936628770930888409649914431709451487436190253056 : ℤ)
  | 47 => (-2461384618338717849762946088077934659602511480214982910566989824 : ℤ)
  | 48 => (2389694655843695639113606753015895754192069281080733567329239040 : ℤ)
  | 49 => (-2323977209031218888305553728618240157339290454751921919395627008 : ℤ)
  | 50 => (2263382240355008491229879367790242498116686216609936394988552192 : ℤ)
  | 51 => (-2207324448637192407782917366932115595212087166517719564793413632 : ℤ)
  | 52 => (2155225294168323676876488994483362474761628934734013963182276608 : ℤ)
  | 53 => (-2106669255192489170755461099451697131489356394880235846825410560 : ℤ)
  | 54 => (2061247459211865623112077754011078122940864907993931596437651456 : ℤ)
  | 55 => (-2018655410951946902108879314236216756007894769832444561020944384 : ℤ)
  | 56 => (1978595157689183220014198510354700086132047665333829405490806784 : ℤ)
  | 57 => (-1940837558325404566361515446741106552219119571461584693814624256 : ℤ)
  | 58 => (1905159912668351700559496958468207949883449814497083296747356160 : ℤ)
  | 59 => (-1871385840591170665553581125455244468362926003879566755755982848 : ℤ)
  | 60 => (1839345305897265415207409214862501487888561536147850987036475392 : ℤ)
  | 61 => (-1808899862002144870797771284696028846921673994631795704911101952 : ℤ)
  | 62 => (1779917313594364996189278463375843652861396951872401644032360448 : ℤ)
  | 63 => (-1752287116761817257022349322805461683988641565805115243600281600 : ℤ)
  | 64 => (1725904890211888383225724437908562006810194149538007829471821824 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment23 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1833566510301406179291985612432031012605367342271601251094364160 : ℤ)
  | 19 => (-1906105474984945733951202297988494529787309577083630697578496000 : ℤ)
  | 20 => (1987907052872932699201622147790912796365542971008522206513725440 : ℤ)
  | 21 => (-2081539268366599758094668177389036502583493377835751523598991360 : ℤ)
  | 22 => (2189578704609979714112593149487458006340850863297844977241948160 : ℤ)
  | 23 => (-2317165880367111447896189984811808549980708157625690581358346240 : ℤ)
  | 24 => (2469449578105138194844346723691791670933347807205222788156620800 : ℤ)
  | 25 => (-2658773012287328703677737988359282101306214553815304505686753280 : ℤ)
  | 26 => (2897487395902711780020997892835876235679472406986319800796446720 : ℤ)
  | 27 => (-3226746305202571049889286848875470177538904526323906657984184320 : ℤ)
  | 28 => (3687711074794383810129944821626797137357900983607024420997038080 : ℤ)
  | 29 => (-4609637781201962021893133182975923640518265628310092873780428800 : ℤ)
  | 30 => (4757244597296569698327448265472129232710822570447658855381860352 : ℤ)
  | 31 => (-590423152284168483404494482020024506141412538103731078150750208 : ℤ)
  | 32 => (-5955018535329386469515800510185745905469001164240759702643802112 : ℤ)
  | 33 => (8333641477790409343388190002956703116478418874433490737889804288 : ℤ)
  | 34 => (-6844885847086726429686145124388497461292061860840808000530677760 : ℤ)
  | 35 => (5475909452380819636891435448876287159430212427326469385515696128 : ℤ)
  | 36 => (-4791419963842135418589881695511033357838349479479595102856282112 : ℤ)
  | 37 => (4302500361285234068907035509800255756869856260783115625742467072 : ℤ)
  | 38 => (-3948032195975110624648867029616130069139912803582594701724745728 : ℤ)
  | 39 => (3666903766807803870354931994084186113039260609833759084327731200 : ℤ)
  | 40 => (-3440777237487791254569328533532526308454233722620701939685392384 : ℤ)
  | 41 => (3251321375769116984956794371635763563030428403038890179193470976 : ℤ)
  | 42 => (-3090893548569059010641220435992713427501594648879837049012617216 : ℤ)
  | 43 => (2951857592290287895542712204626999679832906320891399359109791744 : ℤ)
  | 44 => (-2830390629067007997007557914239170424519142912266172059908833280 : ℤ)
  | 45 => (2722676124050151265375356862431611869297310411979822891987369984 : ℤ)
  | 46 => (-2626562374647270936963222829569363912740362022570532667366834176 : ℤ)
  | 47 => (2539903902116038447472772374342746544254513283352864435298369536 : ℤ)
  | 48 => (-2461384618338717849762946088077934659602511480214982910566989824 : ℤ)
  | 49 => (2389694546495719976266914289460960467015006333065755933802496000 : ℤ)
  | 50 => (-2323977209031218888305553728618240157339290454751921919395627008 : ℤ)
  | 51 => (2263382133151110782556651462344227510688193130320742636629000192 : ℤ)
  | 52 => (-2207324448637192407782917366932115595212087166517719564793413632 : ℤ)
  | 53 => (2155225188987141019310303124989159090869522510450276690829508608 : ℤ)
  | 54 => (-2106669255192489170755461099451697131489356394880235846825410560 : ℤ)
  | 55 => (2061247355943068104774367991234951164210433145969898638127661056 : ℤ)
  | 56 => (-2018655410951946902108879314236216756007894769832444561020944384 : ℤ)
  | 57 => (1978595056232118991471887164469382372291623478082147902589763584 : ℤ)
  | 58 => (-1940837558325404566361515446741106552219119571461584693814624256 : ℤ)
  | 59 => (1905159812930898730128072245563997315938626037198820124403957760 : ℤ)
  | 60 => (-1871385840591170665553581125455244468362926003879566755755982848 : ℤ)
  | 61 => (1839345207794852657406007857907540208598570935526608522436411392 : ℤ)
  | 62 => (-1808899862002144870797771284696028846921673994631795704911101952 : ℤ)
  | 63 => (1779917217049133393273613635896357949433152233800702710616424448 : ℤ)
  | 64 => (-1752287116761817257022349322805461683988641565805115243600281600 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment24 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1768838815011752814317025888186512798237877037584504297923543040 : ℤ)
  | 19 => (1833566360991349528961735511957249323854628996110050567923957760 : ℤ)
  | 20 => (-1906105474984945733951202297988494529787309577083630697578496000 : ℤ)
  | 21 => (1987906910672878746506145861624454045174363593711807270160957440 : ℤ)
  | 22 => (-2081539268366599758094668177389036502583493377835751523598991360 : ℤ)
  | 23 => (2189578568592536802838659310545627896505809719796639385947996160 : ℤ)
  | 24 => (-2317165880367111447896189984811808549980708157625690581358346240 : ℤ)
  | 25 => (2469449447528393000021370238307634765491708309444065420514426880 : ℤ)
  | 26 => (-2658773012287328703677737988359282101306214553815304505686753280 : ℤ)
  | 27 => (2897487270162142333154427943947428845254189927660760854178037760 : ℤ)
  | 28 => (-3226746305202571049889286848875470177538904526323906657984184320 : ℤ)
  | 29 => (3687710953389696068327739353734503105223145486327174403572367360 : ℤ)
  | 30 => (-4609637781201962021893133182975923640518265628310092873780428800 : ℤ)
  | 31 => (4757244479808162206260797812673135008064284992434900774003146752 : ℤ)
  | 32 => (-590423152284168483404494482020024506141412538103731078150750208 : ℤ)
  | 33 => (-5955018649257539189095582767445376668762613361101616023980736512 : ℤ)
  | 34 => (8333641477790409343388190002956703116478418874433490737889804288 : ℤ)
  | 35 => (-6844885957759789071563647888583567345634427994934211284115128320 : ℤ)
  | 36 => (5475909452380819636891435448876287159430212427326469385515696128 : ℤ)
  | 37 => (-4791420071524034205281506006619750002063354366705609108506017792 : ℤ)
  | 38 => (4302500361285234068907035509800255756869856260783115625742467072 : ℤ)
  | 39 => (-3948032300895935083476603537875905260948891924469480143127052288 : ℤ)
  | 40 => (3666903766807803870354931994084186113039260609833759084327731200 : ℤ)
  | 41 => (-3440777339849571214401266590371331373633725547876199931297398784 : ℤ)
  | 42 => (3251321375769116984956794371635763563030428403038890179193470976 : ℤ)
  | 43 => (-3090893648550332459779392491509685816746679687501486250122018816 : ℤ)
  | 44 => (2951857592290287895542712204626999679832906320891399359109791744 : ℤ)
  | 45 => (-2830390726826475369498215035189098982892114950029562389882470400 : ℤ)
  | 46 => (2722676124050151265375356862431611869297310411979822891987369984 : ℤ)
  | 47 => (-2626562470326749641954078735179932289020292102083638096702734336 : ℤ)
  | 48 => (2539903902116038447472772374342746544254513283352864435298369536 : ℤ)
  | 49 => (-2461384712065554132202968199696450620039994007084963739304198144 : ℤ)
  | 50 => (2389694546495719976266914289460960467015006333065755933802496000 : ℤ)
  | 51 => (-2323977300920274067168320504714824432277998814428373712275243008 : ℤ)
  | 52 => (2263382133151110782556651462344227510688193130320742636629000192 : ℤ)
  | 53 => (-2207324538792491828553933826498575638548178387332351512524357632 : ℤ)
  | 54 => (2155225188987141019310303124989159090869522510450276690829508608 : ℤ)
  | 55 => (-2106669343708601329330640896116948810401155048043692668233973760 : ℤ)
  | 56 => (2061247355943068104774367991234951164210433145969898638127661056 : ℤ)
  | 57 => (-2018655497915144812288003324995060510728258358905314420650409984 : ℤ)
  | 58 => (1978595056232118991471887164469382372291623478082147902589763584 : ℤ)
  | 59 => (-1940837643814649969588450914944715667028968523431524555823251456 : ℤ)
  | 60 => (1905159812930898730128072245563997315938626037198820124403957760 : ℤ)
  | 61 => (-1871385924678953029383353717130925564897203661554917439698894848 : ℤ)
  | 62 => (1839345207794852657406007857907540208598570935526608522436411392 : ℤ)
  | 63 => (-1808899944755200530439769708249873735574455181550394790696189952 : ℤ)
  | 64 => (1779917217049133393273613635896357949433152233800702710616424448 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment25 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1710479777679703633238040165350075025322349696156864422650839040 : ℤ)
  | 19 => (-1768838943584301596545852363595352585773235057890284052875837440 : ℤ)
  | 20 => (1833566360991349528961735511957249323854628996110050567923957760 : ℤ)
  | 21 => (-1906105597434992193216751322187389565535269596422468559437824000 : ℤ)
  | 22 => (1987906910672878746506145861624454045174363593711807270160957440 : ℤ)
  | 23 => (-2081539385492731153913888983144501319385889918072900782768783360 : ℤ)
  | 24 => (2189578568592536802838659310545627896505809719796639385947996160 : ℤ)
  | 25 => (-2317165992808197587882641958337054774111008836253353870161346560 : ℤ)
  | 26 => (2469449447528393000021370238307634765491708309444065420514426880 : ℤ)
  | 27 => (-2658773120563930171812839888791000687505763355456758043052605440 : ℤ)
  | 28 => (2897487270162142333154427943947428845254189927660760854178037760 : ℤ)
  | 29 => (-3226746409745496605330074890671612260766055093425999728544317440 : ℤ)
  | 30 => (3687710953389696068327739353734503105223145486327174403572367360 : ℤ)
  | 31 => (-4609637882372535140061637739552835333963895209376634554967654400 : ℤ)
  | 32 => (4757244479808162206260797812673135008064284992434900774003146752 : ℤ)
  | 33 => (-590423250388966658598195870215817663422023040956135132635332608 : ℤ)
  | 34 => (-5955018649257539189095582767445376668762613361101616023980736512 : ℤ)
  | 35 => (8333641382488605401771451511566504049405825814519726799247638528 : ℤ)
  | 36 => (-6844885957759789071563647888583567345634427994934211284115128320 : ℤ)
  | 37 => (5475909359654740126129203403199336715792013774437401769539534848 : ℤ)
  | 38 => (-4791420071524034205281506006619750002063354366705609108506017792 : ℤ)
  | 39 => (4302500270936746340472040183243227119478790906686075384534925312 : ℤ)
  | 40 => (-3948032300895935083476603537875905260948891924469480143127052288 : ℤ)
  | 41 => (3666903678662937793832985334028548418023587093641524702661836800 : ℤ)
  | 42 => (-3440777339849571214401266590371331373633725547876199931297398784 : ℤ)
  | 43 => (3251321289674131514865590657162815116736049619781358922682597376 : ℤ)
  | 44 => (-3090893648550332459779392491509685816746679687501486250122018816 : ℤ)
  | 45 => (2951857508108524324786868572697894532345069288372924352743604224 : ℤ)
  | 46 => (-2830390726826475369498215035189098982892114950029562389882470400 : ℤ)
  | 47 => (2722676041659489047188786499266955767500703954621315438948122624 : ℤ)
  | 48 => (-2626562470326749641954078735179932289020292102083638096702734336 : ℤ)
  | 49 => (2539903821406818315371642222671246689433347774103714277219106816 : ℤ)
  | 50 => (-2461384712065554132202968199696450620039994007084963739304198144 : ℤ)
  | 51 => (2389694467369033572246198454488901785817785245566589112156160000 : ℤ)
  | 52 => (-2323977300920274067168320504714824432277998814428373712275243008 : ℤ)
  | 53 => (2263382055517380725781609511050886917815447912397031792749576192 : ℤ)
  | 54 => (-2207324538792491828553933826498575638548178387332351512524357632 : ℤ)
  | 55 => (2155225112764933327203898300082970145139918114670633316838801408 : ℤ)
  | 56 => (-2106669343708601329330640896116948810401155048043692668233973760 : ℤ)
  | 57 => (2061247281058092126564566759748169042090120055379371814557843456 : ℤ)
  | 58 => (-2018655497915144812288003324995060510728258358905314420650409984 : ℤ)
  | 59 => (1978594982616379894248692733516274523427586880552477465860112384 : ℤ)
  | 60 => (-1940837643814649969588450914944715667028968523431524555823251456 : ℤ)
  | 61 => (1905159740521975027941323624954383038367442498645045924342005760 : ℤ)
  | 62 => (-1871385924678953029383353717130925564897203661554917439698894848 : ℤ)
  | 63 => (1839345136535276950492064770958395998925342691235592643010363392 : ℤ)
  | 64 => (-1808899944755200530439769708249873735574455181550394790696189952 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment26 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1657601181277398569818099676392056139733888771523122123306434560 : ℤ)
  | 19 => (1710479666481823605364460510942429803670148165081595445394800640 : ℤ)
  | 20 => (-1768838943584301596545852363595352585773235057890284052875837440 : ℤ)
  | 21 => (1833566255088606645272612031569015779423960871276461065775349760 : ℤ)
  | 22 => (-1906105597434992193216751322187389565535269596422468559437824000 : ℤ)
  | 23 => (1987906809374602944716549489079187176588507126479678181149245440 : ℤ)
  | 24 => (-2081539385492731153913888983144501319385889918072900782768783360 : ℤ)
  | 25 => (2189578471346192033120646792902171702663387511253795460496752640 : ℤ)
  | 26 => (-2317165992808197587882641958337054774111008836253353870161346560 : ℤ)
  | 27 => (2469449353883764703255876702799121393643449886402808307116933120 : ℤ)
  | 28 => (-2658773120563930171812839888791000687505763355456758043052605440 : ℤ)
  | 29 => (2897487179746639150070503151042657313814492139896788468828733440 : ℤ)
  | 30 => (-3226746409745496605330074890671612260766055093425999728544317440 : ℤ)
  | 31 => (3687710865890822020182005683181498397378276659458814030653685760 : ℤ)
  | 32 => (-4609637882372535140061637739552835333963895209376634554967654400 : ℤ)
  | 33 => (4757244394960769189877056071530827412578351584562551321475940352 : ℤ)
  | 34 => (-590423250388966658598195870215817663422023040956135132635332608 : ℤ)
  | 35 => (-5955018731680720976439789030269332618663234385891898349292879872 : ℤ)
  | 36 => (8333641382488605401771451511566504049405825814519726799247638528 : ℤ)
  | 37 => (-6844886037955317297087740468628497459051248451486918411445862400 : ℤ)
  | 38 => (5475909359654740126129203403199336715792013774437401769539534848 : ℤ)
  | 39 => (-4791420149663266835279339802560963958725897375654400668469297152 : ℤ)
  | 40 => (4302500270936746340472040183243227119478790906686075384534925312 : ℤ)
  | 41 => (-3948032377129332771279368216842943267448933884419520689432690688 : ℤ)
  | 42 => (3666903678662937793832985334028548418023587093641524702661836800 : ℤ)
  | 43 => (-3440777414310099188534199532618205705563999090152983720712208384 : ℤ)
  | 44 => (3251321289674131514865590657162815116736049619781358922682597376 : ℤ)
  | 45 => (-3090893721356182034487149146151074052411836039949897066438721536 : ℤ)
  | 46 => (2951857508108524324786868572697894532345069288372924352743604224 : ℤ)
  | 47 => (-2830390798083264314956870484412585341202693507745028295213711360 : ℤ)
  | 48 => (2722676041659489047188786499266955767500703954621315438948122624 : ℤ)
  | 49 => (-2626562540129318404852353460949878109406164974947767963149664256 : ℤ)
  | 50 => (2539903821406818315371642222671246689433347774103714277219106816 : ℤ)
  | 51 => (-2461384780499445076220884597510122992967320353030189098565894144 : ℤ)
  | 52 => (2389694467369033572246198454488901785817785245566589112156160000 : ℤ)
  | 53 => (-2323977368062959521676464895022578458546319002902934442116907008 : ℤ)
  | 54 => (2263382055517380725781609511050886917815447912397031792749576192 : ℤ)
  | 55 => (-2207324604714401183889202864255279591611620026925556592732536832 : ℤ)
  | 56 => (2155225112764933327203898300082970145139918114670633316838801408 : ℤ)
  | 57 => (-2106669408473985959133712231456868483586290693959823975105167360 : ℤ)
  | 58 => (2061247281058092126564566759748169042090120055379371814557843456 : ℤ)
  | 59 => (-2018655561582811058535090400413964596232290010822867230794973184 : ℤ)
  | 60 => (1978594982616379894248692733516274523427586880552477465860112384 : ℤ)
  | 61 => (-1940837706438583982290503776012490177360802935153707647768723456 : ℤ)
  | 62 => (1905159740521975027941323624954383038367442498645045924342005760 : ℤ)
  | 63 => (-1871385986308856343471088278816671908398374034995796038121422848 : ℤ)
  | 64 => (1839345136535276950492064770958395998925342691235592643010363392 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment27 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1609322301336061351273840760748133374991593680143089525168537600 : ℤ)
  | 19 => (-1657601277843978594024103060482905937484484837983224129870888960 : ℤ)
  | 20 => (1710479666481823605364460510942429803670148165081595445394800640 : ℤ)
  | 21 => (-1768839035552473048170617491300923821726183692614190725794365440 : ℤ)
  | 22 => (1833566255088606645272612031569015779423960871276461065775349760 : ℤ)
  | 23 => (-1906105685404547494770874487818805530359829160071422768316416000 : ℤ)
  | 24 => (1987906809374602944716549489079187176588507126479678181149245440 : ℤ)
  | 25 => (-2081539469943504243405847222150660645617467099175896823292231680 : ℤ)
  | 26 => (2189578471346192033120646792902171702663387511253795460496752640 : ℤ)
  | 27 => (-2317166074131164266652675818120763754926601677315498205480222720 : ℤ)
  | 28 => (2469449353883764703255876702799121393643449886402808307116933120 : ℤ)
  | 29 => (-2658773199082656620280458787892512806913921960620207746119106560 : ℤ)
  | 30 => (2897487179746639150070503151042657313814492139896788468828733440 : ℤ)
  | 31 => (-3226746485731360910298738341415011085999756969390628473447383040 : ℤ)
  | 32 => (3687710865890822020182005683181498397378276659458814030653685760 : ℤ)
  | 33 => (-4609637956055797496394887146334312982675363695160516974267596800 : ℤ)
  | 34 => (4757244394960769189877056071530827412578351584562551321475940352 : ℤ)
  | 35 => (-590423321966992947607638151089253093598878141431906625669562368 : ℤ)
  | 36 => (-5955018731680720976439789030269332618663234385891898349292879872 : ℤ)
  | 37 => (8333641312845120363816318481527485793017534365408165346565685248 : ℤ)
  | 38 => (-6844886037955317297087740468628497459051248451486918411445862400 : ℤ)
  | 39 => (5475909291796985473762663527776703542900858003508188046413529088 : ℤ)
  | 40 => (-4791420149663266835279339802560963958725897375654400668469297152 : ℤ)
  | 41 => (4302500204734058874748586646245536219097175520413671752216870912 : ℤ)
  | 42 => (-3948032377129332771279368216842943267448933884419520689432690688 : ℤ)
  | 43 => (3666903613999847711033333042077315445557823227980107201327923200 : ℤ)
  | 44 => (-3440777414310099188534199532618205705563999090152983720712208384 : ℤ)
  | 45 => (3251321226447998989461486193921609543658413840023528476933881856 : ℤ)
  | 46 => (-3090893721356182034487149146151074052411836039949897066438721536 : ℤ)
  | 47 => (2951857446227628661625404629951182694864830014567388171798052864 : ℤ)
  | 48 => (-2830390798083264314956870484412585341202693507745028295213711360 : ℤ)
  | 49 => (2722675981041468805724495290045687028744551196607728975981051904 : ℤ)
  | 50 => (-2626562540129318404852353460949878109406164974947767963149664256 : ℤ)
  | 51 => (2539903761977386706092925350885689102417511736835492254702370816 : ℤ)
  | 52 => (-2461384780499445076220884597510122992967320353030189098565894144 : ℤ)
  | 53 => (2389694409060911993331230957642694341953191397680786373083136000 : ℤ)
  | 54 => (-2323977368062959521676464895022578458546319002902934442116907008 : ℤ)
  | 55 => (2263381998269406811937823241420065063839301225381880012568788992 : ℤ)
  | 56 => (-2207324604714401183889202864255279591611620026925556592732536832 : ℤ)
  | 57 => (2155225056521309832901231087814092534215984527427677181924343808 : ℤ)
  | 58 => (-2106669408473985959133712231456868483586290693959823975105167360 : ℤ)
  | 59 => (2061247225767750386402622720568594441520829410293075953116512256 : ℤ)
  | 60 => (-2018655561582811058535090400413964596232290010822867230794973184 : ℤ)
  | 61 => (1978594928232437199007436301536365080244678049320055307065360384 : ℤ)
  | 62 => (-1940837706438583982290503776012490177360802935153707647768723456 : ℤ)
  | 63 => (1905159687001269518338817295069392792695373490130598720448757760 : ℤ)
  | 64 => (-1871385986308856343471088278816671908398374034995796038121422848 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment28 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1565065254487010174622639694557361471935669051533862591277301760 : ℤ)
  | 19 => (1609322217149812099401940374617648935926971468357359570727731200 : ℤ)
  | 20 => (-1657601277843978594024103060482905937484484837983224129870888960 : ℤ)
  | 21 => (1710479586304443365486460143199111290275269868142805012594032640 : ℤ)
  | 22 => (-1768839035552473048170617491300923821726183692614190725794365440 : ℤ)
  | 23 => (1833566178397199459302350810249319810089729456813270217009397760 : ℤ)
  | 24 => (-1906105685404547494770874487818805530359829160071422768316416000 : ℤ)
  | 25 => (1987906735750852046185098716612279046027644968595014966333931520 : ℤ)
  | 26 => (-2081539469943504243405847222150660645617467099175896823292231680 : ℤ)
  | 27 => (2189578400449246723423694197193297206567742470327823475859783680 : ℤ)
  | 28 => (-2317166074131164266652675818120763754926601677315498205480222720 : ℤ)
  | 29 => (2469449285431541645617439713838828776723516743439800873674342400 : ℤ)
  | 30 => (-2658773199082656620280458787892512806913921960620207746119106560 : ℤ)
  | 31 => (2897487113502552320097822193984309620021008453158394178400419840 : ℤ)
  | 32 => (-3226746485731360910298738341415011085999756969390628473447383040 : ℤ)
  | 33 => (3687710801654131760814557482397646088245201569288249870238351360 : ℤ)
  | 34 => (-4609637956055797496394887146334312982675363695160516974267596800 : ℤ)
  | 35 => (4757244332559412937920106390769370883706221496968288994215329792 : ℤ)
  | 36 => (-590423321966992947607638151089253093598878141431906625669562368 : ℤ)
  | 37 => (-5955018792395554086451956287226425457565847444091721154195095552 : ℤ)
  | 38 => (8333641312845120363816318481527485793017534365408165346565685248 : ℤ)
  | 39 => (-6844886097113359814535493180535408430289691944091873964940328960 : ℤ)
  | 40 => (5475909291796985473762663527776703542900858003508188046413529088 : ℤ)
  | 41 => (-4791420207378430266935683911738438077007305661122649988951703552 : ℤ)
  | 42 => (4302500204734058874748586646245536219097175520413671752216870912 : ℤ)
  | 43 => (-3948032433502283099873936881620941243444728023714089793159692288 : ℤ)
  | 44 => (3666903613999847711033333042077315445557823227980107201327923200 : ℤ)
  | 45 => (-3440777469430317287604444449290025948759886693018784622134165504 : ℤ)
  | 46 => (3251321226447998989461486193921609543658413840023528476933881856 : ℤ)
  | 47 => (-3090893775303629535704835660340515141497172842754723480596381696 : ℤ)
  | 48 => (2951857446227628661625404629951182694864830014567388171798052864 : ℤ)
  | 49 => (-2830390850929743499823175641169588857041390783962001109082439680 : ℤ)
  | 50 => (2722675981041468805724495290045687028744551196607728975981051904 : ℤ)
  | 51 => (-2626562591939592115505593810711646262189201520258525623805280256 : ℤ)
  | 52 => (2539903761977386706092925350885689102417511736835492254702370816 : ℤ)
  | 53 => (-2461384831332166452710856261427329482490299605033196614680838144 : ℤ)
  | 54 => (2389694409060911993331230957642694341953191397680786373083136000 : ℤ)
  | 55 => (-2323977417971449600412073437777653920987062268505887276120670208 : ℤ)
  | 56 => (2263381998269406811937823241420065063839301225381880012568788992 : ℤ)
  | 57 => (-2207324653747303717383835818540967765237613410675826043683602432 : ℤ)
  | 58 => (2155225056521309832901231087814092534215984527427677181924343808 : ℤ)
  | 59 => (-2106669456675822347992842932280087366133877410188902418412994560 : ℤ)
  | 60 => (2061247225767750386402622720568594441520829410293075953116512256 : ℤ)
  | 61 => (-2018655608994453408232596007781065136443031043179337830769885184 : ℤ)
  | 62 => (1978594928232437199007436301536365080244678049320055307065360384 : ℤ)
  | 63 => (-1940837753097660580405509294373763724869786173345789825521811456 : ℤ)
  | 64 => (1905159687001269518338817295069392792695373490130598720448757760 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment29 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1524258068517321814497053251746608772849333195826369138199101440 : ℤ)
  | 19 => (-1565065328149978270010552532421535356117213486846376301413007360 : ℤ)
  | 20 => (1609322217149812099401940374617648935926971468357359570727731200 : ℤ)
  | 21 => (-1657601347999186303917353382258309636705003347804665758571560960 : ℤ)
  | 22 => (1710479586304443365486460143199111290275269868142805012594032640 : ℤ)
  | 23 => (-1768839102657454335894596059955657794893636180269482718464573440 : ℤ)
  | 24 => (1833566178397199459302350810249319810089729456813270217009397760 : ℤ)
  | 25 => (-1906105749825329530985893913727350144600583548220503081279815680 : ℤ)
  | 26 => (1987906735750852046185098716612279046027644968595014966333931520 : ℤ)
  | 27 => (-2081539531978331389390680743395925829701156509986122309849579520 : ℤ)
  | 28 => (2189578400449246723423694197193297206567742470327823475859783680 : ℤ)
  | 29 => (-2317166134026859442086308183461019794731543177408129709742489600 : ℤ)
  | 30 => (2469449285431541645617439713838828776723516743439800873674342400 : ℤ)
  | 31 => (-2658773257046232596506554625318567038983220186516302750243880960 : ℤ)
  | 32 => (2897487113502552320097822193984309620021008453158394178400419840 : ℤ)
  | 33 => (-3226746541938464887245255517100881856491197673289872113810800640 : ℤ)
  | 34 => (3687710801654131760814557482397646088245201569288249870238351360 : ℤ)
  | 35 => (-4609638010656984216857218117000587445438477521805496510620631040 : ℤ)
  | 36 => (4757244332559412937920106390769370883706221496968288994215329792 : ℤ)
  | 37 => (-590423375092471918868284500926709327638664567356751579959001088 : ℤ)
  | 38 => (-5955018792395554086451956287226425457565847444091721154195095552 : ℤ)
  | 39 => (8333641261081833161049534858608938693183896309378829237258027008 : ℤ)
  | 40 => (-6844886097113359814535493180535408430289691944091873964940328960 : ℤ)
  | 41 => (5475909241296217471063362432246413689404625753723469890991423488 : ℤ)
  | 42 => (-4791420207378430266935683911738438077007305661122649988951703552 : ℤ)
  | 43 => (4302500155407727337228339064564787990100855648530923786455744512 : ℤ)
  | 44 => (-3948032433502283099873936881620941243444728023714089793159692288 : ℤ)
  | 45 => (3666903565769656874346868739989472732761421575472531412583710720 : ℤ)
  | 46 => (-3440777469430317287604444449290025948759886693018784622134165504 : ℤ)
  | 47 => (3251321179243982425896010494005848590708744137569305364545929216 : ℤ)
  | 48 => (-3090893775303629535704835660340515141497172842754723480596381696 : ℤ)
  | 49 => (2951857399986959374867387617788804618505969897877536959662915584 : ℤ)
  | 50 => (-2830390850929743499823175641169588857041390783962001109082439680 : ℤ)
  | 51 => (2722675935707479308902909984004139895059394219460816022907387904 : ℤ)
  | 52 => (-2626562591939592115505593810711646262189201520258525623805280256 : ℤ)
  | 53 => (2539903717498755501664200144958133424084904891332860678101794816 : ℤ)
  | 54 => (-2461384831332166452710856261427329482490299605033196614680838144 : ℤ)
  | 55 => (2389694365390983174437573482732003312317541040278202643329843200 : ℤ)
  | 56 => (-2323977417971449600412073437777653920987062268505887276120670208 : ℤ)
  | 57 => (2263381955365617095130019406420087911916557014600394242986606592 : ℤ)
  | 58 => (-2207324653747303717383835818540967765237613410675826043683602432 : ℤ)
  | 59 => (2155225014344702992649491724593776011986846150727233544029995008 : ℤ)
  | 60 => (-2106669456675822347992842932280087366133877410188902418412994560 : ℤ)
  | 61 => (2061247184282563330417305314122381468836431006981164178138464256 : ℤ)
  | 62 => (-2018655608994453408232596007781065136443031043179337830769885184 : ℤ)
  | 63 => (1978594887405745175656806472970250726174317715901983401531408384 : ℤ)
  | 64 => (-1940837753097660580405509294373763724869786173345789825521811456 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment3 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-3947999617152033831149318272589430976913700224208951840866304000 : ℤ)
  | 19 => (3666926204400712383313651217626912867405669611031859325566976000 : ℤ)
  | 20 => (-3440746079136346569194949484819342182607084594321155025797120000 : ℤ)
  | 21 => (3251342920527852519700994969052136169673230083775775853510656000 : ℤ)
  | 22 => (-3090863637767426576926615571284107335449944801441119188549632000 : ℤ)
  | 23 => (2951878344062126708305401250780913955101067239012028112699392000 : ℤ)
  | 24 => (-2830361825617158948778953637291589937308965566988035947495424000 : ℤ)
  | 25 => (2722696165220294586074625967377995167245977248000711968298106880 : ℤ)
  | 26 => (-2626534562965963179244839464126565110683712885433311793009131520 : ℤ)
  | 27 => (2539923301628054211292614595538550325841086809563013009081630720 : ℤ)
  | 28 => (-2461357701772233574069655153149244147368928750225315276815073280 : ℤ)
  | 29 => (2389713362750119876507567560815121669501651728791186758539673600 : ℤ)
  | 30 => (-2323951105760669935890326941757425915963004282814768550426705920 : ℤ)
  | 31 => (2263400416143625288442720141478863408188395336277931010482503680 : ℤ)
  | 32 => (-2207299088660652580649622924763964227638490767411104568972410880 : ℤ)
  | 33 => (2155242981917797927863501298417380159139234576659747651578757120 : ℤ)
  | 34 => (-2106644578055920996562656881094187314976289447788456578960588800 : ℤ)
  | 35 => (2061264696448294904133928506576891519052449685863001075312754688 : ℤ)
  | 36 => (-2018631364013068864789382667599521698349634012491667112462385152 : ℤ)
  | 37 => (1978611977342787313421059628968413000074884904646040559783247872 : ℤ)
  | 38 => (-1940814095404687108270549560843042866888273522121503672083939328 : ℤ)
  | 39 => (1905176343827514492058686407209666123169321436857899072576552960 : ℤ)
  | 40 => (-1871362920909165312016140272648283402077471131052703437027278848 : ℤ)
  | 41 => (1839361374410168853096599349817837867302597570368754661134958592 : ℤ)
  | 42 => (-1808877449332029451013062893577077570301057125655712705756004352 : ℤ)
  | 43 => (1779933042554338698863655860367083875618165734947992812910542848 : ℤ)
  | 44 => (-1752265178746055220679112862714634932690612082455054653744742400 : ℤ)
  | 45 => (1725920300352877310187234646217181842842301144988237790932107264 : ℤ)
  | 46 => (-1700659533938969363163176443702558382905696095548092381930192896 : ℤ)
  | 47 => (1676547105270341931662405983720711132046610289854199948625575936 : ℤ)
  | 48 => (-1653363102450333068899201042977921362655954016045116556226330624 : ℤ)
  | 49 => (1631184768478535083260765309581307055709749552996249128198471680 : ℤ)
  | 50 => (-1609807391950147186236596457182434117083143053148340611478749184 : ℤ)
  | 51 => (1589317810601585821908939626216763211760710040423193429073330176 : ℤ)
  | 52 => (-1569523708164871957677553326652062237400323275983066114525249536 : ℤ)
  | 53 => (1550519019204773752549688579602801389050823801596812969742106624 : ℤ)
  | 54 => (-1532121693294626796891741914494691456412244412297215622941593600 : ℤ)
  | 55 => (1514430912747773072699143170343053110257402897359773934959607808 : ℤ)
  | 56 => (-1497273250951966521335892594615391164783270257076010662798088192 : ℤ)
  | 57 => (1480751752199669890964210691855537951349486895225017616927301632 : ℤ)
  | 58 => (-1464700328865897713431039694823822572241597651604317685248743808 : ℤ)
  | 59 => (1449224837476500720178559261545190929544875179715018661942248960 : ℤ)
  | 60 => (-1434165510495438615050220974369547681393926504626730038691770304 : ℤ)
  | 61 => (1419630214068118353214172189433783062206474448727848475671224576 : ℤ)
  | 62 => (-1405464682653554613359786592702652126662504056012407924347618896 : ℤ)
  | 63 => (1391778173455593610382698283805905361689285467580393888584289344 : ℤ)
  | 64 => (-1378421258455259047288828492584681240300898159188056412629859320 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment30 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1486506372761457564281942904320103468857016472201971823269642240 : ℤ)
  | 19 => (1524258003837642511229617589231724386738708813600747343933603840 : ℤ)
  | 20 => (-1565065328149978270010552532421535356117213486846376301413007360 : ℤ)
  | 21 => (1609322155550117524861525457936806663440662532904386433332019200 : ℤ)
  | 22 => (-1657601347999186303917353382258309636705003347804665758571560960 : ℤ)
  | 23 => (1710479527382996381143454570721783899201409147274743750737264640 : ℤ)
  | 24 => (-1768839102657454335894596059955657794893636180269482718464573440 : ℤ)
  | 25 => (1833566121832610354333065460671085514658823164779931405626900480 : ℤ)
  | 26 => (-1906105749825329530985893913727350144600583548220503081279815680 : ℤ)
  | 27 => (1987906681281247722881342454055460835612698168859207222039674880 : ℤ)
  | 28 => (-2081539531978331389390680743395925829701156509986122309849579520 : ℤ)
  | 29 => (2189578347857904618164895047138438244787793836100147033092915200 : ℤ)
  | 30 => (-2317166134026859442086308183461019794731543177408129709742489600 : ℤ)
  | 31 => (2469449234536694446979892149269610426613889032896888187125760000 : ℤ)
  | 32 => (-2658773257046232596506554625318567038983220186516302750243880960 : ℤ)
  | 33 => (2897487064149973218388685161674764553248036127783448542959370240 : ℤ)
  | 34 => (-3226746541938464887245255517100881856491197673289872113810800640 : ℤ)
  | 35 => (3687710753711626347725681508154088023380028453209731252952760320 : ℤ)
  | 36 => (-4609638010656984216857218117000587445438477521805496510620631040 : ℤ)
  | 37 => (4757244285912650914374173010424287361134701708351351961180700672 : ℤ)
  | 38 => (-590423375092471918868284500926709327638664567356751579959001088 : ℤ)
  | 39 => (-5955018837846245288881327273203686325712456468897967494074990592 : ℤ)
  | 40 => (8333641261081833161049534858608938693183896309378829237258027008 : ℤ)
  | 41 => (-6844886141455497573003172191244931228481505626829675272140226560 : ℤ)
  | 42 => (5475909241296217471063362432246413689404625753723469890991423488 : ℤ)
  | 43 => (-4791420250689355519392486666384948717101635304727014056449277952 : ℤ)
  | 44 => (4302500155407727337228339064564787990100855648530923786455744512 : ℤ)
  | 45 => (-3948032475850743346720588463941973869314739230793912436935098368 : ℤ)
  | 46 => (3666903565769656874346868739989472732761421575472531412583710720 : ℤ)
  | 47 => (-3440777510877746465369252380923377029398621065905419550084562944 : ℤ)
  | 48 => (3251321179243982425896010494005848590708744137569305364545929216 : ℤ)
  | 49 => (-3090893815905192811882606695409920281714708554970202593690648576 : ℤ)
  | 50 => (2951857399986959374867387617788804618505969897877536959662915584 : ℤ)
  | 51 => (-2830390890735197692154323714767044876862504227310510043488583680 : ℤ)
  | 52 => (2722675935707479308902909984004139895059394219460816022907387904 : ℤ)
  | 53 => (-2626562630994000002321059845184621979749539238260836276430176256 : ℤ)
  | 54 => (2539903717498755501664200144958133424084904891332860678101794816 : ℤ)
  | 55 => (-2461384869676494196129677458909887459731358455435465255439826944 : ℤ)
  | 56 => (2389694365390983174437573482732003312317541040278202643329843200 : ℤ)
  | 57 => (-2323977455643069839560389000216658249504593770655484537217220608 : ℤ)
  | 58 => (2263381955365617095130019406420087911916557014600394242986606592 : ℤ)
  | 59 => (-2207324690780421918580485015514904223780271497534752164761567232 : ℤ)
  | 60 => (2155225014344702992649491724593776011986846150727233544029995008 : ℤ)
  | 61 => (-2106669493101840250809219191598713390929934544804239586686402560 : ℤ)
  | 62 => (2061247184282563330417305314122381468836431006981164178138464256 : ℤ)
  | 63 => (-2018655644842280550686807564570824081480420604229352186848477184 : ℤ)
  | 64 => (1978594887405745175656806472970250726174317715901983401531408384 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment31 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1451420519707457812180695988543572831426866377216058516161167360 : ℤ)
  | 19 => (-1486506429741175045731826702249882570906852237495971975360675840 : ℤ)
  | 20 => (1524258003837642511229617589231724386738708813600747343933603840 : ℤ)
  | 21 => (-1565065382416375871391394244735610691402771358554947874833039360 : ℤ)
  | 22 => (1609322155550117524861525457936806663440662532904386433332019200 : ℤ)
  | 23 => (-1657601399906175313933810672297859957412928268569386394016808960 : ℤ)
  | 24 => (1710479527382996381143454570721783899201409147274743750737264640 : ℤ)
  | 25 => (-1768839152488163785510395058393626102773244104203614528492011520 : ℤ)
  | 26 => (1833566121832610354333065460671085514658823164779931405626900480 : ℤ)
  | 27 => (-1906105797810457149134441097408356663299465252749667046491422720 : ℤ)
  | 28 => (1987906681281247722881342454055460835612698168859207222039674880 : ℤ)
  | 29 => (-2081539578308799434499622851777587296031111259186694414191820800 : ℤ)
  | 30 => (2189578347857904618164895047138438244787793836100147033092915200 : ℤ)
  | 31 => (-2317166178862796259933671514152950246018596160505457552654336000 : ℤ)
  | 32 => (2469449234536694446979892149269610426613889032896888187125760000 : ℤ)
  | 33 => (-2658773300523504662297937249019832931140362473156135810037186560 : ℤ)
  | 34 => (2897487064149973218388685161674764553248036127783448542959370240 : ℤ)
  | 35 => (-3226746584173529179728312922982111580300993037454281371895726080 : ℤ)
  | 36 => (3687710753711626347725681508154088023380028453209731252952760320 : ℤ)
  | 37 => (-4609638051750560285219111809209351501037197335587083896865423360 : ℤ)
  | 38 => (4757244285912650914374173010424287361134701708351351961180700672 : ℤ)
  | 39 => (-590423415132366549579873226668581997196391565400349546043670528 : ℤ)
  | 40 => (-5955018837846245288881327273203686325712456468897967494074990592 : ℤ)
  | 41 => (8333641222018521326208960492031501942395869969824099514248593408 : ℤ)
  | 42 => (-6844886141455497573003172191244931228481505626829675272140226560 : ℤ)
  | 43 => (5475909203141354748660940957914963839797716305786292022005465088 : ℤ)
  | 44 => (-4791420250689355519392486666384948717101635304727014056449277952 : ℤ)
  | 45 => (4302500118100750453101526956329592581596321966103460981225029632 : ℤ)
  | 46 => (-3948032475850743346720588463941973869314739230793912436935098368 : ℤ)
  | 47 => (3666903529256445455839776038312472971246346056500972071294074880 : ℤ)
  | 48 => (-3440777510877746465369252380923377029398621065905419550084562944 : ℤ)
  | 49 => (3251321143475938587358450296444705967183772200617573764915265536 : ℤ)
  | 50 => (-3090893815905192811882606695409920281714708554970202593690648576 : ℤ)
  | 51 => (2951857364920249729242328600571998124854036626356231469828931584 : ℤ)
  | 52 => (-2830390890735197692154323714767044876862504227310510043488583680 : ℤ)
  | 53 => (2722675901302405694327380382206518429589572896458780447975931904 : ℤ)
  | 54 => (-2626562630994000002321059845184621979749539238260836276430176256 : ℤ)
  | 55 => (2539903683719228680080952899556832348896353046930862113623638016 : ℤ)
  | 56 => (-2461384869676494196129677458909887459731358455435465255439826944 : ℤ)
  | 57 => (2389694332204079630425962153916689975290191859813081246649548800 : ℤ)
  | 58 => (-2323977455643069839560389000216658249504593770655484537217220608 : ℤ)
  | 59 => (2263381922741203441694876066228762936533739176177054564894113792 : ℤ)
  | 60 => (-2207324690780421918580485015514904223780271497534752164761567232 : ℤ)
  | 61 => (2155224982255115792549350734241653085380795817851817467217707008 : ℤ)
  | 62 => (-2106669493101840250809219191598713390929934544804239586686402560 : ℤ)
  | 63 => (2061247152702334657302880847426641445827302107960913435878752256 : ℤ)
  | 64 => (-2018655644842280550686807564570824081480420604229352186848477184 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment32 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1418720919945120534272162790649602262293495789171487325709926400 : ℤ)
  | 19 => (1451420469353288875085449841535861066824685933467872335243509760 : ℤ)
  | 20 => (-1486506429741175045731826702249882570906852237495971975360675840 : ℤ)
  | 21 => (1524257955881291142567478401605332229974727438602474790678691840 : ℤ)
  | 22 => (-1565065382416375871391394244735610691402771358554947874833039360 : ℤ)
  | 23 => (1609322109678824911358609713250692426535984695949517034566451200 : ℤ)
  | 24 => (-1657601399906175313933810672297859957412928268569386394016808960 : ℤ)
  | 25 => (1710479483346555472180655455823114231772918423798069127922319360 : ℤ)
  | 26 => (-1768839152488163785510395058393626102773244104203614528492011520 : ℤ)
  | 27 => (1833566079427148738294814461139033242320276542172763250323619840 : ℤ)
  | 28 => (-1906105797810457149134441097408356663299465252749667046491422720 : ℤ)
  | 29 => (1987906640338043403947858730369341400251342809100562106574438400 : ℤ)
  | 30 => (-2081539578308799434499622851777587296031111259186694414191820800 : ℤ)
  | 31 => (2189578308235448825648620475829290404115514455688554985868492800 : ℤ)
  | 32 => (-2317166178862796259933671514152950246018596160505457552654336000 : ℤ)
  | 33 => (2469449196114919133024716807394073126568042360982617111029350400 : ℤ)
  | 34 => (-2658773300523504662297937249019832931140362473156135810037186560 : ℤ)
  | 35 => (2897487026825962913403657686709956890346356503638156640465715200 : ℤ)
  | 36 => (-3226746584173529179728312922982111580300993037454281371895726080 : ℤ)
  | 37 => (3687710717396373078010519640620761648664880710798095888364339200 : ℤ)
  | 38 => (-4609638051750560285219111809209351501037197335587083896865423360 : ℤ)
  | 39 => (4757244250528557984908117857443097560130198779847707246966341632 : ℤ)
  | 40 => (-590423415132366549579873226668581997196391565400349546043670528 : ℤ)
  | 41 => (-5955018872367311561531137178551188570594898350364937946967048192 : ℤ)
  | 42 => (8333641222018521326208960492031501942395869969824099514248593408 : ℤ)
  | 43 => (-6844886175173748350940195819723886909529472115704390598220840960 : ℤ)
  | 44 => (5475909203141354748660940957914963839797716305786292022005465088 : ℤ)
  | 45 => (-4791420283658311835597576436453260938570758093848957930839212032 : ℤ)
  | 46 => (4302500118100750453101526956329592581596321966103460981225029632 : ℤ)
  | 47 => (-3948032508118232507261740153796066681816433875466453250167799808 : ℤ)
  | 48 => (3666903529256445455839776038312472971246346056500972071294074880 : ℤ)
  | 49 => (-3440777542486715438960584648535549580420689289258112591618637824 : ℤ)
  | 50 => (3251321143475938587358450296444705967183772200617573764915265536 : ℤ)
  | 51 => (-3090893846894378080109403036206167880755951911198333026567192576 : ℤ)
  | 52 => (2951857364920249729242328600571998124854036626356231469828931584 : ℤ)
  | 53 => (-2830390921139681351546652200076570823091648652289053109707079680 : ℤ)
  | 54 => (2722675901302405694327380382206518429589572896458780447975931904 : ℤ)
  | 55 => (-2626562660845674867906255085306701999683608310057951286899245056 : ℤ)
  | 56 => (2539903683719228680080952899556832348896353046930862113623638016 : ℤ)
  | 57 => (-2461384899004455467581799098328071338964829824218595792041017344 : ℤ)
  | 58 => (2389694332204079630425962153916689975290191859813081246649548800 : ℤ)
  | 59 => (-2323977484473947021665864510153177995191735116238900996926865408 : ℤ)
  | 60 => (2263381922741203441694876066228762936533739176177054564894113792 : ℤ)
  | 61 => (-2207324719138661769831772402337710531013525280075817534967775232 : ℤ)
  | 62 => (2155224982255115792549350734241653085380795817851817467217707008 : ℤ)
  | 63 => (-2106669521009949310770803604027506899635676362543065824032194560 : ℤ)
  | 64 => (2061247152702334657302880847426641445827302107960913435878752256 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment33 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1388131801226353927420489909064655568206109565288906282539941888 : ℤ)
  | 19 => (-1418720964577224819424767330042801326372701182493743258796032000 : ℤ)
  | 20 => (1451420469353288875085449841535861066824685933467872335243509760 : ℤ)
  | 21 => (-1486506472247941031591450073100548346220381183517168102109347840 : ℤ)
  | 22 => (1524257955881291142567478401605332229974727438602474790678691840 : ℤ)
  | 23 => (-1565065423075021596996251382071030128659190350401309387375247360 : ℤ)
  | 24 => (1609322109678824911358609713250692426535984695949517034566451200 : ℤ)
  | 25 => (-1657601438938475210514473524139862617179090500741893446057328640 : ℤ)
  | 26 => (1710479483346555472180655455823114231772918423798069127922319360 : ℤ)
  | 27 => (-1768839190074822945180662989797036071436955883332695393419919360 : ℤ)
  | 28 => (1833566079427148738294814461139033242320276542172763250323619840 : ℤ)
  | 29 => (-1906105834101024613643665307039235253733393867081193398835609600 : ℤ)
  | 30 => (1987906640338043403947858730369341400251342809100562106574438400 : ℤ)
  | 31 => (-2081539613428703432411775312710695609354267982733332819686195200 : ℤ)
  | 32 => (2189578308235448825648620475829290404115514455688554985868492800 : ℤ)
  | 33 => (-2317166212918460742757576930815358307422869346974925097376153600 : ℤ)
  | 34 => (2469449196114919133024716807394073126568042360982617111029350400 : ℤ)
  | 35 => (-2658773333606150159898302510920457905075942140012189996338380800 : ℤ)
  | 36 => (2897487026825962913403657686709956890346356503638156640465715200 : ℤ)
  | 37 => (-3226746616362049123339479123750287230616692172773685445053644800 : ℤ)
  | 38 => (3687710717396373078010519640620761648664880710798095888364339200 : ℤ)
  | 39 => (-4609638083113733563609478876624497006473006749488041711737241600 : ℤ)
  | 40 => (4757244250528557984908117857443097560130198779847707246966341632 : ℤ)
  | 41 => (-590423445730584382155841097317504441524010505791527902016176128 : ℤ)
  | 42 => (-5955018872367311561531137178551188570594898350364937946967048192 : ℤ)
  | 43 => (8333641192131889954855689548606973043285172400139692747949867008 : ℤ)
  | 44 => (-6844886175173748350940195819723886909529472115704390598220840960 : ℤ)
  | 45 => (5475909173918870741115520479899868916222812015428205406068932608 : ℤ)
  | 46 => (-4791420283658311835597576436453260938570758093848957930839212032 : ℤ)
  | 47 => (4302500089500021424440051594868010315969819894689163442223316992 : ℤ)
  | 48 => (-3948032508118232507261740153796066681816433875466453250167799808 : ℤ)
  | 49 => (3666903501239404774702004255656229119204058313074721420843417600 : ℤ)
  | 50 => (-3440777542486715438960584648535549580420689289258112591618637824 : ℤ)
  | 51 => (3251321116008251645066517176193486504397215589415367244865601536 : ℤ)
  | 52 => (-3090893846894378080109403036206167880755951911198333026567192576 : ℤ)
  | 53 => (2951857337970821031144582897684009217969113158761613752044355584 : ℤ)
  | 54 => (-2830390921139681351546652200076570823091648652289053109707079680 : ℤ)
  | 55 => (2722675874842966608922320964825583866466193491911337597787439104 : ℤ)
  | 56 => (-2626562660845674867906255085306701999683608310057951286899245056 : ℤ)
  | 57 => (2539903657723990280384754173708896637757594333691269137999855616 : ℤ)
  | 58 => (-2461384899004455467581799098328071338964829824218595792041017344 : ℤ)
  | 59 => (2389694306649438491741563406472956564340225667136871202816000000 : ℤ)
  | 60 => (-2323977484473947021665864510153177995191735116238900996926865408 : ℤ)
  | 61 => (2263381897605490846267598609726730073304264232561110259484065792 : ℤ)
  | 62 => (-2207324719138661769831772402337710531013525280075817534967775232 : ℤ)
  | 63 => (2155224957518382762128855459588858839027979206674221484115755008 : ℤ)
  | 64 => (-2106669521009949310770803604027506899635676362543065824032194560 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment34 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1359448679836267904288380461208826444749344129255153701593546752 : ℤ)
  | 19 => (1388131761553372340618174762937367511246815882335789897574514688 : ℤ)
  | 20 => (-1418720964577224819424767330042801326372701182493743258796032000 : ℤ)
  | 21 => (1451420431569496887654673511890824822101549092560142444800245760 : ℤ)
  | 22 => (-1486506472247941031591450073100548346220381183517168102109347840 : ℤ)
  | 23 => (1524257919740272719807605390640514952413466112516820112863395840 : ℤ)
  | 24 => (-1565065423075021596996251382071030128659190350401309387375247360 : ℤ)
  | 25 => (1609322074983447225509131622724467840077173822907288543863767040 : ℤ)
  | 26 => (-1657601438938475210514473524139862617179090500741893446057328640 : ℤ)
  | 27 => (1710479449936191774695972850131194259627396842349997247986401280 : ℤ)
  | 28 => (-1768839190074822945180662989797036071436955883332695393419919360 : ℤ)
  | 29 => (1833566047168866547619948497022696717490117773878073159351009280 : ℤ)
  | 30 => (-1906105834101024613643665307039235253733393867081193398835609600 : ℤ)
  | 31 => (1987906609120350961359278765095467343964092388170216857246105600 : ℤ)
  | 32 => (-2081539613428703432411775312710695609354267982733332819686195200 : ℤ)
  | 33 => (2189578277963747063138482327684927682867271623271250501671321600 : ℤ)
  | 34 => (-2317166212918460742757576930815358307422869346974925097376153600 : ℤ)
  | 35 => (2469449166708123135157725463482406483069749323777235612094955520 : ℤ)
  | 36 => (-2658773333606150159898302510920457905075942140012189996338380800 : ℤ)
  | 37 => (2897486998213945185749287730471578534510179494465353019880898560 : ℤ)
  | 38 => (-3226746616362049123339479123750287230616692172773685445053644800 : ℤ)
  | 39 => (3687710689517996830552415580696187866055272342886133386256056320 : ℤ)
  | 40 => (-4609638083113733563609478876624497006473006749488041711737241600 : ℤ)
  | 41 => (4757244223330142133729479750199610942950093055055548708324114432 : ℤ)
  | 42 => (-590423445730584382155841097317504441524010505791527902016176128 : ℤ)
  | 43 => (-5955018898933206113845155794928547592026629523417743961454804992 : ℤ)
  | 44 => (8333641192131889954855689548606973043285172400139692747949867008 : ℤ)
  | 45 => (-6844886201149289690980569577959526841596053707133800923497758720 : ℤ)
  | 46 => (5475909173918870741115520479899868916222812015428205406068932608 : ℤ)
  | 47 => (-4791420309081182083296665646641334063572093268439444632174067712 : ℤ)
  | 48 => (4302500089500021424440051594868010315969819894689163442223316992 : ℤ)
  | 49 => (-3948032533022268668273092849490505661409578536289787161679495168 : ℤ)
  | 50 => (3666903501239404774702004255656229119204058313074721420843417600 : ℤ)
  | 51 => (-3440777566902437165442302977647744658453184054771185053885005824 : ℤ)
  | 52 => (3251321116008251645066517176193486504397215589415367244865601536 : ℤ)
  | 53 => (-3090893870849425811751843660995491353542550549060215442375704576 : ℤ)
  | 54 => (2951857337970821031144582897684009217969113158761613752044355584 : ℤ)
  | 55 => (-2830390944659182760795593904415179323645763678553446754319073280 : ℤ)
  | 56 => (2722675874842966608922320964825583866466193491911337597787439104 : ℤ)
  | 57 => (-2626562683952553445413987286060422631806949388493145043009273856 : ℤ)
  | 58 => (2539903657723990280384754173708896637757594333691269137999855616 : ℤ)
  | 59 => (-2461384921719692035301264651611389926475910884375226942115282944 : ℤ)
  | 60 => (2389694306649438491741563406472956564340225667136871202816000000 : ℤ)
  | 61 => (-2323977506816802662045666693710540540284601732786407046180241408 : ℤ)
  | 62 => (2263381897605490846267598609726730073304264232561110259484065792 : ℤ)
  | 63 => (-2207324741126868907983323757584638749993806712233680631058399232 : ℤ)
  | 64 => (2155224957518382762128855459588858839027979206674221484115755008 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment35 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1332470188893018821098084726691711161546606182573546827281334272 : ℤ)
  | 19 => (-1359448715196968883829574395800539712908714585800322653410557952 : ℤ)
  | 20 => (1388131761553372340618174762937367511246815882335789897574514688 : ℤ)
  | 21 => (-1418720998254082895178285362987290153191149236346285117669376000 : ℤ)
  | 22 => (1451420431569496887654673511890824822101549092560142444800245760 : ℤ)
  | 23 => (-1486506504460587886660032539395276789264114104593512488857763840 : ℤ)
  | 24 => (1524257919740272719807605390640514952413466112516820112863395840 : ℤ)
  | 25 => (-1565065453999162577862090549713969433981173954634599998653726720 : ℤ)
  | 26 => (1609322074983447225509131622724467840077173822907288543863767040 : ℤ)
  | 27 => (-1657601468717277636533429759647878244526185823336914034695864320 : ℤ)
  | 28 => (1710479449936191774695972850131194259627396842349997247986401280 : ℤ)
  | 29 => (-1768839218826770115130000044770292539220358263769266996243333120 : ℤ)
  | 30 => (1833566047168866547619948497022696717490117773878073159351009280 : ℤ)
  | 31 => (-1906105861925489616820443102174644738685073590084327208019558400 : ℤ)
  | 32 => (1987906609120350961359278765095467343964092388170216857246105600 : ℤ)
  | 33 => (-2081539640410002829431681053448062382640745289887886816470630400 : ℤ)
  | 34 => (2189578277963747063138482327684927682867271623271250501671321600 : ℤ)
  | 35 => (-2317166239128865871291199650388800315758304445353634694252462080 : ℤ)
  | 36 => (2469449166708123135157725463482406483069749323777235612094955520 : ℤ)
  | 37 => (-2658773359108165960633719211045969048321230343840123658163978240 : ℤ)
  | 38 => (2897486998213945185749287730471578534510179494465353019880898560 : ℤ)
  | 39 => (-3226746641210167083030397959770016036855690935477825936063201280 : ℤ)
  | 40 => (3687710689517996830552415580696187866055272342886133386256056320 : ℤ)
  | 41 => (-4609638107355799865746960667863256817437883591150617800527052800 : ℤ)
  | 42 => (4757244223330142133729479750199610942950093055055548708324114432 : ℤ)
  | 43 => (-590423469408881700522683777132107047582727420903811523624828928 : ℤ)
  | 44 => (-5955018898933206113845155794928547592026629523417743961454804992 : ℤ)
  | 45 => (8333641168979777021341443372788250495138871416474348762376962048 : ℤ)
  | 46 => (-6844886201149289690980569577959526841596053707133800923497758720 : ℤ)
  | 47 => (5475909151259355955122854009949629826547708925032336824444387328 : ℤ)
  | 48 => (-4791420309081182083296665646641334063572093268439444632174067712 : ℤ)
  | 49 => (4302500067302945715712541583488184268941147479607496260223762432 : ℤ)
  | 50 => (-3948032533022268668273092849490505661409578536289787161679495168 : ℤ)
  | 51 => (3666903479477565844576994440577968288783791239465243791432089600 : ℤ)
  | 52 => (-3440777566902437165442302977647744658453184054771185053885005824 : ℤ)
  | 53 => (3251321094657013449472167923663872104739595064364559004688449536 : ℤ)
  | 54 => (-3090893870849425811751843660995491353542550549060215442375704576 : ℤ)
  | 55 => (2951857317007787166379221813382205989214358461439002025324969984 : ℤ)
  | 56 => (-2830390944659182760795593904415179323645763678553446754319073280 : ℤ)
  | 57 => (2722675854247705268100211829371180694356259052436490989080674304 : ℤ)
  | 58 => (-2626562683952553445413987286060422631806949388493145043009273856 : ℤ)
  | 59 => (2539903637477801165678274006652025722802065562682097895542358016 : ℤ)
  | 60 => (-2461384921719692035301264651611389926475910884375226942115282944 : ℤ)
  | 61 => (2389694286735154116620435373302263861105279334996702767611904000 : ℤ)
  | 62 => (-2323977506816802662045666693710540540284601732786407046180241408 : ℤ)
  | 63 => (2263381878007306223132520227876207095517491651724754021664161792 : ℤ)
  | 64 => (-2207324741126868907983323757584638749993806712233680631058399232 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment36 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1307042847141175659705085884190260742156903608171589727187632128 : ℤ)
  | 19 => (1332470157294094541508081636205499304893551732043821380976771072 : ℤ)
  | 20 => (-1359448715196968883829574395800539712908714585800322653410557952 : ℤ)
  | 21 => (1388131731459158741008648010093356219196287834212241853474930688 : ℤ)
  | 22 => (-1418720998254082895178285362987290153191149236346285117669376000 : ℤ)
  | 23 => (1451420402783727357593387052648727064488000524789792141748469760 : ℤ)
  | 24 => (-1486506504460587886660032539395276789264114104593512488857763840 : ℤ)
  | 25 => (1524257892105933970948770389768101105104459487457283821933690880 : ℤ)
  | 26 => (-1565065453999162577862090549713969433981173954634599998653726720 : ℤ)
  | 27 => (1609322048372602504385809029291773024149982258035142485931458560 : ℤ)
  | 28 => (-1657601468717277636533429759647878244526185823336914034695864320 : ℤ)
  | 29 => (1710479424242962388783799311644454437352867055576890709293137920 : ℤ)
  | 30 => (-1768839218826770115130000044770292539220358263769266996243333120 : ℤ)
  | 31 => (1833566022304451012866232169454883986256701851194421670293012480 : ℤ)
  | 32 => (-1906105861925489616820443102174644738685073590084327208019558400 : ℤ)
  | 33 => (1987906585009402564022341720181224695495325432840615413311078400 : ℤ)
  | 34 => (-2081539640410002829431681053448062382640745289887886816470630400 : ℤ)
  | 35 => (2189578254541682905725457769768234824354755152379637670420152320 : ℤ)
  | 36 => (-2317166239128865871291199650388800315758304445353634694252462080 : ℤ)
  | 37 => (2469449143919087738755863731455353972084598162909720424931655680 : ℤ)
  | 38 => (-2658773359108165960633719211045969048321230343840123658163978240 : ℤ)
  | 39 => (2897486976009244030280807068496501728934904004389312581106401280 : ℤ)
  | 40 => (-3226746641210167083030397959770016036855690935477825936063201280 : ℤ)
  | 41 => (3687710667854873752046580788525381226469637718421703689890693120 : ℤ)
  | 42 => (-4609638107355799865746960667863256817437883591150617800527052800 : ℤ)
  | 43 => (4757244202170812615188896929939753294982729003253082493269573632 : ℤ)
  | 44 => (-590423469408881700522683777132107047582727420903811523624828928 : ℤ)
  | 45 => (-5955018919622328309751503441404852847816941040735710927285911552 : ℤ)
  | 46 => (8333641168979777021341443372788250495138871416474348762376962048 : ℤ)
  | 47 => (-6844886221398217797612314083021442623858911787913087741119692800 : ℤ)
  | 48 => (5475909151259355955122854009949629826547708925032336824444387328 : ℤ)
  | 49 => (-4791420328916866759180823529150965850278566490427317433109839872 : ℤ)
  | 50 => (4302500067302945715712541583488184268941147479607496260223762432 : ℤ)
  | 51 => (-3948032552469018350512463322539164275827689538238682064557703168 : ℤ)
  | 52 => (3666903479477565844576994440577968288783791239465243791432089600 : ℤ)
  | 53 => (-3440777585982267042356402309695485185806802396305949864256077824 : ℤ)
  | 54 => (3251321094657013449472167923663872104739595064364559004688449536 : ℤ)
  | 55 => (-3090893889582349690903868459733272962217012193476166347103666176 : ℤ)
  | 56 => (2951857317007787166379221813382205989214358461439002025324969984 : ℤ)
  | 57 => (-2830390963063458852594074408438263009361024241488416064227246080 : ℤ)
  | 58 => (2722675854247705268100211829371180694356259052436490989080674304 : ℤ)
  | 59 => (-2626562702044892654300629137472945577086358077480064025630867456 : ℤ)
  | 60 => (2539903637477801165678274006652025722802065562682097895542358016 : ℤ)
  | 61 => (-2461384939515435519452059915295838725111394840755802990595538944 : ℤ)
  | 62 => (2389694286735154116620435373302263861105279334996702767611904000 : ℤ)
  | 63 => (-2323977524330074027400417588130156818306824039065704109763985408 : ℤ)
  | 64 => (2263381878007306223132520227876207095517491651724754021664161792 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment37 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1283015742150921229564980541262073659384627495672974698044456960 : ℤ)
  | 19 => (-1307042875448545326837796986084158863741931553437802106168803328 : ℤ)
  | 20 => (1332470157294094541508081636205499304893551732043821380976771072 : ℤ)
  | 21 => (-1359448742156368566813108778556633162037312628911001109583101952 : ℤ)
  | 22 => (1388131731459158741008648010093356219196287834212241853474930688 : ℤ)
  | 23 => (-1418721024041334765858187816058336061053286494973890597486592000 : ℤ)
  | 24 => (1451420402783727357593387052648727064488000524789792141748469760 : ℤ)
  | 25 => (-1486506529216349682512738894343480860811765872876013749482291200 : ℤ)
  | 26 => (1524257892105933970948770389768101105104459487457283821933690880 : ℤ)
  | 27 => (-1565065477838044307201733706330758539915949731499230842218086400 : ℤ)
  | 28 => (1609322048372602504385809029291773024149982258035142485931458560 : ℤ)
  | 29 => (-1657601491734128961413085221208916001980452090654488642275246080 : ℤ)
  | 30 => (1710479424242962388783799311644454437352867055576890709293137920 : ℤ)
  | 31 => (-1768839241101142365013537588216458110950293361173371455191121920 : ℤ)
  | 32 => (1833566022304451012866232169454883986256701851194421670293012480 : ℤ)
  | 33 => (-1906105883524880889434782538243653777938343987567095168211353600 : ℤ)
  | 34 => (1987906585009402564022341720181224695495325432840615413311078400 : ℤ)
  | 35 => (-2081539661392268637114182219915099735058207961728289977799802880 : ℤ)
  | 36 => (2189578254541682905725457769768234824354755152379637670420152320 : ℤ)
  | 37 => (-2317166259544043413901200785329701523515835693630783716086251520 : ℤ)
  | 38 => (2469449143919087738755863731455353972084598162909720424931655680 : ℤ)
  | 39 => (-2658773378999877412407566470731975353315747970366576551232798720 : ℤ)
  | 40 => (2897486976009244030280807068496501728934904004389312581106401280 : ℤ)
  | 41 => (-3226746660616714840858541627756363651484488619893877539057172480 : ℤ)
  | 42 => (3687710667854873752046580788525381226469637718421703689890693120 : ℤ)
  | 43 => (-4609638126311032559439566111012712627075313887556993784846745600 : ℤ)
  | 44 => (4757244202170812615188896929939753294982729003253082493269573632 : ℤ)
  | 45 => (-590423487942887001022120210433797172561548155167823597181861888 : ℤ)
  | 46 => (-5955018919622328309751503441404852847816941040735710927285911552 : ℤ)
  | 47 => (8333641150840112259150505587003617606861727719109570988257312768 : ℤ)
  | 48 => (-6844886221398217797612314083021442623858911787913087741119692800 : ℤ)
  | 49 => (5475909133489888432976629240201418017623159997001534106939424768 : ℤ)
  | 50 => (-4791420328916866759180823529150965850278566490427317433109839872 : ℤ)
  | 51 => (4302500049881899125373105534715427593524923040361611243062034432 : ℤ)
  | 52 => (-3948032552469018350512463322539164275827689538238682064557703168 : ℤ)
  | 53 => (3666903462385218246508113788951867399696174808507016982141337600 : ℤ)
  | 54 => (-3440777585982267042356402309695485185806802396305949864256077824 : ℤ)
  | 55 => (3251321077875435807731812374794609413635389841241936319202983936 : ℤ)
  | 56 => (-3090893889582349690903868459733272962217012193476166347103666176 : ℤ)
  | 57 => (2951857300520623167476416361861526854094437540476425351865565184 : ℤ)
  | 58 => (-2830390963063458852594074408438263009361024241488416064227246080 : ℤ)
  | 59 => (2722675838039984726805928504147462222543455435219042733815496704 : ℤ)
  | 60 => (-2626562702044892654300629137472945577086358077480064025630867456 : ℤ)
  | 61 => (2539903621535780961126519916268040340691111185091165185445462016 : ℤ)
  | 62 => (-2461384939515435519452059915295838725111394840755802990595538944 : ℤ)
  | 63 => (2389694271046181851823471030384690945377038518954832481484800000 : ℤ)
  | 64 => (-2323977524330074027400417588130156818306824039065704109763985408 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment38 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1260271120309768424512185277794024962711518974230786892374212608 : ℤ)
  | 19 => (1283015716732058671323362408949185550206235055025763582224629760 : ℤ)
  | 20 => (-1307042875448545326837796986084158863741931553437802106168803328 : ℤ)
  | 21 => (1332470133085654009849397700669415391390320836189334604005507072 : ℤ)
  | 22 => (-1359448742156368566813108778556633162037312628911001109583101952 : ℤ)
  | 23 => (1388131708303259102030776419580580301932327846873167545067634688 : ℤ)
  | 24 => (-1418721024041334765858187816058336061053286494973890597486592000 : ℤ)
  | 25 => (1451420380554063704174630325756462183914598936944280805677465600 : ℤ)
  | 26 => (-1486506529216349682512738894343480860811765872876013749482291200 : ℤ)
  | 27 => (1524257870699591193582560208316290479367109810272717350161612800 : ℤ)
  | 28 => (-1565065477838044307201733706330758539915949731499230842218086400 : ℤ)
  | 29 => (1609322027704409477963261267890024833782886017994871409737728000 : ℤ)
  | 30 => (-1657601491734128961413085221208916001980452090654488642275246080 : ℤ)
  | 31 => (1710479404241485266439398252223407801513741661989531603299205120 : ℤ)
  | 32 => (-1768839241101142365013537588216458110950293361173371455191121920 : ℤ)
  | 33 => (1833566002909079257865600839107202399988459045291527991753441280 : ℤ)
  | 34 => (-1906105883524880889434782538243653777938343987567095168211353600 : ℤ)
  | 35 => (1987906566168184287736014142129191154549032421392090125586923520 : ℤ)
  | 36 => (-2081539661392268637114182219915099735058207961728289977799802880 : ℤ)
  | 37 => (2189578236209686745014436342474364352082686276375667120202055680 : ℤ)
  | 38 => (-2317166259544043413901200785329701523515835693630783716086251520 : ℤ)
  | 39 => (2469449126057142761652817212553634024742582335008415786257612800 : ℤ)
  | 40 => (-2658773378999877412407566470731975353315747970366576551232798720 : ℤ)
  | 41 => (2897486958582956247741249489080189585186595879607551958009774080 : ℤ)
  | 42 => (-3226746660616714840858541627756363651484488619893877539057172480 : ℤ)
  | 43 => (3687710650833848476077710594676890295366639084913937499889336320 : ℤ)
  | 44 => (-4609638126311032559439566111012712627075313887556993784846745600 : ℤ)
  | 45 => (4757244185528032345352668295954562162348685894934377774157135872 : ℤ)
  | 46 => (-590423487942887001022120210433797172561548155167823597181861888 : ℤ)
  | 47 => (-5955018935911006871718876147007380339331110891430613418332127232 : ℤ)
  | 48 => (8333641150840112259150505587003617606861727719109570988257312768 : ℤ)
  | 49 => (-6844886237354474348110964896672898125750343478389726916022108160 : ℤ)
  | 50 => (5475909133489888432976629240201418017623159997001534106939424768 : ℤ)
  | 51 => (-4791420344560255534179500797436706538407421088933826428112207872 : ℤ)
  | 52 => (4302500049881899125373105534715427593524923040361611243062034432 : ℤ)
  | 53 => (-3948032567817248846737580642366683441539018578282804097390215168 : ℤ)
  | 54 => (3666903462385218246508113788951867399696174808507016982141337600 : ℤ)
  | 55 => (-3440777601051438802286517496435231275777925453803815132855271424 : ℤ)
  | 56 => (3251321077875435807731812374794609413635389841241936319202983936 : ℤ)
  | 57 => (-3090893904387150016449244783547760348855308530667051523271294976 : ℤ)
  | 58 => (2951857300520623167476416361861526854094437540476425351865565184 : ℤ)
  | 59 => (-2830390977617330359062410455577928575886807081438777762832711680 : ℤ)
  | 60 => (2722675838039984726805928504147462222543455435219042733815496704 : ℤ)
  | 61 => (-2626562716360176103285877708429993675308439559398452581636243456 : ℤ)
  | 62 => (2539903621535780961126519916268040340691111185091165185445462016 : ℤ)
  | 63 => (-2461384953603492247024844223221822567806141695977074267934162944 : ℤ)
  | 64 => (2389694271046181851823471030384690945377038518954832481484800000 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment39 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1238693363229723041075128377352738357072124101829596803846111232 : ℤ)
  | 19 => (-1260271143186744726929641596875624260972072170813276896612057088 : ℤ)
  | 20 => (1283015716732058671323362408949185550206235055025763582224629760 : ℤ)
  | 21 => (-1307042897236141805330612528066634385894839359706840205442940928 : ℤ)
  | 22 => (1332470133085654009849397700669415391390320836189334604005507072 : ℤ)
  | 23 => (-1359448762996678241893193210018131487574876617516167987149668352 : ℤ)
  | 24 => (1388131708303259102030776419580580301932327846873167545067634688 : ℤ)
  | 25 => (-1418721044048032053935068870261374453569347924034850799950495744 : ℤ)
  | 26 => (1451420380554063704174630325756462183914598936944280805677465600 : ℤ)
  | 27 => (-1486506548482058182142328057650110423975380582342123574077161472 : ℤ)
  | 28 => (1524257870699591193582560208316290479367109810272717350161612800 : ℤ)
  | 29 => (-1565065496439418030982026691592331911246336347535474810792443904 : ℤ)
  | 30 => (1609322027704409477963261267890024833782886017994871409737728000 : ℤ)
  | 31 => (-1657601509735458371523046174687857974235664944883111837669785600 : ℤ)
  | 32 => (1710479404241485266439398252223407801513741661989531603299205120 : ℤ)
  | 33 => (-1768839258556976944514105785529371538591711886485975765876736000 : ℤ)
  | 34 => (1833566002909079257865600839107202399988459045291527991753441280 : ℤ)
  | 35 => (-1906105900481977338092477358490483964790007697870767927163092992 : ℤ)
  | 36 => (1987906566168184287736014142129191154549032421392090125586923520 : ℤ)
  | 37 => (-2081539677891065181754101504479583160103069950131863472996089856 : ℤ)
  | 38 => (2189578236209686745014436342474364352082686276375667120202055680 : ℤ)
  | 39 => (-2317166275619793893293942652341249476123649938741957890892890112 : ℤ)
  | 40 => (2469449126057142761652817212553634024742582335008415786257612800 : ℤ)
  | 41 => (-2658773394683536416693168292206656282689225282670161112019763200 : ℤ)
  | 42 => (2897486958582956247741249489080189585186595879607551958009774080 : ℤ)
  | 43 => (-3226746675935637589230524802220005489477187390050867110058393600 : ℤ)
  | 44 => (3687710650833848476077710594676890295366639084913937499889336320 : ℤ)
  | 45 => (-4609638141289534802292171881599384646445952685043828032047939584 : ℤ)
  | 46 => (4757244185528032345352668295954562162348685894934377774157135872 : ℤ)
  | 47 => (-590423502602697706792755645476071914924301020793235839123456000 : ℤ)
  | 48 => (-5955018935911006871718876147007380339331110891430613418332127232 : ℤ)
  | 49 => (8333641136479481363701719854717307655159439197680595730845138944 : ℤ)
  | 50 => (-6844886237354474348110964896672898125750343478389726916022108160 : ℤ)
  | 51 => (5475909119410838535477819698744251398307190858345676011437293568 : ℤ)
  | 52 => (-4791420344560255534179500797436706538407421088933826428112207872 : ℤ)
  | 53 => (4302500036068491678770499946870660344384726904321901413512773632 : ℤ)
  | 54 => (-3948032567817248846737580642366683441539018578282804097390215168 : ℤ)
  | 55 => (3666903448822963662571010120886095918722164056758938240402063360 : ℤ)
  | 56 => (-3440777601051438802286517496435231275777925453803815132855271424 : ℤ)
  | 57 => (3251321064551115514740973683361570765660923137770139660652118016 : ℤ)
  | 58 => (-3090893904387150016449244783547760348855308530667051523271294976 : ℤ)
  | 59 => (2951857287422138811654913919435827844221232984521099823120646144 : ℤ)
  | 60 => (-2830390977617330359062410455577928575886807081438777762832711680 : ℤ)
  | 61 => (2722675825156229622719204790286118934143582101492493033410658304 : ℤ)
  | 62 => (-2626562716360176103285877708429993675308439559398452581636243456 : ℤ)
  | 63 => (2539903608856529906311014039134654882265839015392021035840700416 : ℤ)
  | 64 => (-2461384953603492247024844223221822567806141695977074267934162944 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment4 (i : ℕ) : ℤ :=
  match i with
  | 18 => (4302523814749680782043471620755776842718972995122570079502336000 : ℤ)
  | 19 => (-3948015757952004030952765031606856612121722465672994924108185600 : ℤ)
  | 20 => (3666926204400712383313651217626912867405669611031859325566976000 : ℤ)
  | 21 => (-3440761451326794378531565445788318978043296252858338914598912000 : ℤ)
  | 22 => (3251342920527852519700994969052136169673230083775775853510656000 : ℤ)
  | 23 => (-3090878341601767959770335186123998183258495083520164647403520000 : ℤ)
  | 24 => (2951878344062126708305401250780913955101067239012028112699392000 : ℤ)
  | 25 => (-2830375941298126676308924467537885151205173837783919587995156480 : ℤ)
  | 26 => (2722696165220294586074625967377995167245977248000711968298106880 : ℤ)
  | 27 => (-2626548155843932102051478041400775316657839368421940483860725760 : ℤ)
  | 28 => (2539923301628054211292614595538550325841086809563013009081630720 : ℤ)
  | 29 => (-2461370825930272534020892400172619518654292251041922288671784960 : ℤ)
  | 30 => (2389713362750119876507567560815121669501651728791186758539673600 : ℤ)
  | 31 => (-2323963806558772155197975890489724662368194767476001142546104320 : ℤ)
  | 32 => (2263400416143625288442720141478863408188395336277931010482503680 : ℤ)
  | 33 => (-2207311404586085035735827965958920587788978510112905870421524480 : ℤ)
  | 34 => (2155242981917797927863501298417380159139234576659747651578757120 : ℤ)
  | 35 => (-2106656542097769667217827492540716350551048969270206414654013440 : ℤ)
  | 36 => (2061264696448294904133928506576891519052449685863001075312754688 : ℤ)
  | 37 => (-2018643004702435138940359478736685084314264898257693979623555072 : ℤ)
  | 38 => (1978611977342787313421059628968413000074884904646040559783247872 : ℤ)
  | 39 => (-1940825437614838862571501325540791807058939513380709337523027968 : ℤ)
  | 40 => (1905176343827514492058686407209666123169321436857899072576552960 : ℤ)
  | 41 => (-1871373986480045072309751750402184807122023317647050427699560448 : ℤ)
  | 42 => (1839361374410168853096599349817837867302597570368754661134958592 : ℤ)
  | 43 => (-1808888257564051542462636895104144058949224377678098138505674752 : ℤ)
  | 44 => (1779933042554338698863655860367083875618165734947992812910542848 : ℤ)
  | 45 => (-1752275746795143487874251886429988832702153395543609299099975680 : ℤ)
  | 46 => (1725920300352877310187234646217181842842301144988237790932107264 : ℤ)
  | 47 => (-1700669877135949369354163573296309008448906742400720332703399936 : ℤ)
  | 48 => (1676547105270341931662405983720711132046610289854199948625575936 : ℤ)
  | 49 => (-1653373234561660421902617006661595444820731792553813324330696704 : ℤ)
  | 50 => (1631184768478535083260765309581307055709749552996249128198471680 : ℤ)
  | 51 => (-1609817325392624983298768970597800864303513422274513913541853184 : ℤ)
  | 52 => (1589317810601585821908939626216763211760710040423193429073330176 : ℤ)
  | 53 => (-1569533454183906777436665981323742819578799864559688976926785536 : ℤ)
  | 54 => (1550519019204773752549688579602801389050823801596812969742106624 : ℤ)
  | 55 => (-1532131262113315529018870702717796028005657790172445342390374400 : ℤ)
  | 56 => (1514430912747773072699143170343053110257402897359773934959607808 : ℤ)
  | 57 => (-1497282651896643170443247193571423726348729014286762667870574592 : ℤ)
  | 58 => (1480751752199669890964210691855537951349486895225017616927301632 : ℤ)
  | 59 => (-1464709570472528995604371334475515598865268972252175588540340608 : ℤ)
  | 60 => (1449224837476500720178559261545190929544875179715018661942248960 : ℤ)
  | 61 => (-1434174600600321843417432423207278527253275344608229615699898304 : ℤ)
  | 62 => (1419630214068118353214172189433783062206474448727848475671224576 : ℤ)
  | 63 => (-1405473628471058742864026431241371371793926723930709095371490896 : ℤ)
  | 64 => (1391778173455593610382698283805905361689285467580393888584289344 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment40 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1218190414581877808756182685853101273579656186765072600905285632 : ℤ)
  | 19 => (1238693342595587552620167775828158597856723179421860721592369152 : ℤ)
  | 20 => (-1260271143186744726929641596875624260972072170813276896612057088 : ℤ)
  | 21 => (1283015697080501063271018978925776255715377033685062551506780160 : ℤ)
  | 22 => (-1307042897236141805330612528066634385894839359706840205442940928 : ℤ)
  | 23 => (1332470114288511949973243115429632587964282728819968400710172672 : ℤ)
  | 24 => (-1359448762996678241893193210018131487574876617516167987149668352 : ℤ)
  | 25 => (1388131690258002724549668017750388810643331263798575989904113664 : ℤ)
  | 26 => (-1418721044048032053935068870261374453569347924034850799950495744 : ℤ)
  | 27 => (1451420363177150155489118531401462970080750375465044493297778688 : ℤ)
  | 28 => (-1486506548482058182142328057650110423975380582342123574077161472 : ℤ)
  | 29 => (1524257853921881560368962613766636066010290509534144358898466816 : ℤ)
  | 30 => (-1565065496439418030982026691592331911246336347535474810792443904 : ℤ)
  | 31 => (1609322011467916284530747466712939917631125404376897547225006080 : ℤ)
  | 32 => (-1657601509735458371523046174687857974235664944883111837669785600 : ℤ)
  | 33 => (1710479388497007018262415172294113337366579854844829676014141440 : ℤ)
  | 34 => (-1768839258556976944514105785529371538591711886485975765876736000 : ℤ)
  | 35 => (1833565987614443245350817275747316349102644718350960405247950848 : ℤ)
  | 36 => (-1906105900481977338092477358490483964790007697870767927163092992 : ℤ)
  | 37 => (1987906551286916816100008512914166888822294157341808149527527424 : ℤ)
  | 38 => (-2081539677891065181754101504479583160103069950131863472996089856 : ℤ)
  | 39 => (2189578221709990234189610344777674041887402839608725707631362048 : ℤ)
  | 40 => (-2317166275619793893293942652341249476123649938741957890892890112 : ℤ)
  | 41 => (2469449111911097385238352824556862990405720445479692456920350720 : ℤ)
  | 42 => (-2658773394683536416693168292206656282689225282670161112019763200 : ℤ)
  | 43 => (2897486944765888670778284272897296946997102871230659403773378560 : ℤ)
  | 44 => (-3226746675935637589230524802220005489477187390050867110058393600 : ℤ)
  | 45 => (3687710637323826845269477938853617493581357032278753669080416256 : ℤ)
  | 46 => (-4609638141289534802292171881599384646445952685043828032047939584 : ℤ)
  | 47 => (4757244172305457983285036334936039845707771545546751046131384320 : ℤ)
  | 48 => (-590423502602697706792755645476071914924301020793235839123456000 : ℤ)
  | 49 => (-5955018948863732777417780925147973629101802498994002866194087936 : ℤ)
  | 50 => (8333641136479481363701719854717307655159439197680595730845138944 : ℤ)
  | 51 => (-6844886250053225236051067620340146449054943093647951864906383360 : ℤ)
  | 52 => (5475909119410838535477819698744251398307190858345676011437293568 : ℤ)
  | 53 => (-4791420357019407348762243092355516214102499956734349019470364672 : ℤ)
  | 54 => (4302500036068491678770499946870660344384726904321901413512773632 : ℤ)
  | 55 => (-3948032580049870628327909441014242032221459648486953550723678208 : ℤ)
  | 56 => (3666903448822963662571010120886095918722164056758938240402063360 : ℤ)
  | 57 => (-3440777613069453184199822982825815154343130715758768981744287744 : ℤ)
  | 58 => (3251321064551115514740973683361570765660923137770139660652118016 : ℤ)
  | 59 => (-3090893916201469239347070515931724161682120483097345137433378816 : ℤ)
  | 60 => (2951857287422138811654913919435827844221232984521099823120646144 : ℤ)
  | 61 => (-2830390989237972217650435766119532326208261460878410825942958080 : ℤ)
  | 62 => (2722675825156229622719204790286118934143582101492493033410658304 : ℤ)
  | 63 => (-2626562727796363329197902617216968794672410535989837500887597056 : ℤ)
  | 64 => (2539903608856529906311014039134654882265839015392021035840700416 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment41 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1198672006691161535326441719341093773255476276485938984064647168 : ℤ)
  | 19 => (-1218190433231961807936627844923394517485883943556680213711552512 : ℤ)
  | 20 => (1238693342595587552620167775828158597856723179421860721592369152 : ℤ)
  | 21 => (-1260271160948729488053875081704474969454193843948141289760882688 : ℤ)
  | 22 => (1283015697080501063271018978925776255715377033685062551506780160 : ℤ)
  | 23 => (-1307042914225866359449444557033361150529912264444536581498339328 : ℤ)
  | 24 => (1332470114288511949973243115429632587964282728819968400710172672 : ℤ)
  | 25 => (-1359448779306813813847271957826189181624546606064356508162850816 : ℤ)
  | 26 => (1388131690258002724549668017750388810643331263798575989904113664 : ℤ)
  | 27 => (-1418721059754088530631589145928392973765326431525699005370597376 : ℤ)
  | 28 => (1451420363177150155489118531401462970080750375465044493297778688 : ℤ)
  | 29 => (-1486506563646526504470002806569990374509428796471218393103466496 : ℤ)
  | 30 => (1524257853921881560368962613766636066010290509534144358898466816 : ℤ)
  | 31 => (-1565065511114709955815260319579312508537350748305566571140481024 : ℤ)
  | 32 => (1609322011467916284530747466712939917631125404376897547225006080 : ℤ)
  | 33 => (-1657601523966044480452242420008566432214830424417746271946670080 : ℤ)
  | 34 => (1710479388497007018262415172294113337366579854844829676014141440 : ℤ)
  | 35 => (-1768839272380974878902467852412345469200044066605334930602852352 : ℤ)
  | 36 => (1833565987614443245350817275747316349102644718350960405247950848 : ℤ)
  | 37 => (-1906105913932353706686559369511755897273790359608522790139854848 : ℤ)
  | 38 => (1987906551286916816100008512914166888822294157341808149527527424 : ℤ)
  | 39 => (-2081539690996560104999617310090053248164191517978906672819601408 : ℤ)
  | 40 => (2189578221709990234189610344777674041887402839608725707631362048 : ℤ)
  | 41 => (-2317166288405642598899323926107561757158890492739073207793876992 : ℤ)
  | 42 => (2469449111911097385238352824556862990405720445479692456920350720 : ℤ)
  | 43 => (-2658773407172039803563540699141193859514343963318506305271889920 : ℤ)
  | 44 => (2897486944765888670778284272897296946997102871230659403773378560 : ℤ)
  | 45 => (-3226746688146618678614888933444886675706192322240360187904917504 : ℤ)
  | 46 => (3687710637323826845269477938853617493581357032278753669080416256 : ℤ)
  | 47 => (-4609638153240707783391762307904587509563702193144182959301984256 : ℤ)
  | 48 => (4757244172305457983285036334936039845707771545546751046131384320 : ℤ)
  | 49 => (-590423514309969198482150348795454311447810743013991686229458944 : ℤ)
  | 50 => (-5955018948863732777417780925147973629101802498994002866194087936 : ℤ)
  | 51 => (8333641125001764214986627008325756286018743391581815488584351744 : ℤ)
  | 52 => (-6844886250053225236051067620340146449054943093647951864906383360 : ℤ)
  | 53 => (5475909108149682087681879547567634960659715727833665207709728768 : ℤ)
  | 54 => (-4791420357019407348762243092355516214102499956734349019470364672 : ℤ)
  | 55 => (4302500025012083530025395071169982387421751321637381715307528192 : ℤ)
  | 56 => (-3948032580049870628327909441014242032221459648486953550723678208 : ℤ)
  | 57 => (3666903437960527586610907085109991259249766993068883800060067840 : ℤ)
  | 58 => (-3440777613069453184199822982825815154343130715758768981744287744 : ℤ)
  | 59 => (3251321053872788524814092732937603473298227719227374278621003776 : ℤ)
  | 60 => (-3090893916201469239347070515931724161682120483097345137433378816 : ℤ)
  | 61 => (2951857276918866362546506427215532146815303064642969939155615744 : ℤ)
  | 62 => (-2830390989237972217650435766119532326208261460878410825942958080 : ℤ)
  | 63 => (2722675814819675783914105353497891422410762180342587433318088704 : ℤ)
  | 64 => (-2626562727796363329197902617216968794672410535989837500887597056 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment42 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1180064991037867841494311963081433540959223739502656374093905920 : ℤ)
  | 19 => (1198671989800519422861132896032148948585685100523728315862745088 : ℤ)
  | 20 => (-1218190433231961807936627844923394517485883943556680213711552512 : ℤ)
  | 21 => (1238693326509261731224635563152973050552160154695945799495319552 : ℤ)
  | 22 => (-1260271160948729488053875081704474969454193843948141289760882688 : ℤ)
  | 23 => (1283015681693580712370944688540816166989273270903752626022645760 : ℤ)
  | 24 => (-1307042914225866359449444557033361150529912264444536581498339328 : ℤ)
  | 25 => (1332470099517068413109171796660070902787223116549910872245403648 : ℤ)
  | 26 => (-1359448779306813813847271957826189181624546606064356508162850816 : ℤ)
  | 27 => (1388131676033649689050932673750070150843199785316298369901002752 : ℤ)
  | 28 => (-1418721059754088530631589145928392973765326431525699005370597376 : ℤ)
  | 29 => (1451420349443292052248960268228741505446140672102845411915464704 : ℤ)
  | 30 => (-1486506563646526504470002806569990374509428796471218393103466496 : ℤ)
  | 31 => (1524257840631051137878486875212389487331635957893306538205904896 : ℤ)
  | 32 => (-1565065511114709955815260319579312508537350748305566571140481024 : ℤ)
  | 33 => (1609321998579838299085437659630034144366975536119115418068582400 : ℤ)
  | 34 => (-1657601523966044480452242420008566432214830424417746271946670080 : ℤ)
  | 35 => (1710479375977159832401257073985004871909977125680127036262187008 : ℤ)
  | 36 => (-1768839272380974878902467852412345469200044066605334930602852352 : ℤ)
  | 37 => (1833565975432970307756176963878994598928652873758276755759562752 : ℤ)
  | 38 => (-1906105913932353706686559369511755897273790359608522790139854848 : ℤ)
  | 39 => (1987906539417789338443692311606571337370712360046372798743969792 : ℤ)
  | 40 => (-2081539690996560104999617310090053248164191517978906672819601408 : ℤ)
  | 41 => (2189578210130353670622472587404410089251713281271715609305939968 : ℤ)
  | 42 => (-2317166288405642598899323926107561757158890492739073207793876992 : ℤ)
  | 43 => (2469449100600754695242543852238791222715046923383077942276915200 : ℤ)
  | 44 => (-2658773407172039803563540699141193859514343963318506305271889920 : ℤ)
  | 45 => (2897486933706886929449048833297404551921777649625080767233130496 : ℤ)
  | 46 => (-3226746688146618678614888933444886675706192322240360187904917504 : ℤ)
  | 47 => (3687710626500123013330226232011169617550187666452017131189960704 : ℤ)
  | 48 => (-4609638153240707783391762307904587509563702193144182959301984256 : ℤ)
  | 49 => (4757244161702646066283320377212825599799687268818519335544815616 : ℤ)
  | 50 => (-590423514309969198482150348795454311447810743013991686229458944 : ℤ)
  | 51 => (-5955018959258646421537110295464850340776394927158935915788763136 : ℤ)
  | 52 => (8333641125001764214986627008325756286018743391581815488584351744 : ℤ)
  | 53 => (-6844886260252008434054937945934063222773411136375810706018140160 : ℤ)
  | 54 => (5475909108149682087681879547567634960659715727833665207709728768 : ℤ)
  | 55 => (-4791420367032758124984224866574998137389723125958064972561907712 : ℤ)
  | 56 => (4302500025012083530025395071169982387421751321637381715307528192 : ℤ)
  | 57 => (-3948032589887548583914417850773733044573819253338323609901334528 : ℤ)
  | 58 => (3666903437960527586610907085109991259249766993068883800060067840 : ℤ)
  | 59 => (-3440777622740390835454356673775823268181043547646556497546051584 : ℤ)
  | 60 => (3251321053872788524814092732937603473298227719227374278621003776 : ℤ)
  | 61 => (-3090893925713866929105628244735010831030887202986972202156425216 : ℤ)
  | 62 => (2951857276918866362546506427215532146815303064642969939155615744 : ℤ)
  | 63 => (-2830390998599379467889016388116417619853079502674551746781511680 : ℤ)
  | 64 => (2722675814819675783914105353497891422410762180342587433318088704 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment43 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1162297728165957644646039059297957115149349017024879934690033664 : ℤ)
  | 19 => (-1180065006364561610212832932380290881863293510283180869314150400 : ℤ)
  | 20 => (1198671989800519422861132896032148948585685100523728315862745088 : ℤ)
  | 21 => (-1218190447828813016239981149017544365965950391919084494873690112 : ℤ)
  | 22 => (1238693326509261731224635563152973050552160154695945799495319552 : ℤ)
  | 23 => (-1260271174910934991648386937794531346261213924990441036959449088 : ℤ)
  | 24 => (1283015681693580712370944688540816166989273270903752626022645760 : ℤ)
  | 25 => (-1307042927629583642900175938879815272264651542245144338808963072 : ℤ)
  | 26 => (1332470099517068413109171796660070902787223116549910872245403648 : ℤ)
  | 27 => (-1359448792214097123836865140344996854406147392094571385573081088 : ℤ)
  | 28 => (1388131676033649689050932673750070150843199785316298369901002752 : ℤ)
  | 29 => (-1418721072216293105793954977325862450933768569761768542180474880 : ℤ)
  | 30 => (1451420349443292052248960268228741505446140672102845411915464704 : ℤ)
  | 31 => (-1486506575706724480433582643406251158865985704441608267435606016 : ℤ)
  | 32 => (1524257840631051137878486875212389487331635957893306538205904896 : ℤ)
  | 33 => (-1565065522809447387052671070450838117610375628761702206856495104 : ℤ)
  | 34 => (1609321998579838299085437659630034144366975536119115418068582400 : ℤ)
  | 35 => (-1657601535326646556511441435140905595314340308289420889499369472 : ℤ)
  | 36 => (1710479375977159832401257073985004871909977125680127036262187008 : ℤ)
  | 37 => (-1768839283434533655608715542811378168431999629291288612546019328 : ℤ)
  | 38 => (1833565975432970307756176963878994598928652873758276755759562752 : ℤ)
  | 39 => (-1906105924702487899374698144772351860628003471969195608443453440 : ℤ)
  | 40 => (1987906539417789338443692311606571337370712360046372798743969792 : ℤ)
  | 41 => (-2081539701504008097866094164002829797778057969062489910188965888 : ℤ)
  | 42 => (2189578210130353670622472587404410089251713281271715609305939968 : ℤ)
  | 43 => (-2317166298668731336117743178766552805618946096123038230340698112 : ℤ)
  | 44 => (2469449100600754695242543852238791222715046923383077942276915200 : ℤ)
  | 45 => (-2658773417207059902177106190629985106897509442182827660651003904 : ℤ)
  | 46 => (2897486933706886929449048833297404551921777649625080767233130496 : ℤ)
  | 47 => (-3226746697968127711300506222987107896549290450490547046361071616 : ℤ)
  | 48 => (3687710626500123013330226232011169617550187666452017131189960704 : ℤ)
  | 49 => (-4609638162861777856226652713986763399369186073879059881871278080 : ℤ)
  | 50 => (4757244161702646066283320377212825599799687268818519335544815616 : ℤ)
  | 51 => (-590423523742390838516356629268175772041422390793282786787590144 : ℤ)
  | 52 => (-5955018959258646421537110295464850340776394927158935915788763136 : ℤ)
  | 53 => (8333641115747312794575707638805350324681614982439869503131090944 : ℤ)
  | 54 => (-6844886260252008434054937945934063222773411136375810706018140160 : ℤ)
  | 55 => (5475909099063493420369340530220327289528716926130663694719254528 : ℤ)
  | 56 => (-4791420367032758124984224866574998137389723125958064972561907712 : ℤ)
  | 57 => (4302500016085301681437637440091925728064980569087064439387062272 : ℤ)
  | 58 => (-3948032589887548583914417850773733044573819253338323609901334528 : ℤ)
  | 59 => (3666903429185047125287348735914613526322772015985521054239948800 : ℤ)
  | 60 => (-3440777622740390835454356673775823268181043547646556497546051584 : ℤ)
  | 61 => (3251321045241168398922068127171658162222494954883083053224165376 : ℤ)
  | 62 => (-3090893925713866929105628244735010831030887202986972202156425216 : ℤ)
  | 63 => (2951857268424256079922609196144284380359820026716842066542854144 : ℤ)
  | 64 => (-2830390998599379467889016388116417619853079502674551746781511680 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment44 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1145311259545293112757109129889943854254333509662552831291293696 : ℤ)
  | 19 => (1162297714232599673083747269026268623418376498133494029944356864 : ℤ)
  | 20 => (-1180065006364561610212832932380290881863293510283180869314150400 : ℤ)
  | 21 => (1198671976530654688039902619582921813603806511103360787533529088 : ℤ)
  | 22 => (-1218190447828813016239981149017544365965950391919084494873690112 : ℤ)
  | 23 => (1238693313816347637047806603071103617091232808293855120223895552 : ℤ)
  | 24 => (-1260271174910934991648386937794531346261213924990441036959449088 : ℤ)
  | 25 => (1283015669508383181961188886862221510866783018357745573922078720 : ℤ)
  | 26 => (-1307042927629583642900175938879815272264651542245144338808963072 : ℤ)
  | 27 => (1332470087783174494936814358006609382076676947431533710963376128 : ℤ)
  | 28 => (-1359448792214097123836865140344996854406147392094571385573081088 : ℤ)
  | 29 => (1388131664704372802539691008843279717053706932374416972801114112 : ℤ)
  | 30 => (-1418721072216293105793954977325862450933768569761768542180474880 : ℤ)
  | 31 => (1451420338479475710463887689286686246940179846675218253431701504 : ℤ)
  | 32 => (-1486506575706724480433582643406251158865985704441608267435606016 : ℤ)
  | 33 => (1524257829999471654935386192601911660901613339296819596645892096 : ℤ)
  | 34 => (-1565065522809447387052671070450838117610375628761702206856495104 : ℤ)
  | 35 => (1609321988252018229940711282236998541549239278053956674838855680 : ℤ)
  | 36 => (-1657601535326646556511441435140905595314340308289420889499369472 : ℤ)
  | 37 => (1710479365928470035395577355440429690790017523238350961768398848 : ℤ)
  | 38 => (-1768839283434533655608715542811378168431999629291288612546019328 : ℤ)
  | 39 => (1833565965641939223494232622732998268606640953430392375483564032 : ℤ)
  | 40 => (-1906105924702487899374698144772351860628003471969195608443453440 : ℤ)
  | 41 => (1987906529865563890383258808049501746812651949970388037499092992 : ℤ)
  | 42 => (-2081539701504008097866094164002829797778057969062489910188965888 : ℤ)
  | 43 => (2189578200800273000423909630441690954288026369104474679717920768 : ℤ)
  | 44 => (-2317166298668731336117743178766552805618946096123038230340698112 : ℤ)
  | 45 => (2469449091478009151048393405430799179639441942597331255568629760 : ℤ)
  | 46 => (-2658773417207059902177106190629985106897509442182827660651003904 : ℤ)
  | 47 => (2897486924778242354280305842804476169337142987579456350454808576 : ℤ)
  | 48 => (-3226746697968127711300506222987107896549290450490547046361071616 : ℤ)
  | 49 => (3687710617753695674389416771936464263181565956693038110672420864 : ℤ)
  | 50 => (-4609638162861777856226652713986763399369186073879059881871278080 : ℤ)
  | 51 => (4757244153127717302615860122237624271987313043564618335037423616 : ℤ)
  | 52 => (-590423523742390838516356629268175772041422390793282786787590144 : ℤ)
  | 53 => (-5955018967671784076456127904119764851082875299106159538928091136 : ℤ)
  | 54 => (8333641115747312794575707638805350324681614982439869503131090944 : ℤ)
  | 55 => (-6844886268512179949793609779886161105619773683378539354191298560 : ℤ)
  | 56 => (5475909099063493420369340530220327289528716926130663694719254528 : ℤ)
  | 57 => (-4791420375148014350973095440282322373168605628276535223398694912 : ℤ)
  | 58 => (4302500016085301681437637440091925728064980569087064439387062272 : ℤ)
  | 59 => (-3948032597865258094208561804587712801780178323414107924283260928 : ℤ)
  | 60 => (3666903429185047125287348735914613526322772015985521054239948800 : ℤ)
  | 61 => (-3440777630587318222628924497199409914613527878868639429724995584 : ℤ)
  | 62 => (3251321045241168398922068127171658162222494954883083053224165376 : ℤ)
  | 63 => (-3090893933436239913309171182072508800535871782919815722713481216 : ℤ)
  | 64 => (2951857268424256079922609196144284380359820026716842066542854144 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment45 (i : ℕ) : ℤ :=
  match i with
  | 18 => (1129047908222314014577979200871796876883377849794127065551732736 : ℤ)
  | 19 => (-1145311272234601265429910581744517302080754910795779280256106496 : ℤ)
  | 20 => (1162297714232599673083747269026268623418376498133494029944356864 : ℤ)
  | 21 => (-1180065018449616993710739077003694165507504368505301296899686400 : ℤ)
  | 22 => (1198671976530654688039902619582921813603806511103360787533529088 : ℤ)
  | 23 => (-1218190459388431209151021809092104028582152082392417077781594112 : ℤ)
  | 24 => (1238693313816347637047806603071103617091232808293855120223895552 : ℤ)
  | 25 => (-1260271186008168456842985971466108622372767547844840316551036928 : ℤ)
  | 26 => (1283015669508383181961188886862221510866783018357745573922078720 : ℤ)
  | 27 => (-1307042938315808461235715749082074871483184660549380682119380992 : ℤ)
  | 28 => (1332470087783174494936814358006609382076676947431533710963376128 : ℤ)
  | 29 => (-1359448802531831431195317370885109570893006954595213372217622528 : ℤ)
  | 30 => (1388131664704372802539691008843279717053706932374416972801114112 : ℤ)
  | 31 => (-1418721082201197274205360361719519918501697178633357561513902080 : ℤ)
  | 32 => (1451420338479475710463887689286686246940179846675218253431701504 : ℤ)
  | 33 => (-1486506585389055795256763622212222036507613446377694589213474816 : ℤ)
  | 34 => (1524257829999471654935386192601911660901613339296819596645892096 : ℤ)
  | 35 => (-1565065532215140664309475449862352684462242578071043205154996224 : ℤ)
  | 36 => (1609321988252018229940711282236998541549239278053956674838855680 : ℤ)
  | 37 => (-1657601544478131907355899750244000849548589231941752671627640832 : ℤ)
  | 38 => (1710479365928470035395577355440429690790017523238350961768398848 : ℤ)
  | 39 => (-1768839292351365535918700567783624826403831913875611887440232448 : ℤ)
  | 40 => (1833565965641939223494232622732998268606640953430392375483564032 : ℤ)
  | 41 => (-1906105933401836075286878656940397380600522774002681730291466240 : ℤ)
  | 42 => (1987906529865563890383258808049501746812651949970388037499092992 : ℤ)
  | 43 => (-2081539710001045851082642571236734724262844264071941471063769088 : ℤ)
  | 44 => (2189578200800273000423909630441690954288026369104474679717920768 : ℤ)
  | 45 => (-2317166306976946028151701621395259844848514917910057534307172352 : ℤ)
  | 46 => (2469449091478009151048393405430799179639441942597331255568629760 : ℤ)
  | 47 => (-2658773425338504068848639985543187741037087437974378468788404224 : ℤ)
  | 48 => (2897486924778242354280305842804476169337142987579456350454808576 : ℤ)
  | 49 => (-3226746705933624037835886266983714558563570936163902940046688256 : ℤ)
  | 50 => (3687710617753695674389416771936464263181565956693038110672420864 : ℤ)
  | 51 => (-4609638170671087980280946874767750322912598314735291150190510080 : ℤ)
  | 52 => (4757244153127717302615860122237624271987313043564618335037423616 : ℤ)
  | 53 => (-590423531404355488531890522864615772499109872388075729289478144 : ℤ)
  | 54 => (-5955018967671784076456127904119764851082875299106159538928091136 : ℤ)
  | 55 => (8333641108224656592742274361456118324232249091419527341401964544 : ℤ)
  | 56 => (-6844886268512179949793609779886161105619773683378539354191298560 : ℤ)
  | 57 => (5475909091672813643129476257736871289087234647233485430564323328 : ℤ)
  | 58 => (-4791420375148014350973095440282322373168605628276535223398694912 : ℤ)
  | 59 => (4302500008819887663134042053582765592037760701696618010217807872 : ℤ)
  | 60 => (-3948032597865258094208561804587712801780178323414107924283260928 : ℤ)
  | 61 => (3666903422038738254824795896725275687607473785765409812434124800 : ℤ)
  | 62 => (-3440777630587318222628924497199409914613527878868639429724995584 : ℤ)
  | 63 => (3251321038208293002593841523525008225709026855301386275573989376 : ℤ)
  | 64 => (-3090893933436239913309171182072508800535871782919815722713481216 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment46 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-1113459551494396681013507644858379978663802910434459188539162624 : ℤ)
  | 19 => (1129047896646103068279984893916747415708396922444516971759271936 : ℤ)
  | 20 => (-1145311272234601265429910581744517302080754910795779280256106496 : ℤ)
  | 21 => (1162297703207636867085657452878602469918394662562436797761060864 : ℤ)
  | 22 => (-1180065018449616993710739077003694165507504368505301296899686400 : ℤ)
  | 23 => (1198671965985038090998251491093849840690780407513653869792985088 : ℤ)
  | 24 => (-1218190459388431209151021809092104028582152082392417077781594112 : ℤ)
  | 25 => (1238693303692555703887821519721594523094727748847736479192973312 : ℤ)
  | 26 => (-1260271186008168456842985971466108622372767547844840316551036928 : ℤ)
  | 27 => (1283015659759546505584906954747879420351629998150372067744153600 : ℤ)
  | 28 => (-1307042938315808461235715749082074871483184660549380682119380992 : ℤ)
  | 29 => (1332470078370504600504542147689313570544805065852000670515724288 : ℤ)
  | 30 => (-1359448802531831431195317370885109570893006954595213372217622528 : ℤ)
  | 31 => (1388131655595337420831040482729767641377701885684546288496934912 : ℤ)
  | 32 => (-1418721082201197274205360361719519918501697178633357561513902080 : ℤ)
  | 33 => (1451420329646471703958529603358432112951326468066858801985224704 : ℤ)
  | 34 => (-1486506585389055795256763622212222036507613446377694589213474816 : ℤ)
  | 35 => (1524257821418839191473038337700179073598155771505841843812171776 : ℤ)
  | 36 => (-1565065532215140664309475449862352684462242578071043205154996224 : ℤ)
  | 37 => (1609321979903294751977345801792069537686415698581653996406046720 : ℤ)
  | 38 => (-1657601544478131907355899750244000849548589231941752671627640832 : ℤ)
  | 39 => (1710479357793816390200503297571011687026240702214056044321046528 : ℤ)
  | 40 => (-1768839292351365535918700567783624826403831913875611887440232448 : ℤ)
  | 41 => (1833565957705691764767331102860395338105395274382299773095903232 : ℤ)
  | 42 => (-1906105933401836075286878656940397380600522774002681730291466240 : ℤ)
  | 43 => (1987906522113880326045354997941377954230039891365274332841377792 : ℤ)
  | 44 => (-2081539710001045851082642571236734724262844264071941471063769088 : ℤ)
  | 45 => (2189578193220849070849070349447081023762805689579474612941488128 : ℤ)
  | 46 => (-2317166306976946028151701621395259844848514917910057534307172352 : ℤ)
  | 47 => (2469449084059849560400678364457351162529651490296267360425738240 : ℤ)
  | 48 => (-2658773425338504068848639985543187741037087437974378468788404224 : ℤ)
  | 49 => (2897486917511473775686625802667220968903062544509026412355649536 : ℤ)
  | 50 => (-3226746705933624037835886266983714558563570936163902940046688256 : ℤ)
  | 51 => (3687710610629412754199534379645037596089330228192616602732068864 : ℤ)
  | 52 => (-4609638170671087980280946874767750322912598314735291150190510080 : ℤ)
  | 53 => (4757244146137854814882390605272450938236440253337789685737455616 : ℤ)
  | 54 => (-590423531404355488531890522864615772499109872388075729289478144 : ℤ)
  | 55 => (-5955018974534558155321716157140116851492823129510682212786241536 : ℤ)
  | 56 => (8333641108224656592742274361456118324232249091419527341401964544 : ℤ)
  | 57 => (-6844886275254554483415942098642998158654108393951403735525621760 : ℤ)
  | 58 => (5475909091672813643129476257736871289087234647233485430564323328 : ℤ)
  | 59 => (-4791420381776111350127252634992433374456595682737995123693453312 : ℤ)
  | 60 => (4302500008819887663134042053582765592037760701696618010217807872 : ℤ)
  | 61 => (-3948032604384697765507732815777985917801152147474560285228924928 : ℤ)
  | 62 => (3666903422038738254824795896725275687607473785765409812434124800 : ℤ)
  | 63 => (-3440777637003274724542394381227932663713533864451941753195331584 : ℤ)
  | 64 => (3251321038208293002593841523525008225709026855301386275573989376 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment5 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-4791402784472327105762049373007809171128710800332717663505612800 : ℤ)
  | 19 => (4302512717949701269678601973931296718513457704116040459773542400 : ℤ)
  | 20 => (-3948015757952004030952765031606856612121722465672994924108185600 : ℤ)
  | 21 => (3666915636019779514394727744460741320543274095787545402015744000 : ℤ)
  | 22 => (-3440761451326794378531565445788318978043296252858338914598912000 : ℤ)
  | 23 => (3251332811641742818995937733849711211804851764846432100548608000 : ℤ)
  | 24 => (-3090878341601767959770335186123998183258495083520164647403520000 : ℤ)
  | 25 => (2951868639531461395628546304986585995547424052839858109855825920 : ℤ)
  | 26 => (-2830375941298126676308924467537885151205173837783919587995156480 : ℤ)
  | 27 => (2722686820116690951645061945501975650638765290946029743337635840 : ℤ)
  | 28 => (-2626548155843932102051478041400775316657839368421940483860725760 : ℤ)
  | 29 => (2539914278769402426326138988209979758082399402751595688430141440 : ℤ)
  | 30 => (-2461370825930272534020892400172619518654292251041922288671784960 : ℤ)
  | 31 => (2389704630951424600733558908561666281348083270586589351457587200 : ℤ)
  | 32 => (-2323963806558772155197975890489724662368194767476001142546104320 : ℤ)
  | 33 => (2263391948944890475570954175657330910584935013170442615736238080 : ℤ)
  | 34 => (-2207311404586085035735827965958920587788978510112905870421524480 : ℤ)
  | 35 => (2155234756639026966788071503047891447181587405641044639539527680 : ℤ)
  | 36 => (-2106656542097769667217827492540716350551048969270206414654013440 : ℤ)
  | 37 => (2061256693474355590655131948920091691201765951898857604139450368 : ℤ)
  | 38 => (-2018643004702435138940359478736685084314264898257693979623555072 : ℤ)
  | 39 => (1978604179573307982339155290738710603707552035655336664793874432 : ℤ)
  | 40 => (-1940825437614838862571501325540791807058939513380709337523027968 : ℤ)
  | 41 => (1905168736247534656856828516253858907201191808574285516489359360 : ℤ)
  | 42 => (-1871373986480045072309751750402184807122023317647050427699560448 : ℤ)
  | 43 => (1839353943750653665225017223767979656356982584603364676119560192 : ℤ)
  | 44 => (-1808888257564051542462636895104144058949224377678098138505674752 : ℤ)
  | 45 => (1779925777020590515166997781562778069360231082199611494228819968 : ℤ)
  | 46 => (-1752275746795143487874251886429988832702153395543609299099975680 : ℤ)
  | 47 => (1725913189404953555930930994621478287781343825277056074775527424 : ℤ)
  | 48 => (-1700669877135949369354163573296309008448906742400720332703399936 : ℤ)
  | 49 => (1676540139443804376472557508688185200558325568504470920553824256 : ℤ)
  | 50 => (-1653373234561660421902617006661595444820731792553813324330696704 : ℤ)
  | 51 => (1631177939236831597780521706608242416995744924222004983030087680 : ℤ)
  | 52 => (-1609817325392624983298768970597800864303513422274513913541853184 : ℤ)
  | 53 => (1589311110213499383324549676129982811513007385776765211172274176 : ℤ)
  | 54 => (-1569533454183906777436665981323742819578799864559688976926785536 : ℤ)
  | 55 => (1550512440641925249212287537699416996080352104307592537621069824 : ℤ)
  | 56 => (-1532131262113315529018870702717796028005657790172445342390374400 : ℤ)
  | 57 => (1514424449598307876437836883560780724181150001777381931472273408 : ℤ)
  | 58 => (-1497282651896643170443247193571423726348729014286762667870574592 : ℤ)
  | 59 => (1480745398595110884470045189594998995545712862279615308414328832 : ℤ)
  | 60 => (-1464709570472528995604371334475515598865268972252175588540340608 : ℤ)
  | 61 => (1449218588029393500676101390469250973016572852227737702749160960 : ℤ)
  | 62 => (-1434174600600321843417432423207278527253275344608229615699898304 : ℤ)
  | 63 => (1419624063818584264180007300438413581178621364534016420592312576 : ℤ)
  | 64 => (-1405473628471058742864026431241371371793926723930709095371490896 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment6 (i : ℕ) : ℤ :=
  match i with
  | 18 => (5475922363079423158161790281797039427306588617701528563823411200 : ℤ)
  | 19 => (-4791410617507606761549016182530971611744368652807915042137702400 : ℤ)
  | 20 => (4302512717949701269678601973931296718513457704116040459773542400 : ℤ)
  | 21 => (-3948023217985603703130828659724154174612825182316040046614937600 : ℤ)
  | 22 => (3666915636019779514394727744460741320543274095787545402015744000 : ℤ)
  | 23 => (-3440768587011107108441017611813560124773916242690816857866240000 : ℤ)
  | 24 => (3251332811641742818995937733849711211804851764846432100548608000 : ℤ)
  | 25 => (-3090885191858708180483409265508229684119890273759343472940154880 : ℤ)
  | 26 => (2951868639531461395628546304986585995547424052839858109855825920 : ℤ)
  | 27 => (-2830382537841846888847440247685663633516146983940165864437841920 : ℤ)
  | 28 => (2722686820116690951645061945501975650638765290946029743337635840 : ℤ)
  | 29 => (-2626554524920627479674872587750354540958089302641764474908835840 : ℤ)
  | 30 => (2539914278769402426326138988209979758082399402751595688430141440 : ℤ)
  | 31 => (-2461376989552880963979016154704470380880340574480461634847375360 : ℤ)
  | 32 => (2389704630951424600733558908561666281348083270586589351457587200 : ℤ)
  | 33 => (-2323969783404937905460398925187277013617696172022463538837585920 : ℤ)
  | 34 => (2263391948944890475570954175657330910584935013170442615736238080 : ℤ)
  | 35 => (-2207317210665217478847896056807971443288494160243755055390392320 : ℤ)
  | 36 => (2155234756639026966788071503047891447181587405641044639539527680 : ℤ)
  | 37 => (-2106662191255844476732272121474927993739766899127248864893992960 : ℤ)
  | 38 => (2061256693474355590655131948920091691201765951898857604139450368 : ℤ)
  | 39 => (-2018648509010302902056997835134122069985323394015837905498406912 : ℤ)
  | 40 => (1978604179573307982339155290738710603707552035655336664793874432 : ℤ)
  | 41 => (-1940830807671295216831636307391949841859972192169142435937517568 : ℤ)
  | 42 => (1905168736247534656856828516253858907201191808574285516489359360 : ℤ)
  | 43 => (-1871379231651467557866162662907967073671869189952031593592782848 : ℤ)
  | 44 => (1839353943750653665225017223767979656356982584603364676119560192 : ℤ)
  | 45 => (-1808893386176109083895572009554242275131295897265190834045714432 : ℤ)
  | 46 => (1779925777020590515166997781562778069360231082199611494228819968 : ℤ)
  | 47 => (-1752280766287795549702230934615191342156946797692678745798737920 : ℤ)
  | 48 => (1725913189404953555930930994621478287781343825277056074775527424 : ℤ)
  | 49 => (-1700674794189975878899938967436915548322990075118176117224636416 : ℤ)
  | 50 => (1676540139443804376472557508688185200558325568504470920553824256 : ℤ)
  | 51 => (-1653378055202862882241612491113170483912970354041515073861320704 : ℤ)
  | 52 => (1631177939236831597780521706608242416995744924222004983030087680 : ℤ)
  | 53 => (-1609822055078333057593632464776704676243068237319051479119069184 : ℤ)
  | 54 => (1589311110213499383324549676129982811513007385776765211172274176 : ℤ)
  | 55 => (-1569538097875329250380713775608484744028544592057962223129870336 : ℤ)
  | 56 => (1550512440641925249212287537699416996080352104307592537621069824 : ℤ)
  | 57 => (-1532135824336467432262145728681753006412424539995310286028492800 : ℤ)
  | 58 => (1514424449598307876437836883560780724181150001777381931472273408 : ℤ)
  | 59 => (-1497287136793978939733246371637686518680804802248223120938555392 : ℤ)
  | 60 => (1480745398595110884470045189594998995545712862279615308414328832 : ℤ)
  | 61 => (-1464713981846957621135518066999708509355835321066726853853108608 : ℤ)
  | 62 => (1449218588029393500676101390469250973016572852227737702749160960 : ℤ)
  | 63 => (-1434178941952934141559195874262833455037642227568581654579130304 : ℤ)
  | 64 => (1419624063818584264180007300438413581178621364534016420592312576 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment7 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-6844876082186583461877504491798783689243409528218941919749734400 : ℤ)
  | 19 => (5475916705887276740093425363808088775750835724247219345922457600 : ℤ)
  | 20 => (-4791410617507606761549016182530971611744368652807915042137702400 : ℤ)
  | 21 => (4302507330147657061994444909179915145603216853207174537963110400 : ℤ)
  | 22 => (-3948023217985603703130828659724154174612825182316040046614937600 : ℤ)
  | 23 => (3666910482469998098349012291220289381237826325352977998544896000 : ℤ)
  | 24 => (-3440768587011107108441017611813560124773916242690816857866240000 : ℤ)
  | 25 => (3251327864233952659592050898738877350071621905229247393216593920 : ℤ)
  | 26 => (-3090885191858708180483409265508229684119890273759343472940154880 : ℤ)
  | 27 => (2951863875360996797684062685990968202767276780615902465758330880 : ℤ)
  | 28 => (-2830382537841846888847440247685663633516146983940165864437841920 : ℤ)
  | 29 => (2722682220227966512250388106471723988644140338453934638691778560 : ℤ)
  | 30 => (-2626554524920627479674872587750354540958089302641764474908835840 : ℤ)
  | 31 => (2539909827264185226911938498825865246474697835823761716192215040 : ℤ)
  | 32 => (-2461376989552880963979016154704470380880340574480461634847375360 : ℤ)
  | 33 => (2389700314340304892210697827946767361001221145080810954135961600 : ℤ)
  | 34 => (-2323969783404937905460398925187277013617696172022463538837585920 : ℤ)
  | 35 => (2263387755665517044434460554488571959390840376964829315480944640 : ℤ)
  | 36 => (-2207317210665217478847896056807971443288494160243755055390392320 : ℤ)
  | 37 => (2155230676691528493249861493262071927100846678522069536588431360 : ℤ)
  | 38 => (-2106662191255844476732272121474927993739766899127248864893992960 : ℤ)
  | 39 => (2061252718140895539515337580410831645994890371629086991007612928 : ℤ)
  | 40 => (-2018648509010302902056997835134122069985323394015837905498406912 : ℤ)
  | 41 => (1978600301199200615373502248290652023017917323197023871494520832 : ℤ)
  | 42 => (-1940830807671295216831636307391949841859972192169142435937517568 : ℤ)
  | 43 => (1905164948068173972843865079444127270248525345242910230010920960 : ℤ)
  | 44 => (-1871379231651467557866162662907967073671869189952031593592782848 : ℤ)
  | 45 => (1839350239753056551967897418887353166892153153790464396007309312 : ℤ)
  | 46 => (-1808893386176109083895572009554242275131295897265190834045714432 : ℤ)
  | 47 => (1779922151831452914957901802317909590309546958425283560501936128 : ℤ)
  | 48 => (-1752280766287795549702230934615191342156946797692678745798737920 : ℤ)
  | 49 => (1725909638199267743481204321075484675650061418314449119287967744 : ℤ)
  | 50 => (-1700674794189975878899938967436915548322990075118176117224636416 : ℤ)
  | 51 => (1676536657869602599561060769917603227880597718541130768115040256 : ℤ)
  | 52 => (-1653378055202862882241612491113170483912970354041515073861320704 : ℤ)
  | 53 => (1631174523352709099678675849701256330594955335578727852335431680 : ℤ)
  | 54 => (-1609822055078333057593632464776704676243068237319051479119069184 : ℤ)
  | 55 => (1589307756436360930642737380257669199410413971472456755581157376 : ℤ)
  | 56 => (-1569538097875329250380713775608484744028544592057962223129870336 : ℤ)
  | 57 => (1550509145702982207981033352281003622786576118324412300549095424 : ℤ)
  | 58 => (-1532135824336467432262145728681753006412424539995310286028492800 : ℤ)
  | 59 => (1514421210505787598617281921624035374163539710471882715367620608 : ℤ)
  | 60 => (-1497287136793978939733246371637686518680804802248223120938555392 : ℤ)
  | 61 => (1480742212602467988253105882771970782413637165913550505688440832 : ℤ)
  | 62 => (-1464713981846957621135518066999708509355835321066726853853108608 : ℤ)
  | 63 => (1449215452608062396462605564706905747394530103423039008003048960 : ℤ)
  | 64 => (-1434178941952934141559195874262833455037642227568581654579130304 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment8 (i : ℕ) : ℤ :=
  match i with
  | 18 => (8333649054588156230696661983471142564378294556378950249165619200 : ℤ)
  | 19 => (-6844880250643954506769983905053799958810806397080011869782016000 : ℤ)
  | 20 => (5475916705887276740093425363808088775750835724247219345922457600 : ℤ)
  | 21 => (-4791414587467007756684710861821463297046651385056553089787494400 : ℤ)
  | 22 => (4302507330147657061994444909179915145603216853207174537963110400 : ℤ)
  | 23 => (-3948027015338074220217145309480276656206313013162563396540825600 : ℤ)
  | 24 => (3666910482469998098349012291220289381237826325352977998544896000 : ℤ)
  | 25 => (-3440772232469478804843881595579437707103664560303479273795092480 : ℤ)
  | 26 => (3251327864233952659592050898738877350071621905229247393216593920 : ℤ)
  | 27 => (-3090888702300103147389870879505000689326314579608573947538309120 : ℤ)
  | 28 => (2951863875360996797684062685990968202767276780615902465758330880 : ℤ)
  | 29 => (-2830385927233538581032989392234270121301660106829078046808473600 : ℤ)
  | 30 => (2722682220227966512250388106471723988644140338453934638691778560 : ℤ)
  | 31 => (-2626557804977103310822178211507070496879553615114905296557834240 : ℤ)
  | 32 => (2539909827264185226911938498825865246474697835823761716192215040 : ℤ)
  | 33 => (-2461380170213706012364282214104922216925396877484719401294888960 : ℤ)
  | 34 => (2389700314340304892210697827946767361001221145080810954135961600 : ℤ)
  | 35 => (-2323972873189739381034657382890573082918608009226599654815170560 : ℤ)
  | 36 => (2263387755665517044434460554488571959390840376964829315480944640 : ℤ)
  | 37 => (-2207320216942321617244471853492259510716408380226157762828042240 : ℤ)
  | 38 => (2155230676691528493249861493262071927100846678522069536588431360 : ℤ)
  | 39 => (-2106665120448920303887910077218593290207991010904974579833241600 : ℤ)
  | 40 => (2061252718140895539515337580410831645994890371629086991007612928 : ℤ)
  | 41 => (-2018651366759645172452742182201112603125054234774594700561088512 : ℤ)
  | 42 => (1978600301199200615373502248290652023017917323197023871494520832 : ℤ)
  | 43 => (-1940833598961350457683293576620173153298779059886997910184787968 : ℤ)
  | 44 => (1905164948068173972843865079444127270248525345242910230010920960 : ℤ)
  | 45 => (-1871381960912854904476671992820007644856480349498379168412336128 : ℤ)
  | 46 => (1839350239753056551967897418887353166892153153790464396007309312 : ℤ)
  | 47 => (-1808896057368105210365432204787303259694957883204169311528681472 : ℤ)
  | 48 => (1779922151831452914957901802317909590309546958425283560501936128 : ℤ)
  | 49 => (-1752283382965669306244134799333291898464207518612494397210624000 : ℤ)
  | 50 => (1725909638199267743481204321075484675650061418314449119287967744 : ℤ)
  | 51 => (-1700677359560440346097883932846818054506579017196426755863740416 : ℤ)
  | 52 => (1676536657869602599561060769917603227880597718541130768115040256 : ℤ)
  | 53 => (-1653380572170111038737709438307791810734604787778666643846856704 : ℤ)
  | 54 => (1631174523352709099678675849701256330594955335578727852335431680 : ℤ)
  | 55 => (-1609824526282540338517073103840514706213400226806436656923049984 : ℤ)
  | 56 => (1589307756436360930642737380257669199410413971472456755581157376 : ℤ)
  | 57 => (-1569540525725076754445848438548368282245011108045568713603956736 : ℤ)
  | 58 => (1550509145702982207981033352281003622786576118324412300549095424 : ℤ)
  | 59 => (-1532138211036219215919396753266723264320137386220414971579289600 : ℤ)
  | 60 => (1514421210505787598617281921624035374163539710471882715367620608 : ℤ)
  | 61 => (-1497289484367505284314149018770444149409702683781112975578683392 : ℤ)
  | 62 => (1480742212602467988253105882771970782413637165913550505688440832 : ℤ)
  | 63 => (-1464716292157412118977041307035120780866814188607031155244980608 : ℤ)
  | 64 => (1449215452608062396462605564706905747394530103423039008003048960 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment9 (i : ℕ) : ℤ :=
  match i with
  | 18 => (-5955012688916241222319521114844126378758999604279704267050188800 : ℤ)
  | 19 => (8333645928245127947027302423529880362202746904733147786641408000 : ℤ)
  | 20 => (-6844880250643954506769983905053799958810806397080011869782016000 : ℤ)
  | 21 => (5475913728417725993741654354340220011774123675060740810185113600 : ℤ)
  | 22 => (-4791414587467007756684710861821463297046651385056553089787494400 : ℤ)
  | 23 => (4302504482133304174179707421862823284408100980072282025518694400 : ℤ)
  | 24 => (-3948027015338074220217145309480276656206313013162563396540825600 : ℤ)
  | 25 => (3666907748376219326046864303395881194490515087143481186598256640 : ℤ)
  | 26 => (-3440772232469478804843881595579437707103664560303479273795092480 : ℤ)
  | 27 => (3251325231402906434412204688241299096166803675842324537267978240 : ℤ)
  | 28 => (-3090888702300103147389870879505000689326314579608573947538309120 : ℤ)
  | 29 => (2951861333317228028544900827579513336928141938449218328980357120 : ℤ)
  | 30 => (-2830385927233538581032989392234270121301660106829078046808473600 : ℤ)
  | 31 => (2722679760185609638889908888654187021703042104099079022455029760 : ℤ)
  | 32 => (-2626557804977103310822178211507070496879553615114905296557834240 : ℤ)
  | 33 => (2539907441768566440622988954275526369440905608570568391356579840 : ℤ)
  | 34 => (-2461380170213706012364282214104922216925396877484719401294888960 : ℤ)
  | 35 => (2389697997001703785530003984669295309025537267177708867152773120 : ℤ)
  | 36 => (-2323972873189739381034657382890573082918608009226599654815170560 : ℤ)
  | 37 => (2263385500957688940637028706975355908819904711978027284902707200 : ℤ)
  | 38 => (-2207320216942321617244471853492259510716408380226157762828042240 : ℤ)
  | 39 => (2155228479796721622883133026454322954749678594688775250383994880 : ℤ)
  | 40 => (-2106665120448920303887910077218593290207991010904974579833241600 : ℤ)
  | 41 => (2061250574828888836718529320110588746140092241060019394710601728 : ℤ)
  | 42 => (-2018651366759645172452742182201112603125054234774594700561088512 : ℤ)
  | 43 => (1978598207731659184734759296369484539438812172408632265809068032 : ℤ)
  | 44 => (-1940833598961350457683293576620173153298779059886997910184787968 : ℤ)
  | 45 => (1905162901122133462885983082010096841860066975583149548896256000 : ℤ)
  | 46 => (-1871381960912854904476671992820007644856480349498379168412336128 : ℤ)
  | 47 => (1839348236359059457115502272462557428469406664336230537895084032 : ℤ)
  | 48 => (-1808896057368105210365432204787303259694957883204169311528681472 : ℤ)
  | 49 => (1779920189323047597551473903779334173079101417735421821943021568 : ℤ)
  | 50 => (-1752283382965669306244134799333291898464207518612494397210624000 : ℤ)
  | 51 => (1725907714171419393082745597018057796012369711755761140308639744 : ℤ)
  | 52 => (-1700677359560440346097883932846818054506579017196426755863740416 : ℤ)
  | 53 => (1676534770144166482188988059521637232764371893238267090625888256 : ℤ)
  | 54 => (-1653380572170111038737709438307791810734604787778666643846856704 : ℤ)
  | 55 => (1631172669949553638986095370403398808117206343463188968982446080 : ℤ)
  | 56 => (-1609824526282540338517073103840514706213400226806436656923049984 : ℤ)
  | 57 => (1589305935549050302593886383052756545748064084481751887725592576 : ℤ)
  | 58 => (-1569540525725076754445848438548368282245011108045568713603956736 : ℤ)
  | 59 => (1550507355678168370238095083842275929355791483655583786385997824 : ℤ)
  | 60 => (-1532138211036219215919396753266723264320137386220414971579289600 : ℤ)
  | 61 => (1514419449825642840181604936274467151116866299322215324387524608 : ℤ)
  | 62 => (-1497289484367505284314149018770444149409702683781112975578683392 : ℤ)
  | 63 => (1480740479869627114871963452745411578780403015258322279644536832 : ℤ)
  | 64 => (-1464716292157412118977041307035120780866814188607031155244980608 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta0 (i : ℕ) : ℤ :=
  match i with
  | 19 => (14604765891202278760652024632662355518097474241943306240000 : ℤ)
  | 20 => (13964480641219095734629243288345408624636864048164293836800 : ℤ)
  | 21 => (13378534916037446881442878555241876154987605710594690252800 : ℤ)
  | 22 => (12840242744402541221868826048172854889718975848917028044800 : ℤ)
  | 23 => (12343977821897943528348076912857504474480678433662487756800 : ℤ)
  | 24 => (11884970678507862807508640844722526098432412163496529100800 : ℤ)
  | 25 => (11459150876977012670532416862841445203334494948773687459840 : ℤ)
  | 26 => (11063022962235289274034572979388897598226204322197185495040 : ℤ)
  | 27 => (10693568007092393417191261797030246086651113933891939860480 : ℤ)
  | 28 => (10348164781125837653403001018390101371308992884686014382080 : ℤ)
  | 29 => (10024526114764323279666079648605249742265395401194345594880 : ℤ)
  | 30 => (9720647139271499797563713513029948145410583029647440609280 : ℤ)
  | 31 => (9434762888649883965140197006610845184350567443916841287680 : ℤ)
  | 32 => (9165313341075657533736256747468462846867939922398207279104 : ℤ)
  | 33 => (8910914416655047739135786992703349781339709953419283267584 : ℤ)
  | 34 => (8670333777540932459883276671335441172061102199313084186624 : ℤ)
  | 35 => (8442470525556174407658486769560060717366506167611040989184 : ℤ)
  | 36 => (8226338082571968369268402186440346570224760634700887752704 : ℤ)
  | 37 => (8021049685138442370155451654235270213484587712531629342720 : ℤ)
  | 38 => (7825806038235468039909053945779521502914058942099352453120 : ℤ)
  | 39 => (7639884761527682800739994486097488383075715416540389048320 : ℤ)
  | 40 => (7462631331087579565248540256191679051935447000255320555520 : ℤ)
  | 41 => (7293451274596651644461831906998375718982234761201838981120 : ℤ)
  | 42 => (7131803421847878477089243208545430452671839845527962255360 : ℤ)
  | 43 => (6977194047446913630012429270500573742197384552907339202560 : ℤ)
  | 44 => (6829171770841434078843230790300145693196502594782138204160 : ℤ)
  | 45 => (6687323101651537951100278969204412698191108261440504463360 : ℤ)
  | 46 => (6551268536849278508818347615150240144638172851005984604160 : ℤ)
  | 47 => (6420659131511523104417798479077645956084991017934378762240 : ℤ)
  | 48 => (6295173477325463523238432462190041448996368522765444055040 : ℤ)
  | 49 => (6174515033292354546613487545040998302497767203880241725440 : ℤ)
  | 50 => (6058409761572127408309258441544988899653835563341510082560 : ℤ)
  | 51 => (5946604028472175447605345077529773743726144255480414863360 : ℤ)
  | 52 => (5838862736472959495862562852566563566863405480859423211520 : ℤ)
  | 53 => (5734967658113347528223391465287519274119839574946396241920 : ℤ)
  | 54 => (5634715946700422570256080046105564646656337639791258501120 : ℤ)
  | 55 => (5537918802299658965134435084387685510928873974211406725120 : ℤ)
  | 56 => (5444400274413615152839113469998209350742978952721827102720 : ℤ)
  | 57 => (5353996185261587072397054513785696962865168346506411900928 : ℤ)
  | 58 => (5266553159703351791228742649264391094129228506521600524288 : ℤ)
  | 59 => (5181927749668186051622093442031938025922535665709317357568 : ℤ)
  | 60 => (5099985642505967332695254222262833608228582229891390373888 : ℤ)
  | 61 => (5020600944011820475630052879200801158016156969932347670528 : ℤ)
  | 62 => (4943655528023825150660540539374285322392983982581250785280 : ℤ)
  | 63 => (4869038445483319302259522694657995493298936028867728506880 : ℤ)
  | 64 => (4796645386703148828733270515780054375331372773542650183680 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta1 (i : ℕ) : ℤ :=
  match i with
  | 19 => (9631950764387236336126336111423212322571994250333913088000 : ℤ)
  | 20 => (9213089124016444221905027492063066520139187684394192076800 : ℤ)
  | 21 => (8829550386756396173917817440155609578962305421927042252800 : ℤ)
  | 22 => (8477010582232142755309244791060704338661890658277313740800 : ℤ)
  | 23 => (8151828164240945970784480708521299239320465798874320076800 : ℤ)
  | 24 => (7850913849243081412725579295691430309515439635704892620800 : ℤ)
  | 25 => (7571629264759195176511043132243094900065782917457237770240 : ℤ)
  | 26 => (7311707209910986102265495985457376743366582212197445795840 : ℤ)
  | 27 => (7069188319875411837925686208574609451590436501790434263040 : ℤ)
  | 28 => (6842370316245368746657692410887896802395194964214001172480 : ℤ)
  | 29 => (6629767010652848316336106438666453786510174569134901166080 : ℤ)
  | 30 => (6430074936640433587168081554872390410293204362828269486080 : ℤ)
  | 31 => (6242145999151606546759199228772342340276204605422205665280 : ℤ)
  | 32 => (6064964909158737378423323793736289560626638345448644935680 : ℤ)
  | 33 => (5897630451872121449647167571347681635984129887519956271104 : ℤ)
  | 34 => (5739339847722203892814023968821415076658364919566863171584 : ℤ)
  | 35 => (5589375624863312723456421162421561744656367023570733236224 : ℤ)
  | 36 => (5447094543786266330576821691449344607389680302305977565184 : ℤ)
  | 37 => (5311918208417463213188944272602893057814876008998663880704 : ℤ)
  | 38 => (5183325070830108402393874211814591793506542155926832414720 : ℤ)
  | 39 => (5060843593524783661064440027523475862935450451048524677120 : ℤ)
  | 40 => (4944046377934765531366495915797843884096572137765831966720 : ℤ)
  | 41 => (4832545103192050521957322138826172223663112094133801451520 : ℤ)
  | 42 => (4725986147365301864106118982903476196144955448083213189120 : ℤ)
  | 43 => (4624046785947490319532500352452737895481939121086513807360 : ℤ)
  | 44 => (4526431880544261566945612388409987834034527026748650946560 : ℤ)
  | 45 => (4432870985425507617177898727811572805215041902538087464960 : ℤ)
  | 46 => (4343115811570740325558106299378634872991853236419150479360 : ℤ)
  | 47 => (4256937997621263811479199895746287379549540273325510492160 : ℤ)
  | 48 => (4174127145184092046606549670494608873602371618955581194240 : ℤ)
  | 49 => (4094489082555735140076392812965841857992986254378050519040 : ℤ)
  | 50 => (4017844326418020731114688688801282703314452580860596060160 : ℤ)
  | 51 => (3944026715616898177428083092290365763199605540773230018560 : ℤ)
  | 52 => (3872882194939162163471884638837739513742187887192294031360 : ℤ)
  | 53 => (3804267729987738915203318648566831869520655836501266923520 : ℤ)
  | 54 => (3738050336933408810168948079880375200801955664743020625920 : ℤ)
  | 55 => (3674106213178300919802626540433095920126051618864307896320 : ℤ)
  | 56 => (3612319956876146629867650391316510868800914489372437381120 : ℤ)
  | 57 => (3552583864874725840998061841717757070757615248318629150720 : ℤ)
  | 58 => (3494797300025092403863607223923873170465759188730855292928 : ℤ)
  | 59 => (3438866119979340083178913110078191433804385605657494028288 : ℤ)
  | 60 => (3384702160606241205373094395165508359936440146526279303168 : ℤ)
  | 61 => (3332222768018808467532304340099132297422586637252336549888 : ℤ)
  | 62 => (3281350373951873850227795737071998255448967757819730198528 : ℤ)
  | 63 => (3232012109869591963756731923311018973834797773835500257280 : ℤ)
  | 64 => (3184139455737746008901086088220717681436971479633630330880 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta10 (i : ℕ) : ℤ :=
  match i with
  | 19 => (-4214525635216395813093167013517774201338613975929512454940262400 : ℤ)
  | 20 => (2809684945952673680792535928149063434319556736657812975779840000 : ℤ)
  | 21 => (-702420387101209035390687849320208263274783884613402287407104000 : ℤ)
  | 22 => (648622768984762049774074843981869353137838984366810726400 : ℤ)
  | 23 => (625121944021546033477912711953540753386468006672361062400 : ℤ)
  | 24 => (603299749412845446917190732212949910760194955956086374400 : ℤ)
  | 25 => (582979928971436169969687688769884360760884549885278289920 : ℤ)
  | 26 => (564010329920312765606819455000314540018351630206915051520 : ℤ)
  | 27 => (546258885657652032711366145418696636102369475401047080960 : ℤ)
  | 28 => (529610381100030412242395276845281375682988182297808732160 : ℤ)
  | 29 => (513963827447212641265386419648269391117266923237943541760 : ℤ)
  | 30 => (499230315835012459945746086034846878752067563737065717760 : ℤ)
  | 31 => (485331250475327884331823481202138036905504927564494274560 : ℤ)
  | 32 => (472196884875893225961107805880603751364424718960390307840 : ℤ)
  | 33 => (459765101890668686551193875705804527633425116028353904640 : ℤ)
  | 34 => (447980391279786590982760093643553418892041065086362583040 : ℤ)
  | 35 => (436792988286709086305244564199718149906414242689911357440 : ℤ)
  | 36 => (426158144276060241188584054378163123388881676310035824640 : ℤ)
  | 37 => (416035506299374674776773490564711030170258944097863598080 : ℤ)
  | 38 => (406388586990405548545647262031766836076039757257957703680 : ℤ)
  | 39 => (397184309747042778742322106719192355668504250981789204480 : ℤ)
  | 40 => (388392616963255028445239293125895787963571031507866746880 : ℤ)
  | 41 => (379986131303556394953241506283616308606487928683920097280 : ℤ)
  | 42 => (371939861793629711653210569634517455309154427023659106304 : ℤ)
  | 43 => (364230947931995934792484237225380045607628565190262390784 : ℤ)
  | 44 => (356838436183919099624808901070853125415275033151955533824 : ℤ)
  | 45 => (349743084157682613957797972576459217182517418724304093184 : ℤ)
  | 46 => (342927188529539303811512139851886510205893192317826760704 : ℤ)
  | 47 => (336374433411725182591258863236859771870274318619713208320 : ℤ)
  | 48 => (330069756375105412196935009514520580738753116880209182720 : ℤ)
  | 49 => (323999229765681304726845185220482370639370320097491025920 : ℤ)
  | 50 => (318149955309259183086503934634352089539564082676870676480 : ℤ)
  | 51 => (312509970294531809261872867452256268324208515893564538880 : ℤ)
  | 52 => (307068163872413982375642805529409564522487677513357066240 : ℤ)
  | 53 => (301814202217348007609187296814898083519711500227879895040 : ℤ)
  | 54 => (296738461471422013325237178045119878462073954291354173440 : ℤ)
  | 55 => (291831967540169751033709909564544597250634696324955504640 : ℤ)
  | 56 => (287086341934435453957569551579165999088997596191879331840 : ℤ)
  | 57 => (282493752959439717596710301858965700450751093282082652160 : ℤ)
  | 58 => (278046871643243883859158680874485286537565420964397711360 : ℤ)
  | 59 => (273738831874707515714161272472561343566048265635847208960 : ℤ)
  | 60 => (269563194287851535388928656618389725649516408500031324160 : ℤ)
  | 61 => (265513913487005450136143631495214152818689204210850856960 : ℤ)
  | 62 => (261585308256665713911392272023704920371151080545971077120 : ℤ)
  | 63 => (257772034442819656490087809342731345122099906601308651520 : ℤ)
  | 64 => (254069060229595432885805938946564988209230996417774878720 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta11 (i : ℕ) : ℤ :=
  match i with
  | 19 => (2809684837848878849998860965803256104007997880351315581311385600 : ℤ)
  | 20 => (-4214525797372088059283679457036485196805952260389258546642944000 : ℤ)
  | 21 => (2809684791518681065373000267655052962445901227648530983682048000 : ℤ)
  | 22 => (-702420534515474713745699161609945531881455052304080552591360000 : ℤ)
  | 23 => (507617819205465951997102051811897754629613118200112742400 : ℤ)
  | 24 => (489992200483053939774980452790651304816084884929275494400 : ℤ)
  | 25 => (473575195615893036962375763416576040132627159082724229120 : ℤ)
  | 26 => (458244781089751160397750218773371023618992437507045457920 : ℤ)
  | 27 => (443895002330542015648657446855523919066899966435283435520 : ℤ)
  | 28 => (430433391196087380965995637564791394470612513906973736960 : ℤ)
  | 29 => (417778869206105920902037545124269418245429736717324124160 : ℤ)
  | 30 => (405860032616418966303040612317957832260960425843475087360 : ℤ)
  | 31 => (394613740192308903530572724102287305665319340452096245760 : ℤ)
  | 32 => (383983942821458814054624286829970950477717586257180098560 : ℤ)
  | 33 => (373920707756989885086247981034865970585964266783600803840 : ℤ)
  | 34 => (364379400569380149819712281002588446289625265386175856640 : ℤ)
  | 35 => (355319995710534869586463687360429225586635495891103907840 : ℤ)
  | 36 => (346706492594381023836623058091125184192825494861187645440 : ℤ)
  | 37 => (338506418737578883111006372758991589181065597341547888640 : ℤ)
  | 38 => (330690405117169141911763642672359799494227498786441134080 : ℤ)
  | 39 => (323231821735948875497688948700757944648111682339135815680 : ℤ)
  | 40 => (316106463623947522520562751221458686526274377935937863680 : ℤ)
  | 41 => (309292279282186485789864312152497086361395545609475194880 : ℤ)
  | 42 => (302769134995846627122994501047679480851983287687871201280 : ℤ)
  | 43 => (296518609586099240749248378473834972386149893957750882304 : ℤ)
  | 44 => (290523815092818429136339368591076710023783226057670262784 : ℤ)
  | 45 => (284769239630056649649911696183978752844404034888976564224 : ℤ)
  | 46 => (279240609268034565069311576491473417928404485640955101184 : ℤ)
  | 47 => (273924766297117809154695667087857855616761385470293704704 : ℤ)
  | 48 => (268809561642479135739792733655415047585082757748170424320 : ℤ)
  | 49 => (263883759539925611199580433598003299806320567455024414720 : ℤ)
  | 50 => (259136952867205099749437700822295435325586421660809953280 : ℤ)
  | 51 => (254559487761733491932182871498874701977030848915418644480 : ℤ)
  | 52 => (250142396353689304475904132453999599753262459704448122880 : ℤ)
  | 53 => (245877336609700581453560273078289814226465131818374922240 : ℤ)
  | 54 => (241756538422462632630106292742502773043985668342064087040 : ℤ)
  | 55 => (237772755200080008800321283137677209994997682985280471040 : ℤ)
  | 56 => (233919220309387425161024655637591976434756215577918832640 : ℤ)
  | 57 => (230189607812965098714229652984265178638309965984264355840 : ℤ)
  | 58 => (226577997012477471926531435998459721731971870491840348160 : ℤ)
  | 59 => (223078840373348794895254033079411612542833303645176463360 : ℤ)
  | 60 => (219686934459310678232988368807405564137895016938612981760 : ℤ)
  | 61 => (216397393551395629669742193996925024572644360601112412160 : ℤ)
  | 62 => (213205625665653671928556950528934366275315092568366120960 : ℤ)
  | 63 => (210107310718192535357894268533080368534814653215271813120 : ℤ)
  | 64 => (207098380615885121351488212156647801908206235947651563520 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta12 (i : ℕ) : ℤ :=
  match i with
  | 19 => (-702420574939945705667275245073249261129806183071431145186918400 : ℤ)
  | 20 => (2809684710944424048632372966527743151033559222948036031283200000 : ℤ)
  | 21 => (-4214525918233473584394620408727449913924465267440000975241216000 : ℤ)
  | 22 => (2809684676150994882312556631950041187014593357281913210929152000 : ℤ)
  | 23 => (-702420644867174541020906117501695925772271276133019291746304000 : ℤ)
  | 24 => (401864106870993878664372457684419055748443718575089254400 : ℤ)
  | 25 => (388468636641960749375560042428271753890162261289252945920 : ℤ)
  | 26 => (375956384230226507732163830375826471934624636351933317120 : ℤ)
  | 27 => (364241481236887095213101690660056624613508526729246801920 : ℤ)
  | 28 => (353248963186708809934889223317685034311611909613834731520 : ℤ)
  | 29 => (342913077539972561656150456217912471258610252148333608960 : ℤ)
  | 30 => (333175899338528262235853869822286459140494217017305333760 : ℤ)
  | 31 => (323986190809085748238991894283780775062635729359585935360 : ℤ)
  | 32 => (315298455941454848531025528506678281504442290733328629760 : ℤ)
  | 33 => (307072152032751851630820945646350078564139841075344834560 : ℤ)
  | 34 => (299271028462068421557262385180175124316903514107113635840 : ℤ)
  | 35 => (291862569254313585248697702172317338485394819929016893440 : ℤ)
  | 36 => (284817520820886820697977291275443426332522562807754915840 : ℤ)
  | 37 => (278109489999047787080257915954382244378012911320631869440 : ℤ)
  | 38 => (271714600421070205216650839625847147782432292315217264640 : ℤ)
  | 39 => (265611197526724789091622353978526754028892483632580526080 : ℤ)
  | 40 => (259779594335265631498051192224270725319410042564121722880 : ℤ)
  | 41 => (254201851525719967398964940024885789620223997667631431680 : ℤ)
  | 42 => (248861586519631015314018829793937829857870174395176058880 : ℤ)
  | 43 => (243743807181257562937284960139319276825284087897160417280 : ℤ)
  | 44 => (238834766494569018931395872586119318450966585071374434304 : ℤ)
  | 45 => (234121835181099990025550251723088070620492879590991069184 : ℤ)
  | 46 => (229593389716419046171965820987033344732489565519399092224 : ℤ)
  | 47 => (225238713607878612729194336937016209989083941151581405184 : ℤ)
  | 48 => (221047910129881772488330870024118506176176685657781960704 : ℤ)
  | 49 => (217011824988860161046210891633792827724918153850199736320 : ℤ)
  | 50 => (213121977619379015999870228416813524343359255635013140480 : ℤ)
  | 51 => (209370500003924124063447303585834871146212586543151841280 : ℤ)
  | 52 => (205750082068900227317076904978499917878029587550023188480 : ℤ)
  | 53 => (202253922843739686362969976622688490825940467421418618880 : ℤ)
  | 54 => (198875686683268548861236009021632614723723176429475594240 : ℤ)
  | 55 => (195609463949238455175824288032330249895839021232962928640 : ℤ)
  | 56 => (192449735628163405943437171368757767617353654574556119040 : ℤ)
  | 57 => (189391341431714973231454300215495682169000678893698416640 : ℤ)
  | 58 => (186429450984907689059307062310825717032308835104944291840 : ℤ)
  | 59 => (183559537757776967519997363811010759475224996068101980160 : ℤ)
  | 60 => (180777355439559965562162195428420132990365543795167068160 : ℤ)
  | 61 => (178078916491649534626668528494954928512516892495980789760 : ℤ)
  | 62 => (175460472647729020637717834979836495973482012359167836160 : ℤ)
  | 63 => (172918497157283358277993295623228195272964845092166696960 : ℤ)
  | 64 => (170449668592765507858120670735275856454376128355888005120 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta13 (i : ℕ) : ℤ :=
  match i with
  | 19 => (401864106870993878664372457684419055748443718575089254400 : ℤ)
  | 20 => (-702420675405972423415744911166363682234570120182360788959232000 : ℤ)
  | 21 => (2809684615262493841252878046439062749981403092366198275309568000 : ℤ)
  | 22 => (-4214526009566225145984138286993917569474250664813573378670592000 : ℤ)
  | 23 => (2809684588789232519053017791869072125184363846750670042431488000 : ℤ)
  | 24 => (-702420728588863472477964172579291276692907890392127328223232000 : ℤ)
  | 25 => (321491285496795102931497966147535244598754974860071403520 : ℤ)
  | 26 => (311187077628308080401642262104345012400076930794043473920 : ℤ)
  | 27 => (301537105180042456127650412286119239388616540319509381120 : ℤ)
  | 28 => (292480033581352474023035180359267507515572148412266577920 : ℤ)
  | 29 => (283962048208951244647928454751405886768776785721577963520 : ℤ)
  | 30 => (275935726394806915212088379937175961967202965719152066560 : ℤ)
  | 31 => (268359107907722797935148634711896288858487165634226421760 : ℤ)
  | 32 => (261194924110492954697683697770590297601941398332228239360 : ℤ)
  | 33 => (254409954900395169945514550069645091239526575797709045760 : ℤ)
  | 34 => (247974489257605693003707348928053158601133411873125826560 : ℤ)
  | 35 => (241861870337640724605209176939543830638554411453529456640 : ℤ)
  | 36 => (236048109966675546545312638605036914075888747904698941440 : ℤ)
  | 37 => (230511560432914674932521553750521932312462600838148259840 : ℤ)
  | 38 => (225232633831811750413893118890642894937428211508120125440 : ℤ)
  | 39 => (220193561078635092567372319409895986789042071985077616640 : ℤ)
  | 40 => (215378184167850554258575796767974372060337018810694369280 : ℤ)
  | 41 => (210771776424168817026786258360317181935453491518379130880 : ℤ)
  | 42 => (206360886422030219938920599824359711554933078789644615680 : ℤ)
  | 43 => (202133201999748006166998776574819335003399974560863354880 : ℤ)
  | 44 => (198077431400462803998151726311544384126597301695445729280 : ℤ)
  | 45 => (194183199064458587968687821732294978923361727451920072704 : ℤ)
  | 46 => (190440953999470220605509767192172955865227258006742237184 : ℤ)
  | 47 => (186841888985462250569373006339754721780527467798644916224 : ℤ)
  | 48 => (183377869142150083701655539261555891681954387133342941184 : ℤ)
  | 49 => (180041368612433417522578578423667582120213040905221832704 : ℤ)
  | 50 => (176825414301760773179773645865350922150073781992690810880 : ℤ)
  | 51 => (173723535769281576915127830604615577701354969500200468480 : ℤ)
  | 52 => (170729720497097789576488413423871500401169921295547105280 : ℤ)
  | 53 => (167838373873523446311004031612045289977233010325958164480 : ℤ)
  | 54 => (165044283318647660560713267577834874552936419405206650880 : ℤ)
  | 55 => (162342586058632741709929421959412700564773747468103843840 : ℤ)
  | 56 => (159728740121471144580791032881935691346870832074472816640 : ℤ)
  | 57 => (157198498183339381499193973326264867990297188032881623040 : ℤ)
  | 58 => (154747883942836190587973915932356108397583116947570032640 : ℤ)
  | 59 => (152373170741603123070800921829095288579050892852818083840 : ℤ)
  | 60 => (150070862185194144297966325670642504829521352853511208960 : ℤ)
  | 61 => (147837674548494893540492321847730046453607861944749916160 : ℤ)
  | 62 => (145670520776246802476315910939759843371513366804441333760 : ℤ)
  | 63 => (143566495911935855664354941512819110596621399773843292160 : ℤ)
  | 64 => (141522863807986961507339197366632956542617679578487848960 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta14 (i : ℕ) : ℤ :=
  match i with
  | 19 => (334886755725828232220310381403682546457036432145907712000 : ℤ)
  | 20 => (321491285496795102931497966147535244598754974860071403520 : ℤ)
  | 21 => (-702420751951516589319340847237308003076295024647830993738137600 : ℤ)
  | 22 => (2809684542196292591981263743825888625541574774467340352566067200 : ℤ)
  | 23 => (-4214526079455635036591769359058692818938434273238567913468723200 : ℤ)
  | 24 => (2809684521811881373887371347806995844447854555343383613249945600 : ℤ)
  | 25 => (-702420792887120571836984758878884506199956810143122300237512704 : ℤ)
  | 26 => (259666038285872967752363741888393851406686710463903825920 : ℤ)
  | 27 => (251651654388160839118031527632579226363270453968104325120 : ℤ)
  | 28 => (244127947055614759175597204045487945710267437665925201920 : ℤ)
  | 29 => (237050501599146421793466565506244189481304049298461163520 : ℤ)
  | 30 => (230380167292818727492678793726816679335650956578232729600 : ℤ)
  | 31 => (224082293250162543771524191848863825741597324612688936960 : ℤ)
  | 32 => (218126094548848563102102077501343906889931700812340264960 : ℤ)
  | 33 => (212484123277645211829274915020963745390008826383732572160 : ℤ)
  | 34 => (207131824680278243043823672695007555269121432435933839360 : ℤ)
  | 35 => (202047162758063535442064782335548123658454129750258483200 : ℤ)
  | 36 => (197210302907530293642501126085719491110949553834075095040 : ℤ)
  | 37 => (192603341656297829932948048585099718859840778329013616640 : ℤ)
  | 38 => (188210075499125845599429716099530452759994840988138864640 : ℤ)
  | 39 => (184015802357863660294470302717881966142716035244008407040 : ℤ)
  | 40 => (180007150391535704700935073641454081214197700127568691200 : ℤ)
  | 41 => (176171929838973102681563849676811537353171777974100295680 : ℤ)
  | 42 => (172499004341217019058750786199896319483220756415989678080 : ℤ)
  | 43 => (168978178806123812621304557249064915671356918922194452480 : ℤ)
  | 44 => (165600101375112199015692189512599420844450545599491604480 : ℤ)
  | 45 => (162356177456374459227985285628484912504513415599882240000 : ℤ)
  | 46 => (159238494119154772432655434107562887119149230184521007104 : ℤ)
  | 47 => (156239753414704784123435515474350057503657579830138896384 : ℤ)
  | 48 => (153353213412879427347341968199386467134823824584054145024 : ℤ)
  | 49 => (150572635928191399729053705981195152437183471331294838784 : ℤ)
  | 50 => (147892240062753907229428781808914057660337543419214692352 : ℤ)
  | 51 => (145306660821682821911979727615592564836470353084840673280 : ℤ)
  | 52 => (142810912163820509325560718475044881105320837302116679680 : ℤ)
  | 53 => (140400353940796364771630114730707798080532659516295086080 : ℤ)
  | 54 => (138070662253449825669198664376162396958829771912988590080 : ℤ)
  | 55 => (135817802818939014839667997928058943225776876236109250560 : ℤ)
  | 56 => (133638006996418893233902817839097053725599196141311754240 : ℤ)
  | 57 => (131527750165611925025396474447941371645225658841133219840 : ℤ)
  | 58 => (129483732192236355384409665899753208973163138475978915840 : ℤ)
  | 59 => (127502859748192537797169003546971765634976763145869066240 : ℤ)
  | 60 => (125582230283536864493176091316800684862487978281145466880 : ℤ)
  | 61 => (123719117472342086680630426806090435600115207373177487360 : ℤ)
  | 62 => (121910957976172707820210227803573978340805041391518351360 : ℤ)
  | 63 => (120155339387612270497625596166145935070024876736181698560 : ℤ)
  | 64 => (118449989232498738247831662907542919612343667362900213760 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta15 (i : ℕ) : ℤ :=
  match i with
  | 19 => (281157671840145900457491353178476335706786630944476364800 : ℤ)
  | 20 => (269970246154359990282219445931584083605364754529931755520 : ℤ)
  | 21 => (259666038285872967752363741888393851406686710463903825920 : ℤ)
  | 22 => (-702420810966525290654106245501794795893079435258447008261734400 : ℤ)
  | 23 => (2809684485747153834182792493312031693282041859970229382152192000 : ℤ)
  | 24 => (-4214526133552726346148637640801139045687153316298299260115353600 : ℤ)
  | 25 => (2809684469878673716712777797334247466769084274006041520469180416 : ℤ)
  | 26 => (-702420842822897165274093942025757946275697465275182004834402304 : ℤ)
  | 27 => (211579734899600195946370456353506101146189171489106821120 : ℤ)
  | 28 => (205282718979969237733680859438223181469219255670978641920 : ℤ)
  | 29 => (199357940454602178528637938202661419605666280689390059520 : ℤ)
  | 30 => (193772828551500927168072608524845214246856264221143859200 : ℤ)
  | 31 => (188498548214452119790684641809333800076507938761474048000 : ℤ)
  | 32 => (183509474767994892560217357178802286459302526102703964160 : ℤ)
  | 33 => (178782755414625386169925752972799383949524623469324533760 : ℤ)
  | 34 => (174297941176781540100986129449141120183143133668452597760 : ℤ)
  | 35 => (170036676353724961936343138139522719353880473798233292800 : ℤ)
  | 36 => (165982435218358956587569818184382310963080975519160729600 : ℤ)
  | 37 => (162120297733763676378668187992693294974910809176790794240 : ℤ)
  | 38 => (158436757671314544702373872020837369990539895373236797440 : ℤ)
  | 39 => (154919557770167772810665133806146625656573467851740938240 : ℤ)
  | 40 => (151557547572129539325424834981832734716880196436020428800 : ℤ)
  | 41 => (148340560356673147657963885606284099335333467144165785600 : ℤ)
  | 42 => (145259306233512035091996737547240840757137645776016506880 : ℤ)
  | 43 => (142305278959138766994522444119850522808024627292279930880 : ℤ)
  | 44 => (139470674455456429922172313852656523466051610914932654080 : ℤ)
  | 45 => (136748319343348535932096218191666770688152022214613401600 : ℤ)
  | 46 => (134131608077475223602728357162355146047264860114675302400 : ℤ)
  | 47 => (131614447492998073735595461566244392288650643964956770304 : ℤ)
  | 48 => (129191207759926349982564292360975697982127714156815581184 : ℤ)
  | 49 => (126856678893912797984855872088325870052508854128553754624 : ℤ)
  | 50 => (124606032099604102953817331792355767296514800284904456192 : ℤ)
  | 51 => (122434785328844792743902924761032307522427081609028042752 : ℤ)
  | 52 => (120338772524964267320406290895554694508904323232542228480 : ℤ)
  | 53 => (118314116099115512367790554145951121538652279711182356480 : ℤ)
  | 54 => (116357202247659978868633471963263922950283890028896583680 : ℤ)
  | 55 => (114464658772915919509892869659035683194585525507179151360 : ℤ)
  | 56 => (112633335114843214147492663830880920778751277087546408960 : ℤ)
  | 57 => (110860284339763369746853366796255487812731940837460541440 : ℤ)
  | 58 => (109142746865105634701916841526528108592925080352865648640 : ℤ)
  | 59 => (107478135727331866591836467434635085972596468097681981440 : ℤ)
  | 60 => (105864023224369790484472025056272278017752870607210414080 : ℤ)
  | 61 => (104298128784694817956097096080047090484890706931645153280 : ℤ)
  | 62 => (102778307933158782829633350847348995970543698464798146560 : ℤ)
  | 63 => (101302542239198662760498819717193513943448953259462492160 : ℤ)
  | 64 => (99868930146528444891972178831115165428877477481189212160 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta16 (i : ℕ) : ℤ :=
  match i with
  | 19 => (237671461252304835138040792662869939106413218784870400000 : ℤ)
  | 20 => (228262738115245851470898739090099810420239338072199659520 : ℤ)
  | 21 => (219594118797312324580702670609320726189605427984906321920 : ℤ)
  | 22 => (211579734899600195946370456353506101146189171489106821120 : ℤ)
  | 23 => (-702420856962119834045453190364937481437884032256092984154521600 : ℤ)
  | 24 => (2809684441668042396766085004484853286301604121180818655254937600 : ℤ)
  | 25 => (-4214526175868673326068676830075230316388373545536133557936717824 : ℤ)
  | 26 => (2809684429190263159097355499955313552633295592046585464871714816 : ℤ)
  | 27 => (-702420882004329554088945043205472085813864344199102650965295104 : ℤ)
  | 28 => (173797639381814446670232874861808583084369676580337745920 : ℤ)
  | 29 => (168803454342107134984306642825549715754359053690098155520 : ℤ)
  | 30 => (164094651304668812537576195477077069414634752107872256000 : ℤ)
  | 31 => (159647064858017024596077373629118423739406397851933081600 : ℤ)
  | 32 => (155439214636389589174064258004098471772415880716301107200 : ℤ)
  | 33 => (151451939177146378022888500155543786285637500119505960960 : ℤ)
  | 34 => (147668088517625357354283038803166133780967392367985295360 : ℤ)
  | 35 => (144072264762552940680076064255783105733687537741437337600 : ℤ)
  | 36 => (140650602062113823610458352534869094194687533313635123200 : ℤ)
  | 37 => (137390579150845416594817053812286891889271628020632780800 : ℤ)
  | 38 => (134280858931184703227829970051442492192517497138750423040 : ℤ)
  | 39 => (131311150632904263170787916078080177535900258002838487040 : ℤ)
  | 40 => (128472090907717748317368826761958363013299821415602585600 : ℤ)
  | 41 => (125755140877056344697818681767990527260027858449543987200 : ℤ)
  | 42 => (123152496678149314807205497945152420627453803871653068800 : ℤ)
  | 43 => (120657011477744570447069940296833154577348207230771527680 : ℤ)
  | 44 => (118262127266002381091525801352406647677775857804881428480 : ℤ)
  | 45 => (115961815022167519261464485368933623338697258527254118400 : ℤ)
  | 46 => (113750522071652862459664646848894368389653199226667008000 : ℤ)
  | 47 => (111623125641347543182901712869428965074266012083919257600 : ℤ)
  | 48 => (109574891774289719991181872362754173419255938601508143104 : ℤ)
  | 49 => (107601438892620207539057102937148544803945145637518966784 : ℤ)
  | 50 => (105698705403952778390218826452975259937889936979643072512 : ℤ)
  | 51 => (103862920834937417076722189012600267184143312884011630592 : ℤ)
  | 52 => (102090580050037081595213457803964413181447353581229309952 : ℤ)
  | 53 => (100378420175945380910371342182959779306433646676966113280 : ℤ)
  | 54 => (98723399904708086817200697076182038099190319388116910080 : ℤ)
  | 55 => (97122680893150870146236157749308822846084874438977781760 : ℤ)
  | 56 => (95573611014023044871824078913186924163675778052794613760 : ℤ)
  | 57 => (94073709246457232046933851870047052257155735728852828160 : ℤ)
  | 58 => (92620652020832318372166258489918754955301839847020298240 : ℤ)
  | 59 => (91212260856664940130190531666061489851722608192771850240 : ℤ)
  | 60 => (89846491152365183596305596071842910877080703806923079680 : ℤ)
  | 61 => (88521422003091085898703954863361941858229168026136084480 : ℤ)
  | 62 => (87235246937952866670099478632183695231165773747039764480 : ℤ)
  | 63 => (85986265480809560929127759073261210165290589616456335360 : ℤ)
  | 64 => (84772875450167397452188627814575849791402924236876021760 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta17 (i : ℕ) : ℤ :=
  match i with
  | 19 => (202186004657587952655925282773391407983055695337907814400 : ℤ)
  | 20 => (194222051406851223470482573947417793335320799639785963520 : ℤ)
  | 21 => (186882347786242411787509959361097766828722748410214481920 : ℤ)
  | 22 => (180094655301445404882922471777091502761339592398465925120 : ℤ)
  | 23 => (173797639381814446670232874861808583084369676580337745920 : ℤ)
  | 24 => (-702420893169961371923462913330119744314672174833108938391552000 : ℤ)
  | 25 => (2809684406908514520403195670438278313939887504306883339187388416 : ℤ)
  | 26 => (-4214526209291296284109916574350783174428485677145686746463207424 : ℤ)
  | 27 => (2809684397005515125428013523986262652298372798644793505549910016 : ℤ)
  | 28 => (-702420913039622300841524805747056882565397037836544897454178304 : ℤ)
  | 29 => (143832529143570576554675482644255379104305939238900203520 : ℤ)
  | 30 => (139837181111804727205934497015248285240297440926708531200 : ℤ)
  | 31 => (136062773985021321139151538241301491497800933304591974400 : ℤ)
  | 32 => (132491183704608517303853486931960832632473635886255308800 : ℤ)
  | 33 => (129106238972478309375544125449278989486905323658674176000 : ℤ)
  | 34 => (125893462797467782924324842087630759361465488857691586560 : ℤ)
  | 35 => (122839854320223293544249770965764907626057438570794188800 : ℤ)
  | 36 => (119933703737300934198099276080531913638636193771945984000 : ℤ)
  | 37 => (117164434578084844330697153229219285669772712154130022400 : ℤ)
  | 38 => (114522468705869831506628517646259446746591407417956761600 : ℤ)
  | 39 => (111999110292490543398312934812749084104777795013066096640 : ℤ)
  | 40 => (109586445710177457337008806720354104650354048430296268800 : ℤ)
  | 41 => (107277256836764767016120915193445121173742543783854080000 : ℤ)
  | 42 => (105064945712554624856124291903489505464269563618551398400 : ℤ)
  | 43 => (102943468843054611706015628775174678408341050780916121600 : ℤ)
  | 44 => (100907279729811110598179840880718542863215289437551329280 : ℤ)
  | 45 => (98951278445800775905944370812205694001734782629288345600 : ℤ)
  | 46 => (97070767263274644623395694623084864307787511072869580800 : ℤ)
  | 47 => (95261411499119410686235617608276434018975574058545971200 : ℤ)
  | 48 => (93519204872408538321419121737990571002977504106800742400 : ℤ)
  | 49 => (91840438776145388698300966764610440451463114460657352704 : ℤ)
  | 50 => (90221674954438762872033815450967686495508177979485192192 : ℤ)
  | 51 => (88659721150833714991176387741033241988441929471766822912 : ℤ)
  | 52 => (87151609355916797204584412583580211118338536289748385792 : ℤ)
  | 53 => (85694576334771567758399035647190018550846440696291786752 : ℤ)
  | 54 => (84286046159110709922386816732792317909732750697305210880 : ℤ)
  | 55 => (82923614506361318938088617543290348727883985153540751360 : ℤ)
  | 56 => (81605034519774580264965365350933056499266153315733340160 : ℤ)
  | 57 => (80328204050705988146365054802501960735222297651010600960 : ℤ)
  | 58 => (79091154127335296989155155761270450267123867058134056960 : ℤ)
  | 59 => (77892038513898890688248218247392603846456952001228963840 : ℤ)
  | 60 => (76729124241513736241004458760910774594691801811077038080 : ℤ)
  | 61 => (75600783006314819115138966984809420460329090972469166080 : ℤ)
  | 62 => (74505483343267340199491626245474152899812258624495943680 : ℤ)
  | 63 => (73441783494951720108969885389183014033993577193044705280 : ℤ)
  | 64 => (72408324904105307283015815724682414611824208633617448960 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta18 (i : ℕ) : ℤ :=
  match i with
  | 19 => (173009266900579264605300382708823393543680817288404008960 : ℤ)
  | 20 => (166227872371695308517256412112327563206979210528182763520 : ℤ)
  | 21 => (159976211134572514766988411413071274500962242678143057920 : ℤ)
  | 22 => (154193136617249098934174622396494271577744125855918981120 : ℤ)
  | 23 => (148826714183277888240601714680514246434316562129139793920 : ℤ)
  | 24 => (143832529143570576554675482644255379104305939238900203520 : ℤ)
  | 25 => (-702420921936467200637578224265216273165747995694296786171592704 : ℤ)
  | 26 => (2809684379248412762024238640692993190044622291940356562475810816 : ℤ)
  | 27 => (-4214526235926949829215578899290687367809111437202342161074356224 : ℤ)
  | 28 => (2809684371321134921218981996365640751538483672875875784317730816 : ℤ)
  | 29 => (-702420937838334222146796625518691821230117573061706835195592704 : ℤ)
  | 30 => (119860440952975480462229568870212815920254949365750169600 : ℤ)
  | 31 => (116638386088648182600341677233916772481538418468821401600 : ℤ)
  | 32 => (113588941306338418552483494078136588512753130298513817600 : ℤ)
  | 33 => (110698376258612975401629928955558502465154554183391641600 : ℤ)
  | 34 => (107954396451364989293974201531006139618625038476482969600 : ℤ)
  | 35 => (105345958634100557702228344567022848060850354680705843200 : ℤ)
  | 36 => (102863114161394046800544842820729438306014947009835827200 : ℤ)
  | 37 => (100496875474656261690710697344821727273189445226148659200 : ℤ)
  | 38 => (98239101796036084257713537091817262103416667517432627200 : ℤ)
  | 39 => (96082400866950526820131660896995936605013722900149043200 : ℤ)
  | 40 => (94020044149544221328978499482217161716739552608203571200 : ℤ)
  | 41 => (92045893375595679708389845422274180369341129010918195200 : ℤ)
  | 42 => (90154336700625412664373833926271861756563265303032627200 : ℤ)
  | 43 => (88340233021441767117208538107645856731210733474493235200 : ℤ)
  | 44 => (86598863258557955279347960292872930782851739503768371200 : ℤ)
  | 45 => (84925887602747713203215898364690167407181296188784640000 : ℤ)
  | 46 => (83317307886717017584783992263917065838223267494625280000 : ℤ)
  | 47 => (81769434375660753500557877320504504828606028175114240000 : ℤ)
  | 48 => (80278856379997475628456921499499832028943705387827200000 : ℤ)
  | 49 => (78842416184289091734207337794699205788252408266096640000 : ℤ)
  | 50 => (77457185861788331042833418500184902541032520536767332352 : ℤ)
  | 51 => (76120446607029882817653866172119119916654654524691054592 : ℤ)
  | 52 => (74829670271644236476303745179085609382258666083411034112 : ℤ)
  | 53 => (73582502832938440925841442522801401768875711833248366592 : ℤ)
  | 54 => (72376749562218736595929083550499705670818112988986212352 : ℤ)
  | 55 => (71210361691513384781052681946950919809341301675587010560 : ℤ)
  | 56 => (70081424404256803174278306592910404164999526292924661760 : ℤ)
  | 57 => (68988145998408740216309621259331707455028790224601743360 : ℤ)
  | 58 => (67928848090053352236479237333169600467609716682139893760 : ℤ)
  | 59 => (66901956742286943043843674181248807970148787461617090560 : ℤ)
  | 60 => (65905994418601342642025261360371322254431457064653946880 : ℤ)
  | 61 => (64939572672368607015211386413020989422207708430839316480 : ℤ)
  | 62 => (64001385494736546812342557094143664080949579743525601280 : ℤ)
  | 63 => (63090203252507770631660238734025313288359406303948308480 : ℤ)
  | 64 => (62204867155610268815635863307600562541469675690005626880 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta19 (i : ℕ) : ℤ :=
  match i with
  | 19 => (148850709651668453631177285509454949169396331869015900160 : ℤ)
  | 20 => (143044156662335394489742990491270189563617079946966466560 : ℤ)
  | 21 => (137689672144796384597677943333705464178347079726813675520 : ℤ)
  | 22 => (132735201827078087389208963942568361791813390549563473920 : ℤ)
  | 23 => (128136519018776168398907324816013224638558267298147205120 : ℤ)
  | 24 => (123855788984741329810970554499219909784263447677941841920 : ℤ)
  | 25 => (119860440952975480462229568870212815920254949365750169600 : ℤ)
  | 26 => (-702420944986551999286709082386287209745135672666402433431240704 : ℤ)
  | 27 => (2809684357052034807769520036576406362227434158559810383633186816 : ℤ)
  | 28 => (-4214526257330599999389771838974538951775685708676440262101172224 : ℤ)
  | 29 => (2809684350655541653464588813222611635984549893521574169533218816 : ℤ)
  | 30 => (-702420957815074380976043369223619966265586893104198396153954304 : ℤ)
  | 31 => (100528111767011693290902219052436555287955763984177561600 : ℤ)
  | 32 => (97910192189745763778118307097946019993998582630422937600 : ℤ)
  | 33 => (95428268434675466967297195764467980039987228879460761600 : ℤ)
  | 34 => (93071840824351875333654992356997794241587649864898969600 : ℤ)
  | 35 => (90831476315225634942227120263832880201445759995661516800 : ℤ)
  | 36 => (88698675168409518749140904446159956960814945046573875200 : ℤ)
  | 37 => (86665757275856819711054360540970949668142656555004723200 : ℤ)
  | 38 => (84725764822948961629891017230320040967892741362234163200 : ℤ)
  | 39 => (82872378596936663685632823134097670318768597085926195200 : ℤ)
  | 40 => (81099845747828591762352964788219334614981854229430272000 : ℤ)
  | 41 => (79402917204059406638462698400483891482562119758721843200 : ℤ)
  | 42 => (77776793262146217748600611032963130855025063610233651200 : ℤ)
  | 43 => (76217076124698031215277372429735487812347573516317491200 : ℤ)
  | 44 => (74719728367694553428318814372394400376636307410203443200 : ℤ)
  | 45 => (73281036486005124116878008196182617902823411796462796800 : ℤ)
  | 46 => (71897578803511247935582249574449643937588366909898752000 : ℤ)
  | 47 => (70566197147038774982419144511766766272238698413162496000 : ℤ)
  | 48 => (69283971776392474285742297229857336503579470949515264000 : ℤ)
  | 49 => (68048199139897936805780434880090361016672792187240448000 : ℤ)
  | 50 => (66856372088991543687984380907677924196226913329521623040 : ℤ)
  | 51 => (65706162238947597664183460767811097058654584324438884352 : ℤ)
  | 52 => (64595404207705317388593330703829426078168601701061230592 : ℤ)
  | 53 => (63522081502495606244017936795103268257706312369661018112 : ℤ)
  | 54 => (62484313855811081623783149108892807702185438743827054592 : ℤ)
  | 55 => (61480345839220965644817304562298540587158572137554378752 : ℤ)
  | 56 => (60508536606426288311210756154967632673604252625073602560 : ℤ)
  | 57 => (59567350636451936467065186516575946628135057050314997760 : ℤ)
  | 58 => (58655349364531543624738106701554740565351639417209487360 : ℤ)
  | 59 => (57771183602513057282053002683151565220130483685042421760 : ℤ)
  | 60 => (56913586662872319671991210108731073310127541681137909760 : ℤ)
  | 61 => (56081368110980401620531034403796501277361379247789178880 : ℤ)
  | 62 => (55273408079386713429547711504132859106058115740053012480 : ℤ)
  | 63 => (54488652085770238839149734167936297738072202809735905280 : ℤ)
  | 64 => (53726106303056561220548553666039937044589488384749076480 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta2 (i : ℕ) : ℤ :=
  match i with
  | 19 => (6598726622533862434186493864585040031467555494742196224000 : ℤ)
  | 20 => (6313995830734415081512799409515957554597664061072919756800 : ℤ)
  | 21 => (6053132044347090646082611585484728645877920837478960332800 : ℤ)
  | 22 => (5813227719799285942450965892967196153531096158962502860800 : ℤ)
  | 23 => (5591832379055776446949647658967439323032038319789493452800 : ℤ)
  | 24 => (5386865719530261591939866790265253599341857307823492300800 : ℤ)
  | 25 => (5196549902320824409034749934165626495135975484296097955840 : ℤ)
  | 26 => (5019356238872409596039091823083668155470144310333396746240 : ℤ)
  | 27 => (4853962814612599987736950280340891730052263553485598883840 : ℤ)
  | 28 => (4699220510123396656058874278640856045894486366604010455040 : ℤ)
  | 29 => (4554125534415836846924218823365652134826691385413316116480 : ℤ)
  | 30 => (4417797054884300813260415304061617274527287776294238945280 : ℤ)
  | 31 => (4289458850412806971288380456867709914825894563305047982080 : ℤ)
  | 32 => (4168424165618593262625738790080308110292248237134084833280 : ℤ)
  | 33 => (4054083131187330557445422762277347277005832170138952007680 : ℤ)
  | 34 => (3945892255605756005756851864343414125410994482072313135104 : ℤ)
  | 35 => (3843365599920591747320574424874412352101604811417724125184 : ℤ)
  | 36 => (3746067328389523137560011883584197984670628029536848052224 : ℤ)
  | 37 => (3653605390460417003758693744472450138214366686489224413184 : ℤ)
  | 38 => (3565626138073873079181819692651706337828386435703404232704 : ℤ)
  | 39 => (3481809720238918015412573339041640630442783084510938398720 : ℤ)
  | 40 => (3401866126698373033757671676569848478948285356418028011520 : ℤ)
  | 41 => (3325531776152901504725746305111378143621289118614127902720 : ℤ)
  | 42 => (3252566563357373734046114185537003286532478670676185579520 : ℤ)
  | 43 => (3182751294503524536378892609923357699412708848426937221120 : ℤ)
  | 44 => (3115885452468935203799074578858531182766334489604244111360 : ℤ)
  | 45 => (3051785243365229898228484965340096826045935831521542799360 : ℤ)
  | 46 => (2990281883837324462998100161764940297400115733294177320960 : ℤ)
  | 47 => (2931220095122731281041707702822356248321925496308089487360 : ℤ)
  | 48 => (2874456775265921622056892936618264559560236027800096604160 : ℤ)
  | 49 => (2819859825325797656968371424818178356061828684563339018240 : ℤ)
  | 50 => (2767307109094606638230978132202939950803254178673653186560 : ℤ)
  | 51 => (2716685528907110435187811550798437696265695643895500636160 : ℤ)
  | 52 => (2667890202673505387192107437710652390901786237211309506560 : ℤ)
  | 53 => (2620823729409795652296965128684058469223572721433428623360 : ℤ)
  | 54 => (2575395532338545857939045796008589362863496507145343467520 : ℤ)
  | 55 => (2531521270150564717582207461005009830629471959557204869120 : ℤ)
  | 56 => (2489122308302293328869220575466219217278076551271095992320 : ℤ)
  | 57 => (2448125243313753207196234004682386388809921440508930949120 : ℤ)
  | 58 => (2408461473959959891131325047956634736973363458918286622720 : ℤ)
  | 59 => (2370066814041085198909865969040057994881240480506789756928 : ℤ)
  | 60 => (2332881142095066331641067542775773177812942209237162917888 : ℤ)
  | 61 => (2296848083998758826811279083064769091748135166440707719168 : ℤ)
  | 62 => (2261914724904995159592453791096792049688931737490725797888 : ℤ)
  | 63 => (2228031347395422658286990434879218964028545475514652950528 : ℤ)
  | 64 => (2195151193103085321690001703965001858842819589691439841280 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta20 (i : ℕ) : ℤ :=
  match i with
  | 19 => (128716293866394803489396007819030618385462761916999925760 : ℤ)
  | 20 => (123718681709915530308451730746345810347407390872971509760 : ℤ)
  | 21 => (119108891955904038944290081193071009733151421855495618560 : ℤ)
  | 22 => (114842374015930090667927439003606247067448042457682411520 : ℤ)
  | 23 => (110881264486423371456404133713777806294431702726916177920 : ℤ)
  | 24 => (107193162400648732296636029180088942286900816468110213120 : ℤ)
  | 25 => (103750166631338991152790110688732598726672294881106329600 : ℤ)
  | 26 => (100528111767011693290902219052436555287955763984177561600 : ℤ)
  | 27 => (-702420963602868993177763395516327775011164429695247615686344704 : ℤ)
  | 28 => (2809684339100586277946003377486724388578049285710566815030050816 : ℤ)
  | 29 => (-4214526274663033062667649992578369822885436620392951293855924224 : ℤ)
  | 30 => (2809684333900856358962639931405575127245124012195613505503625216 : ℤ)
  | 31 => (-702420974029285956300510029046558523110192584709966780698722304 : ℤ)
  | 32 => (84820594303416116214198747325493343524212675861649817600 : ℤ)
  | 33 => (82678660103834901158284637544546541920065891117668761600 : ℤ)
  | 34 => (80644722586585512071576281197933192497640792999434649600 : ℤ)
  | 35 => (78710682000493062006383246778078286343308255010016460800 : ℤ)
  | 36 => (76869238569807344207379589839883358633674126108970188800 : ℤ)
  | 37 => (75113795199894425061181145114749611651631733697360691200 : ℤ)
  | 38 => (73438374148618439014883015928808245024990582346560307200 : ℤ)
  | 39 => (71837545365639770182339450685135867213026617774519091200 : ℤ)
  | 40 => (70306364626060202024270045752543100907774126587904000000 : ℤ)
  | 41 => (68840319922583263312242938074507559579865297645993984000 : ℤ)
  | 42 => (67435284850843728865736243751384301567329290712986419200 : ℤ)
  | 43 => (66087477940400672017100353003610043030844160821375795200 : ℤ)
  | 44 => (64793427060264884250402120264685879256898054881751859200 : ℤ)
  | 45 => (63549938171359920840440790033234783122419000300850380800 : ℤ)
  | 46 => (62354067815677766150475593081787340154132567885139148800 : ℤ)
  | 47 => (61203098828297238011018183717807457204827115422220288000 : ℤ)
  | 48 => (60094518837975056931283496693804625096409972998144000000 : ℤ)
  | 49 => (59026001187921893337691050387771973719094188910313472000 : ℤ)
  | 50 => (57995387963196767476690212974846705487877215788822691840 : ℤ)
  | 51 => (57000674856931573757503771196654732501329289409504215040 : ℤ)
  | 52 => (56039997645965704078519785858922966742504991633652580352 : ℤ)
  | 53 => (55111620078741950096998781736618430296285982457270894592 : ℤ)
  | 54 => (54213923005550079087452916512470253879191889778533466112 : ℤ)
  | 55 => (53345394604264564051882947376853120857825823836174548992 : ℤ)
  | 56 => (52504621574309207315272463575473848150733950353252810752 : ℤ)
  | 57 => (51690281188267367847096526413525829578169536486110658560 : ℤ)
  | 58 => (50901134104812997390263271081021071172276801534437621760 : ℤ)
  | 59 => (50136017858852586566187071188636388422304540774482575360 : ℤ)
  | 60 => (49393840955262082841144484428781852279467503353027624960 : ℤ)
  | 61 => (48673577501641853008802503629023158942262315125057781760 : ℤ)
  | 62 => (47974262323318168290619565125374198431558495055516794880 : ℤ)
  | 63 => (47294986510576261581063408404733132495902896376229396480 : ℤ)
  | 64 => (46634893353972450300797998304464691856200658748472033280 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta21 (i : ℕ) : ℤ :=
  match i with
  | 19 => (111833332496018385306627830706131666515751190357249884160 : ℤ)
  | 20 => (107511145290540774435846320987657282504409592951587471360 : ℤ)
  | 21 => (103523302113864074066975838525990252365451991858292981760 : ℤ)
  | 22 => (99831484159673103441063093164549795295830359159666114560 : ℤ)
  | 23 => (96403114384752674099623363498064215866532243357323755520 : ℤ)
  | 24 => (93210307339878347245112728020966693060220728589072465920 : ℤ)
  | 25 => (90229043539965509053796279714990273582058281295780249600 : ℤ)
  | 26 => (87438513880682045726982659279983878818169857215404441600 : ℤ)
  | 27 => (84820594303416116214198747325493343524212675861649817600 : ℤ)
  | 28 => (-702420978749403690216355576623246940277832916161796876695240704 : ℤ)
  | 29 => (2809684324476345880805293685383492091079196953949760631986978816 : ℤ)
  | 30 => (-4214526288799798779903669361611494377134327207761730604130893824 : ℤ)
  | 31 => (2809684320220115342282621187179970719907487959903246431043977216 : ℤ)
  | 32 => (-702420987282503816209278187515112792718527510368197384081506304 : ℤ)
  | 33 => (71968989105928825878714088639812533899331967397763481600 : ℤ)
  | 34 => (70205043294509001715020115879032814931211085843896729600 : ℤ)
  | 35 => (68527494828954638326690745865719857708467553590627532800 : ℤ)
  | 36 => (66930043902796379198855642982870877520500938918120652800 : ℤ)
  | 37 => (65406996096372733908163542904005879779050791533071564800 : ℤ)
  | 38 => (63953190686287041348786573098237329608972171083985715200 : ℤ)
  | 39 => (62563938981513808731011381656309098419322290569425715200 : ℤ)
  | 40 => (61234971077712755655564607269449199272500033291812864000 : ℤ)
  | 41 => (59962389711009456144489710712848790721894531970629632000 : ℤ)
  | 42 => (58742630124557535191504991964329780588887598138654720000 : ℤ)
  | 43 => (57572425048120924654782901039117633715676653984887603200 : ℤ)
  | 44 => (56448774042285204265486858989349435812183629473461043200 : ℤ)
  | 45 => (55368916582107538004380037228519952198652202008235212800 : ℤ)
  | 46 => (54330308355771212556288752280463767521961100750671052800 : ℤ)
  | 47 => (53330600336590945276624662515245495098365261942410444800 : ℤ)
  | 48 => (52367620255024725905372480871401900587721628353298432000 : ℤ)
  | 49 => (51439356153953004256365257170795100247000516277567488000 : ℤ)
  | 50 => (50543941757580281716271175655222639366672921324148490240 : ℤ)
  | 51 => (49679643423646167847847198531170887495307345606308003840 : ℤ)
  | 52 => (48844848481603101044600045492280372547078070576653271040 : ℤ)
  | 53 => (48038054787152862926236885167838689051541531646704484352 : ℤ)
  | 54 => (47257861346944161558647045873146824414414438396007022592 : ℤ)
  | 55 => (46502959887057704886162121301061768104263464700201664512 : ℤ)
  | 56 => (45772127255745267961329487794219786614592549205670100992 : ℤ)
  | 57 => (45064218565237618173676082231132326788960908611002826752 : ℤ)
  | 58 => (44378160989697013001044910264776403412289133394589122560 : ℤ)
  | 59 => (43712948146896377372110834866996211551580812054636789760 : ℤ)
  | 60 => (43067635000234576881670508911511943128620151119345090560 : ℤ)
  | 61 => (42441333225473876594079013336528299531581218446335016960 : ℤ)
  | 62 => (41833206993301843636689701425354340916116131587827957760 : ℤ)
  | 63 => (41242469124634349543460934385255679104240028717290618880 : ℤ)
  | 64 => (40668377580621877501829131269928965033073781074538004480 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta22 (i : ℕ) : ℤ :=
  match i with
  | 19 => (97596066999557828368087208539589119152744325014576168960 : ℤ)
  | 20 => (93841085219536178836949308546178533040918198507809013760 : ℤ)
  | 21 => (90375671693891053988533442740082869671235314999739023360 : ℤ)
  | 22 => (87166713680698431821813545653305585570149271995164917760 : ℤ)
  | 23 => (84186051745340749989168726068938374882932105377543618560 : ℤ)
  | 24 => (81409574987684168708224595031436604637504750149456363520 : ℤ)
  | 25 => (78816509518692582069369910293004186280354335109519769600 : ℤ)
  | 26 => (76388853327286888692505108822718632447571364488518041600 : ℤ)
  | 27 => (74110923305510040934628198420759335503478752141744537600 : ℤ)
  | 28 => (71968989105928825878714088639812533899331967397763481600 : ℤ)
  | 29 => (-702420991157850087790291072953262223004131864322480910792392704 : ℤ)
  | 30 => (2809684312481514363150489372264477317777107970727766065693065216 : ℤ)
  | 31 => (-4214526300407700248601867083984734480329897191524951152157261824 : ℤ)
  | 32 => (2809684308974960794481242143630894369936779538132626525143433216 : ℤ)
  | 33 => (-702420998186896104986373017623308041174972040570010626166882304 : ℤ)
  | 34 => (61385314237409880896550252075134220090606678074562969600 : ℤ)
  | 35 => (59923759136519169446632388930488167231306519072787660800 : ℤ)
  | 36 => (58531801897575634732424900221301450222449224785382604800 : ℤ)
  | 37 => (57204504834427618944975360734247562128699321702206668800 : ℤ)
  | 38 => (55937392266645256818859057556662125318612374770207948800 : ℤ)
  | 39 => (54726397211167961107925792503389568852647559879144243200 : ℤ)
  | 40 => (53567815343272705496172120576332531681905794644705280000 : ℤ)
  | 41 => (52458265089184850060599474508496451235996134828670976000 : ℤ)
  | 42 => (51394652912684595920833271589061584305307392994705408000 : ℤ)
  | 43 => (50374143019216974042817307238770183623848997278449664000 : ℤ)
  | 44 => (49394130831538103532201754602775300318025294053323571200 : ℤ)
  | 45 => (48452219697182001390074182473814709823368966429265100800 : ℤ)
  | 46 => (47546200374941361278432853680714241992203075117173964800 : ℤ)
  | 47 => (46674032918970273633021296042185838383734295708355788800 : ℤ)
  | 48 => (45833830638056692580925278281931689483851515338476748800 : ℤ)
  | 49 => (45023845856460559999381247336727152230646937802506240000 : ℤ)
  | 50 => (44242457243360121668493848306813846857067319537791139840 : ℤ)
  | 51 => (43488158511900985061495284612103763494189395108681482240 : ℤ)
  | 52 => (42759548317306857667201613085035066928063887202676899840 : ℤ)
  | 53 => (42055321207458872188117584299845227839593922708939735040 : ℤ)
  | 54 => (41374259499566860530059654738226417394195979109874532352 : ℤ)
  | 55 => (40715225973677904660582128724072957696293350450755796992 : ℤ)
  | 56 => (40077157288314059718419791958221363291823110468258496512 : ℤ)
  | 57 => (39459058035926949901793164229323950307633604697094356992 : ℤ)
  | 58 => (38859995366450650425511074589769177314880566593954250752 : ℤ)
  | 59 => (38279094116313214197764055295300764946244051411727810560 : ℤ)
  | 60 => (37715532388068975215551327480345167059969814771489832960 : ℤ)
  | 61 => (37168537532535492793251321318084686251625727562151362560 : ℤ)
  | 62 => (36637382491124777732892393284930514539699608172321832960 : ℤ)
  | 63 => (36121382461085270154252075342829536638391372270545141760 : ℤ)
  | 64 => (35619891850733660021686396210270324893354718764340346880 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta23 (i : ℕ) : ℤ :=
  match i with
  | 19 => (85525816078841845877574889718104152798698442701238435840 : ℤ)
  | 20 => (82249738440205358143949645520805564130092655495935426560 : ℤ)
  | 21 => (79225534210629064337770677099718004447916608490055925760 : ℤ)
  | 22 => (76424463912661535602953839995734183287006524528247439360 : ℤ)
  | 23 => (73822080150826718583433056071754668159147820239825141760 : ℤ)
  | 24 => (71397444612547024802387423553285412364055714112009666560 : ℤ)
  | 25 => (69132512140202192528914544616409760619383414534543769600 : ℤ)
  | 26 => (67011641396113758820033323355478374724468435479796121600 : ℤ)
  | 27 => (65021202542581355193143951031027110208570127808043417600 : ℤ)
  | 28 => (63149260048829705060244224835913939058727559628429721600 : ℤ)
  | 29 => (61385314237409880896550252075134220090606678074562969600 : ℤ)
  | 30 => (-702421001388735794025271222378304235526501879423593923219554304 : ℤ)
  | 31 => (2809684302580657228084379550240243112110298278694430892376457216 : ℤ)
  | 32 => (-4214526309999155598197160974070711367069619080682244601307725824 : ℤ)
  | 33 => (2809684299674155606994896553244492540370988615313432877482377216 : ℤ)
  | 34 => (-702421007214148198723120208292462758106474995070992695955554304 : ℤ)
  | 35 => (52615983632065612197043073207257902934805724063911116800 : ℤ)
  | 36 => (51398021047990019322111520586719525552055591562431692800 : ℤ)
  | 37 => (50236489162790515692350541832769798858853727748279500800 : ℤ)
  | 38 => (49127489803189476721745064408572006853619495639764172800 : ℤ)
  | 39 => (48067480184926041319301332931644917614688441683725516800 : ℤ)
  | 40 => (47053232931491725995857010993997791341321725119823872000 : ℤ)
  | 41 => (46081801411881256606348919103755187768417175367319552000 : ℤ)
  | 42 => (45150489584731292811010158785266186939495339819794432000 : ℤ)
  | 43 => (44256825675776470235187893440790163364539174613942272000 : ℤ)
  | 44 => (43398539128602214850027505866595840431734602042703872000 : ℤ)
  | 45 => (42573540360714783432585059927760386974624552045038796800 : ℤ)
  | 46 => (41779902932246144770883937683039251117868240551595212800 : ℤ)
  | 47 => (41015847796493501608587082183359537727244917875199180800 : ℤ)
  | 48 => (40279729352573411039630644784359357124296100075588812800 : ℤ)
  | 49 => (39570023062810786366991579090591462943993691045153996800 : ℤ)
  | 50 => (38885314432719571909726222129213730221586269995049943040 : ℤ)
  | 51 => (38224289180868956874714411828859511554066664824598691840 : ℤ)
  | 52 => (37585724450611573436826991143340857716246445293819658240 : ℤ)
  | 53 => (36968480936419133054319513832663914089327408139038883840 : ℤ)
  | 54 => (36371495815106105438437005403999466720093304368702423040 : ℤ)
  | 55 => (35793776387075053175827813640486942840504462921277898752 : ℤ)
  | 56 => (35234394345337736723390141931650259473917754194098388992 : ℤ)
  | 57 => (34692480600821964902932927741104326441769893093296832512 : ℤ)
  | 58 => (34167220601667477410711245946984793403270960035494100992 : ℤ)
  | 59 => (33657850092093880858006815939334073917371526079160778752 : ℤ)
  | 60 => (33163651263195724123051534289039579938693494905514229760 : ℤ)
  | 61 => (32683949253855050551899667474186624429592218208001064960 : ℤ)
  | 62 => (32218108965002437882239204215251281405609059975493058560 : ℤ)
  | 63 => (31765532154822406233166182802777005008699078166404136960 : ℤ)
  | 64 => (31325654786287623209209086899459675693812725545969909760 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta24 (i : ℕ) : ℤ :=
  match i with
  | 19 => (75241493439224272852408697058464699716231968127073648640 : ℤ)
  | 20 => (72371820170825442828314121416289677064997011685260656640 : ℤ)
  | 21 => (69722123289713545716082247138125111050377006909289922560 : ℤ)
  | 22 => (67267356112432334292988160461704844690006216657348853760 : ℤ)
  | 23 => (64986206601342924255770563211547682649005280166527631360 : ℤ)
  | 24 => (62860416894146382709049082486909271714396627726510325760 : ℤ)
  | 25 => (60874247886133902362978808911833831777094569299227443200 : ℤ)
  | 26 => (59014053749420344029483184384244779285766929137637785600 : ℤ)
  | 27 => (57267940723509015820580902391171355662467375467960729600 : ℤ)
  | 28 => (55625491179712495872243402244016770398783391368059289600 : ℤ)
  | 29 => (54077538732956323646960936351903955794105883065686425600 : ℤ)
  | 30 => (52615983632065612197043073207257902934805724063911116800 : ℤ)
  | 31 => (-702421009875184766939079641256219268955195901166452643205218304 : ℤ)
  | 32 => (2809684294359409785574127644452262923476250945131036507390345216 : ℤ)
  | 33 => (-4214526317971274330328314337259055792411725585955839156445773824 : ℤ)
  | 34 => (2809684291936510955220541818385217068715414654312591103377801216 : ℤ)
  | 35 => (-702421014730717289018207665012901787714746842900381847942856704 : ℤ)
  | 36 => (45308208127612054947453757484027638638304929055034572800 : ℤ)
  | 37 => (44287752989602774430619213396549538668973736959200460800 : ℤ)
  | 38 => (43313333421729250929581716410762180051642448266185932800 : ℤ)
  | 39 => (42381850876001577722124157587128685964541838708493516800 : ℤ)
  | 40 => (41490482230917839794670948780737679747837726175736627200 : ℤ)
  | 41 => (40636649561727626947437124017502925129760051453493248000 : ℤ)
  | 42 => (39817993836635350392415219912414961228559351073996800000 : ℤ)
  | 43 => (39032351953095756509028406086747826133122581207711744000 : ℤ)
  | 44 => (38277736626678105212796635121783583485583978697588736000 : ℤ)
  | 45 => (37552318725039369050356053288011628994533966035602636800 : ℤ)
  | 46 => (36854411705055477758993421535667136655623929864178892800 : ℤ)
  | 47 => (36182457865005122196730419256735218890761248629902540800 : ℤ)
  | 48 => (35535016168153333671395095390936839504869321618541772800 : ℤ)
  | 49 => (34910751430934062856258902620353448661560822109883596800 : ℤ)
  | 50 => (34308424699604225147287271769865672650513118638762885120 : ℤ)
  | 51 => (33726884664870002086486705148110014247585708812313559040 : ℤ)
  | 52 => (33165059985478032624998731712777020887258422126145699840 : ℤ)
  | 53 => (32621952409850666625785191784165583854472320382129930240 : ℤ)
  | 54 => (32096630600116761554593303350510404558326878133121187840 : ℤ)
  | 55 => (31588224575827413420523998748794202816929147635619594240 : ℤ)
  | 56 => (31095920705640623515377539246981772935611094701285834752 : ℤ)
  | 57 => (30618957184630226881544258316978513602443567872702676992 : ℤ)
  | 58 => (30156619942885274196291283499099334809459054811925184512 : ℤ)
  | 59 => (29708238937933103495707595675183276205406068165671124992 : ℤ)
  | 60 => (29273184789421746508253226505395915339471049073834852352 : ℤ)
  | 61 => (28850865719583788697064397140903686255512697851095285760 : ℤ)
  | 62 => (28440724767398146342460709957472277418720788848008232960 : ℤ)
  | 63 => (28042237248171833739616738087691130379037177113277890560 : ℤ)
  | 64 => (27654908433567280280272192708459981341917380973911080960 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta25 (i : ℕ) : ℤ :=
  match i with
  | 19 => (66437585994632444056833714830689093516841662517650391040 : ℤ)
  | 20 => (63914441407321259115545257687457790056655735863315005440 : ℤ)
  | 21 => (61584151569013048793206083920092620246352980957871472640 : ℤ)
  | 22 => (59424803260710805955297302255391556814398613942236610560 : ℤ)
  | 23 => (57417745649907974521802561008655358029505145123645685760 : ℤ)
  | 24 => (55546996574757079475051030402375257932691753280062095360 : ℤ)
  | 25 => (53798775268623971719558330990103743986735641915503411200 : ℤ)
  | 26 => (52161130938516199488468470934136208962035929096336179200 : ℤ)
  | 27 => (50623644836899593113288044109424846204599349683001753600 : ℤ)
  | 28 => (49177189272149720294249874269023563048484352422418841600 : ℤ)
  | 29 => (47813731157710417433027237160563729254248058772363673600 : ℤ)
  | 30 => (46526170711687647822385310104566016021055061556513996800 : ℤ)
  | 31 => (45308208127612054947453757484027638638304929055034572800 : ℤ)
  | 32 => (-702421016954592286878463226795868875834514438401597808054370304 : ℤ)
  | 33 => (2809684287494529766238967803928966334987214787812107862688137216 : ℤ)
  | 34 => (-4214526324634246113800675358943431893004025385706564017480269824 : ℤ)
  | 35 => (2809684285463909794133105397320394570997180563126172666944290816 : ℤ)
  | 36 => (-702421021023523973408770852159256993829696653776066438919880704 : ℤ)
  | 37 => (39185477299556371846446492959159038822317776480029900800 : ℤ)
  | 38 => (38326146657022240884901613727598533584986246294064332800 : ℤ)
  | 39 => (37504588789984115679908157758963764841603354797591756800 : ℤ)
  | 40 => (36718324860050070853692437901625231134753722576614195200 : ℤ)
  | 41 => (35965090995843198947420490550978211621215173851951923200 : ℤ)
  | 42 => (35242815260821429929883105269404396720438036089798656000 : ℤ)
  | 43 => (34549597542726971910153155088690817200849475602481152000 : ℤ)
  | 44 => (33883691938594386628635933645381049015133384724185088000 : ℤ)
  | 45 => (33243491279165654663079550956891623636883431024807116800 : ℤ)
  | 46 => (32627513493777189164763253561486885664283430268751052800 : ℤ)
  | 47 => (32034389563820152764583447335238664460059575709387980800 : ℤ)
  | 48 => (31462852851712199806370652852149006532604485186669772800 : ℤ)
  | 49 => (30911729624519450513491650749709529439736165592517836800 : ℤ)
  | 50 => (30379930618172857361513526871950684797730329204380139520 : ℤ)
  | 51 => (29866443510622651132831021036137472784012635398073221120 : ℤ)
  | 52 => (29370326191061150649231536159261202840056388710867927040 : ℤ)
  | 53 => (28890700728156140648823848931264979506286259007746211840 : ℤ)
  | 54 => (28426747953590291167687621646755617313888530654811914240 : ℤ)
  | 55 => (27977702588515665650279325397416982863935520946299863040 : ℤ)
  | 56 => (27542848850147765657358484687720306509937636112848650240 : ℤ)
  | 57 => (27121516483920267818232472801014436212952767591195082752 : ℤ)
  | 58 => (26713077173629187661936175775251993030175901574854868992 : ℤ)
  | 59 => (26316941288002896658371473542825806111297620146244288512 : ℤ)
  | 60 => (25932554927298765583419782551514306318880657411084910592 : ℤ)
  | 61 => (25559397237978135446986525072278895778954251610307428352 : ℤ)
  | 62 => (25196977967357010072269739279288554107262300346657013760 : ℤ)
  | 63 => (24844835233460681664091364125406591812506111938878504960 : ℤ)
  | 64 => (24502533488202141946846913284251471110419604530853314560 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta26 (i : ℕ) : ℤ :=
  match i with
  | 19 => (58867555801555757331726153199708522768362805284978032640 : ℤ)
  | 20 => (56641216669743351095222091590899333811262218397642915840 : ℤ)
  | 21 => (54584565859807837247343711744800876051341979558545981440 : ℤ)
  | 22 => (52678361273659327919013699156647384150371668121501040640 : ℤ)
  | 23 => (50906221239068116423461108133835244026938227750925762560 : ℤ)
  | 24 => (49254104545833730387126208308830558274855608356972789760 : ℤ)
  | 25 => (47709901114845805105761731810543450168228197984056115200 : ℤ)
  | 26 => (46263106557170823287549390036419313443982223361651507200 : ℤ)
  | 27 => (44904561068227982479867268534291942513458563081515827200 : ℤ)
  | 28 => (43626238176264526712136884652432160700614032454424985600 : ℤ)
  | 29 => (42421072496364138941414272034685797734291632339655065600 : ℤ)
  | 30 => (41282818274451022125286155000703889450528429359025356800 : ℤ)
  | 31 => (40205932437565652363281037046637138791648968575864012800 : ℤ)
  | 32 => (39185477299556371846446492959159038822317776480029900800 : ℤ)
  | 33 => (-702421022891785817114277142924125384798005169055806365634658304 : ℤ)
  | 34 => (2809684281731959575127736650039776193934414961000670145036681216 : ℤ)
  | 35 => (-4214526330232171442308728479864359458598173788894817800341684224 : ℤ)
  | 36 => (2809684280021482391416942640869492771113980726693148155829026816 : ℤ)
  | 37 => (-702421026318858743619091371949323609932269467602792990275272704 : ℤ)
  | 38 => (34029493444351586077177217569796007398328595364236492800 : ℤ)
  | 39 => (33302367516053475263562319758475579889817300591496396800 : ℤ)
  | 40 => (32606404127539569199102346139068884988813632737588019200 : ℤ)
  | 41 => (31939608116201732823637987540752177619836920566854451200 : ℤ)
  | 42 => (31300153222086488013319717579649754618558295699567411200 : ℤ)
  | 43 => (30686364412035805296575373529967299182959224871190528000 : ℤ)
  | 44 => (30096702395050111473056962706968199152858819184295936000 : ℤ)
  | 45 => (29529750016421456423475212205474489145986965115292876800 : ℤ)
  | 46 => (28984200268344309897161453896113467243153237929151692800 : ℤ)
  | 47 => (28458845695952043223651924523278477278930475324067020800 : ℤ)
  | 48 => (27952569011783030697245270985326264582734807326051532800 : ℤ)
  | 49 => (27464334759920733291427133162438900530327161056054476800 : ℤ)
  | 50 => (26993181894563813328847001453793625557504387944514846720 : ℤ)
  | 51 => (26538217157432036592254066777915484913189370725945835520 : ℤ)
  | 52 => (26098609154896076916826550559295257512635926121147269120 : ℤ)
  | 53 => (25673583049593568399566772672548085970026409797657559040 : ℤ)
  | 54 => (25262415793012032144523247731342846281997576000336035840 : ℤ)
  | 55 => (24864431835448802818010667741377522875496005520263741440 : ℤ)
  | 56 => (24478999258198132449703745668920640111942862332011479040 : ℤ)
  | 57 => (24105526280011241811178967761478285560611515368986378240 : ℤ)
  | 58 => (23743458096027477141814671683845553555856407549813194752 : ℤ)
  | 59 => (23392274012649834115627150948204616858793039161293012992 : ℤ)
  | 60 => (23051484846373199004500932462895886209437805439575130112 : ℤ)
  | 61 => (22720630558482669530432365095845532644920183929115246592 : ℤ)
  | 62 => (22399278100917137717434388543314457164251205119982436352 : ℤ)
  | 63 => (22087019451519202782869223965069582772157714911734005760 : ℤ)
  | 64 => (21783469819432840113587731862972291904512535651376168960 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta27 (i : ℕ) : ℤ :=
  match i with
  | 19 => (52331223602291501738423801718152597670985381621624995840 : ℤ)
  | 20 => (50360182440467860812431848807259520918780656443918909440 : ℤ)
  | 21 => (48538956325850116314941801693328855859279219501396131840 : ℤ)
  | 22 => (46850590077000658593439798660756328915358207884855869440 : ℤ)
  | 23 => (45280645307495939641366477945822165150735016955362672640 : ℤ)
  | 24 => (43816743438161535990715854473461075818953103716709826560 : ℤ)
  | 25 => (42448205856963413171690764794871356795189889284125491200 : ℤ)
  | 26 => (41165767760162807783227651508659602591626545029395251200 : ℤ)
  | 27 => (39961348511920529569553609004975608370217668664570675200 : ℤ)
  | 28 => (38827865810308056394657051111114084049471313909330739200 : ℤ)
  | 29 => (37759084134134942905727019554191469769867722908866969600 : ℤ)
  | 30 => (36749490255638874595218069106386463167903533112282316800 : ℤ)
  | 31 => (35794190299555605016064023134607759224991559138987212800 : ℤ)
  | 32 => (34888824086885717038722096801356512635660125550202060800 : ℤ)
  | 33 => (34029493444351586077177217569796007398328595364236492800 : ℤ)
  | 34 => (-702421027896123088342451566038422086238594492339423330963554304 : ℤ)
  | 35 => (2809684276870603368791795781871602255392128189810870807288610816 : ℤ)
  | 36 => (-4214526334958489976246448768361195232180952594218233823152308224 : ℤ)
  | 37 => (2809684275422902196234295873683382288709114862054148782283554816 : ℤ)
  | 38 => (-702421030796423670507457961051589079642270441067081853990600704 : ℤ)
  | 39 => (29666737874562921195487830701873442347260826727795916800 : ℤ)
  | 40 => (29048680835509527003915167562251078965026226170966835200 : ℤ)
  | 41 => (28456465902618644067739270825679127989017462571217715200 : ℤ)
  | 42 => (27888477944255115433497842591966938643845421118731059200 : ℤ)
  | 43 => (27343235379720024515973529490138590967589854378144563200 : ℤ)
  | 44 => (26819376520632215969623416987945025614967339034345472000 : ℤ)
  | 45 => (26315647567899935242259494088101976108600086366047436800 : ℤ)
  | 46 => (25830892033339762284651601600061879646168639532223692800 : ℤ)
  | 47 => (25364041391285630527248983941879849434820408635083980800 : ℤ)
  | 48 => (24914106795498753007279297693091393174937913306959052800 : ℤ)
  | 49 => (24480171721543072934268003886367488317599236370517196800 : ℤ)
  | 50 => (24061385415485574683709411405459299790494301519630827520 : ℤ)
  | 51 => (23656957047078363713437470319499899341981976634295582720 : ℤ)
  | 52 => (23266150480090537930987026626973561124888544248615403520 : ℤ)
  | 53 => (22888279584674229173696624373465445493925681275464581120 : ℤ)
  | 54 => (22522704026968421540568882156826233433144132449117143040 : ℤ)
  | 55 => (22168825479889160682961682497725027427604067330859991040 : ℤ)
  | 56 => (21826084206488839775405559029788593643502380934171197440 : ℤ)
  | 57 => (21493955973605888056968902022447306129633336422867927040 : ℤ)
  | 58 => (21171949258946449907974035212357940095238360596207370240 : ℤ)
  | 59 => (20859602719387512220019992228778095301760763874877898752 : ℤ)
  | 60 => (20556482892287201942529049484054949575598989547606638592 : ℤ)
  | 61 => (20262182105032905063748701514551951176787920573654106112 : ℤ)
  | 62 => (19976316571034960975821299162797467532151748819096174592 : ℤ)
  | 63 => (19698524652952726124007625244124297846923538821233508352 : ℤ)
  | 64 => (19428465276179235120589753842429269694163293398903029760 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta28 (i : ℕ) : ℤ :=
  match i with
  | 19 => (46665102170359356602689808964082808840054242898167726080 : ℤ)
  | 20 => (44914539133650771439551844042684237084170174939676016640 : ℤ)
  | 21 => (43296673422714784337315698640146796550385221508729405440 : ℤ)
  | 22 => (41796515899813088770512749261084891689447213426897059840 : ℤ)
  | 23 => (40401299234704371377029400682088189274649332509248061440 : ℤ)
  | 24 => (39100074916961997725639846549598531328389011387071856640 : ℤ)
  | 25 => (37883395863248951751618288333086387349500938371150643200 : ℤ)
  | 26 => (36743063958009005249481566582972617882255114913395507200 : ℤ)
  | 27 => (35671927413021526080359534712016372527318984524247859200 : ℤ)
  | 28 => (34663716748605722213216496379641065093921092463178547200 : ℤ)
  | 29 => (33712911004348932050607425128032456058564274818331443200 : ℤ)
  | 30 => (32814627821707789373145714437212562711990918454234316800 : ℤ)
  | 31 => (31964532533935177628203902864148811176409851381992652800 : ℤ)
  | 32 => (31158762506655148579269049587440033858232054962769100800 : ℤ)
  | 33 => (30393863802861032009102728513193869855772121500536012800 : ℤ)
  | 34 => (29666737874562921195487830701873442347260826727795916800 : ℤ)
  | 35 => (-702421032134228498994297451108112186506229113376684292077256704 : ℤ)
  | 36 => (2809684272750223108435834504720514657909705641580200428428066816 : ℤ)
  | 37 => (-4214526338967508607944140821805496678380066424929156353935540224 : ℤ)
  | 38 => (2809684271519384054844437821645509827936293500572461054941986816 : ℤ)
  | 39 => (-702421034599851603143729909191054554241429716356931434477256704 : ℤ)
  | 40 => (25958395640242556046051851864139262053853223386821427200 : ℤ)
  | 41 => (25430785972757951248367871135193342093409052179772211200 : ℤ)
  | 42 => (24924711393742105830181195742122765804819745103622963200 : ℤ)
  | 43 => (24438857261166403666580652975470026743001138941080371200 : ℤ)
  | 44 => (23972015166701510743759003274016608882673851340895027200 : ℤ)
  | 45 => (23523072312347446947902546909959087576382802731257036800 : ℤ)
  | 46 => (23091002146751791634054295098767906288245648678243532800 : ℤ)
  | 47 => (22674856089237323859599704716883853864545147327139020800 : ℤ)
  | 48 => (22273756196018659569385668243768032523647405850938572800 : ℤ)
  | 49 => (21886888645033148803658090478614511302768441191877836800 : ℤ)
  | 50 => (21513497934086780814719220816180144082873153697737605120 : ℤ)
  | 51 => (21152881702293131429249820160177589756449122428670443520 : ℤ)
  | 52 => (20804386097601159752332871213550529885514589448930590720 : ℤ)
  | 53 => (20467401623999696308771193541891160903448843613917675520 : ℤ)
  | 54 => (20141359411103588322262565975143830461771901022890885120 : ℤ)
  | 55 => (19825727856553610522797261183928647765211330019317514240 : ℤ)
  | 56 => (19520009598231757004793126185057755789455779230163927040 : ℤ)
  | 57 => (19223738778895601074046977389273379402514589115943485440 : ℤ)
  | 58 => (18936478570626325884944089030906492134179816877368279040 : ℤ)
  | 59 => (18657818930593659976153032610504258540385748161648394240 : ℤ)
  | 60 => (18387374563173935453729339670288641772822361647561572352 : ℤ)
  | 61 => (18124783066503355942898899426524339547134987356803694592 : ℤ)
  | 62 => (17869703244181056580241618393433125181041079708509274112 : ℤ)
  | 63 => (17621813565117268817449249107093226076019937174033006592 : ℤ)
  | 64 => (17380810756502497905610138470540435163543786733124452352 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta29 (i : ℕ) : ℤ :=
  match i with
  | 19 => (41734933948902975517776009654572440557625428728799559680 : ℤ)
  | 20 => (40175503260298717591176845998047993326590937051462369280 : ℤ)
  | 21 => (38733968743116829523825212646460603261824169371385200640 : ℤ)
  | 22 => (37397038049932385235940277761933327901782216193542717440 : ℤ)
  | 23 => (36153386412803837456153651029750269503826947473240227840 : ℤ)
  | 24 => (34993300142987172200768598210392509680096577636993597440 : ℤ)
  | 25 => (33908395788913486516429476176770678917618366709707571200 : ℤ)
  | 26 => (32891396701663844819685239897674990800683010796761907200 : ℤ)
  | 27 => (31935953654260383759471964385909791575985999471391539200 : ℤ)
  | 28 => (31036499620121069643564561164848647160559480348029747200 : ℤ)
  | 29 => (30188131293391488412173073644444640601877433258554163200 : ℤ)
  | 30 => (29386511730975172709598783150675912382922070920527872000 : ℤ)
  | 31 => (28627789815217054527008318975254617219433946940230860800 : ℤ)
  | 32 => (27908533215147278246008301010377051480495285227801804800 : ℤ)
  | 33 => (27225672258133549178352102335297721425830051419311308800 : ℤ)
  | 34 => (26576452679295950237624515003761625436087823943650508800 : ℤ)
  | 35 => (25958395640242556046051851864139262053853223386821427200 : ℤ)
  | 36 => (-702421035739561226805763568615313834303348843078520873580232704 : ℤ)
  | 37 => (2809684269242331805700353957956750892485481039708143213992738816 : ℤ)
  | 38 => (-4214526342383086981660266617338635081556285116225633115359412224 : ℤ)
  | 39 => (2809684268191384613787699867023477537662029134693842672016162816 : ℤ)
  | 40 => (-702421037844651058174049414947536037258837473088584357829935104 : ℤ)
  | 41 => (22792737635334927259947967490463742291188196144526131200 : ℤ)
  | 42 => (22340500777490980290504555437081525182236049395626803200 : ℤ)
  | 43 => (21906293296039483034128654827687967891580998198178611200 : ℤ)
  | 44 => (21489039574775204115892942536363292418699636283487027200 : ℤ)
  | 45 => (21087748984452337849753241955778913098912382075692646400 : ℤ)
  | 46 => (20701507568842821290722997794291776483572669754428620800 : ℤ)
  | 47 => (20329470695662158012133885325987133729325092998794444800 : ℤ)
  | 48 => (19970856543378724271469303481036014067268769891011788800 : ℤ)
  | 49 => (19624940314361255891217111931100760885499117750242508800 : ℤ)
  | 50 => (19291049081008893199052905292200585097383118853195694080 : ℤ)
  | 51 => (18968557185043392967067078476558647803083621993147269120 : ℤ)
  | 52 => (18656882121500577963283295942471891482040158641476075520 : ℤ)
  | 53 => (18355480848521673332894017264103429691754851393570078720 : ℤ)
  | 54 => (18063846472125385563766392443359747750314285892915691520 : ℤ)
  | 55 => (17781505261990628681712397623858443002330698896816209920 : ℤ)
  | 56 => (17508013960103382304399774410344785081831577931208458240 : ℤ)
  | 57 => (17242957349087673141104367249606943328591461389214679040 : ℤ)
  | 58 => (16985946051288484173525266021675167156492759513631293440 : ℤ)
  | 59 => (16736614533317634694600711754284520773683780997129175040 : ℤ)
  | 60 => (16494619293906780305648711621825986702564646212746608640 : ℤ)
  | 61 => (16259637215613070204052958369949357997916359730608996352 : ℤ)
  | 62 => (16031364063257988519830201695545366800856501599801966592 : ℤ)
  | 63 => (15809513114003075941666074594691913906925744519079002112 : ℤ)
  | 64 => (15593813905723319126351448180207346228062654096937582592 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta3 (i : ℕ) : ℤ :=
  match i with
  | 19 => (4665569129960470213652464781408567802429690502813266739200 : ℤ)
  | 20 => (4465755593757048770506363127644661966341200373074414796800 : ℤ)
  | 21 => (4282594850946973497055532041001311778286849659484556492800 : ℤ)
  | 22 => (4114067472731805497282492733720748586672143454144613580800 : ℤ)
  | 23 => (3958470303471621887076939165192954357769048227077475532800 : ℤ)
  | 24 => (3814356521741765060549538711517124268760075718399675596800 : ℤ)
  | 25 => (3680488896508810660995762200712951147240773210489267159040 : ℤ)
  | 26 => (3555802957107890821588495521134566445038779236859343011840 : ℤ)
  | 27 => (3439377699037732808127883869794499218339510886875780874240 : ℤ)
  | 28 => (3330412079772018799393999753954907397819152752294326435840 : ℤ)
  | 29 => (3228206007518697577658784115233698759600448351660712919040 : ℤ)
  | 30 => (3132144848564627737804131665405400091409121304301461831680 : ℤ)
  | 31 => (3041686713737969417337750312487179813155445762315025121280 : ℤ)
  | 32 => (2956351957427298431488298746279973624121922612262684590080 : ℤ)
  | 33 => (2875714451208403163425659555570988070821729981577853665280 : ℤ)
  | 34 => (2799394290730381343515934093488889591637387980922609991680 : ℤ)
  | 35 => (2727051667733291055082491443234626659624505841119295176704 : ℤ)
  | 36 => (2658381695044584156387168459907535649253629743824512221184 : ℤ)
  | 37 => (2593110015537191427462643917670480111629354990797506740224 : ℤ)
  | 38 => (2530989059525251917611256514503830103937337675085128925184 : ℤ)
  | 39 => (2471794841265250687550983417297666304430255604078900936704 : ℤ)
  | 40 => (2415324205850511183572507970571451597879605523677047685120 : ℤ)
  | 41 => (2361392454124317588060046926842834788642746272677646827520 : ℤ)
  | 42 => (2309831286259180712497112620854055255465881917819946270720 : ℤ)
  | 43 => (2260487015089088309078611517192641395776034428040008171520 : ℤ)
  | 44 => (2213219008695881961978833184041367669809820156759763845120 : ℤ)
  | 45 => (2167898328568129131052349806885029820487954435529674588160 : ℤ)
  | 46 => (2124406535201397870541471601452975928164911865579029135360 : ℤ)
  | 47 => (2082634637549318648666129635407332610112305043222780968960 : ℤ)
  | 48 => (2042482166465725587841653229097198721185944195613180559360 : ℤ)
  | 49 => (2003856355357018085860921207254844941141315569976512348160 : ℤ)
  | 50 => (1966671413815072191496319130042027130011286635896226447360 : ℤ)
  | 51 => (1930847882123307162277985686343968160557624719196091842560 : ℤ)
  | 52 => (1896312056300643641464684344282907671217097520177123164160 : ℤ)
  | 53 => (1862995474833198344293944895469000290854105059223467458560 : ℤ)
  | 54 => (1830834459492457258341361152039474000658256009704620687360 : ℤ)
  | 55 => (1799769703692431798418998255302997339181185553811604766720 : ℤ)
  | 56 => (1769745902730274123410732197812017664512916558961568645120 : ℤ)
  | 57 => (1740711421012183271437595755487139194426723877001699000320 : ℤ)
  | 58 => (1712617992011403667996188922978807745662902433037282181120 : ℤ)
  | 59 => (1685420447255955259375348526959896409811887146488530206720 : ℤ)
  | 60 => (1659076471115480644349822390059931973172455439950862614528 : ℤ)
  | 61 => (1633546378561684802565614842139583648263317579182152613888 : ℤ)
  | 62 => (1608792913425593128849946587277550361062214159451100807168 : ℤ)
  | 63 => (1584781064975847964773364668258576790918660270294604709888 : ℤ)
  | 64 => (1561477900902668388386949579585350818676559499993471254528 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta30 (i : ℕ) : ℤ :=
  match i with
  | 19 => (37429889332182964550087818253638645497071512232373780480 : ℤ)
  | 20 => (36036749540069243702789017781956504984828379692668026880 : ℤ)
  | 21 => (34748660966171353957855901357461388019165176064670433280 : ℤ)
  | 22 => (33553801098722527873837038216809752741099579338538352640 : ℤ)
  | 23 => (32442095085729140179429850046615123055871738770819645440 : ℤ)
  | 24 => (31404899405442394276997824469236989859829406609797283840 : ℤ)
  | 25 => (30434752615920186748779004712299761221858938408088371200 : ℤ)
  | 26 => (29525177012887538966439482428604574630851405912683315200 : ℤ)
  | 27 => (28670519361787006438213394066107631117129641140368179200 : ℤ)
  | 28 => (27865821933664861034481255905469837595416678731297587200 : ℤ)
  | 29 => (27106717269201254598745946080285932972423584461042483200 : ℤ)
  | 30 => (26389341687502333868848412396034016886679400567799808000 : ℤ)
  | 31 => (25710263725275990893478143232859179755311071542378496000 : ℤ)
  | 32 => (25066424559695972142641449054869657486435791292648652800 : ℤ)
  | 33 => (24455088118884410479349518057276484466678891872570572800 : ℤ)
  | 34 => (23873799076466648110712695351405994618302375515704524800 : ℤ)
  | 35 => (23320347302819532057631948219409662251632367351575347200 : ℤ)
  | 36 => (22792737635334927259947967490463742291188196144526131200 : ℤ)
  | 37 => (-702421038819660907256429414554228360041692395941790622840520704 : ℤ)
  | 38 => (2809684266243287379998389844805702538477093896130748984449826816 : ℤ)
  | 39 => (-4214526345305232832344231650665297580333687974070273646708916224 : ℤ)
  | 40 => (2809684265342292409370833959529981601354061348295318153950396416 : ℤ)
  | 41 => (-702421040624253208824650300307044267803196289087144863259951104 : ℤ)
  | 42 => (20079316488271245443287495170170439637475315651130163200 : ℤ)
  | 43 => (19690182447800872469580373170748531892563003332309811200 : ℤ)
  | 44 => (19316209473842332209134567612862542631218703181755187200 : ℤ)
  | 45 => (18956513170849101087009835037422876608567614489650790400 : ℤ)
  | 46 => (18610277502350715321498028098119810675957143364331110400 : ℤ)
  | 47 => (18276748245934850305622150188923293261105840377351372800 : ℤ)
  | 48 => (17955227191981436422555972045730493907326322567072972800 : ℤ)
  | 49 => (17645066988752711285760327206498897506943443753815244800 : ℤ)
  | 50 => (17345666550827763165222315182054386656380298135789895680 : ℤ)
  | 51 => (17056466959897625820626633969606100559031334917457838080 : ℤ)
  | 52 => (16776947797030419192072081602475595659700141594635141120 : ℤ)
  | 53 => (16506623854016150863288204669786632775324291080671723520 : ℤ)
  | 54 => (16245042178583254142158094348319749849978166565373214720 : ℤ)
  | 55 => (15991779414367664903771122671499407542024449879776952320 : ℤ)
  | 56 => (15746439401692867319217043383638466012046038526769233920 : ℤ)
  | 57 => (15508651009635406228965742174339193652779981778179850240 : ℤ)
  | 58 => (15278066173627765618695059707325586234523513445721047040 : ℤ)
  | 59 => (15054358116090608982004251827568070352154776789518909440 : ℤ)
  | 60 => (14837219730373057422938381130079208916084764651751997440 : ℤ)
  | 61 => (14626362110682605940079206089820761924598400627129712640 : ℤ)
  | 62 => (14421513212763479295992638411040991684110860041534308352 : ℤ)
  | 63 => (14222416631882200642056553482016498365047914604204654592 : ℤ)
  | 64 => (14028830486242534749482639634499434040426666695287898112 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta31 (i : ℕ) : ℤ :=
  match i with
  | 19 => (33658025670463025613826878452884687701507121671233863680 : ℤ)
  | 20 => (32410060210115153189265944461096035587702683319591239680 : ℤ)
  | 21 => (31255959900004661454387233217630209833048542632875130880 : ℤ)
  | 22 => (30185179946109707266199652455149924465193513416686305280 : ℤ)
  | 23 => (29188732296924431038339756658077048472083206370901360640 : ℤ)
  | 24 => (28258904150672630712078288552829614798064381343500861440 : ℤ)
  | 25 => (27389036107788145188340325435202901932334343479571251200 : ℤ)
  | 26 => (26573345598944947240454486410343907445421377705947955200 : ℤ)
  | 27 => (25806785070615086106571427767461900623911532643955507200 : ℤ)
  | 28 => (25084927131738569751912055642862909753294763345523507200 : ℤ)
  | 29 => (24403870814997404923569618807164589382058865687999283200 : ℤ)
  | 30 => (23760164521156047024864696885257526366177698519187456000 : ℤ)
  | 31 => (23150742253910197507027848658909752429022091591811072000 : ℤ)
  | 32 => (22572870523983608792964472112520048561955553471889408000 : ℤ)
  | 33 => (22024103879654874348203949786662015117121349527325900800 : ℤ)
  | 34 => (21502247458844521443571945238133772755285463100345548800 : ℤ)
  | 35 => (21005325292427898761671624612810217527234473279828787200 : ℤ)
  | 36 => (20531553346115192412730907223552656746427462400029491200 : ℤ)
  | 37 => (20079316488271245443287495170170439637475315651130163200 : ℤ)
  | 38 => (-702421041461676234660540657092056671906223927188542682199752704 : ℤ)
  | 39 => (2809684263669016035348230172589357003839858045172375183022882816 : ℤ)
  | 40 => (-4214526347815147393378137331076234476604992928754688103100186624 : ℤ)
  | 41 => (2809684262893595276654828417665652922064983343725157708690620416 : ℤ)
  | 42 => (-702421043014648028856941424507936549966343864977063393156399104 : ℤ)
  | 43 => (17744512245449007601044763173638993168001441738208051200 : ℤ)
  | 44 => (17408441937770049123752248719592800115577172008317747200 : ℤ)
  | 45 => (17085174308478860493213734816176938227054779220518502400 : ℤ)
  | 46 => (16773978769950052669261194258056524474059428005832294400 : ℤ)
  | 47 => (16474180003598455167956805207676146884736365103572582400 : ℤ)
  | 48 => (16185152778406595571946369442030539132202161663691980800 : ℤ)
  | 49 => (15906317346239472601812350089590653127992106684304588800 : ℤ)
  | 50 => (15637135339925586741431577689481853543195912188702228480 : ℤ)
  | 51 => (15377106110801170474703933302625912182118012287639879680 : ℤ)
  | 52 => (15125763451410006066464374818628173670812554566387630080 : ℤ)
  | 53 => (14882672656627471508743072624157629656164734457736069120 : ℤ)
  | 54 => (14647427882879924433354177339215295771854354446307819520 : ℤ)
  | 55 => (14419649770558595465495594787395164428389501506179563520 : ℤ)
  | 56 => (14198983299343446560620453459877046860107010982354616320 : ℤ)
  | 57 => (13985095850090126490858491175728778324548203820529745920 : ℤ)
  | 58 => (13777675450301678173509923625186569546101075256530698240 : ℤ)
  | 59 => (13576429183096304140450356726802667621178147712574423040 : ℤ)
  | 60 => (13381081742068005195063627230053867049031833818591395840 : ℤ)
  | 61 => (13191374116580332386603340542360320421209738778708541440 : ℤ)
  | 62 => (13007062393886537759168924221258629695769746139135344640 : ℤ)
  | 63 => (12827916666075285213192043556265559966850914354936676352 : ℤ)
  | 64 => (12653720031236009591799717921846932768370155568960110592 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta32 (i : ℕ) : ℤ :=
  match i with
  | 19 => (30342710373585105194497271103041834673693438351853486080 : ℤ)
  | 20 => (29221897609100773713565687659474939409506761236681850880 : ℤ)
  | 21 => (28185176342151103760445762753086751500083292429541703680 : ℤ)
  | 22 => (27223116207857159726877059769075893203957305874191482880 : ℤ)
  | 23 => (26327677284055575179016008286967534646062765212728033280 : ℤ)
  | 24 => (25491958912455887788122097663568924895416239342108016640 : ℤ)
  | 25 => (24710001701582829191869335918101816164464092995859251200 : ℤ)
  | 26 => (23976629906740259111216332517195403246180220068377395200 : ℤ)
  | 27 => (23287324812750686573594345081892242043939629235909427200 : ℤ)
  | 28 => (22638122169642049034956291486454937558196989476418355200 : ℤ)
  | 29 => (22025528468730120165525027509476876448466928563073843200 : ℤ)
  | 30 => (21446452107422570323395491611558090520725292064964608000 : ℤ)
  | 31 => (20898146417051368379534896373380269403596820819476480000 : ℤ)
  | 32 => (20378162215558790069364604413028659746521866320216064000 : ℤ)
  | 33 => (19884308062551940974624356480150504142561395632766976000 : ℤ)
  | 34 => (19414616784735902642167955202303339651238784565824716800 : ℤ)
  | 35 => (18967317138066091786279836213328202302713828566315827200 : ℤ)
  | 36 => (18540809702782203261526518616471468476123161927299891200 : ℤ)
  | 37 => (18133646285919380574751885173060900912913754057028403200 : ℤ)
  | 38 => (17744512245449007601044763173638993168001441738208051200 : ℤ)
  | 39 => (-702421043736613702025798041841385283911223051291291622995656704 : ℤ)
  | 40 => (2809684261450952004667104222458761607134983899172194965746876416 : ℤ)
  | 41 => (-4214526349979112301359723623886571448999992095584132217515802624 : ℤ)
  | 42 => (2809684260781153342672803703255562068060341299915462263665852416 : ℤ)
  | 43 => (-702421045077963406234733006024769477133668651953975223180591104 : ℤ)
  | 44 => (15728090399375256737289676449361834853455823358866227200 : ℤ)
  | 45 => (15436829466053492723636163922521800874688122926294630400 : ℤ)
  | 46 => (15156422977451794449621912732085743317489405118539366400 : ℤ)
  | 47 => (14886264701285264626596857750222589030655019310278246400 : ℤ)
  | 48 => (14625793311364183542847975710422085096402881589175910400 : ℤ)
  | 49 => (14374488263564860102452005852883703094650994139385036800 : ℤ)
  | 50 => (14131866121694571841707873772226753811191962510483783680 : ℤ)
  | 51 => (13897477276646272270740914633242736565940868881034772480 : ℤ)
  | 52 => (13670903010277227436141936843622162839040950582042951680 : ℤ)
  | 53 => (13451752862216703462592227349416947900246380817500078080 : ℤ)
  | 54 => (13239662263530341175313001959931796955423860222716805120 : ℤ)
  | 55 => (13034290406020923742350107959793569120217859742834360320 : ℤ)
  | 56 => (12835318320072076929688026646891682895532229922410987520 : ℤ)
  | 57 => (12642447137461954665791965462189415880457761707073208320 : ℤ)
  | 58 => (12455396518585901697664977109035761672134286429304913920 : ℤ)
  | 59 => (12273903226111084309014604712166315887795868329563914240 : ℤ)
  | 60 => (12097719829308886840363293128999418190511360901057085440 : ℤ)
  | 61 => (11926613525227922604814056478116244658212043512180899840 : ℤ)
  | 62 => (11760365064527993063938440286421691939919299928853053440 : ℤ)
  | 63 => (11598767771231854616228863651922201666563282509118832640 : ℤ)
  | 64 => (11441626646899581494360421433325013625600801719139172352 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta33 (i : ℕ) : ℤ :=
  match i with
  | 19 => (27419786378743135503055752172305834709645915353256034304 : ℤ)
  | 20 => (26410687773741291010174851990701375960329482512136929280 : ℤ)
  | 21 => (25477114180678093538020526600103073968207755675047034880 : ℤ)
  | 22 => (24610610342293090865607199923686334487934241666163015680 : ℤ)
  | 23 => (23803966121036451740509738801823320409727779057046650880 : ℤ)
  | 24 => (23050991784185730025413992360017152384926135346297569280 : ℤ)
  | 25 => (22346340832580836440664162373696557924725074670334771200 : ℤ)
  | 26 => (21685368932472202896236705831686078692645665426846515200 : ℤ)
  | 27 => (21064020573522618974681207248795063458503215742661427200 : ℤ)
  | 28 => (20478737241433676441935474287363342962965375064683315200 : ℤ)
  | 29 => (19926382445611832356113243822771862583463226828337971200 : ℤ)
  | 30 => (19404180068834244042643414767916570639557624669929472000 : ℤ)
  | 31 => (18909663333329786978671350248757794576619514103857152000 : ℤ)
  | 32 => (18440632292148984514333384428167482707744348419653632000 : ℤ)
  | 33 => (17995118215653448139472229193428381738422499144630272000 : ℤ)
  | 34 => (17571353592055579689728815825832587252347303962345472000 : ℤ)
  | 35 => (17167746727682294536840858566680220386459381228843827200 : ℤ)
  | 36 => (16782860138152861683878492262027947461956075322028851200 : ℤ)
  | 37 => (16415392081245006405136021798990139441872374986912563200 : ℤ)
  | 38 => (16064160707054215214582190903408027905880093088756531200 : ℤ)
  | 39 => (15728090399375256737289676449361834853455823358866227200 : ℤ)
  | 40 => (-702421045702625001947705134002594840081452407973269542853935104 : ℤ)
  | 41 => (2809684259532892199865243644740508381603052819482460409787580416 : ℤ)
  | 42 => (-4214526351851504015571063711659151978685924816233634998333210624 : ℤ)
  | 43 => (2809684258952305621815215710547460155343848875095017687053500416 : ℤ)
  | 44 => (-702421046865246406163739453444050891833877158028500604869935104 : ℤ)
  | 45 => (13980524799444672655368601288321630980849620763436646400 : ℤ)
  | 46 => (13727254422643138730452503438895514477573359517722214400 : ℤ)
  | 47 => (13483221871135277775442159918323845992653679229298278400 : ℤ)
  | 48 => (13247921951350342049795849786747397900086704377063014400 : ℤ)
  | 49 => (13020886127754463467614335256405571335846164919903846400 : ℤ)
  | 50 => (12801679223627334428723038207947519609305411803498414080 : ℤ)
  | 51 => (12589896474696997651777513336014809217715901396869447680 : ℤ)
  | 52 => (12385160892090959122924599590034867830031655096528404480 : ℤ)
  | 53 => (12187120897128618309982533405003121815130023850074439680 : ℤ)
  | 54 => (11995448195607883394324664715216778006407878654642094080 : ℤ)
  | 55 => (11809835863587136017377576828171630150564239917365329920 : ℤ)
  | 56 => (11629996620362418676520672562529119579730732657221304320 : ℤ)
  | 57 => (11455661267495300022908230467123100890843122610229739520 : ℤ)
  | 58 => (11286577275446846326370441630347878393090880383033016320 : ℤ)
  | 59 => (11122507501689693499589580799767809565909216653129809920 : ℤ)
  | 60 => (10963229026163146247573798341386162983341216382991728640 : ℤ)
  | 61 => (10808532091655177271732991780691071071375637674920509440 : ℤ)
  | 62 => (10658219138181530932451985796716096686159154531627171840 : ℤ)
  | 63 => (10512103921720433005423386599964403459486298074974781440 : ℤ)
  | 64 => (10370010708780662683628107679315808318637046309207408640 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta34 (i : ℕ) : ℤ :=
  match i with
  | 19 => (24835312998108815724654377002308872454108166393675382784 : ℤ)
  | 20 => (23924655178881967339213601850225426964433510162396872704 : ℤ)
  | 21 => (23081991392921130854134708826815273345841477568461537280 : ℤ)
  | 22 => (22299722180804304298164026307302703290741932774265978880 : ℤ)
  | 23 => (21571365820674683766614025730572936448619106717589831680 : ℤ)
  | 24 => (20891356787818811603974613533422980622050774731330682880 : ℤ)
  | 25 => (20254886824296795494340272102352826188756211193610240000 : ℤ)
  | 26 => (19657778371149168622324046741327013505330916831212339200 : ℤ)
  | 27 => (19096382858500967219316594481996887770266106026210099200 : ℤ)
  | 28 => (18567498287907498857651099875880486497637212034904883200 : ℤ)
  | 29 => (18068301931184594949630543030756165207646474933056307200 : ℤ)
  | 30 => (17596294979037720246885143608051590753321623367765196800 : ℤ)
  | 31 => (17149256714085103291777511334316307578130266482278400000 : ℤ)
  | 32 => (16725206333416556876270006297457539735861760859570176000 : ℤ)
  | 33 => (16322370958899791687762384232967235589433799819132928000 : ℤ)
  | 34 => (15939158686323349219565081945145788947121084326477824000 : ℤ)
  | 35 => (15574135763563483596104729927500925683654500996140236800 : ℤ)
  | 36 => (15226007172203867779150775054413327194674711678366515200 : ℤ)
  | 37 => (14893600030119797811531383979822321653733153597240115200 : ℤ)
  | 38 => (14575849344475970529429626892632030102286898570670899200 : ℤ)
  | 39 => (14271785732766436669022113815161664959617321196008243200 : ℤ)
  | 40 => (13980524799444672655368601288321630980849620763436646400 : ℤ)
  | 41 => (-702421047407567050660470091974375484998724478808589148151087104 : ℤ)
  | 42 => (2809684257868544009455163566720436799660001512238457937949884416 : ℤ)
  | 43 => (-4214526353477146434111141927399687012211695860518474621988634624 : ℤ)
  | 44 => (2809684257363609621878321090619210008943663536362106236662972416 : ℤ)
  | 45 => (-702421048418638050546480859596117701647391711456236245251784704 : ℤ)
  | 46 => (12460902538635469105872014191764931961192053289150054400 : ℤ)
  | 47 => (12239964550361790575626056493329383522163825393952358400 : ℤ)
  | 48 => (12026917204526457707174597284123676098815177066440294400 : ℤ)
  | 49 => (11821337788141701982921502716510496779591845115487846400 : ℤ)
  | 50 => (11622833647809996202077475127573408237761202843560181760 : ℤ)
  | 51 => (11431039537407268482118273375759124415104468591396782080 : ℤ)
  | 52 => (11245615243981163742607455519830037008018822477308231680 : ℤ)
  | 53 => (11066243458181084344116240977929053586555275779223060480 : ℤ)
  | 54 => (10892627860143000471522477730158526353940244149756231680 : ℤ)
  | 55 => (10724491395658367698382064598096629735421549494329671680 : ℤ)
  | 56 => (10561574720779575958862523141714341670131238063487057920 : ℤ)
  | 57 => (10403634795849728092716409291623713353340415046393528320 : ℤ)
  | 58 => (10250443612370759276755764838819512013183672544416235520 : ℤ)
  | 59 => (10101787038205772372525644910998587632001929470877368320 : ℤ)
  | 60 => (9957463768402637444975530692407673650838414922843422720 : ℤ)
  | 61 => (9817284370470959964346863809556521099665017959759216640 : ℤ)
  | 62 => (9681070414280606896300040063890939540661958581094973440 : ℤ)
  | 63 => (9548653677908144213771938075420729147996486217068707840 : ℤ)
  | 64 => (9419875421763817954222714624314276039107421452831293440 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta35 (i : ℕ) : ℤ :=
  match i with
  | 19 => (22543755505613751535990976481837772362827404707652173824 : ℤ)
  | 20 => (21720087363449948448186373454367639463810153071387869184 : ℤ)
  | 21 => (20957773622063998504482169899805205068911592712599240704 : ℤ)
  | 22 => (20249968088685796966436523783232334263752374548200161280 : ℤ)
  | 23 => (19590830324579202318626631917788587647004529885320314880 : ℤ)
  | 24 => (18975344458458961036224022773955242290037428949016903680 : ℤ)
  | 25 => (18399176280091717782800210695069994229812364073500672000 : ℤ)
  | 26 => (17858559413020743743211038603936493119296200945696768000 : ℤ)
  | 27 => (17350203826957415084199599668777952031036092148036403200 : ℤ)
  | 28 => (16871221690887490593268020519181721348624667938861875200 : ℤ)
  | 29 => (16419066815728969701466269842817567193983409743672115200 : ℤ)
  | 30 => (15991484841412016765318540665462009880781132718197964800 : ℤ)
  | 31 => (15586471988935225229809012286799182372484195417902284800 : ℤ)
  | 32 => (15202240692423311243985009116853036959194008155848704000 : ℤ)
  | 33 => (14837190797259667617804549601735580347802358846062592000 : ℤ)
  | 34 => (14489885291453399172192970381237098536317321394257920000 : ℤ)
  | 35 => (14159029752232567918726222774893655809807933856599244800 : ℤ)
  | 36 => (13843454855419668442511394623089129577933382483758284800 : ℤ)
  | 37 => (13542101423739615197276178542012660713432542314967859200 : ℤ)
  | 38 => (13254007590825657139706118954590093764102620269720371200 : ℤ)
  | 39 => (12978297736958602695343471227021141389313558405395251200 : ℤ)
  | 40 => (12714172915437003030788112041191048464468314534864486400 : ℤ)
  | 41 => (12460902538635469105872014191764931961192053289150054400 : ℤ)
  | 42 => (-702421048891007829069454509340091460208835426569547873049903104 : ℤ)
  | 43 => (2809684256419601853799876461386481661082683842332405229909180416 : ℤ)
  | 44 => (-4214526354893158086228808871248779534003165401563026132119322624 : ℤ)
  | 45 => (2809684255979064895363268967744541765414226651785211426757410816 : ℤ)
  | 46 => (-702421049773083978659031849364814896404449533324937689724616704 : ℤ)
  | 47 => (11135274608993397924396268001151641327022685917963878400 : ℤ)
  | 48 => (10941953869253929210431055015020536442872986509665894400 : ℤ)
  | 49 => (10755396537318756778003983591086438143591498159384166400 : ℤ)
  | 50 => (10575247534278155072334301297334003583472639786572840960 : ℤ)
  | 51 => (10401176536179067858364532559753316869016883893643509760 : ℤ)
  | 52 => (10232875831769242606553656626550957880374463467440046080 : ℤ)
  | 53 => (10070058400713666657147831539474854747529006129275207680 : ℤ)
  | 54 => (9912456186085207575054017441654522849407863437635092480 : ℤ)
  | 55 => (9759818538448866916443203712725350721104602941651681280 : ℤ)
  | 56 => (9611910811851629385357777616689046524600830450655559680 : ℤ)
  | 57 => (9468513094583482177645679791559523077044215845140561920 : ℤ)
  | 58 => (9329419059760463514623994275092253701513513900777144320 : ℤ)
  | 59 => (9194434922655889013546272110703839813082651079234027520 : ℤ)
  | 60 => (9063378493319483280369643728351509968569258363448197120 : ℤ)
  | 61 => (8936078314416123583838480348820384145822672849962270720 : ℤ)
  | 62 => (8812372875419712455808798148930316909246303984827760640 : ℤ)
  | 63 => (8692109895341283951389562747084198908821319431162429440 : ℤ)
  | 64 => (8575145667077248189875686966689093838528357053853859840 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta36 (i : ℕ) : ℤ :=
  match i with
  | 19 => (20506526774074402676777635681715248963576562066636406784 : ℤ)
  | 20 => (19759936853365402054891909481549862031071733228161204224 : ℤ)
  | 21 => (19068831504165806085234881073141058195471418329015517184 : ℤ)
  | 22 => (18427029392747317158028472626816195676406436822152904704 : ℤ)
  | 23 => (17829256217165493069828639435155890497008312392121057280 : ℤ)
  | 24 => (17270981447705577751044076084215329037208136985744506880 : ℤ)
  | 25 => (16748289536660281451344769173724914024632891765424128000 : ℤ)
  | 26 => (16257777316823756643493236079463909359231078320046080000 : ℤ)
  | 27 => (15796471522466410794248766751871374355032740590518272000 : ℤ)
  | 28 => (15361761932494308311985980382858016079782041091257139200 : ℤ)
  | 29 => (14951346758302421985613491553465921119827653125419827200 : ℤ)
  | 30 => (14563187714230070047400225175958960306146295424011468800 : ℤ)
  | 31 => (14195472807703404196867529697534325795777473699171532800 : ℤ)
  | 32 => (13846585331280006804122095411619238415136900743220428800 : ℤ)
  | 33 => (13515077872878857013015877601527030697523904228884480000 : ℤ)
  | 34 => (13199650413584167923040392542742691917357846211067904000 : ℤ)
  | 35 => (12899131775882913754422074952501149775314080548834508800 : ℤ)
  | 36 => (12612463834316818207004518885844816736610338590215372800 : ℤ)
  | 37 => (12338688016366506560836223271582151020227614116465868800 : ℤ)
  | 38 => (12076933712029957575645090647124286854613767852077875200 : ℤ)
  | 39 => (11826408281980349713501469210852703850381763100750643200 : ℤ)
  | 40 => (11586388410834427954793937726877186223435722665649766400 : ℤ)
  | 41 => (11356212597267076454642225699587189766050913813161574400 : ℤ)
  | 42 => (11135274608993397924396268001151641327022685917963878400 : ℤ)
  | 43 => (-702421050185807202208221709851285413831119301804743910022447104 : ℤ)
  | 44 => (2809684255154229739141535788159633024588179146079827284686012416 : ℤ)
  | 45 => (-4214526356130410820561408640626142645242236660121102345226420224 : ℤ)
  | 46 => (2809684254768708959603117019440599591376004768413180348717858816 : ℤ)
  | 47 => (-702421050957687660466840139194205109292922014923095766103752704 : ℤ)
  | 48 => (9975350170556585640604990084365012022124489468175974400 : ℤ)
  | 49 => (9805701358132153912023272565923430185013528762934886400 : ℤ)
  | 50 => (9641869076419416985564356790971274010889229567587778560 : ℤ)
  | 51 => (9483553945161155275824863258005411296509631363243048960 : ℤ)
  | 52 => (9330477054545087288711045251950274433726241016916213760 : ℤ)
  | 53 => (9182378227147223934440801154744199264617606305367982080 : ℤ)
  | 54 => (9039014455436500182666695613442295365397275951685959680 : ℤ)
  | 55 => (8900158494358535036472538532458919092405801081456558080 : ℤ)
  | 56 => (8765597591217313530336394069765382745477577413262049280 : ℤ)
  | 57 => (8635132337378524304270385686763463952054980808728903680 : ℤ)
  | 58 => (8508575628290947873818415308701622962645708438419537920 : ℤ)
  | 59 => (8385751720015260300692107156350589182274303229763256320 : ℤ)
  | 60 => (8266495371906439186513249777274536369164093919403704320 : ℤ)
  | 61 => (8150651066352811319353556187273506581108382468533125120 : ℤ)
  | 62 => (8038072297561817299612974864856542103320843340449054720 : ℤ)
  | 63 => (7928620922324998334824967355188123153133392404036976640 : ℤ)
  | 64 => (7822166566513674738546104309494226930147672093821501440 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta37 (i : ℕ) : ℤ :=
  match i with
  | 19 => (18690806670019606636058214026999690870222756446212194304 : ℤ)
  | 20 => (18012689231435256266626388160623995958045439699592413184 : ℤ)
  | 21 => (17384853479423357854747864223367716311518283354785972224 : ℤ)
  | 22 => (16801706465402945712370110599421737281352216177157341184 : ℤ)
  | 23 => (16258475007843711583983909564997714802031547807332040704 : ℤ)
  | 24 => (15751058264966204394702599834246512992399043752917729280 : ℤ)
  | 25 => (15275911413594260622923078067342326632783239092109312000 : ℤ)
  | 26 => (14829952965399399597382271080577796328070489944621056000 : ℤ)
  | 27 => (14410490248202166710047867545322240466245061751865344000 : ℤ)
  | 28 => (14015158992009877644140732808234765065367653185486848000 : ℤ)
  | 29 => (13641873972053517684295464851070945041484715320881971200 : ℤ)
  | 30 => (13288788396542991045512659872738419116140238214057164800 : ℤ)
  | 31 => (12954260267366104621496194517190409979997184219466956800 : ℤ)
  | 32 => (12636824343553937690522999996852292667320522219769036800 : ℤ)
  | 33 => (12335168638771433222212248429139691139057432641981644800 : ℤ)
  | 34 => (12048114612502888536456320236179234811917361660035072000 : ℤ)
  | 35 => (11774600389218941402953965387833404485625776287042764800 : ℤ)
  | 36 => (11513666474416721304338048551894898105574568122698956800 : ℤ)
  | 37 => (11264443540998360688003844550119815111998921094515916800 : ℤ)
  | 38 => (11026141941293271608125040365744649438369128660126924800 : ℤ)
  | 39 => (10798042664522703006336758585026208390238833304875827200 : ℤ)
  | 40 => (10579489510660776508425845450307077347616201917228646400 : ℤ)
  | 41 => (10369882292473868730329914545857062806103467852457574400 : ℤ)
  | 42 => (10168670910296054354570203070496116906274188876473958400 : ℤ)
  | 43 => (9975350170556585640604990084365012022124489468175974400 : ℤ)
  | 44 => (-702421051319369721589651896283670650690779758864344985951535104 : ℤ)
  | 45 => (2809684254045857497968581828092411904103177810288217343777570816 : ℤ)
  | 46 => (-4214526357214688013013211427648424176151477097308546852636852224 : ℤ)
  | 47 => (2809684253707501494650288759801770858996748170314830405294882816 : ℤ)
  | 48 => (-702421051996786636566484476757224909747610767227730085705416704 : ℤ)
  | 49 => (8957457296009995269114684973715520999458725236729446400 : ℤ)
  | 50 => (8808166341076495347962773557486928982801079816117288960 : ℤ)
  | 51 => (8663893569502104667857985214072743420484867855021506560 : ℤ)
  | 52 => (8524385659530714348843614211431852448228430452841512960 : ℤ)
  | 53 => (8389406283737862228276612225123386507110723142559989760 : ℤ)
  | 54 => (8258734692836428967718116887673364818124598021277614080 : ℤ)
  | 55 => (8132164439931356033520787423954566999749595090942689280 : ℤ)
  | 56 => (8009502229130268461418521560640614447573257378940846080 : ℤ)
  | 57 => (7890566874501823561862272132540381690905253775702753280 : ℤ)
  | 58 => (7775188357158128990425127920869928432906317923541319680 : ℤ)
  | 59 => (7663206969769203328004433098162215164160582212302929920 : ℤ)
  | 60 => (7554472539135544830641691315986838180430595774081925120 : ℤ)
  | 61 => (7448843718582128888103004688392158334563725930208952320 : ℤ)
  | 62 => (7346187342920828606401540857889231418033826866260869120 : ℤ)
  | 63 => (7246377839581135899564959778795826863469693382657310720 : ℤ)
  | 64 => (7149296690250265081652702504847106588904916664335728640 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta38 (i : ℕ) : ℤ :=
  match i with
  | 19 => (17068581774351338074900959184785662558428751244631736320 : ℤ)
  | 20 => (16451442346017107818779542783570810620358075137029832704 : ℤ)
  | 21 => (15879961303813828821599082214501252862936219405133021184 : ℤ)
  | 22 => (15349067730330177111767254002068734266186754891892916224 : ℤ)
  | 23 => (14854433140183381523432135605135754455382928082216157184 : ℤ)
  | 24 => (14392338071174962569585016862140314593810980049680072704 : ℤ)
  | 25 => (13959566805764205340879662839503408792507298705571840000 : ℤ)
  | 26 => (13553323472053876917324100187781649517502715008122880000 : ℤ)
  | 27 => (13171164577249400473472144233593440587429985271152640000 : ℤ)
  | 28 => (12810944302486096126277388085730183144913146531020800000 : ℤ)
  | 29 => (12470769803042637080500269881732089030978217799843840000 : ℤ)
  | 30 => (12148964422718518472776350688785024874908261114760396800 : ℤ)
  | 31 => (11844037219767185356945775199558496374292056724262092800 : ℤ)
  | 32 => (11554657564864542860697024990047359823831758401227980800 : ℤ)
  | 33 => (11279633844158483861869259849319637970432836577840332800 : ℤ)
  | 34 => (11017895507005257447342441815357996874431149518933196800 : ℤ)
  | 35 => (10768477855930032069439936668505588954851829483359436800 : ℤ)
  | 36 => (10530509098106442060021370252595137680145397781941452800 : ℤ)
  | 37 => (10303199272253208430133361393284692565107172820438220800 : ℤ)
  | 38 => (10085830738891782363120333369367772875228036194946252800 : ℤ)
  | 39 => (9877749980266349137725721779370864694848779270802636800 : ℤ)
  | 40 => (9678360502521453597697422963311768265306492650284646400 : ℤ)
  | 41 => (9487116669683947817070396063268599176950503717627494400 : ℤ)
  | 42 => (9303518328663155007816261572795691258548857705227878400 : ℤ)
  | 43 => (9127106108434426997696402492157102836569685941970534400 : ℤ)
  | 44 => (8957457296009995269114684973715520999458725236729446400 : ℤ)
  | 45 => (-702421052314642754479651370629746758881393203248647790032584704 : ℤ)
  | 46 => (2809684253072220835358799733623424406960186397303573296306978816 : ℤ)
  | 47 => (-4214526358167609001950444966915943854206319756825432516118708224 : ℤ)
  | 48 => (2809684252774433026315914252602324507568048066204546526468898816 : ℤ)
  | 49 => (-702421052910812891261381953197498886657357807988824497616584704 : ℤ)
  | 50 => (8061711566408995742203216476343968899512852713056501760 : ℤ)
  | 51 => (7929984253232378164716235814965799473050224400751656960 : ℤ)
  | 52 => (7802599598731912815058496274292404862844605813028290560 : ℤ)
  | 53 => (7679342518397695927229021289383218391675720524848168960 : ℤ)
  | 54 => (7560012089662862666321548801631208636790470805825781760 : ℤ)
  | 55 => (7444420393199156670525872799153771999991986636120391680 : ℤ)
  | 56 => (7332391467073320741635547694158538339083637480520417280 : ℤ)
  | 57 => (7223760361059216244829514106805919623059334112561070080 : ℤ)
  | 58 => (7118372280018203280042040669289043673710536082881249280 : ℤ)
  | 59 => (7016081806648807357449307160385562246511510700089671680 : ℤ)
  | 60 => (6916752195101703722244876017019255080872355109242142720 : ℤ)
  | 61 => (6820254727987184562681471236174090557524142885825413120 : ℤ)
  | 62 => (6726468130194226043819562351802196963639635185311416320 : ℤ)
  | 63 => (6635278033713686124725772209181650386330753434774405120 : ℤ)
  | 64 => (6546576488330355019165375015224301785386980473537822720 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta39 (i : ℕ) : ℤ :=
  match i with
  | 19 => (15615860773070315118014226489875711968281025675022827520 : ℤ)
  | 20 => (15053153882749089139350155065699670333550538066367610880 : ℤ)
  | 21 => (14531987211157823118254967432060341834759776872016379904 : ℤ)
  | 22 => (14047754129629966152916533015332169022137843788529270784 : ℤ)
  | 23 => (13596521737632569341723076507211349722814395606445850624 : ℤ)
  | 24 => (13174909897181507410473132172564094267984417100329385984 : ℤ)
  | 25 => (12779995757893163421144373566871520813908409507068772352 : ℤ)
  | 26 => (12409237658377860005840582747898799388754827029984051200 : ℤ)
  | 27 => (12060413922718877705804986025495729350926260802001305600 : ℤ)
  | 28 => (11731573226104936948078712719960588998231261572392550400 : ℤ)
  | 29 => (11420994032415579619000971451877774713962654683942092800 : ℤ)
  | 30 => (11127151208641137790133067135674760881059409014334423040 : ℤ)
  | 31 => (10848688363620293353066154482923094407244897773944832000 : ℤ)
  | 32 => (10584394787515779772226522625129751233743173487847014400 : ℤ)
  | 33 => (10333186115408634414908658857267970596632841323492147200 : ℤ)
  | 34 => (10094088025568925664486433896916113132269181767096729600 : ℤ)
  | 35 => (9866222426089686627027696604451715603072170559925125120 : ℤ)
  | 36 => (9648795693928782660800601046791148829919488828768256000 : ℤ)
  | 37 => (9441088616159280473237151809845952693724742009906790400 : ℤ)
  | 38 => (9242447750357287937738201330607854552013376410825523200 : ℤ)
  | 39 => (9052277973967552139760946641631366606059721744554393600 : ℤ)
  | 40 => (8870036034465224669950319719827868582409672681670574080 : ℤ)
  | 41 => (8695224945642307775477518514977137911707364270643609600 : ℤ)
  | 42 => (8527389102254305466808108387513364784151354585120768000 : ℤ)
  | 43 => (8366110006987690386629841052290578595814805064174796800 : ℤ)
  | 44 => (8211002521342495663355127892572560916170498133668659200 : ℤ)
  | 45 => (8061711566408995742203216476343968899512852713056501760 : ℤ)
  | 46 => (-702421053190915750828455255651835506310085474934827432756117504 : ℤ)
  | 47 => (2809684252214591945315289548282656696710828003738376199173308416 : ℤ)
  | 48 => (-4214526359007370623451382023395445570492149850524688007062093824 : ℤ)
  | 49 => (2809684251951809397090506523806077928349275729519561555748847616 : ℤ)
  | 50 => (-702421053716984047902281527417820534291754697940109768922234880 : ℤ)
  | 51 => (7271347687349290277281332508074952340737082839227432960 : ℤ)
  | 52 => (7154819679539205497196695769163494771173988562957762560 : ℤ)
  | 53 => (7042060771712196235605362644448634211947166877834280960 : ℤ)
  | 54 => (6932887743730196321469464208240258308387493421787381760 : ℤ)
  | 55 => (6827129219989317598848529121963575100471120559184281600 : ℤ)
  | 56 => (6724624717626924907829157042337346205392624786740346880 : ℤ)
  | 57 => (6625223785809373746705440985707312997021106540778618880 : ℤ)
  | 58 => (6528785226023957991191305789879715407584088189021716480 : ℤ)
  | 59 => (6435176384559813810363801984853114105955209581774766080 : ℤ)
  | 60 => (6344272509448057712265705787356898171552106307334963200 : ℤ)
  | 61 => (6255956165068179481080677945187782220256547509811281920 : ℤ)
  | 62 => (6170116698438072002826373133243125323692461215417630720 : ℤ)
  | 63 => (6086649751907797810311370567965374035106869096973598720 : ℤ)
  | 64 => (6005456817587983332366145921967277816056311816566865920 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta4 (i : ℕ) : ℤ :=
  match i with
  | 19 => (3387627113155012435117609968368017338378953225770578739200 : ℤ)
  | 20 => (3243588444109261104532377623448315759012120421701412454400 : ℤ)
  | 21 => (3111488273898754380868184881968231448800657438682172620800 : ℤ)
  | 22 => (2989885136536783397855452806491991738816331403928325324800 : ℤ)
  | 23 => (2877562528513362793699808248537920722830778166221262028800 : ℤ)
  | 24 => (2773486398595614296143533200226077654921073159484263628800 : ℤ)
  | 25 => (2676771973060797773253468985148922634026019653510192168960 : ℤ)
  | 26 => (2586657599700188269364925925358911113842642378864763863040 : ℤ)
  | 27 => (2502483930551439629647690218941787153618356954554265763840 : ℤ)
  | 28 => (2423677209144012015899250185537176330184103686081599242240 : ℤ)
  | 29 => (2349735744702219413793939645016802540289794075665461411840 : ℤ)
  | 30 => (2280218883617891504912059343260197397322068297586143395840 : ℤ)
  | 31 => (2214737954467073473855688337689108450494559961648652615680 : ℤ)
  | 32 => (2152948785080963724137695838762022286019464461620116193280 : ℤ)
  | 33 => (2094545481153838365354912589940426931141577108558530478080 : ℤ)
  | 34 => (2039255224237103687472667109712016280576100522100292321280 : ℤ)
  | 35 => (1986833898815404709733027146083031281113062220287264686080 : ℤ)
  | 36 => (1937062397815952661126887466590042191059189129390487240704 : ℤ)
  | 37 => (1889743486476363016322256482631723733892781051331618013184 : ℤ)
  | 38 => (1844699128247081370031019097691400088778002316528109748224 : ℤ)
  | 39 => (1801768194986170323190698997601136748338583787335460061184 : ℤ)
  | 40 => (1760804498339646132990939838317540282721470563522973794304 : ℤ)
  | 41 => (1721675090801140886440758137420109137675912801183460229120 : ℤ)
  | 42 => (1684258794195170393240957804004619529872474805481525739520 : ℤ)
  | 43 => (1648444920746990429185444175291147328294919089395827998720 : ℤ)
  | 44 => (1614132157883993259478571899937981376040775300261892587520 : ℤ)
  | 45 => (1581227592762011246814350002725700094957566787376717496320 : ℤ)
  | 46 => (1549645856458907779261007564293615888567271791567998812160 : ℤ)
  | 47 => (1519308371009393994320157917214570803306371405531431567360 : ℤ)
  | 48 => (1490142685111314853199426652923894258688317509426175016960 : ℤ)
  | 49 => (1462081886526456563711005409521585642239997223730791055360 : ℤ)
  | 50 => (1435064081016534442212886344070744123774287537531770634240 : ℤ)
  | 51 => (1409031929167539207527657499469379269847533662911185551360 : ℤ)
  | 52 => (1383932233718995966462567548666948143858559303383840194560 : ℤ)
  | 53 => (1359715571073772279532575982788472937851976734851895132160 : ℤ)
  | 54 => (1336335961554972748323542244372610645143893918070928834560 : ℤ)
  | 55 => (1313750573728381218661329458235745984870048707482128220160 : ℤ)
  | 56 => (1291919458745571402304681413174335895103481953414513950720 : ℤ)
  | 57 => (1270805311203534085122982317825964315945348109448637317120 : ℤ)
  | 58 => (1250373253477283578637565701018086765662044538687266488320 : ℤ)
  | 59 => (1230590640875400580158871242314315527555251558084111237120 : ℤ)
  | 60 => (1211426885305552223001986140973145728672697119451245445120 : ℤ)
  | 61 => (1192853295426559624966187256302472286806039019914189078528 : ℤ)
  | 62 => (1174842931512907670591393178281437827806036907855748005888 : ℤ)
  | 63 => (1157370473472828332303887172052073521882033181320353415168 : ℤ)
  | 64 => (1140412100647345118173337431395998027350669619947150245888 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta40 (i : ℕ) : ℤ :=
  match i with
  | 19 => (14312030603426404986649711805219343276477284606929797120 : ℤ)
  | 20 => (13798023851232992548693893362856973883096754965215969280 : ℤ)
  | 21 => (13321880623856400978092694944729443585755994533218222080 : ℤ)
  | 22 => (12879408191305711691600119134770579939137712590373781504 : ℤ)
  | 23 => (12467026371510555223072765078794135904586304040871133184 : ℤ)
  | 24 => (12081657636101467200622798901362401318494170014940135424 : ℤ)
  | 25 => (11720640359711649355016865670949103799837000532483899392 : ℤ)
  | 26 => (11381659664172146060128732699934029979151278191832727552 : ℤ)
  | 27 => (11062691790350213658195891542699734140470182059756748800 : ℤ)
  | 28 => (10761958978549361584861890934768059290080353152139264000 : ℤ)
  | 29 => (10477892590355059314064689873740769629138661082870579200 : ℤ)
  | 30 => (10209102751190697906120749367198615990506474210737520640 : ℤ)
  | 31 => (9954353194552542584119948989211058890617944040265482240 : ℤ)
  | 32 => (9712540287471966747240946278536383104004728580315545600 : ℤ)
  | 33 => (9482675440947705487789957093603243303328463966751948800 : ℤ)
  | 34 => (9263870279033738785896698194315771722995035023605760000 : ℤ)
  | 35 => (9055324070233312767731957824333977083592455647207096320 : ℤ)
  | 36 => (8856313025068951866294178200552416666858686832254648320 : ℤ)
  | 37 => (8666181141584283974681502059213452567657720877521305600 : ℤ)
  | 38 => (8484332341508058068331713321941353701522494267903180800 : ℤ)
  | 39 => (8310223687876609697061107419316193995508622200668160000 : ℤ)
  | 40 => (8143359513048890855100780078121997563467586389650964480 : ℤ)
  | 41 => (7983286316495799026379425511526045126222223554935521280 : ℤ)
  | 42 => (7829588316195963694848788454492024537810092504068915200 : ℤ)
  | 43 => (7681883557213690318287023212155812186391228673582694400 : ℤ)
  | 44 => (7539820497061634673302416903645697648003772923353497600 : ℤ)
  | 45 => (7403075000525907854768313169453121767199711151532277760 : ℤ)
  | 46 => (7271347687349290277281332508074952340737082839227432960 : ℤ)
  | 47 => (-702421053964463377142209540468998539084016575013240500759035904 : ℤ)
  | 48 => (2809684251457159894549738477732517893786353801578263403420450816 : ℤ)
  | 49 => (-4214526359749344877262534092505785622336532742436635235554689024 : ℤ)
  | 50 => (2809684251224674628355577496077944677541780495445853271826104320 : ℤ)
  | 51 => (-702421054429861272152211946759127642926553947031980635513159680 : ℤ)
  | 52 => (6572179640488781596773512074606206923358517181609410560 : ℤ)
  | 53 => (6468843482619461131415437985382838889972376974351400960 : ℤ)
  | 54 => (6368787837698373061783017041849101587804844392720629760 : ℤ)
  | 55 => (6271856135789351750807524889324353550138667709130342400 : ℤ)
  | 56 => (6177901747904559538376981576599740070048166734253260800 : ℤ)
  | 57 => (6086787201192776637892198050400946877257792958737940480 : ℤ)
  | 58 => (5998383467934434929698429562597403312474806296017633280 : ℤ)
  | 59 => (5912569320316391018540345407839465209216538795866849280 : ℤ)
  | 60 => (5829230743947372953923690942513534744227119345172480000 : ℤ)
  | 61 => (5748260403927624082980350663744197160016279845103206400 : ℤ)
  | 62 => (5669557158023881878074118871955931225035815022776811520 : ℤ)
  | 63 => (5593025612140509282407219759586383074427613371034501120 : ℤ)
  | 64 => (5518575713833634507398766465772018383486784500158955520 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta41 (i : ℕ) : ℤ :=
  match i with
  | 19 => (13139325912072219624547257300580989283580501663699435520 : ℤ)
  | 20 => (12668985693304209587456333786567791545637655311527444480 : ℤ)
  | 21 => (12233219174926139787557342868903115091820917541023252480 : ℤ)
  | 22 => (11828203432836223342462351291409851103174513355579719680 : ℤ)
  | 23 => (11450673486851628735779790422899665390581513203067387904 : ℤ)
  | 24 => (11097822279742059057078283396584509462219946294702505984 : ℤ)
  | 25 => (10767221708003710881268096486441159933822466578618253312 : ℤ)
  | 26 => (10456759659617652894098882579678679391498824151405166592 : ℤ)
  | 27 => (10164589360377927245911415649081028697047849084127281152 : ℤ)
  | 28 => (9889088283120074087343478672234340047013303991612211200 : ℤ)
  | 29 => (9628824557775433723349216439146299475708195017379020800 : ℤ)
  | 30 => (9382529316940262381269104527973068475245574885935677440 : ℤ)
  | 31 => (9149073776918313777608892580971808422222842407252131840 : ℤ)
  | 32 => (8927450125726170459624087727553839058843175730639011840 : ℤ)
  | 33 => (8716755493458514990154050509656654782283741128556544000 : ℤ)
  | 34 => (8516178434993472900029146494396448167540446734162329600 : ℤ)
  | 35 => (8324987473249627129214767897943456448229532569090129920 : ℤ)
  | 36 => (8142521342387648657068970036194226122014883816428011520 : ℤ)
  | 37 => (7968180641219116515378838731011037352891319645550673920 : ℤ)
  | 38 => (7801420662572602185632355733607372709321073879941120000 : ℤ)
  | 39 => (7641745208112060427719724594427737429297043347184025600 : ℤ)
  | 40 => (7488701232815511997464418409990418130088807552966983680 : ℤ)
  | 41 => (7341874191038063831104010312926118670375084294332743680 : ℤ)
  | 42 => (7200883978342372645811150264549115730584304842839162880 : ℤ)
  | 43 => (7065381381255407695223961469072698151373055622486425600 : ℤ)
  | 44 => (6935044961703601500471851385496015945100488084763443200 : ℤ)
  | 45 => (6809578314785103384772026673133896878741715458730229760 : ℤ)
  | 46 => (6688707648298866376858148813517664492921611457879080960 : ℤ)
  | 47 => (6572179640488781596773512074606206923358517181609410560 : ℤ)
  | 48 => (-702421054649065423026457623466239380188829796196419373843349504 : ℤ)
  | 49 => (2809684250786529318989658722959710539234700033888618793052143616 : ℤ)
  | 50 => (-4214526360406562841311412252183136829797153434772486953715630080 : ℤ)
  | 51 => (2809684250580343291052755770904070944737250404920508450099691520 : ℤ)
  | 52 => (-702421055061801622199210177218119188561766151201068826052526080 : ℤ)
  | 53 => (5952162693272858804625067539265998723041675938061352960 : ℤ)
  | 54 => (5860308330722351724306779459956338248920662420498677760 : ℤ)
  | 55 => (5771316961290302007530879580521264594772251921665228800 : ℤ)
  | 56 => (5685054382174281965381318454091656503410228675058073600 : ℤ)
  | 57 => (5601394761896771679010884026195686831157068735866470400 : ℤ)
  | 58 => (5520219990805812707135860802590066970071713891357818880 : ℤ)
  | 59 => (5441419091621826319802369217291792556257982806050734080 : ℤ)
  | 60 => (5364887683608992552142552734955614632269995697399398400 : ℤ)
  | 61 => (5290527494726981019761927657709747291492814658155315200 : ℤ)
  | 62 => (5218245916791432018724422270630793375874463943360512000 : ℤ)
  | 63 => (5147955599254930957695268707304644961277202548045905920 : ℤ)
  | 64 => (5079574077727323220159289128757773158540229216221265920 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta42 (i : ℕ) : ℤ :=
  match i with
  | 19 => (12082390144601725386323405865093490671736556704046776320 : ℤ)
  | 20 => (11651285238754004923390990415764489602820082679184097280 : ℤ)
  | 21 => (11251804099667814633974174848647315659199161040560455680 : ℤ)
  | 22 => (10880454926455035513778918428160842654765991191463854080 : ℤ)
  | 23 => (10534255021255167080587336608960720945991540325566382080 : ℤ)
  | 24 => (10210639592419783151482901352219248989947830715971272704 : ℤ)
  | 25 => (9907389741087487296153269888731309717611611107090235392 : ℤ)
  | 26 => (9622575036220468803455583498120775564006759667452608512 : ℤ)
  | 27 => (9354507309011567930279425627962753702046661940653064192 : ℤ)
  | 28 => (9101703165150631030799796445640671782218978380902039552 : ℤ)
  | 29 => (8862853336004063948615018751671236818902670209187840000 : ℤ)
  | 30 => (8636797442229957255911705182601966355201249027702128640 : ℤ)
  | 31 => (8422503076089801283748932344220488036045304573345136640 : ℤ)
  | 32 => (8219048356094429589386225777961496121747580541930045440 : ℤ)
  | 33 => (8025607293412100943771804767058990767473224830932746240 : ℤ)
  | 34 => (7841437450330153401238599400941066734777612314135756800 : ℤ)
  | 35 => (7665869478811635927939851131644162635677350171582136320 : ℤ)
  | 36 => (7498298210295063406350175184156512181140410911026053120 : ℤ)
  | 37 => (7338175032485910980768285233590712781063305986960261120 : ℤ)
  | 38 => (7185001339472687725296593002160248047227941232647864320 : ℤ)
  | 39 => (7038322881383774133757347074727116462777269272497356800 : ℤ)
  | 40 => (6897724871452953077141591152019487588916833854926356480 : ℤ)
  | 41 => (6762827733635895070071117490567735358986164145886330880 : ℤ)
  | 42 => (6633283394219866354362930843965880727155837158849249280 : ℤ)
  | 43 => (6508772037264133249924514504169348437207365780273889280 : ℤ)
  | 44 => (6388999257019855558334749248701561932845592447706726400 : ℤ)
  | 45 => (6273693551339950522180177214466460531429190758312181760 : ℤ)
  | 46 => (6162604108994575253834519331909331800150228943723560960 : ℤ)
  | 47 => (6055498851142179269983141628489366756427816145319362560 : ℤ)
  | 48 => (5952162693272858804625067539265998723041675938061352960 : ℤ)
  | 49 => (-702421055256428963156341174958593210726176604670059775686344704 : ℤ)
  | 50 => (2809684250191313049662372842497203785308100161584451199246008320 : ℤ)
  | 51 => (-4214526360990108203396986644793437568940878799776572829996154880 : ℤ)
  | 52 => (2809684250008019955161134731997814450577058220012654994516869120 : ℤ)
  | 53 => (-702421055623326404583442139918597258303841502431415612662087680 : ℤ)
  | 54 => (5401036517969816322715339063408035878315594832685301760 : ℤ)
  | 55 => (5319202631333910014795409683659429274098691880674918400 : ℤ)
  | 56 => (5239873863676653899975069978801086137357816570052608000 : ℤ)
  | 57 => (5162934847676662771993154634857796966301309733122867200 : ℤ)
  | 58 => (5088277288338766609646654065914135217101751844654284800 : ℤ)
  | 59 => (5015799423579299249116787282313287417271571862708551680 : ℤ)
  | 60 => (4945405533849088086083613589019625996004509811212288000 : ℤ)
  | 61 => (4877005495635807404222465231737090146774776358214041600 : ℤ)
  | 62 => (4810514374301750471001841565833457071892679501860044800 : ℤ)
  | 63 => (4745852052245967034230369291323968080394965853038182400 : ℤ)
  | 64 => (4682942888842988863583935305799488811039571615384862720 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta43 (i : ℕ) : ℤ :=
  match i with
  | 19 => (11127911055082881234379396321995568558390705008137994240 : ℤ)
  | 20 => (10732131015109271305644571099241481702157657995875450880 : ℤ)
  | 21 => (10365324163046905798934957305429242965125893433306644480 : ℤ)
  | 22 => (10024295800129220015175234152418216595945616760404705280 : ℤ)
  | 23 => (9706316552983336313188627327419965289914774923488788480 : ℤ)
  | 24 => (9409039080011455346688307637417380138009124735423610880 : ℤ)
  | 25 => (9130432288825819886939833539537641814284711749434212352 : ℤ)
  | 26 => (8868728872247138003323396991922072048704765946958446592 : ℤ)
  | 27 => (8622383088448280595545335523415583734689056920659034112 : ℤ)
  | 28 => (8390036502231243586937400795211318723776020006244974592 : ℤ)
  | 29 => (8170489972397214423435082814018596630785255133887332352 : ℤ)
  | 30 => (7962680583009094561495795574436564172516737737073623040 : ℤ)
  | 31 => (7765662519976761074828585978826476697408411151462563840 : ℤ)
  | 32 => (7578591120157017483324660615562982430058492880738058240 : ℤ)
  | 33 => (7400709489735366510186931980475430079578551021826211840 : ℤ)
  | 34 => (7231337217240069131607784316557809020662107943773143040 : ℤ)
  | 35 => (7069860804905893926564979534739918752161098766609285120 : ℤ)
  | 36 => (6915725517982494772007165150615268763689073111486955520 : ℤ)
  | 37 => (6768428410569412551929183418831101927313979176879390720 : ℤ)
  | 38 => (6627512332753040411989951146300181744442832982659563520 : ℤ)
  | 39 => (6492560760245788196743344404287422934623377792560005120 : ℤ)
  | 40 => (6363193316637547093417929691801111977987819918411694080 : ℤ)
  | 41 => (6239061881456634013395818095506312481805175948501319680 : ℤ)
  | 42 => (6119847195782345507843100935400112040139069522947604480 : ℤ)
  | 43 => (6005255892130352828465798394732388183165651713188167680 : ℤ)
  | 44 => (5895017887494835940525044156054798905580593640196014080 : ℤ)
  | 45 => (5788884088356542633588600463878446835254970799630581760 : ℤ)
  | 46 => (5686624364604100921885031664096021849003582624324648960 : ℤ)
  | 47 => (5588025756019062879077568367716987557776229493437890560 : ℤ)
  | 48 => (5492890880520323403033627142717696352436608350247976960 : ℤ)
  | 49 => (5401036517969816322715339063408035878315594832685301760 : ℤ)
  | 50 => (-702421055796532614953322807230127117066980192501619258954874880 : ℤ)
  | 51 => (2809684249661799665547684967721190151640645663710373274472939520 : ℤ)
  | 52 => (-4214526361509438637817161291208374017345497634229995410062049280 : ℤ)
  | 53 => (2809684249498488208182850173251084350255545401303636614074859520 : ℤ)
  | 54 => (-702421056123422378469536243873721245656437417090266986058874880 : ℤ)
  | 55 => (4910033198154378475195762784916396253014177120623001600 : ℤ)
  | 56 => (4836967227943747843124397267283711784963370913470873600 : ℤ)
  | 57 => (4766098730521406854122847253940732112944167900518809600 : ℤ)
  | 58 => (4697328251299954468310797819046759390584448109615513600 : ℤ)
  | 59 => (4630562329188782175518235501218538956227548892731801600 : ℤ)
  | 60 => (4565713047081814555557175693695951094078605626651443200 : ℤ)
  | 61 => (4502697622540086748156126780543557481388477447877427200 : ℤ)
  | 62 => (4441438034509209313680905629849345317878357420094259200 : ℤ)
  | 63 => (4381860682399384096183163862388374859327949753234227200 : ℤ)
  | 64 => (4323896074279575134018233426995215277401560006734643200 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta44 (i : ℕ) : ℤ :=
  match i with
  | 19 => (10264316908287255851159447219623461293755076134872023040 : ℤ)
  | 20 => (9900402755544286615580455625766469495137160727982243840 : ℤ)
  | 21 => (9563075491739181192502722817118530213344758681441402880 : ℤ)
  | 22 => (9249407527102728872754102127039152907622671360437780480 : ℤ)
  | 23 => (8956897278791311651002242242653782627899056516791009280 : ℤ)
  | 24 => (8683392970034507464189510080562382737203488023358996480 : ℤ)
  | 25 => (8427032440380579651649155080434100887406289311299010560 : ℤ)
  | 26 => (8186195135334593257094494542438334842551216149314404352 : ℤ)
  | 27 => (7959463465181512359768626105826443112961399813509742592 : ℤ)
  | 28 => (7745591445920713010688949311823370118079382434833498112 : ℤ)
  | 29 => (7543479054273592125696752039191250404290817054413422592 : ℤ)
  | 30 => (7352151106038151344235789016532530588616225613783498752 : ℤ)
  | 31 => (7170739744597098033238414480095209938159612395037655040 : ℤ)
  | 32 => (6998469832765139438079248043683289782874945976365219840 : ℤ)
  | 33 => (6834646696194232865870757163302922391723011498825482240 : ℤ)
  | 34 => (6678645784124428499128731570928901218841172033499299840 : ℤ)
  | 35 => (6529903903218015063722675347284038127374368355112714240 : ℤ)
  | 36 => (6387911749606674693898901370168197050353574166522757120 : ℤ)
  | 37 => (6252207518231903086169899909410350351119589716808171520 : ℤ)
  | 38 => (6122371410812257489403425157657891894022640082060574720 : ℤ)
  | 39 => (5998020897092222658759725148233977096620502582579691520 : ℤ)
  | 40 => (5878806610476490887343874056172873402996605652482129920 : ℤ)
  | 41 => (5764408780277257035467226913152770971522676367116206080 : ℤ)
  | 42 => (5654534119771588956824893954444836737398726291284295680 : ℤ)
  | 43 => (5548913102973696847936616890642391545602537299619348480 : ℤ)
  | 44 => (5447297574158264365375370805537343154414040676753735680 : ℤ)
  | 45 => (5349458643255460554392181624397421544134573960126791680 : ℤ)
  | 46 => (5255184827687588451502104508996229851231690677823733760 : ℤ)
  | 47 => (5164280407353635126651439878466617992299946760428584960 : ℤ)
  | 48 => (5076563964544648454578009744288196281420586043372994560 : ℤ)
  | 49 => (4991867084790284783115692164665002857231080072633384960 : ℤ)
  | 50 => (4910033198154378475195762784916396253014177120623001600 : ℤ)
  | 51 => (-702421056277908418693948147935594056764666099659871917839482880 : ℤ)
  | 52 => (2809684249189681088802071652798520653090992177843625474413035520 : ℤ)
  | 53 => (-4214526361972649316888329071887219563092327469420012119554785280 : ℤ)
  | 54 => (2809684249043855504650037351473698907207730933431953547350507520 : ℤ)
  | 55 => (-702421056569789032847207014346063317012473440091555815206420480 : ℤ)
  | 56 => (4471637376890594682767569679120289444709339877710233600 : ℤ)
  | 57 => (4406262561438977801440558426501571762769144850258329600 : ℤ)
  | 58 => (4342820006542581123502522875930697953201566424603033600 : ℤ)
  | 59 => (4281223742981786800921326396596217335244263607867801600 : ℤ)
  | 60 => (4221392896009250635918588602475505935143034132679884800 : ℤ)
  | 61 => (4163251309528176975623096776899525171700394387256115200 : ℤ)
  | 62 => (4106727203334088484027436233372880364209914776859443200 : ℤ)
  | 63 => (4051752860052512609300289535808361488274057648616243200 : ℤ)
  | 64 => (3998264338793573277808494894816781402061217165685555200 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta45 (i : ℕ) : ℤ :=
  match i with
  | 19 => (9481522377017436774349734038474384016857003667687997440 : ℤ)
  | 20 => (9146407564064607180467554799843388932577741165444464640 : ℤ)
  | 21 => (8835727189617954548254843797404495817825413138051235840 : ℤ)
  | 22 => (8546794269718591491873729708227555339547181436507258880 : ℤ)
  | 23 => (8277312445169990898239413066360829115294553995718164480 : ℤ)
  | 24 => (8025306158605771092092331892837055660251277375601377280 : ℤ)
  | 25 => (7789065494656388527635996144738324848261620047816949760 : ℤ)
  | 26 => (7567102175593926828040007065218660609577570104047042560 : ℤ)
  | 27 => (7358114139614112760285685342601244204642079134923620352 : ℤ)
  | 28 => (7160956790736763309274417234554962854977589121061486592 : ℤ)
  | 29 => (6974619484387851858487644194733665041405358317986906112 : ℤ)
  | 30 => (6798206158125159678568823759337868830172593741461716992 : ℤ)
  | 31 => (6630919271055797363144245519900225839469557891572170752 : ℤ)
  | 32 => (6472046404457942614055981717732664712423778039145431040 : ℤ)
  | 33 => (6320949018084746304326585971089306533676561146409123840 : ℤ)
  | 34 => (6177052964298557177228467504608762179265755634456330240 : ℤ)
  | 35 => (6039840444568629258733364473911717012454123479540695040 : ℤ)
  | 36 => (5908843156427654691116068447406220148942515594319626240 : ℤ)
  | 37 => (5783636428405242980011391954070860638906366074940293120 : ℤ)
  | 38 => (5663834179167351154226798635841891213657834469741035520 : ℤ)
  | 39 => (5549084567621155606997326480847598375470160610559262720 : ℤ)
  | 40 => (5439066224980898323413778938343940916031835097865912320 : ℤ)
  | 41 => (5333484979148369584567341168475277129251564203980881920 : ℤ)
  | 42 => (5232070997314091001804420998971784132866802572150702080 : ℤ)
  | 43 => (5134576285249426784410060270826198429874384445038919680 : ℤ)
  | 44 => (5040772491963401997622120336196904108703748677152276480 : ℤ)
  | 45 => (4950448976725976067290085285635088771668558468119265280 : ℤ)
  | 46 => (4863411102289091567134837094058259647970515277766983680 : ℤ)
  | 47 => (4779478723763057102271511989940879910305165158918389760 : ℤ)
  | 48 => (4698484847260864847196484703558254508476057189833768960 : ℤ)
  | 49 => (4620274436290506140009890389275921848286979933402562560 : ℤ)
  | 50 => (4544703347101225314838935196752973912760146084862361600 : ℤ)
  | 51 => (4471637376890594682767569679120289444709339877710233600 : ℤ)
  | 52 => (-702421056707873551087274559740168064372386238574231521465466880 : ℤ)
  | 53 => (2809684248767828506076543852537429173928700720795574542553579520 : ℤ)
  | 54 => (-4214526362386689814748569320291624163010872788374580626750177280 : ℤ)
  | 55 => (2809684248637343015841801471222101663651340983912922649376849920 : ℤ)
  | 56 => (-702421056969042370069581539593167752648213569083461161430548480 : ℤ)
  | 57 => (4079388484180893394805502163407983353068169712998809600 : ℤ)
  | 58 => (4020776580672547225339905867956719224432132791835033600 : ℤ)
  | 59 => (3963867686467106997844254259056097152802469824797081600 : ℤ)
  | 60 => (3908587294907570577357362256669526548185151951391948800 : ℤ)
  | 61 => (3854865242165759268478623874678760898691448896801996800 : ℤ)
  | 62 => (3802635392036999985077325028583372797127060526150451200 : ℤ)
  | 63 => (3751835348025311128252232290585555805105998913549107200 : ℤ)
  | 64 => (3702406189982934899709073154627088875406140470670131200 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta46 (i : ℕ) : ℤ :=
  match i with
  | 19 => (8770715285854733698093914054913015508463736042070999040 : ℤ)
  | 20 => (8461675255972213425648358497622388178589961239438295040 : ℤ)
  | 21 => (8175124591640584943609101903793869086609129329016176640 : ℤ)
  | 22 => (7908593443213206049435411487539045055764465476006051840 : ℤ)
  | 23 => (7659970686201005971263837933573645914967144542377082880 : ℤ)
  | 24 => (7427439844298971440988266782317499250072018638843412480 : ℤ)
  | 25 => (7209428461769592413131231460155458989637643433001615360 : ℤ)
  | 26 => (7004567709236985951711861113313712664979279718394101760 : ℤ)
  | 27 => (6811659863708576199372321479402367396046427564602818560 : ℤ)
  | 28 => (6629651910296096082641845670564104320165620257602404352 : ℤ)
  | 29 => (6457613948636609275687261689139793311345146067096174592 : ℤ)
  | 30 => (6294721403691036292686727167499001149227330032487104512 : ℤ)
  | 31 => (6140240273579854292309871797497871515161598626461908992 : ℤ)
  | 32 => (5993514820402532770205885806867728440552656373916106752 : ℤ)
  | 33 => (5853957240188110281509693511155697537716479597781975040 : ℤ)
  | 34 => (5721038946881673746266953299999897217048889129791651840 : ℤ)
  | 35 => (5594283180844143835113395766979050271684588532599357440 : ℤ)
  | 36 => (5473258710654616287232600284549497102305766574957527040 : ℤ)
  | 37 => (5357574442349155583709919506405141317446816984454922240 : ℤ)
  | 38 => (5246874785749862270168562722043494408239501639019397120 : ℤ)
  | 39 => (5140835655554416103610708614892149758136274250125803520 : ℤ)
  | 40 => (5039161007098543932646638710421600456336639396434411520 : ℤ)
  | 41 => (4941579824471033275266766479391747824194253425548984320 : ℤ)
  | 42 => (4847843492936358466138114720450517206267258285766737920 : ℤ)
  | 43 => (4757723499153522002408432375319693045300736326453166080 : ℤ)
  | 44 => (4671009412047052535000344115893473048843910614016327680 : ℤ)
  | 45 => (4587507104832191620421508984707128180585063153485742080 : ℤ)
  | 46 => (4507037184967183306985139398308134059378540021054177280 : ℤ)
  | 47 => (4429433603971975248538507076674431631686667435958599680 : ℤ)
  | 48 => (4354542423327547373645938847919214977693897480481013760 : ℤ)
  | 49 => (4282220716221998174257147748108460288775223545650216960 : ℤ)
  | 50 => (4212335587872416800529340172935123512980162962102681600 : ℤ)
  | 51 => (4144763299632510276132513416026701035008364740450713600 : ℤ)
  | 52 => (4079388484180893394805502163407983353068169712998809600 : ℤ)
  | 53 => (-702421057092721521293019219627479589222195988863681494389882880 : ℤ)
  | 54 => (2809684248390107350133868538203586381020554114030003272831467520 : ℤ)
  | 55 => (-4214526362757543313310468719819397086957053093198959691568250880 : ℤ)
  | 56 => (2809684248273111901182793132400181827632771041674693210716241920 : ℤ)
  | 57 => (-702421057326883465173168679488387240666457722861370785377812480 : ℤ)
  | 58 => (3727717063130816378011924390700398581251948186016153600 : ℤ)
  | 59 => (3675065692182641005441134498176381652138220104292761600 : ℤ)
  | 60 => (3623918646118699214943795745438765206713455682047180800 : ℤ)
  | 61 => (3574211189646841610570026013767232830720547876555980800 : ℤ)
  | 62 => (3525882299893106575349147893758762241185951339302092800 : ℤ)
  | 63 => (3478874401228992572791174063233532848470856580674355200 : ℤ)
  | 64 => (3433133122698678831783052434069307105647548154721075200 : ℤ)
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta5 (i : ℕ) : ℤ :=
  match i with
  | 19 => (2516260824928658076846560441663557703346679063625544499200 : ℤ)
  | 20 => (2410015391632306172597550047270344058529373795006178918400 : ℤ)
  | 21 => (2312529661706683711656130079545769778202997154306745958400 : ℤ)
  | 22 => (2222750345241748687668130408243073921664676137987263692800 : ℤ)
  | 23 => (2139787987386604039142357222928797582425392768481021132800 : ℤ)
  | 24 => (2062886093911107574933091647623192989622795307250928844800 : ℤ)
  | 25 => (1991397021377449286127485263347939031041409614872743772160 : ℤ)
  | 26 => (1924762956504869879007269045843020111064804706768346152960 : ℤ)
  | 27 => (1862500768942628074905622280101375350991102059780023255040 : ℤ)
  | 28 => (1804189843749506584990504561014877668011514504008265891840 : ℤ)
  | 29 => (1749462228783524938299208860642229240632669595899254538240 : ℤ)
  | 30 => (1697994597020415238780566364285020353723407788489194864640 : ℤ)
  | 31 => (1649501643925822948447504555455246894193307374512337059840 : ℤ)
  | 32 => (1603730628515382059780650887003062650588572817420902727680 : ℤ)
  | 33 => (1560456832642959928670992856278583934595476927823510241280 : ℤ)
  | 34 => (1519479762611069975637230283412383825347706855167707054080 : ℤ)
  | 35 => (1480619954795557251746918583370488692090626561663492423680 : ℤ)
  | 36 => (1443716275747234563888549412139879458974406980973709230080 : ℤ)
  | 37 => (1408623629425300627332260482212921499248605653301622472704 : ℤ)
  | 38 => (1375211001464412351838014418896106218182476087771407581184 : ℤ)
  | 39 => (1343359783876462773866885804820798406803859018700212404224 : ℤ)
  | 40 => (1312962334224817191930669037052300108413794071953260150784 : ℤ)
  | 41 => (1283920731743204053712861828025992341331431816808632418304 : ℤ)
  | 42 => (1256145699599852190002634365468836147271351167486126981120 : ℤ)
  | 43 => (1229555667905539573464185747680120329942437860939944427520 : ℤ)
  | 44 => (1204075956418487582585416938428568564726928439048373534720 : ℤ)
  | 45 => (1179638059429457142802989712783459918329851108811048222720 : ℤ)
  | 46 => (1156179018186921567457802210944103016762097469653065400320 : ℤ)
  | 47 => (1133640868576905114358854406379712365227025225285275484160 : ℤ)
  | 48 => (1111970153708266384936799616757206936702379976046264975360 : ℤ)
  | 49 => (1091117492653067399109606276965660266912978966257032232960 : ℤ)
  | 50 => (1071037197917374058702981441082516330300165451425031127040 : ℤ)
  | 51 => (1051686935321355515734431473052048719911707368604555018240 : ℤ)
  | 52 => (1033027420889575260404557529816428008366926189540262543360 : ℤ)
  | 53 => (1015022150125521905134243050139524264670038763472745922560 : ℤ)
  | 54 => (997637155694992182302924160159705056426206575309524828160 : ℤ)
  | 55 => (980840790092170471043520454882547634289501397792965263360 : ℤ)
  | 56 => (964603530327414696332736629272291242066627482209128284160 : ℤ)
  | 57 => (948897802070937625981853370683924217963278644374373662720 : ℤ)
  | 58 => (933697821023290546322961655378490771169631064357464965120 : ℤ)
  | 59 => (918979449571281455749409795561248365713034562156961464320 : ℤ)
  | 60 => (904720067034498492652184601948424434272058414495977963520 : ℤ)
  | 61 => (890898452019419022175736986514892194295785830676032389120 : ℤ)
  | 62 => (877494675580525346733909862399997035241658558377285910528 : ℤ)
  | 63 => (864490004045381872965977330313922500869662485390859173888 : ℤ)
  | 64 => (851866810496982625266368446709050621929039609206478471168 : ℤ)
  | _ => 0

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta6 (i : ℕ) : ℤ :=
  match i with
  | 19 => (1906124264737082592350773867485934692186933681999524659200 : ℤ)
  | 20 => (1826181962677336009185341673829905976394034759556556390400 : ℤ)
  | 21 => (1752797427583428012920198839809723366193522076845237862400 : ℤ)
  | 22 => (1685185241478209104691385745151540935518775059698574950400 : ℤ)
  | 23 => (1622681769371033846223592349257289811271072395318578380800 : ℤ)
  | 24 => (1564722268843835649424674916400754476631522515090197708800 : ℤ)
  | 25 => (1510823004110049920804116633356271608060679863995738357760 : ℤ)
  | 26 => (1460567127337970772541932365014360779539375534819675996160 : ℤ)
  | 27 => (1413593428911297977035995884484759572581364481532058664960 : ℤ)
  | 28 => (1369587295905969455147608874505909831739213271159317463040 : ℤ)
  | 29 => (1328273387024456883155181272853738545975208087408963747840 : ℤ)
  | 30 => (1289409653949310226525063015419794755997573393186595799040 : ℤ)
  | 31 => (1252782427826013904805586514069761175044282431025331568640 : ℤ)
  | 32 => (1218202355018746656159242825559214564847904684469219491840 : ℤ)
  | 33 => (1185501015029732321804154664073576755465758087682122055680 : ℤ)
  | 34 => (1154528090142182241811452404611729977564509690135870177280 : ℤ)
  | 35 => (1125148984181743079830819558936011409946195824271142420480 : ℤ)
  | 36 => (1097242809100378325268463712351793288228046392736276807680 : ℤ)
  | 37 => (1070700674530303716504106834932500147108112762558039982080 : ℤ)
  | 38 => (1045424228240394275931619025458367958747213914317944520704 : ℤ)
  | 39 => (1021324405438093342780979153340387383847786701069362397184 : ℤ)
  | 40 => (998320352750801740036276420903972543327536866665718349824 : ℤ)
  | 41 => (976338498980269841852025735670030973314943191919607414784 : ℤ)
  | 42 => (955311749718764973874186224295681995163505957728161890304 : ℤ)
  | 43 => (935178786924818670160207031592719064967795677221481349120 : ℤ)
  | 44 => (915883457791302269981813580483005908600326813635858923520 : ℤ)
  | 45 => (897374239862344441402653041613612241636864303906601041920 : ℤ)
  | 46 => (879603771494099722080720683290567863133049237476705566720 : ℤ)
  | 47 => (862528438505507921644517628887229941463099893453495992320 : ℤ)
  | 48 => (846108009305520919500013253115690812330090098589863772160 : ℤ)
  | 49 => (830305311973032887932220527845512354272729239691575951360 : ℤ)
  | 50 => (815085947752538572045118769832199576131921244629436989440 : ℤ)
  | 51 => (800418036250188934129954473304613692279520626299937751040 : ℤ)
  | 52 => (786271988301616258941655023885259594160690328578021130240 : ℤ)
  | 53 => (772620303058887687702210824973540564233852867250078351360 : ℤ)
  | 54 => (759437386328735954148606469460393995428318650854602178560 : ℤ)
  | 55 => (746699387603602339517026426402013519352517737466256424960 : ℤ)
  | 56 => (734384053573841161164513752084814874663557003482612367360 : ℤ)
  | 57 => (722470596204143795398975658102588881732366322886676316160 : ℤ)
  | 58 => (710939573708412775064191726603354656945125436074722590720 : ℤ)
  | 59 => (699772782971994930166616310350134253558565198571367301120 : ℤ)
  | 60 => (688953162154174099862336872950031123395486460800632094720 : ℤ)
  | 61 => (678464702361933880304244022330833704123650445948768747520 : ℤ)
  | 62 => (668292367422218355188247061407262604956223151944100741120 : ℤ)
  | 63 => (658422020897565960174792793246456804463041318990305558528 : ℤ)
  | 64 => (648840359591843726821846465365906336196961140369300389888 : ℤ)
  | _ => 0

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta7 (i : ℕ) : ℤ :=
  match i with
  | 19 => (1468939800347843465664816558429527652694517699889541939200 : ℤ)
  | 20 => (1407733975333349987928782535161630667165579462394144358400 : ℤ)
  | 21 => (1351524544197590671640588023997235476373697407551432294400 : ℤ)
  | 22 => (1299715346307307463445661264969446979810472786294892134400 : ℤ)
  | 23 => (1251802381127137274759219369217363522456727912215635558400 : ℤ)
  | 24 => (1207356528201256675871932905653703123753277212314094796800 : ℤ)
  | 25 => (1166010037320849565887081850541311256614439139405893468160 : ℤ)
  | 26 => (1127445858414870994325661762337576204198099695068522741760 : ℤ)
  | 27 => (1091389135187057732229346192922283723968002038815690588160 : ℤ)
  | 28 => (1057600365051488973877430647110256697566111467528215592960 : ℤ)
  | 29 => (1025869854937878003822097610833976021379658636948710359040 : ℤ)
  | 30 => (996013194088635146873853717970869195960971941005376880640 : ℤ)
  | 31 => (967867531753353707543133123597663126951538412796027863040 : ℤ)
  | 32 => (941288496948681027041841931367071159405936043771968880640 : ℤ)
  | 33 => (916147634167999623176217775665696973925871824102322339840 : ℤ)
  | 34 => (892330256556948436850042115647515564276726193796604231680 : ℤ)
  | 35 => (869733639054335039284600214712127677552307278932795719680 : ℤ)
  | 36 => (848265490068558299596379929866953618267665702268153364480 : ℤ)
  | 37 => (827842652665928268824144073257574896324611679436071239680 : ℤ)
  | 38 => (808389995896760240492532449498655923412663173292050350080 : ℤ)
  | 39 => (789839464443608324945982444779237689505493801699800776704 : ℤ)
  | 40 => (772129260736227040569983487178235371337109591266672246784 : ℤ)
  | 41 => (755203138407517542757256258794555945756144564419191373824 : ℤ)
  | 42 => (739009789740397173079648910753695723304774515917045366784 : ℤ)
  | 43 => (723502312786796320654655372051819657944271436981473378304 : ℤ)
  | 44 => (708637746286758395422938244172580871776271031946308485120 : ℤ)
  | 45 => (694376662500754445794261877227759675257502716033467678720 : ℤ)
  | 46 => (680682809686808526436569853646523535105840730165131345920 : ℤ)
  | 47 => (667522797279745422326681818471715086528217654665905438720 : ℤ)
  | 48 => (654865817920619336468687907085436597704202301951254200320 : ℤ)
  | 49 => (642683401385630060552261688901689169464231233444810588160 : ℤ)
  | 50 => (630949196211539846163423994915790744264187551849423831040 : ℤ)
  | 51 => (619638775437349315409043737548158782005899982039091773440 : ℤ)
  | 52 => (608729463402599470890727037795265990348230541836329943040 : ℤ)
  | 53 => (598200180979453011989960181498729773397915151368443658240 : ℤ)
  | 54 => (588031306983431167545917738927502036448166119248085647360 : ℤ)
  | 55 => (578204553818287734358791439524283440875098934634463887360 : ℤ)
  | 56 => (568702855673697837937743807714762081844891230464334888960 : ℤ)
  | 57 => (559510267818145510490130828462252058866590610638619279360 : ℤ)
  | 58 => (550611875720098069736220026266621976552589005781372764160 : ℤ)
  | 59 => (541993712893588163395720088527319394226022310784763166720 : ℤ)
  | 60 => (533642686504084062025952532908699578551447125369573867520 : ℤ)
  | 61 => (525546509890655213166602009892882262732747372405425438720 : ℤ)
  | 62 => (517693641263955620813279076419767889600632955753484779520 : ℤ)
  | 63 => (510073227928969909339995844796372438282777367942392709120 : ℤ)
  | 64 => (502675055458899521292920501895111796643868125363624214528 : ℤ)
  | _ => 0

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta8 (i : ℕ) : ℤ :=
  match i with
  | 19 => (-702419911819241320803580123586619417666559522144027450697318400 : ℤ)
  | 20 => (1101704850260882599248612418822145739520888274917156454400 : ℤ)
  | 21 => (1057986403821958686580016687916505035571646676706158182400 : ℤ)
  | 22 => (1017674589573080793080402442535979191670397930303809126400 : ℤ)
  | 23 => (980380607101254536127222882702158359659490677623252582400 : ℤ)
  | 24 => (945773256054669886079049252877878594812036724738647654400 : ℤ)
  | 25 => (913568568131687982738969593967797593214373672336186408960 : ℤ)
  | 26 => (883521614177033514797694050843325169557801120196366172160 : ℤ)
  | 27 => (855419969461566648832177214480256268513929750644533493760 : ℤ)
  | 28 => (829078456553514256217771807488439500272552449549700956160 : ℤ)
  | 29 => (804334882232895272900738137036200205722229105478294568960 : ℤ)
  | 30 => (781046554879904092877961517762388079263905686967120035840 : ℤ)
  | 31 => (759087419838982974992431692417719574558630376507063664640 : ℤ)
  | 32 => (738345687949003166033005536343049431218020022188286935040 : ℤ)
  | 33 => (718721860532341108001718210392900302937069725606886768640 : ℤ)
  | 34 => (700127075293316760578450634720178201470795691765624995840 : ℤ)
  | 35 => (682481713650113656040782607300440185320366522383812526080 : ℤ)
  | 36 => (665714222339356780164486803819137725789179820614803783680 : ℤ)
  | 37 => (649760111643174047479512827376476908444082229310107156480 : ℤ)
  | 38 => (634561099988580444394562947148426520970069876819026247680 : ℤ)
  | 39 => (620064380467549539766273916366665198708237827152365486080 : ℤ)
  | 40 => (606221989400127891737880374975546732918679089213608034304 : ℤ)
  | 41 => (592990260693807105732810736150244194179241579085020790784 : ℤ)
  | 42 => (580329352651821892082873335171993129959178171575198285824 : ℤ)
  | 43 => (568202836211578165444205124889797159037970132208959094784 : ℤ)
  | 44 => (556577335474541381374562581321191515592621698357661794304 : ℤ)
  | 45 => (545422212914775788126847515458188910365769065291914936320 : ℤ)
  | 46 => (534709292897727982135042686094115365182011661697647902720 : ℤ)
  | 47 => (524412618160442200302014900622105699712806932304541777920 : ℤ)
  | 48 => (514508234743511727986596760301972622705872060927411486720 : ℤ)
  | 49 => (504974001558594493033502543980382755592516822370688696320 : ℤ)
  | 50 => (495789421350845713985780033058736404194779463455856394240 : ℤ)
  | 51 => (486935490295084604431579234285444895960803463624958935040 : ℤ)
  | 52 => (478394563865441289864349837699165738477580972434328125440 : ℤ)
  | 53 => (470150236954689709978951890773612438207238305997693911040 : ℤ)
  | 54 => (462187236502800839243217907570069805555830179156449034240 : ℤ)
  | 55 => (454491325133627216121843506342999522566846328349036380160 : ℤ)
  | 56 => (447049214501515996353004246807361329027374140001469071360 : ℤ)
  | 57 => (439848487222132621651356390308663164941863362052971560960 : ℤ)
  | 58 => (432877526408848660001784573425223812944649429613658767360 : ℤ)
  | 59 => (426125451961806250612083029789543361917460387146665820160 : ℤ)
  | 60 => (419582062864601207923652041991525423168145835793968005120 : ℤ)
  | 61 => (413237784836228040250147896971853049642060428657316331520 : ℤ)
  | 62 => (407083622765829127225890997116307452031576590156268830720 : ℤ)
  | 63 => (401111117426825187030357127338059345735988693857489387520 : ℤ)
  | 64 => (395312306026794638584932051169065590416018172638522245120 : ℤ)
  | _ => 0

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def fixedClearedZeta9 (i : ℕ) : ℤ :=
  match i with
  | 19 => (2809685155801216587627316737408571781394935693017484388571545600 : ℤ)
  | 20 => (-702420187245453886024229935739724123202994402366096179986432000 : ℤ)
  | 21 => (839394171627339123237038033388301515825438685651166822400 : ℤ)
  | 22 => (807598937853576277659877501820562822044172068770440806400 : ℤ)
  | 23 => (778173535168541097591573655835512726557161348800079462400 : ℤ)
  | 24 => (750858763296903994617095295447544663925972287015511654400 : ℤ)
  | 25 => (725432286002493366229326769113449446907859069755216363520 : ℤ)
  | 26 => (701702250773825944421928744194308027921895157929040936960 : ℤ)
  | 27 => (679502197462055255677580639950335217794673661878374236160 : ℤ)
  | 28 => (658686960486409041823496425404873100742342558695041269760 : ℤ)
  | 29 => (639129344439568980485252424932897131389640678012260188160 : ℤ)
  | 30 => (620717407189414839692636067232509249135414392992101826560 : ℤ)
  | 31 => (603352224192664963966894998597525863212149513593385123840 : ℤ)
  | 32 => (586946036985720068859836001976759302758491583551257968640 : ℤ)
  | 33 => (571420710636748226752912745612421288866370283564475351040 : ℤ)
  | 34 => (556706441376328961053392854683761223595762626354363760640 : ℤ)
  | 35 => (542740668113190674971506003459871667253525938206031216640 : ℤ)
  | 36 => (529467151113879961700697549130697721498020928645318574080 : ℤ)
  | 37 => (516835188520318591076836476951280193421492215896269127680 : ℤ)
  | 38 => (504798947135163179157326982794615626928175877347323412480 : ℤ)
  | 39 => (493316888416672418849869047299433477441750867214262599680 : ℤ)
  | 40 => (482351274184939214860197364013896981268126792787720929280 : ℤ)
  | 41 => (471867739368312940610000811704553350050278080077369442304 : ℤ)
  | 42 => (461834921377035367727023543433322082331516784452025974784 : ℤ)
  | 43 => (452224137505207636356290495774069206759074883794133581824 : ℤ)
  | 44 => (443009103227386960984135531841826052274232828241100406784 : ℤ)
  | 45 => (434165685445554425902494534785397544534745223366866632704 : ℤ)
  | 46 => (425671685712505940382433122107955677809150774540050104320 : ℤ)
  | 47 => (417506649252953237534126471325801988637236313302205726720 : ℤ)
  | 48 => (409651696258266929546951106994798851846047737000671313920 : ℤ)
  | 49 => (402089372471993095410207737973182241122107951241987358720 : ℤ)
  | 50 => (394803516532506233108641302098168181640427994878973050880 : ℤ)
  | 51 => (387779141913504282686896462585977017967241397287507722240 : ℤ)
  | 52 => (381002331616153585273058809398700113314564206421386199040 : ℤ)
  | 53 => (374460144029508969180518477432925574371836795555351101440 : ℤ)
  | 54 => (368140528597200580418895185327117462325674576838697943040 : ℤ)
  | 55 => (362032250115447875675162233131692920144840335982162083840 : ℤ)
  | 56 => (356124820646048412617503111805307938681052732374290268160 : ℤ)
  | 57 => (350408438162842084138213683752787141350103238692946575360 : ℤ)
  | 58 => (344873931165159983785096699030891980500407476284251176960 : ℤ)
  | 59 => (339512708590129795658681826067414851968302965637628559360 : ℤ)
  | 60 => (334316714440066034008031994887697883624053030903569448960 : ℤ)
  | 61 => (329278386613709191591798565038890526486105813259774853120 : ℤ)
  | 62 => (324390619492608475794614637389421941616182341970448875520 : ℤ)
  | 63 => (319646729887981301888699535305026044133093393734272286720 : ℤ)
  | 64 => (315040426000193733964059282117579209835919297379586539520 : ℤ)
  | _ => 0

end InternalCatalan

end

end

section

noncomputable section
namespace InternalCatalan

def fixedClearedMoment (i : ℕ) (k : Fin 48) : ℤ :=
  match k.val with
  | 0 => fixedClearedMoment0 i
  | 1 => fixedClearedMoment1 i
  | 2 => fixedClearedMoment2 i
  | 3 => fixedClearedMoment3 i
  | 4 => fixedClearedMoment4 i
  | 5 => fixedClearedMoment5 i
  | 6 => fixedClearedMoment6 i
  | 7 => fixedClearedMoment7 i
  | 8 => fixedClearedMoment8 i
  | 9 => fixedClearedMoment9 i
  | 10 => fixedClearedMoment10 i
  | 11 => fixedClearedMoment11 i
  | 12 => fixedClearedMoment12 i
  | 13 => fixedClearedMoment13 i
  | 14 => fixedClearedMoment14 i
  | 15 => fixedClearedMoment15 i
  | 16 => fixedClearedMoment16 i
  | 17 => fixedClearedMoment17 i
  | 18 => fixedClearedMoment18 i
  | 19 => fixedClearedMoment19 i
  | 20 => fixedClearedMoment20 i
  | 21 => fixedClearedMoment21 i
  | 22 => fixedClearedMoment22 i
  | 23 => fixedClearedMoment23 i
  | 24 => fixedClearedMoment24 i
  | 25 => fixedClearedMoment25 i
  | 26 => fixedClearedMoment26 i
  | 27 => fixedClearedMoment27 i
  | 28 => fixedClearedMoment28 i
  | 29 => fixedClearedMoment29 i
  | 30 => fixedClearedMoment30 i
  | 31 => fixedClearedMoment31 i
  | 32 => fixedClearedMoment32 i
  | 33 => fixedClearedMoment33 i
  | 34 => fixedClearedMoment34 i
  | 35 => fixedClearedMoment35 i
  | 36 => fixedClearedMoment36 i
  | 37 => fixedClearedMoment37 i
  | 38 => fixedClearedMoment38 i
  | 39 => fixedClearedMoment39 i
  | 40 => fixedClearedMoment40 i
  | 41 => fixedClearedMoment41 i
  | 42 => fixedClearedMoment42 i
  | 43 => fixedClearedMoment43 i
  | 44 => fixedClearedMoment44 i
  | 45 => fixedClearedMoment45 i
  | 46 => fixedClearedMoment46 i
  | 47 => fixedClearedMoment47 i
  | _ => 0

def fixedClearedZeta (i : ℕ) (k : Fin 48) : ℤ :=
  match k.val with
  | 0 => fixedClearedZeta0 i
  | 1 => fixedClearedZeta1 i
  | 2 => fixedClearedZeta2 i
  | 3 => fixedClearedZeta3 i
  | 4 => fixedClearedZeta4 i
  | 5 => fixedClearedZeta5 i
  | 6 => fixedClearedZeta6 i
  | 7 => fixedClearedZeta7 i
  | 8 => fixedClearedZeta8 i
  | 9 => fixedClearedZeta9 i
  | 10 => fixedClearedZeta10 i
  | 11 => fixedClearedZeta11 i
  | 12 => fixedClearedZeta12 i
  | 13 => fixedClearedZeta13 i
  | 14 => fixedClearedZeta14 i
  | 15 => fixedClearedZeta15 i
  | 16 => fixedClearedZeta16 i
  | 17 => fixedClearedZeta17 i
  | 18 => fixedClearedZeta18 i
  | 19 => fixedClearedZeta19 i
  | 20 => fixedClearedZeta20 i
  | 21 => fixedClearedZeta21 i
  | 22 => fixedClearedZeta22 i
  | 23 => fixedClearedZeta23 i
  | 24 => fixedClearedZeta24 i
  | 25 => fixedClearedZeta25 i
  | 26 => fixedClearedZeta26 i
  | 27 => fixedClearedZeta27 i
  | 28 => fixedClearedZeta28 i
  | 29 => fixedClearedZeta29 i
  | 30 => fixedClearedZeta30 i
  | 31 => fixedClearedZeta31 i
  | 32 => fixedClearedZeta32 i
  | 33 => fixedClearedZeta33 i
  | 34 => fixedClearedZeta34 i
  | 35 => fixedClearedZeta35 i
  | 36 => fixedClearedZeta36 i
  | 37 => fixedClearedZeta37 i
  | 38 => fixedClearedZeta38 i
  | 39 => fixedClearedZeta39 i
  | 40 => fixedClearedZeta40 i
  | 41 => fixedClearedZeta41 i
  | 42 => fixedClearedZeta42 i
  | 43 => fixedClearedZeta43 i
  | 44 => fixedClearedZeta44 i
  | 45 => fixedClearedZeta45 i
  | 46 => fixedClearedZeta46 i
  | 47 => fixedClearedZeta47 i
  | _ => 0

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace InternalCatalan

def fixedIntegerBaseCanonical (r : Fin 49) (k : Fin 48) : ℤ :=
  2 * (∑ i ∈ Finset.range 65,
    (rowP 1 r.val).coeff i * fixedClearedMoment i k) -
  3 * (∑ i ∈ Finset.range 65,
    (rowD 1 r.val).coeff i * fixedClearedZeta i k)

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

noncomputable section

namespace InternalCatalan

open scoped BigOperators

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def fixedDeterminantPrimeCutoff : ℕ :=
  260 + (fixedMatrix 0).det.num.natAbs + (fixedMatrix 0).det.den +
    (fixedMatrix 1).det.num.natAbs + (fixedMatrix 1).det.den +
    (fixedMatrix (-1)).det.num.natAbs + (fixedMatrix (-1)).det.den

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvMinusRow_0 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 91
  | 1 => 22
  | 2 => 5
  | 3 => 45
  | 4 => 83
  | 5 => 13
  | 6 => 97
  | 7 => 68
  | 8 => 95
  | 9 => 100
  | 10 => 13
  | 11 => 23
  | 12 => 79
  | 13 => 36
  | 14 => 88
  | 15 => 2
  | 16 => 30
  | 17 => 96
  | 18 => 63
  | 19 => 96
  | 20 => 32
  | 21 => 39
  | 22 => 51
  | 23 => 58
  | 24 => 73
  | 25 => 98
  | 26 => 42
  | 27 => 54
  | 28 => 66
  | 29 => 20
  | 30 => 52
  | 31 => 89
  | 32 => 16
  | 33 => 14
  | 34 => 74
  | 35 => 82
  | 36 => 80
  | 37 => 98
  | 38 => 97
  | 39 => 95
  | 40 => 42
  | 41 => 87
  | 42 => 14
  | 43 => 79
  | 44 => 45
  | 45 => 25
  | 46 => 42
  | 47 => 82
  | _ => 0

def fixedLiteralInvMinusRow_1 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 86
  | 1 => 4
  | 2 => 15
  | 3 => 68
  | 4 => 89
  | 5 => 66
  | 6 => 26
  | 7 => 99
  | 8 => 84
  | 9 => 49
  | 10 => 99
  | 11 => 0
  | 12 => 26
  | 13 => 74
  | 14 => 55
  | 15 => 55
  | 16 => 47
  | 17 => 75
  | 18 => 4
  | 19 => 48
  | 20 => 41
  | 21 => 15
  | 22 => 37
  | 23 => 41
  | 24 => 83
  | 25 => 94
  | 26 => 17
  | 27 => 96
  | 28 => 28
  | 29 => 66
  | 30 => 29
  | 31 => 57
  | 32 => 34
  | 33 => 58
  | 34 => 3
  | 35 => 6
  | 36 => 71
  | 37 => 34
  | 38 => 7
  | 39 => 13
  | 40 => 92
  | 41 => 76
  | 42 => 5
  | 43 => 12
  | 44 => 14
  | 45 => 65
  | 46 => 91
  | 47 => 19
  | _ => 0

def fixedLiteralInvMinusRow_2 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 12
  | 1 => 85
  | 2 => 20
  | 3 => 50
  | 4 => 10
  | 5 => 72
  | 6 => 10
  | 7 => 57
  | 8 => 88
  | 9 => 40
  | 10 => 51
  | 11 => 59
  | 12 => 46
  | 13 => 80
  | 14 => 28
  | 15 => 73
  | 16 => 66
  | 17 => 7
  | 18 => 69
  | 19 => 62
  | 20 => 83
  | 21 => 14
  | 22 => 78
  | 23 => 42
  | 24 => 35
  | 25 => 100
  | 26 => 67
  | 27 => 79
  | 28 => 79
  | 29 => 45
  | 30 => 47
  | 31 => 33
  | 32 => 30
  | 33 => 99
  | 34 => 89
  | 35 => 15
  | 36 => 53
  | 37 => 14
  | 38 => 62
  | 39 => 21
  | 40 => 26
  | 41 => 75
  | 42 => 89
  | 43 => 20
  | 44 => 34
  | 45 => 7
  | 46 => 71
  | 47 => 38
  | _ => 0

def fixedLiteralInvMinusRow_3 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 60
  | 1 => 93
  | 2 => 40
  | 3 => 94
  | 4 => 52
  | 5 => 29
  | 6 => 44
  | 7 => 88
  | 8 => 89
  | 9 => 64
  | 10 => 64
  | 11 => 74
  | 12 => 2
  | 13 => 67
  | 14 => 29
  | 15 => 68
  | 16 => 92
  | 17 => 81
  | 18 => 21
  | 19 => 32
  | 20 => 4
  | 21 => 18
  | 22 => 62
  | 23 => 66
  | 24 => 67
  | 25 => 6
  | 26 => 20
  | 27 => 24
  | 28 => 33
  | 29 => 5
  | 30 => 17
  | 31 => 4
  | 32 => 41
  | 33 => 82
  | 34 => 98
  | 35 => 79
  | 36 => 74
  | 37 => 61
  | 38 => 63
  | 39 => 9
  | 40 => 5
  | 41 => 49
  | 42 => 70
  | 43 => 91
  | 44 => 66
  | 45 => 87
  | 46 => 36
  | 47 => 81
  | _ => 0

def fixedLiteralInvMinusRow_4 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 37
  | 1 => 24
  | 2 => 33
  | 3 => 56
  | 4 => 82
  | 5 => 76
  | 6 => 22
  | 7 => 44
  | 8 => 96
  | 9 => 84
  | 10 => 41
  | 11 => 37
  | 12 => 47
  | 13 => 19
  | 14 => 80
  | 15 => 43
  | 16 => 53
  | 17 => 9
  | 18 => 67
  | 19 => 36
  | 20 => 75
  | 21 => 30
  | 22 => 8
  | 23 => 11
  | 24 => 38
  | 25 => 24
  | 26 => 60
  | 27 => 19
  | 28 => 46
  | 29 => 96
  | 30 => 15
  | 31 => 33
  | 32 => 64
  | 33 => 31
  | 34 => 25
  | 35 => 75
  | 36 => 15
  | 37 => 92
  | 38 => 37
  | 39 => 56
  | 40 => 1
  | 41 => 15
  | 42 => 70
  | 43 => 93
  | 44 => 55
  | 45 => 85
  | 46 => 94
  | 47 => 54
  | _ => 0

def fixedLiteralInvMinusRow_5 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 11
  | 1 => 8
  | 2 => 74
  | 3 => 48
  | 4 => 5
  | 5 => 62
  | 6 => 43
  | 7 => 31
  | 8 => 35
  | 9 => 85
  | 10 => 19
  | 11 => 57
  | 12 => 20
  | 13 => 22
  | 14 => 38
  | 15 => 22
  | 16 => 42
  | 17 => 85
  | 18 => 55
  | 19 => 88
  | 20 => 26
  | 21 => 53
  | 22 => 68
  | 23 => 31
  | 24 => 21
  | 25 => 36
  | 26 => 45
  | 27 => 23
  | 28 => 3
  | 29 => 1
  | 30 => 12
  | 31 => 13
  | 32 => 15
  | 33 => 95
  | 34 => 84
  | 35 => 89
  | 36 => 21
  | 37 => 65
  | 38 => 17
  | 39 => 85
  | 40 => 15
  | 41 => 99
  | 42 => 1
  | 43 => 55
  | 44 => 1
  | 45 => 22
  | 46 => 20
  | 47 => 58
  | _ => 0

def fixedLiteralInvMinusRow_6 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 99
  | 1 => 75
  | 2 => 19
  | 3 => 65
  | 4 => 92
  | 5 => 74
  | 6 => 62
  | 7 => 49
  | 8 => 11
  | 9 => 98
  | 10 => 23
  | 11 => 24
  | 12 => 98
  | 13 => 18
  | 14 => 75
  | 15 => 53
  | 16 => 10
  | 17 => 21
  | 18 => 50
  | 19 => 97
  | 20 => 87
  | 21 => 56
  | 22 => 98
  | 23 => 23
  | 24 => 49
  | 25 => 53
  | 26 => 1
  | 27 => 27
  | 28 => 79
  | 29 => 5
  | 30 => 92
  | 31 => 60
  | 32 => 10
  | 33 => 65
  | 34 => 76
  | 35 => 6
  | 36 => 87
  | 37 => 2
  | 38 => 17
  | 39 => 45
  | 40 => 89
  | 41 => 54
  | 42 => 41
  | 43 => 83
  | 44 => 73
  | 45 => 23
  | 46 => 51
  | 47 => 62
  | _ => 0

def fixedLiteralInvMinusRow_7 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 80
  | 2 => 73
  | 3 => 35
  | 4 => 25
  | 5 => 83
  | 6 => 74
  | 7 => 8
  | 8 => 51
  | 9 => 39
  | 10 => 17
  | 11 => 19
  | 12 => 86
  | 13 => 99
  | 14 => 18
  | 15 => 65
  | 16 => 80
  | 17 => 92
  | 18 => 56
  | 19 => 18
  | 20 => 80
  | 21 => 62
  | 22 => 50
  | 23 => 28
  | 24 => 68
  | 25 => 10
  | 26 => 81
  | 27 => 28
  | 28 => 64
  | 29 => 64
  | 30 => 67
  | 31 => 3
  | 32 => 91
  | 33 => 88
  | 34 => 31
  | 35 => 96
  | 36 => 90
  | 37 => 49
  | 38 => 38
  | 39 => 12
  | 40 => 99
  | 41 => 59
  | 42 => 94
  | 43 => 57
  | 44 => 93
  | 45 => 43
  | 46 => 100
  | 47 => 99
  | _ => 0

def fixedLiteralInvMinusRow_8 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 18
  | 1 => 53
  | 2 => 85
  | 3 => 76
  | 4 => 17
  | 5 => 66
  | 6 => 76
  | 7 => 15
  | 8 => 85
  | 9 => 15
  | 10 => 4
  | 11 => 90
  | 12 => 78
  | 13 => 80
  | 14 => 26
  | 15 => 53
  | 16 => 7
  | 17 => 59
  | 18 => 42
  | 19 => 32
  | 20 => 12
  | 21 => 47
  | 22 => 1
  | 23 => 77
  | 24 => 28
  | 25 => 51
  | 26 => 16
  | 27 => 33
  | 28 => 52
  | 29 => 5
  | 30 => 54
  | 31 => 3
  | 32 => 22
  | 33 => 81
  | 34 => 32
  | 35 => 30
  | 36 => 44
  | 37 => 81
  | 38 => 34
  | 39 => 90
  | 40 => 63
  | 41 => 74
  | 42 => 32
  | 43 => 16
  | 44 => 30
  | 45 => 76
  | 46 => 45
  | 47 => 66
  | _ => 0

def fixedLiteralInvMinusRow_9 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 33
  | 1 => 45
  | 2 => 18
  | 3 => 20
  | 4 => 73
  | 5 => 12
  | 6 => 3
  | 7 => 75
  | 8 => 17
  | 9 => 67
  | 10 => 84
  | 11 => 42
  | 12 => 48
  | 13 => 55
  | 14 => 16
  | 15 => 54
  | 16 => 17
  | 17 => 84
  | 18 => 61
  | 19 => 44
  | 20 => 72
  | 21 => 58
  | 22 => 49
  | 23 => 77
  | 24 => 16
  | 25 => 0
  | 26 => 21
  | 27 => 39
  | 28 => 97
  | 29 => 1
  | 30 => 27
  | 31 => 63
  | 32 => 31
  | 33 => 2
  | 34 => 14
  | 35 => 44
  | 36 => 18
  | 37 => 88
  | 38 => 93
  | 39 => 85
  | 40 => 5
  | 41 => 14
  | 42 => 29
  | 43 => 64
  | 44 => 100
  | 45 => 7
  | 46 => 69
  | 47 => 45
  | _ => 0

def fixedLiteralInvMinusRow_10 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 76
  | 1 => 56
  | 2 => 40
  | 3 => 89
  | 4 => 48
  | 5 => 41
  | 6 => 24
  | 7 => 99
  | 8 => 90
  | 9 => 98
  | 10 => 58
  | 11 => 29
  | 12 => 80
  | 13 => 25
  | 14 => 83
  | 15 => 52
  | 16 => 59
  | 17 => 59
  | 18 => 81
  | 19 => 24
  | 20 => 75
  | 21 => 29
  | 22 => 37
  | 23 => 27
  | 24 => 75
  | 25 => 90
  | 26 => 82
  | 27 => 33
  | 28 => 4
  | 29 => 23
  | 30 => 25
  | 31 => 7
  | 32 => 68
  | 33 => 70
  | 34 => 4
  | 35 => 56
  | 36 => 13
  | 37 => 58
  | 38 => 38
  | 39 => 36
  | 40 => 52
  | 41 => 35
  | 42 => 29
  | 43 => 27
  | 44 => 95
  | 45 => 83
  | 46 => 28
  | 47 => 66
  | _ => 0

def fixedLiteralInvMinusRow_11 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 30
  | 1 => 30
  | 2 => 49
  | 3 => 90
  | 4 => 23
  | 5 => 81
  | 6 => 74
  | 7 => 44
  | 8 => 75
  | 9 => 98
  | 10 => 73
  | 11 => 80
  | 12 => 2
  | 13 => 40
  | 14 => 93
  | 15 => 10
  | 16 => 85
  | 17 => 1
  | 18 => 48
  | 19 => 39
  | 20 => 15
  | 21 => 59
  | 22 => 59
  | 23 => 13
  | 24 => 11
  | 25 => 81
  | 26 => 60
  | 27 => 88
  | 28 => 14
  | 29 => 3
  | 30 => 52
  | 31 => 40
  | 32 => 9
  | 33 => 74
  | 34 => 22
  | 35 => 4
  | 36 => 38
  | 37 => 8
  | 38 => 23
  | 39 => 73
  | 40 => 97
  | 41 => 30
  | 42 => 44
  | 43 => 99
  | 44 => 38
  | 45 => 39
  | 46 => 83
  | 47 => 44
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvMinusRow_12 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 33
  | 1 => 23
  | 2 => 56
  | 3 => 85
  | 4 => 19
  | 5 => 16
  | 6 => 47
  | 7 => 81
  | 8 => 93
  | 9 => 27
  | 10 => 38
  | 11 => 52
  | 12 => 48
  | 13 => 9
  | 14 => 95
  | 15 => 32
  | 16 => 95
  | 17 => 29
  | 18 => 51
  | 19 => 97
  | 20 => 97
  | 21 => 2
  | 22 => 41
  | 23 => 63
  | 24 => 15
  | 25 => 14
  | 26 => 80
  | 27 => 45
  | 28 => 95
  | 29 => 8
  | 30 => 69
  | 31 => 45
  | 32 => 30
  | 33 => 46
  | 34 => 23
  | 35 => 23
  | 36 => 60
  | 37 => 98
  | 38 => 46
  | 39 => 81
  | 40 => 64
  | 41 => 30
  | 42 => 34
  | 43 => 48
  | 44 => 93
  | 45 => 65
  | 46 => 8
  | 47 => 13
  | _ => 0

def fixedLiteralInvMinusRow_13 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 60
  | 1 => 91
  | 2 => 88
  | 3 => 77
  | 4 => 25
  | 5 => 26
  | 6 => 59
  | 7 => 100
  | 8 => 76
  | 9 => 50
  | 10 => 28
  | 11 => 70
  | 12 => 29
  | 13 => 97
  | 14 => 30
  | 15 => 60
  | 16 => 14
  | 17 => 11
  | 18 => 66
  | 19 => 87
  | 20 => 51
  | 21 => 34
  | 22 => 48
  | 23 => 20
  | 24 => 14
  | 25 => 53
  | 26 => 38
  | 27 => 81
  | 28 => 64
  | 29 => 7
  | 30 => 22
  | 31 => 81
  | 32 => 93
  | 33 => 60
  | 34 => 21
  | 35 => 68
  | 36 => 81
  | 37 => 51
  | 38 => 63
  | 39 => 6
  | 40 => 27
  | 41 => 27
  | 42 => 88
  | 43 => 23
  | 44 => 55
  | 45 => 70
  | 46 => 48
  | 47 => 99
  | _ => 0

def fixedLiteralInvMinusRow_14 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 34
  | 1 => 39
  | 2 => 90
  | 3 => 32
  | 4 => 41
  | 5 => 65
  | 6 => 52
  | 7 => 9
  | 8 => 58
  | 9 => 2
  | 10 => 88
  | 11 => 49
  | 12 => 100
  | 13 => 14
  | 14 => 87
  | 15 => 5
  | 16 => 73
  | 17 => 65
  | 18 => 5
  | 19 => 58
  | 20 => 12
  | 21 => 15
  | 22 => 7
  | 23 => 82
  | 24 => 21
  | 25 => 23
  | 26 => 85
  | 27 => 80
  | 28 => 21
  | 29 => 73
  | 30 => 33
  | 31 => 35
  | 32 => 8
  | 33 => 31
  | 34 => 26
  | 35 => 76
  | 36 => 33
  | 37 => 27
  | 38 => 94
  | 39 => 73
  | 40 => 57
  | 41 => 50
  | 42 => 39
  | 43 => 64
  | 44 => 84
  | 45 => 41
  | 46 => 3
  | 47 => 12
  | _ => 0

def fixedLiteralInvMinusRow_15 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 7
  | 1 => 99
  | 2 => 54
  | 3 => 32
  | 4 => 10
  | 5 => 25
  | 6 => 79
  | 7 => 21
  | 8 => 14
  | 9 => 85
  | 10 => 94
  | 11 => 39
  | 12 => 61
  | 13 => 28
  | 14 => 13
  | 15 => 49
  | 16 => 30
  | 17 => 76
  | 18 => 32
  | 19 => 65
  | 20 => 67
  | 21 => 24
  | 22 => 92
  | 23 => 30
  | 24 => 53
  | 25 => 47
  | 26 => 97
  | 27 => 46
  | 28 => 69
  | 29 => 17
  | 30 => 12
  | 31 => 56
  | 32 => 7
  | 33 => 94
  | 34 => 84
  | 35 => 69
  | 36 => 54
  | 37 => 24
  | 38 => 26
  | 39 => 72
  | 40 => 11
  | 41 => 98
  | 42 => 54
  | 43 => 72
  | 44 => 38
  | 45 => 15
  | 46 => 10
  | 47 => 40
  | _ => 0

def fixedLiteralInvMinusRow_16 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 52
  | 1 => 4
  | 2 => 95
  | 3 => 79
  | 4 => 97
  | 5 => 25
  | 6 => 59
  | 7 => 29
  | 8 => 97
  | 9 => 37
  | 10 => 49
  | 11 => 34
  | 12 => 98
  | 13 => 82
  | 14 => 50
  | 15 => 40
  | 16 => 63
  | 17 => 16
  | 18 => 6
  | 19 => 49
  | 20 => 58
  | 21 => 44
  | 22 => 40
  | 23 => 24
  | 24 => 36
  | 25 => 57
  | 26 => 31
  | 27 => 31
  | 28 => 51
  | 29 => 100
  | 30 => 23
  | 31 => 87
  | 32 => 8
  | 33 => 62
  | 34 => 84
  | 35 => 46
  | 36 => 36
  | 37 => 93
  | 38 => 72
  | 39 => 20
  | 40 => 51
  | 41 => 96
  | 42 => 15
  | 43 => 90
  | 44 => 26
  | 45 => 53
  | 46 => 14
  | 47 => 59
  | _ => 0

def fixedLiteralInvMinusRow_17 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 24
  | 1 => 67
  | 2 => 79
  | 3 => 40
  | 4 => 3
  | 5 => 91
  | 6 => 27
  | 7 => 18
  | 8 => 61
  | 9 => 26
  | 10 => 18
  | 11 => 55
  | 12 => 53
  | 13 => 80
  | 14 => 33
  | 15 => 21
  | 16 => 38
  | 17 => 30
  | 18 => 100
  | 19 => 93
  | 20 => 57
  | 21 => 38
  | 22 => 45
  | 23 => 88
  | 24 => 26
  | 25 => 81
  | 26 => 74
  | 27 => 93
  | 28 => 30
  | 29 => 70
  | 30 => 45
  | 31 => 6
  | 32 => 59
  | 33 => 40
  | 34 => 3
  | 35 => 68
  | 36 => 40
  | 37 => 25
  | 38 => 95
  | 39 => 28
  | 40 => 11
  | 41 => 35
  | 42 => 42
  | 43 => 0
  | 44 => 28
  | 45 => 16
  | 46 => 79
  | 47 => 60
  | _ => 0

def fixedLiteralInvMinusRow_18 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 90
  | 1 => 6
  | 2 => 100
  | 3 => 11
  | 4 => 94
  | 5 => 66
  | 6 => 16
  | 7 => 61
  | 8 => 59
  | 9 => 19
  | 10 => 53
  | 11 => 19
  | 12 => 71
  | 13 => 41
  | 14 => 22
  | 15 => 90
  | 16 => 97
  | 17 => 26
  | 18 => 19
  | 19 => 48
  | 20 => 78
  | 21 => 41
  | 22 => 16
  | 23 => 4
  | 24 => 44
  | 25 => 24
  | 26 => 10
  | 27 => 57
  | 28 => 51
  | 29 => 17
  | 30 => 38
  | 31 => 91
  | 32 => 61
  | 33 => 53
  | 34 => 69
  | 35 => 51
  | 36 => 55
  | 37 => 14
  | 38 => 15
  | 39 => 35
  | 40 => 6
  | 41 => 25
  | 42 => 21
  | 43 => 80
  | 44 => 55
  | 45 => 18
  | 46 => 78
  | 47 => 83
  | _ => 0

def fixedLiteralInvMinusRow_19 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 16
  | 1 => 59
  | 2 => 99
  | 3 => 44
  | 4 => 9
  | 5 => 24
  | 6 => 84
  | 7 => 67
  | 8 => 35
  | 9 => 19
  | 10 => 5
  | 11 => 83
  | 12 => 4
  | 13 => 1
  | 14 => 59
  | 15 => 87
  | 16 => 96
  | 17 => 40
  | 18 => 91
  | 19 => 56
  | 20 => 38
  | 21 => 38
  | 22 => 57
  | 23 => 65
  | 24 => 47
  | 25 => 85
  | 26 => 69
  | 27 => 56
  | 28 => 81
  | 29 => 26
  | 30 => 56
  | 31 => 32
  | 32 => 12
  | 33 => 31
  | 34 => 100
  | 35 => 68
  | 36 => 89
  | 37 => 15
  | 38 => 91
  | 39 => 78
  | 40 => 46
  | 41 => 1
  | 42 => 89
  | 43 => 49
  | 44 => 93
  | 45 => 61
  | 46 => 18
  | 47 => 60
  | _ => 0

def fixedLiteralInvMinusRow_20 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 16
  | 1 => 76
  | 2 => 1
  | 3 => 72
  | 4 => 81
  | 5 => 37
  | 6 => 98
  | 7 => 44
  | 8 => 79
  | 9 => 38
  | 10 => 14
  | 11 => 90
  | 12 => 28
  | 13 => 54
  | 14 => 14
  | 15 => 42
  | 16 => 41
  | 17 => 51
  | 18 => 48
  | 19 => 29
  | 20 => 92
  | 21 => 99
  | 22 => 5
  | 23 => 67
  | 24 => 37
  | 25 => 19
  | 26 => 58
  | 27 => 16
  | 28 => 96
  | 29 => 40
  | 30 => 49
  | 31 => 2
  | 32 => 51
  | 33 => 78
  | 34 => 100
  | 35 => 79
  | 36 => 34
  | 37 => 15
  | 38 => 41
  | 39 => 72
  | 40 => 92
  | 41 => 66
  | 42 => 67
  | 43 => 7
  | 44 => 61
  | 45 => 53
  | 46 => 57
  | 47 => 49
  | _ => 0

def fixedLiteralInvMinusRow_21 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 59
  | 1 => 80
  | 2 => 69
  | 3 => 17
  | 4 => 15
  | 5 => 69
  | 6 => 5
  | 7 => 40
  | 8 => 80
  | 9 => 9
  | 10 => 22
  | 11 => 43
  | 12 => 29
  | 13 => 51
  | 14 => 83
  | 15 => 16
  | 16 => 86
  | 17 => 86
  | 18 => 81
  | 19 => 75
  | 20 => 45
  | 21 => 17
  | 22 => 68
  | 23 => 79
  | 24 => 12
  | 25 => 95
  | 26 => 21
  | 27 => 42
  | 28 => 6
  | 29 => 70
  | 30 => 87
  | 31 => 87
  | 32 => 64
  | 33 => 33
  | 34 => 82
  | 35 => 51
  | 36 => 10
  | 37 => 43
  | 38 => 3
  | 39 => 26
  | 40 => 71
  | 41 => 99
  | 42 => 29
  | 43 => 96
  | 44 => 26
  | 45 => 33
  | 46 => 20
  | 47 => 38
  | _ => 0

def fixedLiteralInvMinusRow_22 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 36
  | 2 => 75
  | 3 => 52
  | 4 => 29
  | 5 => 93
  | 6 => 99
  | 7 => 46
  | 8 => 83
  | 9 => 37
  | 10 => 38
  | 11 => 20
  | 12 => 86
  | 13 => 80
  | 14 => 92
  | 15 => 79
  | 16 => 47
  | 17 => 18
  | 18 => 75
  | 19 => 0
  | 20 => 96
  | 21 => 37
  | 22 => 79
  | 23 => 32
  | 24 => 9
  | 25 => 100
  | 26 => 68
  | 27 => 52
  | 28 => 15
  | 29 => 93
  | 30 => 29
  | 31 => 46
  | 32 => 1
  | 33 => 77
  | 34 => 38
  | 35 => 97
  | 36 => 33
  | 37 => 47
  | 38 => 21
  | 39 => 84
  | 40 => 3
  | 41 => 18
  | 42 => 65
  | 43 => 26
  | 44 => 51
  | 45 => 21
  | 46 => 59
  | 47 => 51
  | _ => 0

def fixedLiteralInvMinusRow_23 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 45
  | 1 => 24
  | 2 => 84
  | 3 => 37
  | 4 => 40
  | 5 => 19
  | 6 => 96
  | 7 => 35
  | 8 => 2
  | 9 => 66
  | 10 => 66
  | 11 => 76
  | 12 => 59
  | 13 => 33
  | 14 => 99
  | 15 => 84
  | 16 => 44
  | 17 => 51
  | 18 => 9
  | 19 => 90
  | 20 => 86
  | 21 => 34
  | 22 => 81
  | 23 => 45
  | 24 => 93
  | 25 => 32
  | 26 => 16
  | 27 => 66
  | 28 => 21
  | 29 => 29
  | 30 => 10
  | 31 => 78
  | 32 => 97
  | 33 => 73
  | 34 => 66
  | 35 => 61
  | 36 => 24
  | 37 => 96
  | 38 => 4
  | 39 => 26
  | 40 => 30
  | 41 => 61
  | 42 => 37
  | 43 => 37
  | 44 => 81
  | 45 => 28
  | 46 => 54
  | 47 => 28
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvMinusRow_24 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 23
  | 1 => 92
  | 2 => 26
  | 3 => 14
  | 4 => 53
  | 5 => 49
  | 6 => 5
  | 7 => 41
  | 8 => 63
  | 9 => 17
  | 10 => 13
  | 11 => 42
  | 12 => 47
  | 13 => 0
  | 14 => 24
  | 15 => 82
  | 16 => 85
  | 17 => 39
  | 18 => 54
  | 19 => 66
  | 20 => 81
  | 21 => 16
  | 22 => 43
  | 23 => 58
  | 24 => 45
  | 25 => 11
  | 26 => 78
  | 27 => 35
  | 28 => 2
  | 29 => 79
  | 30 => 63
  | 31 => 27
  | 32 => 24
  | 33 => 19
  | 34 => 20
  | 35 => 79
  | 36 => 93
  | 37 => 100
  | 38 => 8
  | 39 => 7
  | 40 => 21
  | 41 => 50
  | 42 => 10
  | 43 => 71
  | 44 => 1
  | 45 => 95
  | 46 => 24
  | 47 => 25
  | _ => 0

def fixedLiteralInvMinusRow_25 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 92
  | 1 => 72
  | 2 => 2
  | 3 => 53
  | 4 => 41
  | 5 => 94
  | 6 => 16
  | 7 => 72
  | 8 => 87
  | 9 => 25
  | 10 => 53
  | 11 => 9
  | 12 => 50
  | 13 => 89
  | 14 => 90
  | 15 => 80
  | 16 => 32
  | 17 => 69
  | 18 => 53
  | 19 => 92
  | 20 => 11
  | 21 => 97
  | 22 => 56
  | 23 => 93
  | 24 => 6
  | 25 => 10
  | 26 => 3
  | 27 => 43
  | 28 => 60
  | 29 => 79
  | 30 => 53
  | 31 => 31
  | 32 => 46
  | 33 => 96
  | 34 => 74
  | 35 => 34
  | 36 => 69
  | 37 => 41
  | 38 => 99
  | 39 => 8
  | 40 => 87
  | 41 => 42
  | 42 => 23
  | 43 => 47
  | 44 => 95
  | 45 => 70
  | 46 => 85
  | 47 => 48
  | _ => 0

def fixedLiteralInvMinusRow_26 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 46
  | 1 => 32
  | 2 => 37
  | 3 => 33
  | 4 => 100
  | 5 => 12
  | 6 => 64
  | 7 => 64
  | 8 => 97
  | 9 => 39
  | 10 => 11
  | 11 => 53
  | 12 => 35
  | 13 => 22
  | 14 => 42
  | 15 => 82
  | 16 => 92
  | 17 => 3
  | 18 => 26
  | 19 => 30
  | 20 => 81
  | 21 => 32
  | 22 => 49
  | 23 => 56
  | 24 => 50
  | 25 => 65
  | 26 => 19
  | 27 => 20
  | 28 => 87
  | 29 => 94
  | 30 => 89
  | 31 => 75
  | 32 => 2
  | 33 => 3
  | 34 => 95
  | 35 => 42
  | 36 => 37
  | 37 => 76
  | 38 => 81
  | 39 => 76
  | 40 => 12
  | 41 => 5
  | 42 => 25
  | 43 => 85
  | 44 => 5
  | 45 => 68
  | 46 => 35
  | 47 => 81
  | _ => 0

def fixedLiteralInvMinusRow_27 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 20
  | 1 => 89
  | 2 => 61
  | 3 => 52
  | 4 => 73
  | 5 => 11
  | 6 => 93
  | 7 => 89
  | 8 => 66
  | 9 => 72
  | 10 => 88
  | 11 => 65
  | 12 => 74
  | 13 => 24
  | 14 => 88
  | 15 => 86
  | 16 => 55
  | 17 => 32
  | 18 => 55
  | 19 => 45
  | 20 => 59
  | 21 => 45
  | 22 => 19
  | 23 => 14
  | 24 => 23
  | 25 => 87
  | 26 => 45
  | 27 => 0
  | 28 => 31
  | 29 => 81
  | 30 => 49
  | 31 => 46
  | 32 => 30
  | 33 => 78
  | 34 => 8
  | 35 => 48
  | 36 => 51
  | 37 => 56
  | 38 => 30
  | 39 => 93
  | 40 => 44
  | 41 => 65
  | 42 => 24
  | 43 => 56
  | 44 => 85
  | 45 => 59
  | 46 => 53
  | 47 => 91
  | _ => 0

def fixedLiteralInvMinusRow_28 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 21
  | 1 => 37
  | 2 => 97
  | 3 => 66
  | 4 => 96
  | 5 => 93
  | 6 => 97
  | 7 => 25
  | 8 => 53
  | 9 => 72
  | 10 => 23
  | 11 => 53
  | 12 => 13
  | 13 => 67
  | 14 => 0
  | 15 => 64
  | 16 => 91
  | 17 => 38
  | 18 => 76
  | 19 => 39
  | 20 => 96
  | 21 => 89
  | 22 => 59
  | 23 => 26
  | 24 => 32
  | 25 => 95
  | 26 => 83
  | 27 => 16
  | 28 => 28
  | 29 => 63
  | 30 => 67
  | 31 => 23
  | 32 => 56
  | 33 => 80
  | 34 => 75
  | 35 => 68
  | 36 => 16
  | 37 => 82
  | 38 => 97
  | 39 => 58
  | 40 => 47
  | 41 => 25
  | 42 => 41
  | 43 => 63
  | 44 => 74
  | 45 => 14
  | 46 => 43
  | 47 => 37
  | _ => 0

def fixedLiteralInvMinusRow_29 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 21
  | 1 => 31
  | 2 => 91
  | 3 => 76
  | 4 => 78
  | 5 => 76
  | 6 => 83
  | 7 => 84
  | 8 => 2
  | 9 => 29
  | 10 => 53
  | 11 => 80
  | 12 => 96
  | 13 => 99
  | 14 => 98
  | 15 => 68
  | 16 => 5
  | 17 => 81
  | 18 => 46
  | 19 => 13
  | 20 => 89
  | 21 => 20
  | 22 => 61
  | 23 => 38
  | 24 => 30
  | 25 => 27
  | 26 => 59
  | 27 => 86
  | 28 => 56
  | 29 => 5
  | 30 => 45
  | 31 => 25
  | 32 => 5
  | 33 => 21
  | 34 => 54
  | 35 => 56
  | 36 => 45
  | 37 => 48
  | 38 => 88
  | 39 => 51
  | 40 => 38
  | 41 => 77
  | 42 => 49
  | 43 => 99
  | 44 => 77
  | 45 => 37
  | 46 => 100
  | 47 => 28
  | _ => 0

def fixedLiteralInvMinusRow_30 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 57
  | 1 => 38
  | 2 => 30
  | 3 => 16
  | 4 => 65
  | 5 => 89
  | 6 => 99
  | 7 => 53
  | 8 => 28
  | 9 => 79
  | 10 => 39
  | 11 => 33
  | 12 => 1
  | 13 => 54
  | 14 => 48
  | 15 => 37
  | 16 => 71
  | 17 => 2
  | 18 => 7
  | 19 => 40
  | 20 => 90
  | 21 => 47
  | 22 => 100
  | 23 => 81
  | 24 => 30
  | 25 => 73
  | 26 => 26
  | 27 => 58
  | 28 => 25
  | 29 => 77
  | 30 => 28
  | 31 => 41
  | 32 => 84
  | 33 => 11
  | 34 => 90
  | 35 => 69
  | 36 => 14
  | 37 => 10
  | 38 => 68
  | 39 => 56
  | 40 => 9
  | 41 => 6
  | 42 => 27
  | 43 => 56
  | 44 => 54
  | 45 => 29
  | 46 => 24
  | 47 => 75
  | _ => 0

def fixedLiteralInvMinusRow_31 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 77
  | 1 => 91
  | 2 => 71
  | 3 => 10
  | 4 => 92
  | 5 => 71
  | 6 => 82
  | 7 => 88
  | 8 => 4
  | 9 => 39
  | 10 => 20
  | 11 => 48
  | 12 => 53
  | 13 => 7
  | 14 => 23
  | 15 => 64
  | 16 => 60
  | 17 => 43
  | 18 => 93
  | 19 => 21
  | 20 => 62
  | 21 => 56
  | 22 => 91
  | 23 => 23
  | 24 => 18
  | 25 => 69
  | 26 => 76
  | 27 => 94
  | 28 => 4
  | 29 => 33
  | 30 => 73
  | 31 => 6
  | 32 => 44
  | 33 => 88
  | 34 => 4
  | 35 => 36
  | 36 => 49
  | 37 => 18
  | 38 => 48
  | 39 => 72
  | 40 => 39
  | 41 => 3
  | 42 => 67
  | 43 => 28
  | 44 => 3
  | 45 => 1
  | 46 => 42
  | 47 => 85
  | _ => 0

def fixedLiteralInvMinusRow_32 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 86
  | 1 => 52
  | 2 => 72
  | 3 => 62
  | 4 => 93
  | 5 => 92
  | 6 => 36
  | 7 => 31
  | 8 => 4
  | 9 => 27
  | 10 => 11
  | 11 => 62
  | 12 => 40
  | 13 => 100
  | 14 => 24
  | 15 => 48
  | 16 => 77
  | 17 => 26
  | 18 => 37
  | 19 => 34
  | 20 => 78
  | 21 => 18
  | 22 => 31
  | 23 => 85
  | 24 => 44
  | 25 => 32
  | 26 => 71
  | 27 => 97
  | 28 => 20
  | 29 => 63
  | 30 => 28
  | 31 => 63
  | 32 => 47
  | 33 => 48
  | 34 => 20
  | 35 => 12
  | 36 => 7
  | 37 => 1
  | 38 => 39
  | 39 => 3
  | 40 => 38
  | 41 => 6
  | 42 => 3
  | 43 => 63
  | 44 => 37
  | 45 => 71
  | 46 => 86
  | 47 => 81
  | _ => 0

def fixedLiteralInvMinusRow_33 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 29
  | 1 => 22
  | 2 => 28
  | 3 => 1
  | 4 => 42
  | 5 => 58
  | 6 => 95
  | 7 => 8
  | 8 => 72
  | 9 => 37
  | 10 => 54
  | 11 => 0
  | 12 => 88
  | 13 => 57
  | 14 => 93
  | 15 => 25
  | 16 => 3
  | 17 => 23
  | 18 => 82
  | 19 => 57
  | 20 => 50
  | 21 => 43
  | 22 => 53
  | 23 => 54
  | 24 => 84
  | 25 => 82
  | 26 => 48
  | 27 => 83
  | 28 => 27
  | 29 => 20
  | 30 => 12
  | 31 => 89
  | 32 => 66
  | 33 => 17
  | 34 => 20
  | 35 => 49
  | 36 => 33
  | 37 => 92
  | 38 => 52
  | 39 => 11
  | 40 => 99
  | 41 => 2
  | 42 => 77
  | 43 => 83
  | 44 => 1
  | 45 => 10
  | 46 => 68
  | 47 => 53
  | _ => 0

def fixedLiteralInvMinusRow_34 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 73
  | 1 => 65
  | 2 => 1
  | 3 => 23
  | 4 => 58
  | 5 => 73
  | 6 => 39
  | 7 => 29
  | 8 => 5
  | 9 => 93
  | 10 => 35
  | 11 => 16
  | 12 => 64
  | 13 => 42
  | 14 => 56
  | 15 => 82
  | 16 => 91
  | 17 => 27
  | 18 => 20
  | 19 => 59
  | 20 => 99
  | 21 => 29
  | 22 => 32
  | 23 => 13
  | 24 => 10
  | 25 => 11
  | 26 => 24
  | 27 => 91
  | 28 => 1
  | 29 => 34
  | 30 => 15
  | 31 => 15
  | 32 => 69
  | 33 => 43
  | 34 => 26
  | 35 => 79
  | 36 => 47
  | 37 => 19
  | 38 => 96
  | 39 => 70
  | 40 => 29
  | 41 => 86
  | 42 => 58
  | 43 => 52
  | 44 => 90
  | 45 => 52
  | 46 => 95
  | 47 => 57
  | _ => 0

def fixedLiteralInvMinusRow_35 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 47
  | 1 => 31
  | 2 => 48
  | 3 => 67
  | 4 => 73
  | 5 => 60
  | 6 => 26
  | 7 => 20
  | 8 => 87
  | 9 => 76
  | 10 => 85
  | 11 => 37
  | 12 => 70
  | 13 => 33
  | 14 => 58
  | 15 => 38
  | 16 => 37
  | 17 => 23
  | 18 => 12
  | 19 => 52
  | 20 => 65
  | 21 => 16
  | 22 => 94
  | 23 => 96
  | 24 => 98
  | 25 => 65
  | 26 => 49
  | 27 => 62
  | 28 => 78
  | 29 => 76
  | 30 => 38
  | 31 => 63
  | 32 => 58
  | 33 => 33
  | 34 => 61
  | 35 => 80
  | 36 => 34
  | 37 => 59
  | 38 => 26
  | 39 => 67
  | 40 => 21
  | 41 => 79
  | 42 => 95
  | 43 => 20
  | 44 => 94
  | 45 => 4
  | 46 => 10
  | 47 => 15
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvMinusRow_36 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 62
  | 1 => 41
  | 2 => 56
  | 3 => 54
  | 4 => 3
  | 5 => 34
  | 6 => 24
  | 7 => 11
  | 8 => 7
  | 9 => 67
  | 10 => 92
  | 11 => 24
  | 12 => 6
  | 13 => 98
  | 14 => 89
  | 15 => 79
  | 16 => 23
  | 17 => 44
  | 18 => 8
  | 19 => 67
  | 20 => 74
  | 21 => 5
  | 22 => 38
  | 23 => 3
  | 24 => 50
  | 25 => 16
  | 26 => 1
  | 27 => 29
  | 28 => 66
  | 29 => 66
  | 30 => 72
  | 31 => 100
  | 32 => 54
  | 33 => 84
  | 34 => 91
  | 35 => 15
  | 36 => 85
  | 37 => 53
  | 38 => 52
  | 39 => 75
  | 40 => 0
  | 41 => 62
  | 42 => 11
  | 43 => 15
  | 44 => 73
  | 45 => 6
  | 46 => 64
  | 47 => 85
  | _ => 0

def fixedLiteralInvMinusRow_37 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 48
  | 1 => 57
  | 2 => 50
  | 3 => 18
  | 4 => 20
  | 5 => 24
  | 6 => 32
  | 7 => 70
  | 8 => 64
  | 9 => 30
  | 10 => 97
  | 11 => 55
  | 12 => 69
  | 13 => 68
  | 14 => 5
  | 15 => 26
  | 16 => 78
  | 17 => 73
  | 18 => 31
  | 19 => 45
  | 20 => 73
  | 21 => 13
  | 22 => 79
  | 23 => 7
  | 24 => 89
  | 25 => 81
  | 26 => 68
  | 27 => 5
  | 28 => 14
  | 29 => 92
  | 30 => 90
  | 31 => 22
  | 32 => 59
  | 33 => 89
  | 34 => 52
  | 35 => 9
  | 36 => 70
  | 37 => 12
  | 38 => 29
  | 39 => 92
  | 40 => 46
  | 41 => 4
  | 42 => 2
  | 43 => 74
  | 44 => 53
  | 45 => 20
  | 46 => 39
  | 47 => 76
  | _ => 0

def fixedLiteralInvMinusRow_38 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 71
  | 1 => 92
  | 2 => 48
  | 3 => 10
  | 4 => 52
  | 5 => 91
  | 6 => 83
  | 7 => 20
  | 8 => 54
  | 9 => 44
  | 10 => 10
  | 11 => 40
  | 12 => 97
  | 13 => 96
  | 14 => 83
  | 15 => 13
  | 16 => 94
  | 17 => 71
  | 18 => 75
  | 19 => 51
  | 20 => 14
  | 21 => 66
  | 22 => 59
  | 23 => 99
  | 24 => 1
  | 25 => 61
  | 26 => 78
  | 27 => 7
  | 28 => 43
  | 29 => 85
  | 30 => 40
  | 31 => 38
  | 32 => 93
  | 33 => 83
  | 34 => 3
  | 35 => 79
  | 36 => 74
  | 37 => 77
  | 38 => 89
  | 39 => 25
  | 40 => 29
  | 41 => 19
  | 42 => 10
  | 43 => 100
  | 44 => 88
  | 45 => 25
  | 46 => 86
  | 47 => 99
  | _ => 0

def fixedLiteralInvMinusRow_39 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 66
  | 1 => 8
  | 2 => 100
  | 3 => 37
  | 4 => 30
  | 5 => 17
  | 6 => 17
  | 7 => 17
  | 8 => 48
  | 9 => 15
  | 10 => 36
  | 11 => 40
  | 12 => 93
  | 13 => 9
  | 14 => 41
  | 15 => 42
  | 16 => 26
  | 17 => 42
  | 18 => 76
  | 19 => 52
  | 20 => 91
  | 21 => 35
  | 22 => 38
  | 23 => 56
  | 24 => 21
  | 25 => 83
  | 26 => 83
  | 27 => 17
  | 28 => 42
  | 29 => 63
  | 30 => 30
  | 31 => 13
  | 32 => 14
  | 33 => 98
  | 34 => 31
  | 35 => 97
  | 36 => 74
  | 37 => 42
  | 38 => 2
  | 39 => 94
  | 40 => 92
  | 41 => 28
  | 42 => 95
  | 43 => 11
  | 44 => 100
  | 45 => 75
  | 46 => 36
  | 47 => 86
  | _ => 0

def fixedLiteralInvMinusRow_40 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 75
  | 1 => 5
  | 2 => 66
  | 3 => 63
  | 4 => 9
  | 5 => 43
  | 6 => 95
  | 7 => 4
  | 8 => 93
  | 9 => 5
  | 10 => 62
  | 11 => 98
  | 12 => 54
  | 13 => 4
  | 14 => 14
  | 15 => 36
  | 16 => 13
  | 17 => 89
  | 18 => 10
  | 19 => 20
  | 20 => 35
  | 21 => 15
  | 22 => 19
  | 23 => 62
  | 24 => 71
  | 25 => 100
  | 26 => 22
  | 27 => 71
  | 28 => 67
  | 29 => 96
  | 30 => 27
  | 31 => 5
  | 32 => 69
  | 33 => 66
  | 34 => 99
  | 35 => 75
  | 36 => 67
  | 37 => 88
  | 38 => 99
  | 39 => 77
  | 40 => 21
  | 41 => 4
  | 42 => 26
  | 43 => 33
  | 44 => 6
  | 45 => 69
  | 46 => 73
  | 47 => 92
  | _ => 0

def fixedLiteralInvMinusRow_41 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 65
  | 1 => 23
  | 2 => 6
  | 3 => 16
  | 4 => 5
  | 5 => 51
  | 6 => 39
  | 7 => 40
  | 8 => 71
  | 9 => 17
  | 10 => 73
  | 11 => 24
  | 12 => 91
  | 13 => 66
  | 14 => 62
  | 15 => 33
  | 16 => 96
  | 17 => 91
  | 18 => 31
  | 19 => 80
  | 20 => 58
  | 21 => 100
  | 22 => 33
  | 23 => 58
  | 24 => 88
  | 25 => 28
  | 26 => 69
  | 27 => 65
  | 28 => 87
  | 29 => 51
  | 30 => 80
  | 31 => 71
  | 32 => 27
  | 33 => 52
  | 34 => 38
  | 35 => 9
  | 36 => 23
  | 37 => 71
  | 38 => 22
  | 39 => 18
  | 40 => 67
  | 41 => 37
  | 42 => 88
  | 43 => 67
  | 44 => 40
  | 45 => 95
  | 46 => 64
  | 47 => 9
  | _ => 0

def fixedLiteralInvMinusRow_42 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 8
  | 1 => 51
  | 2 => 99
  | 3 => 44
  | 4 => 62
  | 5 => 87
  | 6 => 24
  | 7 => 65
  | 8 => 58
  | 9 => 62
  | 10 => 65
  | 11 => 64
  | 12 => 27
  | 13 => 3
  | 14 => 85
  | 15 => 77
  | 16 => 83
  | 17 => 35
  | 18 => 75
  | 19 => 46
  | 20 => 80
  | 21 => 34
  | 22 => 59
  | 23 => 82
  | 24 => 47
  | 25 => 54
  | 26 => 4
  | 27 => 73
  | 28 => 67
  | 29 => 31
  | 30 => 35
  | 31 => 22
  | 32 => 95
  | 33 => 85
  | 34 => 52
  | 35 => 33
  | 36 => 66
  | 37 => 35
  | 38 => 99
  | 39 => 98
  | 40 => 84
  | 41 => 39
  | 42 => 45
  | 43 => 58
  | 44 => 53
  | 45 => 37
  | 46 => 12
  | 47 => 55
  | _ => 0

def fixedLiteralInvMinusRow_43 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 17
  | 1 => 85
  | 2 => 36
  | 3 => 70
  | 4 => 77
  | 5 => 50
  | 6 => 37
  | 7 => 97
  | 8 => 87
  | 9 => 29
  | 10 => 69
  | 11 => 59
  | 12 => 25
  | 13 => 19
  | 14 => 28
  | 15 => 35
  | 16 => 27
  | 17 => 97
  | 18 => 22
  | 19 => 50
  | 20 => 8
  | 21 => 59
  | 22 => 48
  | 23 => 83
  | 24 => 62
  | 25 => 61
  | 26 => 34
  | 27 => 75
  | 28 => 52
  | 29 => 71
  | 30 => 44
  | 31 => 77
  | 32 => 18
  | 33 => 48
  | 34 => 6
  | 35 => 16
  | 36 => 4
  | 37 => 58
  | 38 => 90
  | 39 => 57
  | 40 => 29
  | 41 => 71
  | 42 => 43
  | 43 => 42
  | 44 => 96
  | 45 => 22
  | 46 => 60
  | 47 => 77
  | _ => 0

def fixedLiteralInvMinusRow_44 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 90
  | 1 => 34
  | 2 => 43
  | 3 => 15
  | 4 => 23
  | 5 => 23
  | 6 => 64
  | 7 => 80
  | 8 => 4
  | 9 => 94
  | 10 => 18
  | 11 => 78
  | 12 => 51
  | 13 => 77
  | 14 => 76
  | 15 => 70
  | 16 => 32
  | 17 => 59
  | 18 => 84
  | 19 => 15
  | 20 => 69
  | 21 => 46
  | 22 => 26
  | 23 => 25
  | 24 => 20
  | 25 => 60
  | 26 => 14
  | 27 => 61
  | 28 => 76
  | 29 => 46
  | 30 => 85
  | 31 => 14
  | 32 => 58
  | 33 => 4
  | 34 => 71
  | 35 => 30
  | 36 => 1
  | 37 => 66
  | 38 => 86
  | 39 => 9
  | 40 => 13
  | 41 => 14
  | 42 => 57
  | 43 => 30
  | 44 => 2
  | 45 => 41
  | 46 => 79
  | 47 => 13
  | _ => 0

def fixedLiteralInvMinusRow_45 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 3
  | 1 => 17
  | 2 => 37
  | 3 => 63
  | 4 => 23
  | 5 => 59
  | 6 => 63
  | 7 => 90
  | 8 => 88
  | 9 => 72
  | 10 => 28
  | 11 => 77
  | 12 => 19
  | 13 => 7
  | 14 => 27
  | 15 => 58
  | 16 => 59
  | 17 => 88
  | 18 => 62
  | 19 => 22
  | 20 => 85
  | 21 => 77
  | 22 => 90
  | 23 => 83
  | 24 => 1
  | 25 => 23
  | 26 => 8
  | 27 => 34
  | 28 => 0
  | 29 => 80
  | 30 => 8
  | 31 => 91
  | 32 => 69
  | 33 => 25
  | 34 => 71
  | 35 => 89
  | 36 => 42
  | 37 => 52
  | 38 => 39
  | 39 => 58
  | 40 => 7
  | 41 => 43
  | 42 => 6
  | 43 => 49
  | 44 => 49
  | 45 => 66
  | 46 => 100
  | 47 => 60
  | _ => 0

def fixedLiteralInvMinusRow_46 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 8
  | 1 => 76
  | 2 => 73
  | 3 => 65
  | 4 => 7
  | 5 => 4
  | 6 => 47
  | 7 => 72
  | 8 => 38
  | 9 => 99
  | 10 => 52
  | 11 => 52
  | 12 => 41
  | 13 => 69
  | 14 => 44
  | 15 => 38
  | 16 => 53
  | 17 => 84
  | 18 => 52
  | 19 => 39
  | 20 => 29
  | 21 => 56
  | 22 => 97
  | 23 => 35
  | 24 => 62
  | 25 => 63
  | 26 => 32
  | 27 => 51
  | 28 => 51
  | 29 => 34
  | 30 => 25
  | 31 => 4
  | 32 => 44
  | 33 => 3
  | 34 => 58
  | 35 => 10
  | 36 => 43
  | 37 => 23
  | 38 => 99
  | 39 => 44
  | 40 => 72
  | 41 => 42
  | 42 => 15
  | 43 => 37
  | 44 => 36
  | 45 => 2
  | 46 => 28
  | 47 => 84
  | _ => 0

def fixedLiteralInvMinusRow_47 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 49
  | 1 => 22
  | 2 => 14
  | 3 => 12
  | 4 => 24
  | 5 => 51
  | 6 => 74
  | 7 => 80
  | 8 => 16
  | 9 => 86
  | 10 => 8
  | 11 => 29
  | 12 => 8
  | 13 => 50
  | 14 => 59
  | 15 => 3
  | 16 => 12
  | 17 => 37
  | 18 => 97
  | 19 => 46
  | 20 => 18
  | 21 => 52
  | 22 => 88
  | 23 => 14
  | 24 => 21
  | 25 => 91
  | 26 => 13
  | 27 => 10
  | 28 => 48
  | 29 => 100
  | 30 => 65
  | 31 => 1
  | 32 => 89
  | 33 => 100
  | 34 => 94
  | 35 => 52
  | 36 => 52
  | 37 => 58
  | 38 => 96
  | 39 => 23
  | 40 => 36
  | 41 => 26
  | 42 => 49
  | 43 => 96
  | 44 => 31
  | 45 => 21
  | 46 => 91
  | 47 => 15
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModMinusRow_0 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 34
  | 1 => 67
  | 2 => 62
  | 3 => 46
  | 4 => 83
  | 5 => 43
  | 6 => 9
  | 7 => 90
  | 8 => 93
  | 9 => 95
  | 10 => 82
  | 11 => 80
  | 12 => 62
  | 13 => 34
  | 14 => 85
  | 15 => 38
  | 16 => 5
  | 17 => 49
  | 18 => 88
  | 19 => 48
  | 20 => 42
  | 21 => 90
  | 22 => 15
  | 23 => 3
  | 24 => 4
  | 25 => 43
  | 26 => 59
  | 27 => 71
  | 28 => 25
  | 29 => 21
  | 30 => 56
  | 31 => 84
  | 32 => 19
  | 33 => 75
  | 34 => 100
  | 35 => 30
  | 36 => 40
  | 37 => 58
  | 38 => 40
  | 39 => 4
  | 40 => 54
  | 41 => 7
  | 42 => 1
  | 43 => 78
  | 44 => 88
  | 45 => 55
  | 46 => 62
  | 47 => 64
  | _ => 0

def fixedLiteralModMinusRow_1 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 8
  | 1 => 40
  | 2 => 46
  | 3 => 69
  | 4 => 99
  | 5 => 35
  | 6 => 31
  | 7 => 48
  | 8 => 27
  | 9 => 80
  | 10 => 70
  | 11 => 12
  | 12 => 97
  | 13 => 56
  | 14 => 17
  | 15 => 80
  | 16 => 22
  | 17 => 0
  | 18 => 97
  | 19 => 31
  | 20 => 89
  | 21 => 32
  | 22 => 5
  | 23 => 35
  | 24 => 28
  | 25 => 85
  | 26 => 3
  | 27 => 72
  | 28 => 20
  | 29 => 44
  | 30 => 98
  | 31 => 84
  | 32 => 60
  | 33 => 79
  | 34 => 52
  | 35 => 44
  | 36 => 6
  | 37 => 14
  | 38 => 28
  | 39 => 94
  | 40 => 25
  | 41 => 22
  | 42 => 38
  | 43 => 6
  | 44 => 67
  | 45 => 2
  | 46 => 56
  | 47 => 94
  | _ => 0

def fixedLiteralModMinusRow_2 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 30
  | 1 => 54
  | 2 => 73
  | 3 => 49
  | 4 => 74
  | 5 => 21
  | 6 => 66
  | 7 => 7
  | 8 => 74
  | 9 => 84
  | 10 => 41
  | 11 => 29
  | 12 => 29
  | 13 => 64
  | 14 => 49
  | 15 => 11
  | 16 => 46
  | 17 => 27
  | 18 => 44
  | 19 => 3
  | 20 => 19
  | 21 => 46
  | 22 => 8
  | 23 => 56
  | 24 => 76
  | 25 => 8
  | 26 => 47
  | 27 => 55
  | 28 => 12
  | 29 => 44
  | 30 => 100
  | 31 => 16
  | 32 => 57
  | 33 => 1
  | 34 => 86
  | 35 => 18
  | 36 => 96
  | 37 => 62
  | 38 => 44
  | 39 => 73
  | 40 => 28
  | 41 => 31
  | 42 => 85
  | 43 => 59
  | 44 => 54
  | 45 => 50
  | 46 => 90
  | 47 => 44
  | _ => 0

def fixedLiteralModMinusRow_3 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 16
  | 1 => 31
  | 2 => 11
  | 3 => 18
  | 4 => 21
  | 5 => 57
  | 6 => 100
  | 7 => 48
  | 8 => 1
  | 9 => 30
  | 10 => 28
  | 11 => 29
  | 12 => 47
  | 13 => 75
  | 14 => 20
  | 15 => 13
  | 16 => 22
  | 17 => 24
  | 18 => 24
  | 19 => 22
  | 20 => 63
  | 21 => 90
  | 22 => 37
  | 23 => 57
  | 24 => 71
  | 25 => 18
  | 26 => 59
  | 27 => 50
  | 28 => 78
  | 29 => 49
  | 30 => 73
  | 31 => 26
  | 32 => 67
  | 33 => 47
  | 34 => 44
  | 35 => 34
  | 36 => 79
  | 37 => 6
  | 38 => 77
  | 39 => 28
  | 40 => 85
  | 41 => 100
  | 42 => 14
  | 43 => 42
  | 44 => 0
  | 45 => 15
  | 46 => 45
  | 47 => 99
  | _ => 0

def fixedLiteralModMinusRow_4 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 72
  | 1 => 47
  | 2 => 21
  | 3 => 99
  | 4 => 75
  | 5 => 73
  | 6 => 32
  | 7 => 39
  | 8 => 19
  | 9 => 26
  | 10 => 22
  | 11 => 25
  | 12 => 22
  | 13 => 18
  | 14 => 42
  | 15 => 71
  | 16 => 26
  | 17 => 13
  | 18 => 27
  | 19 => 87
  | 20 => 17
  | 21 => 16
  | 22 => 72
  | 23 => 28
  | 24 => 84
  | 25 => 48
  | 26 => 47
  | 27 => 88
  | 28 => 62
  | 29 => 76
  | 30 => 83
  | 31 => 67
  | 32 => 40
  | 33 => 56
  | 34 => 40
  | 35 => 50
  | 36 => 50
  | 37 => 33
  | 38 => 70
  | 39 => 80
  | 40 => 77
  | 41 => 92
  | 42 => 16
  | 43 => 85
  | 44 => 35
  | 45 => 7
  | 46 => 97
  | 47 => 93
  | _ => 0

def fixedLiteralModMinusRow_5 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 74
  | 1 => 94
  | 2 => 60
  | 3 => 81
  | 4 => 71
  | 5 => 58
  | 6 => 99
  | 7 => 26
  | 8 => 78
  | 9 => 49
  | 10 => 72
  | 11 => 19
  | 12 => 9
  | 13 => 25
  | 14 => 65
  | 15 => 15
  | 16 => 42
  | 17 => 51
  | 18 => 16
  | 19 => 56
  | 20 => 44
  | 21 => 35
  | 22 => 83
  | 23 => 36
  | 24 => 53
  | 25 => 62
  | 26 => 57
  | 27 => 45
  | 28 => 36
  | 29 => 59
  | 30 => 58
  | 31 => 49
  | 32 => 75
  | 33 => 26
  | 34 => 30
  | 35 => 75
  | 36 => 14
  | 37 => 49
  | 38 => 57
  | 39 => 57
  | 40 => 58
  | 41 => 74
  | 42 => 23
  | 43 => 54
  | 44 => 99
  | 45 => 51
  | 46 => 31
  | 47 => 91
  | _ => 0

def fixedLiteralModMinusRow_6 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 69
  | 1 => 13
  | 2 => 88
  | 3 => 75
  | 4 => 63
  | 5 => 93
  | 6 => 53
  | 7 => 35
  | 8 => 68
  | 9 => 100
  | 10 => 48
  | 11 => 40
  | 12 => 61
  | 13 => 98
  | 14 => 0
  | 15 => 34
  | 16 => 68
  | 17 => 89
  | 18 => 76
  | 19 => 13
  | 20 => 0
  | 21 => 53
  | 22 => 45
  | 23 => 30
  | 24 => 66
  | 25 => 53
  | 26 => 45
  | 27 => 22
  | 28 => 64
  | 29 => 15
  | 30 => 5
  | 31 => 100
  | 32 => 11
  | 33 => 48
  | 34 => 57
  | 35 => 8
  | 36 => 37
  | 37 => 67
  | 38 => 92
  | 39 => 8
  | 40 => 69
  | 41 => 57
  | 42 => 19
  | 43 => 65
  | 44 => 81
  | 45 => 66
  | 46 => 55
  | 47 => 97
  | _ => 0

def fixedLiteralModMinusRow_7 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 80
  | 1 => 52
  | 2 => 13
  | 3 => 61
  | 4 => 25
  | 5 => 32
  | 6 => 38
  | 7 => 69
  | 8 => 66
  | 9 => 38
  | 10 => 24
  | 11 => 76
  | 12 => 52
  | 13 => 69
  | 14 => 9
  | 15 => 81
  | 16 => 31
  | 17 => 35
  | 18 => 56
  | 19 => 51
  | 20 => 86
  | 21 => 57
  | 22 => 50
  | 23 => 72
  | 24 => 66
  | 25 => 72
  | 26 => 89
  | 27 => 1
  | 28 => 99
  | 29 => 90
  | 30 => 36
  | 31 => 32
  | 32 => 71
  | 33 => 9
  | 34 => 10
  | 35 => 14
  | 36 => 64
  | 37 => 27
  | 38 => 84
  | 39 => 67
  | 40 => 55
  | 41 => 66
  | 42 => 20
  | 43 => 84
  | 44 => 40
  | 45 => 14
  | 46 => 47
  | 47 => 99
  | _ => 0

def fixedLiteralModMinusRow_8 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 50
  | 1 => 30
  | 2 => 81
  | 3 => 40
  | 4 => 52
  | 5 => 19
  | 6 => 10
  | 7 => 63
  | 8 => 33
  | 9 => 44
  | 10 => 68
  | 11 => 49
  | 12 => 2
  | 13 => 62
  | 14 => 98
  | 15 => 17
  | 16 => 11
  | 17 => 20
  | 18 => 74
  | 19 => 95
  | 20 => 60
  | 21 => 93
  | 22 => 61
  | 23 => 55
  | 24 => 74
  | 25 => 26
  | 26 => 81
  | 27 => 7
  | 28 => 6
  | 29 => 22
  | 30 => 45
  | 31 => 86
  | 32 => 46
  | 33 => 74
  | 34 => 18
  | 35 => 61
  | 36 => 42
  | 37 => 41
  | 38 => 89
  | 39 => 83
  | 40 => 40
  | 41 => 6
  | 42 => 67
  | 43 => 69
  | 44 => 7
  | 45 => 3
  | 46 => 0
  | 47 => 52
  | _ => 0

def fixedLiteralModMinusRow_9 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 81
  | 1 => 9
  | 2 => 67
  | 3 => 43
  | 4 => 13
  | 5 => 89
  | 6 => 88
  | 7 => 98
  | 8 => 22
  | 9 => 98
  | 10 => 74
  | 11 => 29
  | 12 => 72
  | 13 => 26
  | 14 => 25
  | 15 => 42
  | 16 => 9
  | 17 => 12
  | 18 => 33
  | 19 => 69
  | 20 => 100
  | 21 => 65
  | 22 => 60
  | 23 => 76
  | 24 => 87
  | 25 => 90
  | 26 => 26
  | 27 => 11
  | 28 => 46
  | 29 => 0
  | 30 => 35
  | 31 => 60
  | 32 => 77
  | 33 => 27
  | 34 => 11
  | 35 => 70
  | 36 => 18
  | 37 => 50
  | 38 => 82
  | 39 => 13
  | 40 => 58
  | 41 => 68
  | 42 => 17
  | 43 => 31
  | 44 => 67
  | 45 => 87
  | 46 => 57
  | 47 => 100
  | _ => 0

def fixedLiteralModMinusRow_10 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 25
  | 1 => 7
  | 2 => 22
  | 3 => 31
  | 4 => 37
  | 5 => 11
  | 6 => 2
  | 7 => 74
  | 8 => 56
  | 9 => 85
  | 10 => 35
  | 11 => 38
  | 12 => 68
  | 13 => 63
  | 14 => 66
  | 15 => 40
  | 16 => 27
  | 17 => 75
  | 18 => 4
  | 19 => 84
  | 20 => 87
  | 21 => 20
  | 22 => 88
  | 23 => 1
  | 24 => 10
  | 25 => 74
  | 26 => 89
  | 27 => 69
  | 28 => 81
  | 29 => 16
  | 30 => 42
  | 31 => 13
  | 32 => 35
  | 33 => 73
  | 34 => 38
  | 35 => 74
  | 36 => 52
  | 37 => 97
  | 38 => 55
  | 39 => 82
  | 40 => 49
  | 41 => 75
  | 42 => 47
  | 43 => 48
  | 44 => 92
  | 45 => 16
  | 46 => 0
  | 47 => 86
  | _ => 0

def fixedLiteralModMinusRow_11 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 65
  | 1 => 23
  | 2 => 45
  | 3 => 98
  | 4 => 74
  | 5 => 50
  | 6 => 6
  | 7 => 38
  | 8 => 65
  | 9 => 29
  | 10 => 69
  | 11 => 76
  | 12 => 0
  | 13 => 83
  | 14 => 17
  | 15 => 97
  | 16 => 99
  | 17 => 10
  | 18 => 12
  | 19 => 67
  | 20 => 91
  | 21 => 31
  | 22 => 52
  | 23 => 96
  | 24 => 46
  | 25 => 45
  | 26 => 72
  | 27 => 98
  | 28 => 28
  | 29 => 79
  | 30 => 90
  | 31 => 74
  | 32 => 89
  | 33 => 78
  | 34 => 86
  | 35 => 40
  | 36 => 93
  | 37 => 37
  | 38 => 31
  | 39 => 39
  | 40 => 31
  | 41 => 87
  | 42 => 24
  | 43 => 2
  | 44 => 89
  | 45 => 97
  | 46 => 8
  | 47 => 12
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModMinusRow_12 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 8
  | 1 => 75
  | 2 => 39
  | 3 => 27
  | 4 => 39
  | 5 => 91
  | 6 => 38
  | 7 => 72
  | 8 => 14
  | 9 => 91
  | 10 => 27
  | 11 => 76
  | 12 => 62
  | 13 => 23
  | 14 => 69
  | 15 => 80
  | 16 => 66
  | 17 => 93
  | 18 => 48
  | 19 => 39
  | 20 => 42
  | 21 => 98
  | 22 => 9
  | 23 => 24
  | 24 => 70
  | 25 => 75
  | 26 => 13
  | 27 => 19
  | 28 => 4
  | 29 => 26
  | 30 => 71
  | 31 => 73
  | 32 => 67
  | 33 => 51
  | 34 => 8
  | 35 => 15
  | 36 => 34
  | 37 => 17
  | 38 => 90
  | 39 => 84
  | 40 => 17
  | 41 => 81
  | 42 => 55
  | 43 => 63
  | 44 => 50
  | 45 => 89
  | 46 => 20
  | 47 => 74
  | _ => 0

def fixedLiteralModMinusRow_13 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 45
  | 1 => 77
  | 2 => 52
  | 3 => 76
  | 4 => 73
  | 5 => 31
  | 6 => 35
  | 7 => 47
  | 8 => 84
  | 9 => 72
  | 10 => 78
  | 11 => 88
  | 12 => 44
  | 13 => 13
  | 14 => 78
  | 15 => 98
  | 16 => 63
  | 17 => 94
  | 18 => 39
  | 19 => 53
  | 20 => 47
  | 21 => 100
  | 22 => 30
  | 23 => 1
  | 24 => 81
  | 25 => 43
  | 26 => 73
  | 27 => 24
  | 28 => 48
  | 29 => 89
  | 30 => 26
  | 31 => 10
  | 32 => 10
  | 33 => 70
  | 34 => 88
  | 35 => 17
  | 36 => 9
  | 37 => 0
  | 38 => 79
  | 39 => 12
  | 40 => 24
  | 41 => 29
  | 42 => 85
  | 43 => 55
  | 44 => 30
  | 45 => 77
  | 46 => 50
  | 47 => 11
  | _ => 0

def fixedLiteralModMinusRow_14 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 37
  | 1 => 94
  | 2 => 61
  | 3 => 17
  | 4 => 16
  | 5 => 81
  | 6 => 96
  | 7 => 67
  | 8 => 83
  | 9 => 34
  | 10 => 47
  | 11 => 20
  | 12 => 4
  | 13 => 64
  | 14 => 13
  | 15 => 99
  | 16 => 97
  | 17 => 27
  | 18 => 93
  | 19 => 42
  | 20 => 5
  | 21 => 25
  | 22 => 20
  | 23 => 89
  | 24 => 72
  | 25 => 43
  | 26 => 16
  | 27 => 19
  | 28 => 98
  | 29 => 11
  | 30 => 44
  | 31 => 38
  | 32 => 32
  | 33 => 10
  | 34 => 75
  | 35 => 21
  | 36 => 20
  | 37 => 72
  | 38 => 84
  | 39 => 28
  | 40 => 60
  | 41 => 70
  | 42 => 92
  | 43 => 49
  | 44 => 72
  | 45 => 58
  | 46 => 85
  | 47 => 97
  | _ => 0

def fixedLiteralModMinusRow_15 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 97
  | 1 => 40
  | 2 => 87
  | 3 => 26
  | 4 => 74
  | 5 => 91
  | 6 => 26
  | 7 => 28
  | 8 => 42
  | 9 => 71
  | 10 => 32
  | 11 => 67
  | 12 => 11
  | 13 => 96
  | 14 => 20
  | 15 => 22
  | 16 => 24
  | 17 => 81
  | 18 => 19
  | 19 => 59
  | 20 => 7
  | 21 => 75
  | 22 => 76
  | 23 => 38
  | 24 => 24
  | 25 => 30
  | 26 => 83
  | 27 => 91
  | 28 => 42
  | 29 => 39
  | 30 => 66
  | 31 => 47
  | 32 => 52
  | 33 => 50
  | 34 => 59
  | 35 => 76
  | 36 => 92
  | 37 => 49
  | 38 => 82
  | 39 => 72
  | 40 => 99
  | 41 => 71
  | 42 => 49
  | 43 => 85
  | 44 => 3
  | 45 => 35
  | 46 => 91
  | 47 => 13
  | _ => 0

def fixedLiteralModMinusRow_16 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 55
  | 1 => 33
  | 2 => 69
  | 3 => 82
  | 4 => 25
  | 5 => 20
  | 6 => 1
  | 7 => 10
  | 8 => 79
  | 9 => 26
  | 10 => 38
  | 11 => 91
  | 12 => 27
  | 13 => 29
  | 14 => 0
  | 15 => 21
  | 16 => 52
  | 17 => 49
  | 18 => 23
  | 19 => 42
  | 20 => 21
  | 21 => 83
  | 22 => 66
  | 23 => 83
  | 24 => 5
  | 25 => 64
  | 26 => 43
  | 27 => 51
  | 28 => 94
  | 29 => 93
  | 30 => 59
  | 31 => 81
  | 32 => 79
  | 33 => 28
  | 34 => 54
  | 35 => 35
  | 36 => 98
  | 37 => 44
  | 38 => 37
  | 39 => 74
  | 40 => 3
  | 41 => 6
  | 42 => 73
  | 43 => 81
  | 44 => 46
  | 45 => 3
  | 46 => 69
  | 47 => 50
  | _ => 0

def fixedLiteralModMinusRow_17 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 3
  | 1 => 49
  | 2 => 96
  | 3 => 3
  | 4 => 21
  | 5 => 33
  | 6 => 26
  | 7 => 26
  | 8 => 33
  | 9 => 61
  | 10 => 28
  | 11 => 54
  | 12 => 79
  | 13 => 71
  | 14 => 52
  | 15 => 84
  | 16 => 54
  | 17 => 39
  | 18 => 93
  | 19 => 13
  | 20 => 77
  | 21 => 67
  | 22 => 51
  | 23 => 54
  | 24 => 68
  | 25 => 74
  | 26 => 24
  | 27 => 91
  | 28 => 63
  | 29 => 67
  | 30 => 71
  | 31 => 2
  | 32 => 52
  | 33 => 67
  | 34 => 30
  | 35 => 94
  | 36 => 19
  | 37 => 91
  | 38 => 85
  | 39 => 66
  | 40 => 9
  | 41 => 80
  | 42 => 82
  | 43 => 89
  | 44 => 38
  | 45 => 80
  | 46 => 35
  | 47 => 6
  | _ => 0

def fixedLiteralModMinusRow_18 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 33
  | 1 => 13
  | 2 => 74
  | 3 => 85
  | 4 => 7
  | 5 => 8
  | 6 => 0
  | 7 => 45
  | 8 => 60
  | 9 => 67
  | 10 => 94
  | 11 => 77
  | 12 => 64
  | 13 => 14
  | 14 => 76
  | 15 => 27
  | 16 => 20
  | 17 => 38
  | 18 => 72
  | 19 => 20
  | 20 => 48
  | 21 => 22
  | 22 => 0
  | 23 => 17
  | 24 => 11
  | 25 => 50
  | 26 => 90
  | 27 => 53
  | 28 => 46
  | 29 => 5
  | 30 => 89
  | 31 => 61
  | 32 => 29
  | 33 => 65
  | 34 => 69
  | 35 => 76
  | 36 => 0
  | 37 => 65
  | 38 => 30
  | 39 => 24
  | 40 => 4
  | 41 => 8
  | 42 => 25
  | 43 => 60
  | 44 => 74
  | 45 => 50
  | 46 => 72
  | 47 => 59
  | _ => 0

def fixedLiteralModMinusRow_19 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 92
  | 1 => 56
  | 2 => 68
  | 3 => 7
  | 4 => 68
  | 5 => 72
  | 6 => 22
  | 7 => 79
  | 8 => 14
  | 9 => 3
  | 10 => 21
  | 11 => 5
  | 12 => 8
  | 13 => 7
  | 14 => 51
  | 15 => 67
  | 16 => 23
  | 17 => 71
  | 18 => 87
  | 19 => 31
  | 20 => 62
  | 21 => 84
  | 22 => 91
  | 23 => 75
  | 24 => 54
  | 25 => 95
  | 26 => 6
  | 27 => 72
  | 28 => 47
  | 29 => 51
  | 30 => 27
  | 31 => 16
  | 32 => 15
  | 33 => 15
  | 34 => 15
  | 35 => 79
  | 36 => 24
  | 37 => 97
  | 38 => 58
  | 39 => 97
  | 40 => 83
  | 41 => 96
  | 42 => 85
  | 43 => 65
  | 44 => 35
  | 45 => 50
  | 46 => 11
  | 47 => 67
  | _ => 0

def fixedLiteralModMinusRow_20 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 23
  | 1 => 73
  | 2 => 81
  | 3 => 44
  | 4 => 88
  | 5 => 43
  | 6 => 34
  | 7 => 83
  | 8 => 21
  | 9 => 61
  | 10 => 10
  | 11 => 96
  | 12 => 28
  | 13 => 9
  | 14 => 68
  | 15 => 87
  | 16 => 48
  | 17 => 26
  | 18 => 33
  | 19 => 13
  | 20 => 59
  | 21 => 96
  | 22 => 36
  | 23 => 51
  | 24 => 66
  | 25 => 69
  | 26 => 22
  | 27 => 39
  | 28 => 29
  | 29 => 45
  | 30 => 2
  | 31 => 0
  | 32 => 17
  | 33 => 69
  | 34 => 28
  | 35 => 98
  | 36 => 67
  | 37 => 73
  | 38 => 2
  | 39 => 85
  | 40 => 18
  | 41 => 29
  | 42 => 61
  | 43 => 71
  | 44 => 4
  | 45 => 99
  | 46 => 37
  | 47 => 10
  | _ => 0

def fixedLiteralModMinusRow_21 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 38
  | 1 => 34
  | 2 => 17
  | 3 => 66
  | 4 => 4
  | 5 => 99
  | 6 => 22
  | 7 => 6
  | 8 => 14
  | 9 => 56
  | 10 => 68
  | 11 => 67
  | 12 => 90
  | 13 => 92
  | 14 => 97
  | 15 => 34
  | 16 => 80
  | 17 => 79
  | 18 => 9
  | 19 => 61
  | 20 => 26
  | 21 => 13
  | 22 => 65
  | 23 => 60
  | 24 => 95
  | 25 => 95
  | 26 => 34
  | 27 => 72
  | 28 => 93
  | 29 => 24
  | 30 => 62
  | 31 => 99
  | 32 => 41
  | 33 => 13
  | 34 => 77
  | 35 => 91
  | 36 => 28
  | 37 => 72
  | 38 => 8
  | 39 => 67
  | 40 => 13
  | 41 => 89
  | 42 => 30
  | 43 => 47
  | 44 => 99
  | 45 => 17
  | 46 => 74
  | 47 => 66
  | _ => 0

def fixedLiteralModMinusRow_22 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 12
  | 1 => 65
  | 2 => 89
  | 3 => 23
  | 4 => 18
  | 5 => 43
  | 6 => 42
  | 7 => 40
  | 8 => 36
  | 9 => 86
  | 10 => 82
  | 11 => 16
  | 12 => 18
  | 13 => 14
  | 14 => 60
  | 15 => 77
  | 16 => 70
  | 17 => 39
  | 18 => 44
  | 19 => 99
  | 20 => 5
  | 21 => 54
  | 22 => 6
  | 23 => 0
  | 24 => 52
  | 25 => 35
  | 26 => 31
  | 27 => 34
  | 28 => 59
  | 29 => 55
  | 30 => 45
  | 31 => 66
  | 32 => 4
  | 33 => 2
  | 34 => 91
  | 35 => 7
  | 36 => 22
  | 37 => 75
  | 38 => 69
  | 39 => 3
  | 40 => 49
  | 41 => 41
  | 42 => 72
  | 43 => 89
  | 44 => 100
  | 45 => 3
  | 46 => 46
  | 47 => 61
  | _ => 0

def fixedLiteralModMinusRow_23 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 36
  | 1 => 94
  | 2 => 69
  | 3 => 64
  | 4 => 33
  | 5 => 93
  | 6 => 35
  | 7 => 65
  | 8 => 31
  | 9 => 93
  | 10 => 58
  | 11 => 25
  | 12 => 16
  | 13 => 50
  | 14 => 67
  | 15 => 73
  | 16 => 25
  | 17 => 0
  | 18 => 30
  | 19 => 60
  | 20 => 21
  | 21 => 36
  | 22 => 23
  | 23 => 4
  | 24 => 64
  | 25 => 74
  | 26 => 2
  | 27 => 44
  | 28 => 91
  | 29 => 62
  | 30 => 28
  | 31 => 41
  | 32 => 80
  | 33 => 71
  | 34 => 78
  | 35 => 79
  | 36 => 96
  | 37 => 88
  | 38 => 38
  | 39 => 75
  | 40 => 0
  | 41 => 23
  | 42 => 3
  | 43 => 12
  | 44 => 87
  | 45 => 0
  | 46 => 23
  | 47 => 69
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModMinusRow_24 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 74
  | 1 => 18
  | 2 => 83
  | 3 => 5
  | 4 => 3
  | 5 => 65
  | 6 => 93
  | 7 => 31
  | 8 => 81
  | 9 => 64
  | 10 => 31
  | 11 => 17
  | 12 => 87
  | 13 => 23
  | 14 => 97
  | 15 => 68
  | 16 => 91
  | 17 => 1
  | 18 => 93
  | 19 => 55
  | 20 => 10
  | 21 => 63
  | 22 => 18
  | 23 => 84
  | 24 => 2
  | 25 => 16
  | 26 => 42
  | 27 => 65
  | 28 => 5
  | 29 => 37
  | 30 => 11
  | 31 => 17
  | 32 => 95
  | 33 => 26
  | 34 => 10
  | 35 => 61
  | 36 => 85
  | 37 => 5
  | 38 => 24
  | 39 => 5
  | 40 => 12
  | 41 => 51
  | 42 => 45
  | 43 => 41
  | 44 => 98
  | 45 => 11
  | 46 => 14
  | 47 => 69
  | _ => 0

def fixedLiteralModMinusRow_25 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 24
  | 1 => 79
  | 2 => 97
  | 3 => 46
  | 4 => 17
  | 5 => 90
  | 6 => 8
  | 7 => 83
  | 8 => 36
  | 9 => 62
  | 10 => 80
  | 11 => 24
  | 12 => 11
  | 13 => 48
  | 14 => 7
  | 15 => 51
  | 16 => 52
  | 17 => 60
  | 18 => 76
  | 19 => 100
  | 20 => 59
  | 21 => 13
  | 22 => 64
  | 23 => 46
  | 24 => 2
  | 25 => 94
  | 26 => 84
  | 27 => 39
  | 28 => 9
  | 29 => 5
  | 30 => 24
  | 31 => 78
  | 32 => 95
  | 33 => 92
  | 34 => 99
  | 35 => 37
  | 36 => 55
  | 37 => 66
  | 38 => 27
  | 39 => 60
  | 40 => 45
  | 41 => 23
  | 42 => 69
  | 43 => 28
  | 44 => 31
  | 45 => 89
  | 46 => 68
  | 47 => 100
  | _ => 0

def fixedLiteralModMinusRow_26 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 87
  | 1 => 38
  | 2 => 79
  | 3 => 42
  | 4 => 66
  | 5 => 39
  | 6 => 58
  | 7 => 14
  | 8 => 48
  | 9 => 95
  | 10 => 30
  | 11 => 2
  | 12 => 95
  | 13 => 80
  | 14 => 73
  | 15 => 54
  | 16 => 51
  | 17 => 9
  | 18 => 56
  | 19 => 30
  | 20 => 86
  | 21 => 54
  | 22 => 26
  | 23 => 52
  | 24 => 64
  | 25 => 11
  | 26 => 81
  | 27 => 0
  | 28 => 84
  | 29 => 4
  | 30 => 21
  | 31 => 0
  | 32 => 16
  | 33 => 51
  | 34 => 33
  | 35 => 17
  | 36 => 52
  | 37 => 37
  | 38 => 65
  | 39 => 61
  | 40 => 90
  | 41 => 31
  | 42 => 35
  | 43 => 52
  | 44 => 92
  | 45 => 19
  | 46 => 16
  | 47 => 47
  | _ => 0

def fixedLiteralModMinusRow_27 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 80
  | 1 => 3
  | 2 => 68
  | 3 => 39
  | 4 => 35
  | 5 => 73
  | 6 => 82
  | 7 => 64
  | 8 => 66
  | 9 => 56
  | 10 => 79
  | 11 => 37
  | 12 => 9
  | 13 => 87
  | 14 => 96
  | 15 => 17
  | 16 => 3
  | 17 => 6
  | 18 => 13
  | 19 => 67
  | 20 => 29
  | 21 => 71
  | 22 => 97
  | 23 => 1
  | 24 => 26
  | 25 => 65
  | 26 => 33
  | 27 => 29
  | 28 => 63
  | 29 => 39
  | 30 => 98
  | 31 => 90
  | 32 => 100
  | 33 => 23
  | 34 => 16
  | 35 => 4
  | 36 => 32
  | 37 => 53
  | 38 => 75
  | 39 => 98
  | 40 => 1
  | 41 => 63
  | 42 => 57
  | 43 => 75
  | 44 => 18
  | 45 => 31
  | 46 => 89
  | 47 => 35
  | _ => 0

def fixedLiteralModMinusRow_28 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 78
  | 1 => 56
  | 2 => 73
  | 3 => 10
  | 4 => 55
  | 5 => 42
  | 6 => 83
  | 7 => 0
  | 8 => 26
  | 9 => 10
  | 10 => 26
  | 11 => 59
  | 12 => 92
  | 13 => 82
  | 14 => 30
  | 15 => 98
  | 16 => 16
  | 17 => 66
  | 18 => 1
  | 19 => 97
  | 20 => 29
  | 21 => 62
  | 22 => 58
  | 23 => 27
  | 24 => 64
  | 25 => 56
  | 26 => 39
  | 27 => 92
  | 28 => 40
  | 29 => 23
  | 30 => 51
  | 31 => 20
  | 32 => 100
  | 33 => 32
  | 34 => 49
  | 35 => 68
  | 36 => 16
  | 37 => 83
  | 38 => 3
  | 39 => 83
  | 40 => 75
  | 41 => 44
  | 42 => 74
  | 43 => 11
  | 44 => 0
  | 45 => 96
  | 46 => 33
  | 47 => 69
  | _ => 0

def fixedLiteralModMinusRow_29 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 10
  | 1 => 44
  | 2 => 11
  | 3 => 43
  | 4 => 55
  | 5 => 20
  | 6 => 28
  | 7 => 85
  | 8 => 52
  | 9 => 37
  | 10 => 11
  | 11 => 68
  | 12 => 63
  | 13 => 61
  | 14 => 39
  | 15 => 85
  | 16 => 35
  | 17 => 61
  | 18 => 50
  | 19 => 31
  | 20 => 53
  | 21 => 92
  | 22 => 6
  | 23 => 68
  | 24 => 38
  | 25 => 37
  | 26 => 23
  | 27 => 43
  | 28 => 77
  | 29 => 47
  | 30 => 77
  | 31 => 32
  | 32 => 28
  | 33 => 87
  | 34 => 78
  | 35 => 27
  | 36 => 30
  | 37 => 41
  | 38 => 49
  | 39 => 26
  | 40 => 13
  | 41 => 58
  | 42 => 92
  | 43 => 68
  | 44 => 86
  | 45 => 38
  | 46 => 50
  | 47 => 31
  | _ => 0

def fixedLiteralModMinusRow_30 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 30
  | 1 => 56
  | 2 => 42
  | 3 => 52
  | 4 => 53
  | 5 => 62
  | 6 => 88
  | 7 => 25
  | 8 => 14
  | 9 => 39
  | 10 => 62
  | 11 => 47
  | 12 => 31
  | 13 => 17
  | 14 => 21
  | 15 => 92
  | 16 => 17
  | 17 => 30
  | 18 => 24
  | 19 => 92
  | 20 => 83
  | 21 => 45
  | 22 => 61
  | 23 => 20
  | 24 => 72
  | 25 => 60
  | 26 => 44
  | 27 => 5
  | 28 => 42
  | 29 => 17
  | 30 => 28
  | 31 => 61
  | 32 => 25
  | 33 => 58
  | 34 => 34
  | 35 => 48
  | 36 => 32
  | 37 => 36
  | 38 => 78
  | 39 => 86
  | 40 => 44
  | 41 => 36
  | 42 => 20
  | 43 => 31
  | 44 => 55
  | 45 => 38
  | 46 => 74
  | 47 => 37
  | _ => 0

def fixedLiteralModMinusRow_31 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 54
  | 1 => 26
  | 2 => 84
  | 3 => 57
  | 4 => 27
  | 5 => 61
  | 6 => 60
  | 7 => 72
  | 8 => 47
  | 9 => 2
  | 10 => 77
  | 11 => 42
  | 12 => 9
  | 13 => 72
  | 14 => 67
  | 15 => 65
  | 16 => 77
  | 17 => 37
  | 18 => 41
  | 19 => 57
  | 20 => 28
  | 21 => 4
  | 22 => 95
  | 23 => 85
  | 24 => 14
  | 25 => 85
  | 26 => 75
  | 27 => 97
  | 28 => 6
  | 29 => 20
  | 30 => 9
  | 31 => 59
  | 32 => 44
  | 33 => 99
  | 34 => 9
  | 35 => 44
  | 36 => 63
  | 37 => 4
  | 38 => 13
  | 39 => 42
  | 40 => 72
  | 41 => 70
  | 42 => 91
  | 43 => 51
  | 44 => 0
  | 45 => 89
  | 46 => 17
  | 47 => 1
  | _ => 0

def fixedLiteralModMinusRow_32 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 13
  | 1 => 21
  | 2 => 64
  | 3 => 64
  | 4 => 99
  | 5 => 97
  | 6 => 0
  | 7 => 49
  | 8 => 76
  | 9 => 17
  | 10 => 84
  | 11 => 81
  | 12 => 57
  | 13 => 52
  | 14 => 6
  | 15 => 8
  | 16 => 92
  | 17 => 74
  | 18 => 41
  | 19 => 63
  | 20 => 18
  | 21 => 77
  | 22 => 51
  | 23 => 16
  | 24 => 60
  | 25 => 8
  | 26 => 15
  | 27 => 68
  | 28 => 64
  | 29 => 22
  | 30 => 58
  | 31 => 41
  | 32 => 89
  | 33 => 20
  | 34 => 46
  | 35 => 73
  | 36 => 62
  | 37 => 26
  | 38 => 99
  | 39 => 29
  | 40 => 29
  | 41 => 11
  | 42 => 10
  | 43 => 78
  | 44 => 87
  | 45 => 11
  | 46 => 34
  | 47 => 51
  | _ => 0

def fixedLiteralModMinusRow_33 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 90
  | 1 => 56
  | 2 => 0
  | 3 => 78
  | 4 => 29
  | 5 => 2
  | 6 => 33
  | 7 => 71
  | 8 => 56
  | 9 => 31
  | 10 => 22
  | 11 => 71
  | 12 => 90
  | 13 => 37
  | 14 => 39
  | 15 => 24
  | 16 => 11
  | 17 => 65
  | 18 => 68
  | 19 => 69
  | 20 => 82
  | 21 => 27
  | 22 => 22
  | 23 => 79
  | 24 => 96
  | 25 => 100
  | 26 => 76
  | 27 => 13
  | 28 => 98
  | 29 => 60
  | 30 => 99
  | 31 => 95
  | 32 => 39
  | 33 => 20
  | 34 => 93
  | 35 => 2
  | 36 => 58
  | 37 => 89
  | 38 => 1
  | 39 => 8
  | 40 => 36
  | 41 => 66
  | 42 => 73
  | 43 => 66
  | 44 => 26
  | 45 => 11
  | 46 => 62
  | 47 => 64
  | _ => 0

def fixedLiteralModMinusRow_34 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 66
  | 1 => 83
  | 2 => 29
  | 3 => 53
  | 4 => 15
  | 5 => 11
  | 6 => 4
  | 7 => 57
  | 8 => 32
  | 9 => 38
  | 10 => 16
  | 11 => 31
  | 12 => 81
  | 13 => 57
  | 14 => 1
  | 15 => 18
  | 16 => 99
  | 17 => 8
  | 18 => 52
  | 19 => 60
  | 20 => 74
  | 21 => 88
  | 22 => 29
  | 23 => 37
  | 24 => 68
  | 25 => 79
  | 26 => 21
  | 27 => 15
  | 28 => 96
  | 29 => 51
  | 30 => 82
  | 31 => 21
  | 32 => 47
  | 33 => 83
  | 34 => 97
  | 35 => 92
  | 36 => 61
  | 37 => 7
  | 38 => 56
  | 39 => 4
  | 40 => 93
  | 41 => 44
  | 42 => 60
  | 43 => 37
  | 44 => 5
  | 45 => 67
  | 46 => 45
  | 47 => 94
  | _ => 0

def fixedLiteralModMinusRow_35 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 2
  | 1 => 73
  | 2 => 29
  | 3 => 69
  | 4 => 4
  | 5 => 91
  | 6 => 47
  | 7 => 53
  | 8 => 65
  | 9 => 93
  | 10 => 56
  | 11 => 64
  | 12 => 91
  | 13 => 59
  | 14 => 3
  | 15 => 33
  | 16 => 1
  | 17 => 74
  | 18 => 98
  | 19 => 85
  | 20 => 17
  | 21 => 33
  | 22 => 24
  | 23 => 33
  | 24 => 75
  | 25 => 87
  | 26 => 56
  | 27 => 97
  | 28 => 8
  | 29 => 41
  | 30 => 39
  | 31 => 58
  | 32 => 76
  | 33 => 95
  | 34 => 14
  | 35 => 34
  | 36 => 1
  | 37 => 16
  | 38 => 31
  | 39 => 63
  | 40 => 51
  | 41 => 55
  | 42 => 15
  | 43 => 21
  | 44 => 14
  | 45 => 34
  | 46 => 10
  | 47 => 44
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModMinusRow_36 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 94
  | 1 => 38
  | 2 => 99
  | 3 => 83
  | 4 => 53
  | 5 => 56
  | 6 => 32
  | 7 => 48
  | 8 => 9
  | 9 => 2
  | 10 => 38
  | 11 => 36
  | 12 => 68
  | 13 => 95
  | 14 => 12
  | 15 => 68
  | 16 => 17
  | 17 => 64
  | 18 => 82
  | 19 => 22
  | 20 => 83
  | 21 => 77
  | 22 => 15
  | 23 => 22
  | 24 => 8
  | 25 => 82
  | 26 => 80
  | 27 => 52
  | 28 => 18
  | 29 => 28
  | 30 => 95
  | 31 => 98
  | 32 => 38
  | 33 => 20
  | 34 => 62
  | 35 => 30
  | 36 => 28
  | 37 => 100
  | 38 => 60
  | 39 => 87
  | 40 => 9
  | 41 => 95
  | 42 => 94
  | 43 => 1
  | 44 => 18
  | 45 => 98
  | 46 => 24
  | 47 => 75
  | _ => 0

def fixedLiteralModMinusRow_37 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 53
  | 2 => 33
  | 3 => 35
  | 4 => 94
  | 5 => 76
  | 6 => 28
  | 7 => 8
  | 8 => 47
  | 9 => 22
  | 10 => 14
  | 11 => 88
  | 12 => 78
  | 13 => 29
  | 14 => 6
  | 15 => 6
  | 16 => 77
  | 17 => 73
  | 18 => 16
  | 19 => 55
  | 20 => 33
  | 21 => 22
  | 22 => 74
  | 23 => 87
  | 24 => 100
  | 25 => 17
  | 26 => 10
  | 27 => 25
  | 28 => 98
  | 29 => 18
  | 30 => 44
  | 31 => 99
  | 32 => 84
  | 33 => 1
  | 34 => 43
  | 35 => 58
  | 36 => 4
  | 37 => 67
  | 38 => 39
  | 39 => 83
  | 40 => 76
  | 41 => 95
  | 42 => 61
  | 43 => 18
  | 44 => 17
  | 45 => 7
  | 46 => 3
  | 47 => 73
  | _ => 0

def fixedLiteralModMinusRow_38 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 34
  | 1 => 26
  | 2 => 13
  | 3 => 32
  | 4 => 93
  | 5 => 73
  | 6 => 76
  | 7 => 50
  | 8 => 38
  | 9 => 86
  | 10 => 65
  | 11 => 98
  | 12 => 82
  | 13 => 31
  | 14 => 61
  | 15 => 16
  | 16 => 21
  | 17 => 4
  | 18 => 58
  | 19 => 4
  | 20 => 3
  | 21 => 24
  | 22 => 9
  | 23 => 35
  | 24 => 74
  | 25 => 15
  | 26 => 98
  | 27 => 51
  | 28 => 25
  | 29 => 76
  | 30 => 69
  | 31 => 47
  | 32 => 1
  | 33 => 54
  | 34 => 96
  | 35 => 80
  | 36 => 8
  | 37 => 92
  | 38 => 47
  | 39 => 91
  | 40 => 53
  | 41 => 54
  | 42 => 17
  | 43 => 92
  | 44 => 84
  | 45 => 6
  | 46 => 20
  | 47 => 55
  | _ => 0

def fixedLiteralModMinusRow_39 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 32
  | 1 => 43
  | 2 => 76
  | 3 => 80
  | 4 => 60
  | 5 => 46
  | 6 => 84
  | 7 => 29
  | 8 => 20
  | 9 => 28
  | 10 => 10
  | 11 => 38
  | 12 => 97
  | 13 => 42
  | 14 => 12
  | 15 => 62
  | 16 => 75
  | 17 => 96
  | 18 => 53
  | 19 => 38
  | 20 => 60
  | 21 => 25
  | 22 => 95
  | 23 => 16
  | 24 => 68
  | 25 => 9
  | 26 => 56
  | 27 => 48
  | 28 => 11
  | 29 => 65
  | 30 => 28
  | 31 => 1
  | 32 => 42
  | 33 => 5
  | 34 => 61
  | 35 => 24
  | 36 => 75
  | 37 => 77
  | 38 => 87
  | 39 => 22
  | 40 => 68
  | 41 => 4
  | 42 => 23
  | 43 => 4
  | 44 => 46
  | 45 => 37
  | 46 => 41
  | 47 => 36
  | _ => 0

def fixedLiteralModMinusRow_40 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 50
  | 1 => 16
  | 2 => 33
  | 3 => 12
  | 4 => 73
  | 5 => 70
  | 6 => 93
  | 7 => 8
  | 8 => 82
  | 9 => 2
  | 10 => 36
  | 11 => 98
  | 12 => 12
  | 13 => 1
  | 14 => 85
  | 15 => 21
  | 16 => 89
  | 17 => 62
  | 18 => 52
  | 19 => 37
  | 20 => 34
  | 21 => 5
  | 22 => 55
  | 23 => 13
  | 24 => 59
  | 25 => 90
  | 26 => 69
  | 27 => 7
  | 28 => 86
  | 29 => 52
  | 30 => 83
  | 31 => 85
  | 32 => 24
  | 33 => 14
  | 34 => 40
  | 35 => 24
  | 36 => 8
  | 37 => 90
  | 38 => 85
  | 39 => 61
  | 40 => 86
  | 41 => 63
  | 42 => 76
  | 43 => 13
  | 44 => 83
  | 45 => 12
  | 46 => 98
  | 47 => 28
  | _ => 0

def fixedLiteralModMinusRow_41 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 11
  | 1 => 22
  | 2 => 70
  | 3 => 80
  | 4 => 77
  | 5 => 25
  | 6 => 79
  | 7 => 36
  | 8 => 36
  | 9 => 74
  | 10 => 99
  | 11 => 76
  | 12 => 52
  | 13 => 84
  | 14 => 10
  | 15 => 81
  | 16 => 96
  | 17 => 26
  | 18 => 36
  | 19 => 10
  | 20 => 72
  | 21 => 11
  | 22 => 58
  | 23 => 81
  | 24 => 35
  | 25 => 16
  | 26 => 22
  | 27 => 27
  | 28 => 46
  | 29 => 8
  | 30 => 24
  | 31 => 86
  | 32 => 55
  | 33 => 69
  | 34 => 8
  | 35 => 43
  | 36 => 56
  | 37 => 49
  | 38 => 56
  | 39 => 62
  | 40 => 95
  | 41 => 10
  | 42 => 91
  | 43 => 40
  | 44 => 22
  | 45 => 6
  | 46 => 65
  | 47 => 9
  | _ => 0

def fixedLiteralModMinusRow_42 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 8
  | 2 => 38
  | 3 => 49
  | 4 => 33
  | 5 => 80
  | 6 => 63
  | 7 => 94
  | 8 => 38
  | 9 => 40
  | 10 => 23
  | 11 => 43
  | 12 => 38
  | 13 => 66
  | 14 => 80
  | 15 => 50
  | 16 => 62
  | 17 => 78
  | 18 => 92
  | 19 => 9
  | 20 => 0
  | 21 => 11
  | 22 => 93
  | 23 => 45
  | 24 => 30
  | 25 => 77
  | 26 => 36
  | 27 => 44
  | 28 => 33
  | 29 => 15
  | 30 => 36
  | 31 => 4
  | 32 => 38
  | 33 => 13
  | 34 => 58
  | 35 => 45
  | 36 => 62
  | 37 => 69
  | 38 => 51
  | 39 => 21
  | 40 => 85
  | 41 => 69
  | 42 => 11
  | 43 => 19
  | 44 => 84
  | 45 => 45
  | 46 => 64
  | 47 => 38
  | _ => 0

def fixedLiteralModMinusRow_43 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 23
  | 1 => 34
  | 2 => 44
  | 3 => 64
  | 4 => 23
  | 5 => 23
  | 6 => 19
  | 7 => 80
  | 8 => 74
  | 9 => 67
  | 10 => 65
  | 11 => 83
  | 12 => 91
  | 13 => 4
  | 14 => 94
  | 15 => 50
  | 16 => 91
  | 17 => 13
  | 18 => 80
  | 19 => 95
  | 20 => 67
  | 21 => 8
  | 22 => 47
  | 23 => 64
  | 24 => 94
  | 25 => 18
  | 26 => 33
  | 27 => 18
  | 28 => 54
  | 29 => 22
  | 30 => 48
  | 31 => 63
  | 32 => 38
  | 33 => 28
  | 34 => 98
  | 35 => 91
  | 36 => 11
  | 37 => 82
  | 38 => 2
  | 39 => 65
  | 40 => 76
  | 41 => 80
  | 42 => 91
  | 43 => 11
  | 44 => 39
  | 45 => 92
  | 46 => 1
  | 47 => 26
  | _ => 0

def fixedLiteralModMinusRow_44 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 36
  | 1 => 96
  | 2 => 57
  | 3 => 76
  | 4 => 61
  | 5 => 81
  | 6 => 68
  | 7 => 22
  | 8 => 72
  | 9 => 14
  | 10 => 20
  | 11 => 12
  | 12 => 42
  | 13 => 18
  | 14 => 37
  | 15 => 86
  | 16 => 20
  | 17 => 97
  | 18 => 60
  | 19 => 41
  | 20 => 84
  | 21 => 55
  | 22 => 23
  | 23 => 75
  | 24 => 26
  | 25 => 80
  | 26 => 87
  | 27 => 0
  | 28 => 56
  | 29 => 54
  | 30 => 59
  | 31 => 54
  | 32 => 25
  | 33 => 77
  | 34 => 91
  | 35 => 70
  | 36 => 78
  | 37 => 33
  | 38 => 46
  | 39 => 24
  | 40 => 89
  | 41 => 99
  | 42 => 17
  | 43 => 92
  | 44 => 2
  | 45 => 82
  | 46 => 97
  | 47 => 26
  | _ => 0

def fixedLiteralModMinusRow_45 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 53
  | 1 => 63
  | 2 => 61
  | 3 => 94
  | 4 => 88
  | 5 => 77
  | 6 => 100
  | 7 => 98
  | 8 => 30
  | 9 => 79
  | 10 => 96
  | 11 => 16
  | 12 => 20
  | 13 => 29
  | 14 => 41
  | 15 => 1
  | 16 => 94
  | 17 => 9
  | 18 => 55
  | 19 => 36
  | 20 => 97
  | 21 => 93
  | 22 => 40
  | 23 => 35
  | 24 => 70
  | 25 => 53
  | 26 => 45
  | 27 => 61
  | 28 => 63
  | 29 => 30
  | 30 => 74
  | 31 => 44
  | 32 => 77
  | 33 => 52
  | 34 => 96
  | 35 => 23
  | 36 => 30
  | 37 => 70
  | 38 => 100
  | 39 => 31
  | 40 => 44
  | 41 => 32
  | 42 => 74
  | 43 => 40
  | 44 => 65
  | 45 => 26
  | 46 => 93
  | 47 => 25
  | _ => 0

def fixedLiteralModMinusRow_46 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 6
  | 1 => 52
  | 2 => 90
  | 3 => 39
  | 4 => 70
  | 5 => 79
  | 6 => 43
  | 7 => 87
  | 8 => 47
  | 9 => 4
  | 10 => 52
  | 11 => 11
  | 12 => 32
  | 13 => 97
  | 14 => 81
  | 15 => 2
  | 16 => 89
  | 17 => 50
  | 18 => 26
  | 19 => 67
  | 20 => 61
  | 21 => 30
  | 22 => 78
  | 23 => 5
  | 24 => 62
  | 25 => 19
  | 26 => 88
  | 27 => 22
  | 28 => 14
  | 29 => 88
  | 30 => 67
  | 31 => 96
  | 32 => 2
  | 33 => 69
  | 34 => 15
  | 35 => 78
  | 36 => 23
  | 37 => 99
  | 38 => 76
  | 39 => 29
  | 40 => 23
  | 41 => 1
  | 42 => 98
  | 43 => 79
  | 44 => 17
  | 45 => 42
  | 46 => 67
  | 47 => 95
  | _ => 0

def fixedLiteralModMinusRow_47 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 11
  | 1 => 38
  | 2 => 60
  | 3 => 41
  | 4 => 35
  | 5 => 14
  | 6 => 72
  | 7 => 53
  | 8 => 46
  | 9 => 72
  | 10 => 22
  | 11 => 88
  | 12 => 71
  | 13 => 91
  | 14 => 100
  | 15 => 38
  | 16 => 83
  | 17 => 51
  | 18 => 52
  | 19 => 21
  | 20 => 6
  | 21 => 75
  | 22 => 4
  | 23 => 46
  | 24 => 46
  | 25 => 84
  | 26 => 5
  | 27 => 81
  | 28 => 36
  | 29 => 29
  | 30 => 88
  | 31 => 11
  | 32 => 58
  | 33 => 9
  | 34 => 2
  | 35 => 12
  | 36 => 34
  | 37 => 40
  | 38 => 1
  | 39 => 32
  | 40 => 53
  | 41 => 69
  | 42 => 67
  | 43 => 52
  | 44 => 61
  | 45 => 40
  | 46 => 7
  | 47 => 63
  | _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

def fixedLiteralModMinus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralModMinusRow_0
  | 1 => fixedLiteralModMinusRow_1
  | 2 => fixedLiteralModMinusRow_2
  | 3 => fixedLiteralModMinusRow_3
  | 4 => fixedLiteralModMinusRow_4
  | 5 => fixedLiteralModMinusRow_5
  | 6 => fixedLiteralModMinusRow_6
  | 7 => fixedLiteralModMinusRow_7
  | 8 => fixedLiteralModMinusRow_8
  | 9 => fixedLiteralModMinusRow_9
  | 10 => fixedLiteralModMinusRow_10
  | 11 => fixedLiteralModMinusRow_11
  | 12 => fixedLiteralModMinusRow_12
  | 13 => fixedLiteralModMinusRow_13
  | 14 => fixedLiteralModMinusRow_14
  | 15 => fixedLiteralModMinusRow_15
  | 16 => fixedLiteralModMinusRow_16
  | 17 => fixedLiteralModMinusRow_17
  | 18 => fixedLiteralModMinusRow_18
  | 19 => fixedLiteralModMinusRow_19
  | 20 => fixedLiteralModMinusRow_20
  | 21 => fixedLiteralModMinusRow_21
  | 22 => fixedLiteralModMinusRow_22
  | 23 => fixedLiteralModMinusRow_23
  | 24 => fixedLiteralModMinusRow_24
  | 25 => fixedLiteralModMinusRow_25
  | 26 => fixedLiteralModMinusRow_26
  | 27 => fixedLiteralModMinusRow_27
  | 28 => fixedLiteralModMinusRow_28
  | 29 => fixedLiteralModMinusRow_29
  | 30 => fixedLiteralModMinusRow_30
  | 31 => fixedLiteralModMinusRow_31
  | 32 => fixedLiteralModMinusRow_32
  | 33 => fixedLiteralModMinusRow_33
  | 34 => fixedLiteralModMinusRow_34
  | 35 => fixedLiteralModMinusRow_35
  | 36 => fixedLiteralModMinusRow_36
  | 37 => fixedLiteralModMinusRow_37
  | 38 => fixedLiteralModMinusRow_38
  | 39 => fixedLiteralModMinusRow_39
  | 40 => fixedLiteralModMinusRow_40
  | 41 => fixedLiteralModMinusRow_41
  | 42 => fixedLiteralModMinusRow_42
  | 43 => fixedLiteralModMinusRow_43
  | 44 => fixedLiteralModMinusRow_44
  | 45 => fixedLiteralModMinusRow_45
  | 46 => fixedLiteralModMinusRow_46
  | 47 => fixedLiteralModMinusRow_47
  | _ => fun _ => 0

def fixedLiteralInvMinus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralInvMinusRow_0
  | 1 => fixedLiteralInvMinusRow_1
  | 2 => fixedLiteralInvMinusRow_2
  | 3 => fixedLiteralInvMinusRow_3
  | 4 => fixedLiteralInvMinusRow_4
  | 5 => fixedLiteralInvMinusRow_5
  | 6 => fixedLiteralInvMinusRow_6
  | 7 => fixedLiteralInvMinusRow_7
  | 8 => fixedLiteralInvMinusRow_8
  | 9 => fixedLiteralInvMinusRow_9
  | 10 => fixedLiteralInvMinusRow_10
  | 11 => fixedLiteralInvMinusRow_11
  | 12 => fixedLiteralInvMinusRow_12
  | 13 => fixedLiteralInvMinusRow_13
  | 14 => fixedLiteralInvMinusRow_14
  | 15 => fixedLiteralInvMinusRow_15
  | 16 => fixedLiteralInvMinusRow_16
  | 17 => fixedLiteralInvMinusRow_17
  | 18 => fixedLiteralInvMinusRow_18
  | 19 => fixedLiteralInvMinusRow_19
  | 20 => fixedLiteralInvMinusRow_20
  | 21 => fixedLiteralInvMinusRow_21
  | 22 => fixedLiteralInvMinusRow_22
  | 23 => fixedLiteralInvMinusRow_23
  | 24 => fixedLiteralInvMinusRow_24
  | 25 => fixedLiteralInvMinusRow_25
  | 26 => fixedLiteralInvMinusRow_26
  | 27 => fixedLiteralInvMinusRow_27
  | 28 => fixedLiteralInvMinusRow_28
  | 29 => fixedLiteralInvMinusRow_29
  | 30 => fixedLiteralInvMinusRow_30
  | 31 => fixedLiteralInvMinusRow_31
  | 32 => fixedLiteralInvMinusRow_32
  | 33 => fixedLiteralInvMinusRow_33
  | 34 => fixedLiteralInvMinusRow_34
  | 35 => fixedLiteralInvMinusRow_35
  | 36 => fixedLiteralInvMinusRow_36
  | 37 => fixedLiteralInvMinusRow_37
  | 38 => fixedLiteralInvMinusRow_38
  | 39 => fixedLiteralInvMinusRow_39
  | 40 => fixedLiteralInvMinusRow_40
  | 41 => fixedLiteralInvMinusRow_41
  | 42 => fixedLiteralInvMinusRow_42
  | 43 => fixedLiteralInvMinusRow_43
  | 44 => fixedLiteralInvMinusRow_44
  | 45 => fixedLiteralInvMinusRow_45
  | 46 => fixedLiteralInvMinusRow_46
  | 47 => fixedLiteralInvMinusRow_47
  | _ => fun _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvPlusRow_0 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 43
  | 1 => 48
  | 2 => 52
  | 3 => 53
  | 4 => 37
  | 5 => 2
  | 6 => 47
  | 7 => 30
  | 8 => 20
  | 9 => 90
  | 10 => 49
  | 11 => 58
  | 12 => 43
  | 13 => 25
  | 14 => 65
  | 15 => 97
  | 16 => 21
  | 17 => 94
  | 18 => 29
  | 19 => 51
  | 20 => 35
  | 21 => 22
  | 22 => 56
  | 23 => 17
  | 24 => 58
  | 25 => 46
  | 26 => 57
  | 27 => 83
  | 28 => 72
  | 29 => 19
  | 30 => 40
  | 31 => 96
  | 32 => 77
  | 33 => 42
  | 34 => 89
  | 35 => 58
  | 36 => 49
  | 37 => 42
  | 38 => 13
  | 39 => 82
  | 40 => 90
  | 41 => 5
  | 42 => 98
  | 43 => 99
  | 44 => 63
  | 45 => 73
  | 46 => 51
  | 47 => 66
  | _ => 0

def fixedLiteralInvPlusRow_1 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 15
  | 1 => 5
  | 2 => 97
  | 3 => 29
  | 4 => 10
  | 5 => 63
  | 6 => 83
  | 7 => 50
  | 8 => 9
  | 9 => 4
  | 10 => 31
  | 11 => 24
  | 12 => 37
  | 13 => 30
  | 14 => 3
  | 15 => 44
  | 16 => 18
  | 17 => 93
  | 18 => 92
  | 19 => 11
  | 20 => 65
  | 21 => 4
  | 22 => 2
  | 23 => 87
  | 24 => 69
  | 25 => 82
  | 26 => 32
  | 27 => 68
  | 28 => 65
  | 29 => 1
  | 30 => 84
  | 31 => 21
  | 32 => 80
  | 33 => 83
  | 34 => 7
  | 35 => 48
  | 36 => 12
  | 37 => 19
  | 38 => 20
  | 39 => 39
  | 40 => 13
  | 41 => 66
  | 42 => 56
  | 43 => 20
  | 44 => 11
  | 45 => 94
  | 46 => 4
  | 47 => 40
  | _ => 0

def fixedLiteralInvPlusRow_2 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 35
  | 1 => 96
  | 2 => 67
  | 3 => 56
  | 4 => 39
  | 5 => 36
  | 6 => 85
  | 7 => 8
  | 8 => 73
  | 9 => 37
  | 10 => 13
  | 11 => 39
  | 12 => 59
  | 13 => 67
  | 14 => 69
  | 15 => 76
  | 16 => 38
  | 17 => 71
  | 18 => 93
  | 19 => 90
  | 20 => 99
  | 21 => 90
  | 22 => 56
  | 23 => 91
  | 24 => 50
  | 25 => 55
  | 26 => 82
  | 27 => 37
  | 28 => 6
  | 29 => 69
  | 30 => 40
  | 31 => 69
  | 32 => 50
  | 33 => 1
  | 34 => 16
  | 35 => 98
  | 36 => 54
  | 37 => 13
  | 38 => 25
  | 39 => 79
  | 40 => 77
  | 41 => 28
  | 42 => 70
  | 43 => 25
  | 44 => 55
  | 45 => 20
  | 46 => 79
  | 47 => 51
  | _ => 0

def fixedLiteralInvPlusRow_3 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 65
  | 1 => 86
  | 2 => 95
  | 3 => 89
  | 4 => 74
  | 5 => 20
  | 6 => 26
  | 7 => 28
  | 8 => 19
  | 9 => 65
  | 10 => 84
  | 11 => 19
  | 12 => 100
  | 13 => 86
  | 14 => 53
  | 15 => 78
  | 16 => 25
  | 17 => 62
  | 18 => 89
  | 19 => 16
  | 20 => 54
  | 21 => 60
  | 22 => 15
  | 23 => 20
  | 24 => 0
  | 25 => 97
  | 26 => 33
  | 27 => 25
  | 28 => 68
  | 29 => 77
  | 30 => 90
  | 31 => 95
  | 32 => 30
  | 33 => 51
  | 34 => 6
  | 35 => 51
  | 36 => 61
  | 37 => 72
  | 38 => 42
  | 39 => 98
  | 40 => 45
  | 41 => 99
  | 42 => 72
  | 43 => 11
  | 44 => 53
  | 45 => 78
  | 46 => 85
  | 47 => 13
  | _ => 0

def fixedLiteralInvPlusRow_4 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 43
  | 1 => 25
  | 2 => 83
  | 3 => 96
  | 4 => 75
  | 5 => 19
  | 6 => 45
  | 7 => 90
  | 8 => 98
  | 9 => 41
  | 10 => 14
  | 11 => 33
  | 12 => 85
  | 13 => 12
  | 14 => 19
  | 15 => 14
  | 16 => 10
  | 17 => 3
  | 18 => 86
  | 19 => 16
  | 20 => 80
  | 21 => 96
  | 22 => 0
  | 23 => 20
  | 24 => 50
  | 25 => 65
  | 26 => 90
  | 27 => 55
  | 28 => 93
  | 29 => 3
  | 30 => 1
  | 31 => 93
  | 32 => 84
  | 33 => 32
  | 34 => 92
  | 35 => 29
  | 36 => 11
  | 37 => 19
  | 38 => 20
  | 39 => 50
  | 40 => 31
  | 41 => 2
  | 42 => 31
  | 43 => 26
  | 44 => 63
  | 45 => 99
  | 46 => 86
  | 47 => 79
  | _ => 0

def fixedLiteralInvPlusRow_5 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 95
  | 1 => 26
  | 2 => 12
  | 3 => 25
  | 4 => 43
  | 5 => 0
  | 6 => 17
  | 7 => 38
  | 8 => 52
  | 9 => 92
  | 10 => 2
  | 11 => 43
  | 12 => 18
  | 13 => 17
  | 14 => 84
  | 15 => 72
  | 16 => 43
  | 17 => 91
  | 18 => 10
  | 19 => 67
  | 20 => 63
  | 21 => 28
  | 22 => 23
  | 23 => 77
  | 24 => 10
  | 25 => 94
  | 26 => 66
  | 27 => 92
  | 28 => 67
  | 29 => 70
  | 30 => 20
  | 31 => 35
  | 32 => 92
  | 33 => 54
  | 34 => 38
  | 35 => 52
  | 36 => 68
  | 37 => 25
  | 38 => 31
  | 39 => 44
  | 40 => 73
  | 41 => 75
  | 42 => 24
  | 43 => 1
  | 44 => 6
  | 45 => 45
  | 46 => 94
  | 47 => 87
  | _ => 0

def fixedLiteralInvPlusRow_6 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 56
  | 1 => 97
  | 2 => 97
  | 3 => 43
  | 4 => 39
  | 5 => 68
  | 6 => 17
  | 7 => 86
  | 8 => 46
  | 9 => 53
  | 10 => 45
  | 11 => 45
  | 12 => 63
  | 13 => 89
  | 14 => 82
  | 15 => 34
  | 16 => 92
  | 17 => 66
  | 18 => 27
  | 19 => 60
  | 20 => 77
  | 21 => 42
  | 22 => 97
  | 23 => 26
  | 24 => 79
  | 25 => 61
  | 26 => 61
  | 27 => 46
  | 28 => 31
  | 29 => 3
  | 30 => 64
  | 31 => 100
  | 32 => 83
  | 33 => 32
  | 34 => 91
  | 35 => 54
  | 36 => 51
  | 37 => 83
  | 38 => 100
  | 39 => 17
  | 40 => 96
  | 41 => 19
  | 42 => 92
  | 43 => 43
  | 44 => 30
  | 45 => 85
  | 46 => 62
  | 47 => 79
  | _ => 0

def fixedLiteralInvPlusRow_7 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 35
  | 1 => 30
  | 2 => 38
  | 3 => 33
  | 4 => 24
  | 5 => 21
  | 6 => 90
  | 7 => 0
  | 8 => 94
  | 9 => 39
  | 10 => 1
  | 11 => 58
  | 12 => 100
  | 13 => 23
  | 14 => 11
  | 15 => 37
  | 16 => 59
  | 17 => 88
  | 18 => 77
  | 19 => 99
  | 20 => 98
  | 21 => 30
  | 22 => 78
  | 23 => 20
  | 24 => 74
  | 25 => 30
  | 26 => 73
  | 27 => 70
  | 28 => 24
  | 29 => 69
  | 30 => 29
  | 31 => 87
  | 32 => 81
  | 33 => 35
  | 34 => 83
  | 35 => 97
  | 36 => 86
  | 37 => 70
  | 38 => 30
  | 39 => 1
  | 40 => 36
  | 41 => 70
  | 42 => 83
  | 43 => 19
  | 44 => 52
  | 45 => 99
  | 46 => 24
  | 47 => 14
  | _ => 0

def fixedLiteralInvPlusRow_8 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 30
  | 1 => 66
  | 2 => 63
  | 3 => 38
  | 4 => 92
  | 5 => 56
  | 6 => 89
  | 7 => 76
  | 8 => 64
  | 9 => 67
  | 10 => 17
  | 11 => 70
  | 12 => 33
  | 13 => 17
  | 14 => 71
  | 15 => 96
  | 16 => 88
  | 17 => 78
  | 18 => 68
  | 19 => 87
  | 20 => 7
  | 21 => 66
  | 22 => 23
  | 23 => 87
  | 24 => 51
  | 25 => 28
  | 26 => 74
  | 27 => 12
  | 28 => 47
  | 29 => 99
  | 30 => 19
  | 31 => 82
  | 32 => 27
  | 33 => 27
  | 34 => 83
  | 35 => 57
  | 36 => 56
  | 37 => 89
  | 38 => 52
  | 39 => 5
  | 40 => 38
  | 41 => 11
  | 42 => 4
  | 43 => 48
  | 44 => 18
  | 45 => 90
  | 46 => 29
  | 47 => 99
  | _ => 0

def fixedLiteralInvPlusRow_9 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 100
  | 1 => 59
  | 2 => 60
  | 3 => 68
  | 4 => 5
  | 5 => 7
  | 6 => 56
  | 7 => 49
  | 8 => 65
  | 9 => 72
  | 10 => 63
  | 11 => 10
  | 12 => 91
  | 13 => 83
  | 14 => 48
  | 15 => 31
  | 16 => 21
  | 17 => 26
  | 18 => 11
  | 19 => 60
  | 20 => 49
  | 21 => 65
  | 22 => 99
  | 23 => 1
  | 24 => 31
  | 25 => 30
  | 26 => 91
  | 27 => 85
  | 28 => 28
  | 29 => 53
  | 30 => 30
  | 31 => 13
  | 32 => 3
  | 33 => 100
  | 34 => 17
  | 35 => 82
  | 36 => 66
  | 37 => 1
  | 38 => 10
  | 39 => 97
  | 40 => 96
  | 41 => 41
  | 42 => 65
  | 43 => 13
  | 44 => 44
  | 45 => 24
  | 46 => 17
  | 47 => 43
  | _ => 0

def fixedLiteralInvPlusRow_10 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 18
  | 1 => 88
  | 2 => 50
  | 3 => 6
  | 4 => 100
  | 5 => 71
  | 6 => 17
  | 7 => 43
  | 8 => 81
  | 9 => 16
  | 10 => 74
  | 11 => 10
  | 12 => 7
  | 13 => 9
  | 14 => 36
  | 15 => 98
  | 16 => 43
  | 17 => 12
  | 18 => 47
  | 19 => 58
  | 20 => 48
  | 21 => 59
  | 22 => 54
  | 23 => 41
  | 24 => 29
  | 25 => 52
  | 26 => 69
  | 27 => 3
  | 28 => 44
  | 29 => 69
  | 30 => 54
  | 31 => 35
  | 32 => 96
  | 33 => 48
  | 34 => 77
  | 35 => 63
  | 36 => 72
  | 37 => 57
  | 38 => 58
  | 39 => 53
  | 40 => 96
  | 41 => 40
  | 42 => 32
  | 43 => 75
  | 44 => 11
  | 45 => 14
  | 46 => 14
  | 47 => 96
  | _ => 0

def fixedLiteralInvPlusRow_11 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 83
  | 1 => 77
  | 2 => 59
  | 3 => 47
  | 4 => 39
  | 5 => 27
  | 6 => 32
  | 7 => 44
  | 8 => 10
  | 9 => 17
  | 10 => 83
  | 11 => 21
  | 12 => 47
  | 13 => 1
  | 14 => 90
  | 15 => 75
  | 16 => 90
  | 17 => 77
  | 18 => 25
  | 19 => 13
  | 20 => 12
  | 21 => 82
  | 22 => 85
  | 23 => 36
  | 24 => 22
  | 25 => 26
  | 26 => 11
  | 27 => 44
  | 28 => 25
  | 29 => 0
  | 30 => 76
  | 31 => 11
  | 32 => 2
  | 33 => 83
  | 34 => 37
  | 35 => 84
  | 36 => 59
  | 37 => 85
  | 38 => 87
  | 39 => 60
  | 40 => 88
  | 41 => 97
  | 42 => 93
  | 43 => 94
  | 44 => 41
  | 45 => 15
  | 46 => 35
  | 47 => 3
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvPlusRow_12 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 17
  | 2 => 75
  | 3 => 99
  | 4 => 52
  | 5 => 25
  | 6 => 60
  | 7 => 24
  | 8 => 16
  | 9 => 59
  | 10 => 91
  | 11 => 85
  | 12 => 58
  | 13 => 3
  | 14 => 59
  | 15 => 35
  | 16 => 19
  | 17 => 1
  | 18 => 66
  | 19 => 46
  | 20 => 40
  | 21 => 62
  | 22 => 31
  | 23 => 45
  | 24 => 2
  | 25 => 80
  | 26 => 61
  | 27 => 73
  | 28 => 94
  | 29 => 78
  | 30 => 51
  | 31 => 6
  | 32 => 15
  | 33 => 100
  | 34 => 82
  | 35 => 96
  | 36 => 21
  | 37 => 40
  | 38 => 64
  | 39 => 32
  | 40 => 80
  | 41 => 83
  | 42 => 65
  | 43 => 57
  | 44 => 29
  | 45 => 89
  | 46 => 15
  | 47 => 53
  | _ => 0

def fixedLiteralInvPlusRow_13 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 57
  | 1 => 85
  | 2 => 14
  | 3 => 99
  | 4 => 29
  | 5 => 23
  | 6 => 52
  | 7 => 84
  | 8 => 26
  | 9 => 24
  | 10 => 6
  | 11 => 61
  | 12 => 46
  | 13 => 10
  | 14 => 39
  | 15 => 57
  | 16 => 92
  | 17 => 28
  | 18 => 62
  | 19 => 44
  | 20 => 43
  | 21 => 82
  | 22 => 75
  | 23 => 40
  | 24 => 84
  | 25 => 42
  | 26 => 35
  | 27 => 16
  | 28 => 58
  | 29 => 64
  | 30 => 60
  | 31 => 62
  | 32 => 79
  | 33 => 66
  | 34 => 32
  | 35 => 30
  | 36 => 34
  | 37 => 10
  | 38 => 56
  | 39 => 13
  | 40 => 41
  | 41 => 0
  | 42 => 72
  | 43 => 48
  | 44 => 72
  | 45 => 79
  | 46 => 13
  | 47 => 87
  | _ => 0

def fixedLiteralInvPlusRow_14 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 86
  | 1 => 15
  | 2 => 86
  | 3 => 97
  | 4 => 24
  | 5 => 25
  | 6 => 42
  | 7 => 19
  | 8 => 64
  | 9 => 44
  | 10 => 16
  | 11 => 84
  | 12 => 95
  | 13 => 27
  | 14 => 89
  | 15 => 99
  | 16 => 23
  | 17 => 59
  | 18 => 15
  | 19 => 46
  | 20 => 99
  | 21 => 35
  | 22 => 37
  | 23 => 17
  | 24 => 59
  | 25 => 51
  | 26 => 66
  | 27 => 26
  | 28 => 21
  | 29 => 93
  | 30 => 65
  | 31 => 57
  | 32 => 3
  | 33 => 32
  | 34 => 46
  | 35 => 47
  | 36 => 36
  | 37 => 22
  | 38 => 18
  | 39 => 100
  | 40 => 19
  | 41 => 4
  | 42 => 30
  | 43 => 54
  | 44 => 23
  | 45 => 68
  | 46 => 39
  | 47 => 97
  | _ => 0

def fixedLiteralInvPlusRow_15 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 75
  | 1 => 26
  | 2 => 41
  | 3 => 89
  | 4 => 51
  | 5 => 20
  | 6 => 92
  | 7 => 87
  | 8 => 67
  | 9 => 32
  | 10 => 44
  | 11 => 75
  | 12 => 60
  | 13 => 78
  | 14 => 72
  | 15 => 84
  | 16 => 22
  | 17 => 64
  | 18 => 75
  | 19 => 85
  | 20 => 58
  | 21 => 47
  | 22 => 79
  | 23 => 18
  | 24 => 21
  | 25 => 21
  | 26 => 31
  | 27 => 6
  | 28 => 8
  | 29 => 91
  | 30 => 93
  | 31 => 38
  | 32 => 19
  | 33 => 6
  | 34 => 77
  | 35 => 73
  | 36 => 69
  | 37 => 8
  | 38 => 83
  | 39 => 36
  | 40 => 64
  | 41 => 70
  | 42 => 7
  | 43 => 26
  | 44 => 100
  | 45 => 60
  | 46 => 78
  | 47 => 87
  | _ => 0

def fixedLiteralInvPlusRow_16 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 80
  | 1 => 48
  | 2 => 0
  | 3 => 5
  | 4 => 50
  | 5 => 8
  | 6 => 38
  | 7 => 89
  | 8 => 75
  | 9 => 31
  | 10 => 68
  | 11 => 54
  | 12 => 9
  | 13 => 87
  | 14 => 44
  | 15 => 37
  | 16 => 85
  | 17 => 33
  | 18 => 68
  | 19 => 57
  | 20 => 16
  | 21 => 25
  | 22 => 84
  | 23 => 13
  | 24 => 65
  | 25 => 53
  | 26 => 5
  | 27 => 55
  | 28 => 92
  | 29 => 37
  | 30 => 47
  | 31 => 35
  | 32 => 96
  | 33 => 81
  | 34 => 9
  | 35 => 15
  | 36 => 4
  | 37 => 2
  | 38 => 79
  | 39 => 6
  | 40 => 20
  | 41 => 80
  | 42 => 73
  | 43 => 26
  | 44 => 65
  | 45 => 73
  | 46 => 36
  | 47 => 23
  | _ => 0

def fixedLiteralInvPlusRow_17 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 14
  | 1 => 96
  | 2 => 54
  | 3 => 51
  | 4 => 7
  | 5 => 49
  | 6 => 27
  | 7 => 45
  | 8 => 7
  | 9 => 43
  | 10 => 55
  | 11 => 99
  | 12 => 22
  | 13 => 66
  | 14 => 38
  | 15 => 69
  | 16 => 93
  | 17 => 6
  | 18 => 46
  | 19 => 62
  | 20 => 9
  | 21 => 75
  | 22 => 72
  | 23 => 10
  | 24 => 92
  | 25 => 51
  | 26 => 13
  | 27 => 100
  | 28 => 73
  | 29 => 25
  | 30 => 44
  | 31 => 26
  | 32 => 53
  | 33 => 50
  | 34 => 33
  | 35 => 82
  | 36 => 60
  | 37 => 37
  | 38 => 11
  | 39 => 39
  | 40 => 54
  | 41 => 73
  | 42 => 38
  | 43 => 99
  | 44 => 54
  | 45 => 17
  | 46 => 22
  | 47 => 55
  | _ => 0

def fixedLiteralInvPlusRow_18 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 11
  | 1 => 0
  | 2 => 53
  | 3 => 26
  | 4 => 50
  | 5 => 53
  | 6 => 94
  | 7 => 96
  | 8 => 64
  | 9 => 12
  | 10 => 11
  | 11 => 41
  | 12 => 3
  | 13 => 55
  | 14 => 18
  | 15 => 71
  | 16 => 21
  | 17 => 16
  | 18 => 57
  | 19 => 22
  | 20 => 15
  | 21 => 85
  | 22 => 87
  | 23 => 98
  | 24 => 66
  | 25 => 84
  | 26 => 69
  | 27 => 54
  | 28 => 47
  | 29 => 54
  | 30 => 43
  | 31 => 53
  | 32 => 82
  | 33 => 86
  | 34 => 70
  | 35 => 4
  | 36 => 30
  | 37 => 26
  | 38 => 84
  | 39 => 22
  | 40 => 10
  | 41 => 45
  | 42 => 5
  | 43 => 44
  | 44 => 60
  | 45 => 84
  | 46 => 49
  | 47 => 68
  | _ => 0

def fixedLiteralInvPlusRow_19 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 33
  | 1 => 88
  | 2 => 81
  | 3 => 3
  | 4 => 53
  | 5 => 77
  | 6 => 48
  | 7 => 70
  | 8 => 14
  | 9 => 78
  | 10 => 51
  | 11 => 20
  | 12 => 5
  | 13 => 60
  | 14 => 14
  | 15 => 44
  | 16 => 72
  | 17 => 84
  | 18 => 38
  | 19 => 85
  | 20 => 8
  | 21 => 29
  | 22 => 55
  | 23 => 18
  | 24 => 69
  | 25 => 82
  | 26 => 54
  | 27 => 56
  | 28 => 93
  | 29 => 16
  | 30 => 36
  | 31 => 88
  | 32 => 70
  | 33 => 85
  | 34 => 83
  | 35 => 2
  | 36 => 33
  | 37 => 46
  | 38 => 27
  | 39 => 54
  | 40 => 30
  | 41 => 63
  | 42 => 30
  | 43 => 60
  | 44 => 24
  | 45 => 15
  | 46 => 3
  | 47 => 98
  | _ => 0

def fixedLiteralInvPlusRow_20 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 95
  | 1 => 72
  | 2 => 96
  | 3 => 9
  | 4 => 7
  | 5 => 20
  | 6 => 46
  | 7 => 58
  | 8 => 17
  | 9 => 28
  | 10 => 60
  | 11 => 31
  | 12 => 16
  | 13 => 23
  | 14 => 47
  | 15 => 61
  | 16 => 55
  | 17 => 49
  | 18 => 70
  | 19 => 63
  | 20 => 94
  | 21 => 79
  | 22 => 34
  | 23 => 33
  | 24 => 15
  | 25 => 100
  | 26 => 75
  | 27 => 9
  | 28 => 65
  | 29 => 47
  | 30 => 88
  | 31 => 24
  | 32 => 62
  | 33 => 92
  | 34 => 93
  | 35 => 97
  | 36 => 30
  | 37 => 56
  | 38 => 63
  | 39 => 84
  | 40 => 77
  | 41 => 63
  | 42 => 86
  | 43 => 66
  | 44 => 61
  | 45 => 53
  | 46 => 80
  | 47 => 2
  | _ => 0

def fixedLiteralInvPlusRow_21 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 0
  | 2 => 23
  | 3 => 0
  | 4 => 58
  | 5 => 13
  | 6 => 38
  | 7 => 96
  | 8 => 56
  | 9 => 33
  | 10 => 31
  | 11 => 32
  | 12 => 37
  | 13 => 82
  | 14 => 56
  | 15 => 0
  | 16 => 34
  | 17 => 7
  | 18 => 67
  | 19 => 90
  | 20 => 22
  | 21 => 31
  | 22 => 34
  | 23 => 92
  | 24 => 19
  | 25 => 93
  | 26 => 32
  | 27 => 59
  | 28 => 70
  | 29 => 20
  | 30 => 67
  | 31 => 55
  | 32 => 66
  | 33 => 97
  | 34 => 65
  | 35 => 10
  | 36 => 67
  | 37 => 58
  | 38 => 21
  | 39 => 44
  | 40 => 12
  | 41 => 97
  | 42 => 5
  | 43 => 90
  | 44 => 4
  | 45 => 82
  | 46 => 44
  | 47 => 24
  | _ => 0

def fixedLiteralInvPlusRow_22 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 23
  | 1 => 38
  | 2 => 80
  | 3 => 98
  | 4 => 60
  | 5 => 94
  | 6 => 99
  | 7 => 81
  | 8 => 38
  | 9 => 62
  | 10 => 7
  | 11 => 31
  | 12 => 11
  | 13 => 45
  | 14 => 41
  | 15 => 9
  | 16 => 12
  | 17 => 81
  | 18 => 14
  | 19 => 61
  | 20 => 56
  | 21 => 94
  | 22 => 34
  | 23 => 5
  | 24 => 41
  | 25 => 55
  | 26 => 10
  | 27 => 0
  | 28 => 82
  | 29 => 98
  | 30 => 66
  | 31 => 80
  | 32 => 67
  | 33 => 32
  | 34 => 46
  | 35 => 87
  | 36 => 40
  | 37 => 63
  | 38 => 36
  | 39 => 83
  | 40 => 19
  | 41 => 3
  | 42 => 4
  | 43 => 28
  | 44 => 81
  | 45 => 28
  | 46 => 27
  | 47 => 99
  | _ => 0

def fixedLiteralInvPlusRow_23 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 72
  | 1 => 19
  | 2 => 32
  | 3 => 17
  | 4 => 83
  | 5 => 43
  | 6 => 60
  | 7 => 34
  | 8 => 40
  | 9 => 47
  | 10 => 91
  | 11 => 98
  | 12 => 68
  | 13 => 14
  | 14 => 18
  | 15 => 80
  | 16 => 44
  | 17 => 68
  | 18 => 80
  | 19 => 44
  | 20 => 57
  | 21 => 27
  | 22 => 46
  | 23 => 45
  | 24 => 45
  | 25 => 20
  | 26 => 45
  | 27 => 34
  | 28 => 11
  | 29 => 2
  | 30 => 8
  | 31 => 99
  | 32 => 72
  | 33 => 19
  | 34 => 54
  | 35 => 8
  | 36 => 1
  | 37 => 11
  | 38 => 17
  | 39 => 83
  | 40 => 28
  | 41 => 38
  | 42 => 41
  | 43 => 11
  | 44 => 49
  | 45 => 88
  | 46 => 23
  | 47 => 15
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvPlusRow_24 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 53
  | 1 => 17
  | 2 => 8
  | 3 => 53
  | 4 => 4
  | 5 => 88
  | 6 => 54
  | 7 => 42
  | 8 => 54
  | 9 => 49
  | 10 => 33
  | 11 => 49
  | 12 => 92
  | 13 => 82
  | 14 => 95
  | 15 => 10
  | 16 => 63
  | 17 => 75
  | 18 => 95
  | 19 => 77
  | 20 => 21
  | 21 => 9
  | 22 => 2
  | 23 => 98
  | 24 => 3
  | 25 => 2
  | 26 => 54
  | 27 => 25
  | 28 => 42
  | 29 => 63
  | 30 => 43
  | 31 => 99
  | 32 => 22
  | 33 => 11
  | 34 => 34
  | 35 => 77
  | 36 => 33
  | 37 => 42
  | 38 => 33
  | 39 => 19
  | 40 => 69
  | 41 => 55
  | 42 => 98
  | 43 => 32
  | 44 => 28
  | 45 => 19
  | 46 => 83
  | 47 => 34
  | _ => 0

def fixedLiteralInvPlusRow_25 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 41
  | 1 => 8
  | 2 => 40
  | 3 => 99
  | 4 => 20
  | 5 => 92
  | 6 => 39
  | 7 => 16
  | 8 => 55
  | 9 => 64
  | 10 => 40
  | 11 => 38
  | 12 => 95
  | 13 => 43
  | 14 => 11
  | 15 => 91
  | 16 => 45
  | 17 => 63
  | 18 => 11
  | 19 => 59
  | 20 => 32
  | 21 => 44
  | 22 => 23
  | 23 => 21
  | 24 => 82
  | 25 => 88
  | 26 => 55
  | 27 => 20
  | 28 => 29
  | 29 => 3
  | 30 => 6
  | 31 => 33
  | 32 => 54
  | 33 => 93
  | 34 => 93
  | 35 => 21
  | 36 => 73
  | 37 => 46
  | 38 => 21
  | 39 => 10
  | 40 => 24
  | 41 => 22
  | 42 => 45
  | 43 => 94
  | 44 => 36
  | 45 => 29
  | 46 => 5
  | 47 => 84
  | _ => 0

def fixedLiteralInvPlusRow_26 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 4
  | 1 => 21
  | 2 => 99
  | 3 => 17
  | 4 => 45
  | 5 => 76
  | 6 => 59
  | 7 => 59
  | 8 => 32
  | 9 => 65
  | 10 => 29
  | 11 => 60
  | 12 => 75
  | 13 => 47
  | 14 => 82
  | 15 => 74
  | 16 => 40
  | 17 => 78
  | 18 => 31
  | 19 => 52
  | 20 => 4
  | 21 => 16
  | 22 => 84
  | 23 => 6
  | 24 => 91
  | 25 => 31
  | 26 => 100
  | 27 => 13
  | 28 => 15
  | 29 => 74
  | 30 => 33
  | 31 => 27
  | 32 => 90
  | 33 => 80
  | 34 => 11
  | 35 => 45
  | 36 => 58
  | 37 => 7
  | 38 => 47
  | 39 => 96
  | 40 => 100
  | 41 => 63
  | 42 => 10
  | 43 => 14
  | 44 => 27
  | 45 => 21
  | 46 => 27
  | 47 => 99
  | _ => 0

def fixedLiteralInvPlusRow_27 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 12
  | 1 => 50
  | 2 => 93
  | 3 => 94
  | 4 => 3
  | 5 => 71
  | 6 => 22
  | 7 => 59
  | 8 => 6
  | 9 => 68
  | 10 => 53
  | 11 => 58
  | 12 => 9
  | 13 => 10
  | 14 => 94
  | 15 => 80
  | 16 => 5
  | 17 => 98
  | 18 => 52
  | 19 => 30
  | 20 => 9
  | 21 => 19
  | 22 => 67
  | 23 => 40
  | 24 => 80
  | 25 => 14
  | 26 => 21
  | 27 => 90
  | 28 => 49
  | 29 => 7
  | 30 => 16
  | 31 => 48
  | 32 => 78
  | 33 => 7
  | 34 => 19
  | 35 => 61
  | 36 => 78
  | 37 => 57
  | 38 => 61
  | 39 => 35
  | 40 => 4
  | 41 => 59
  | 42 => 64
  | 43 => 91
  | 44 => 38
  | 45 => 63
  | 46 => 33
  | 47 => 1
  | _ => 0

def fixedLiteralInvPlusRow_28 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 86
  | 1 => 50
  | 2 => 22
  | 3 => 21
  | 4 => 48
  | 5 => 56
  | 6 => 48
  | 7 => 10
  | 8 => 10
  | 9 => 12
  | 10 => 58
  | 11 => 70
  | 12 => 50
  | 13 => 62
  | 14 => 51
  | 15 => 98
  | 16 => 47
  | 17 => 63
  | 18 => 92
  | 19 => 83
  | 20 => 36
  | 21 => 45
  | 22 => 25
  | 23 => 42
  | 24 => 9
  | 25 => 88
  | 26 => 95
  | 27 => 35
  | 28 => 59
  | 29 => 3
  | 30 => 97
  | 31 => 9
  | 32 => 57
  | 33 => 83
  | 34 => 41
  | 35 => 31
  | 36 => 24
  | 37 => 21
  | 38 => 36
  | 39 => 23
  | 40 => 59
  | 41 => 7
  | 42 => 40
  | 43 => 81
  | 44 => 77
  | 45 => 81
  | 46 => 3
  | 47 => 74
  | _ => 0

def fixedLiteralInvPlusRow_29 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 57
  | 1 => 35
  | 2 => 13
  | 3 => 100
  | 4 => 65
  | 5 => 28
  | 6 => 81
  | 7 => 93
  | 8 => 35
  | 9 => 90
  | 10 => 17
  | 11 => 13
  | 12 => 45
  | 13 => 1
  | 14 => 20
  | 15 => 67
  | 16 => 55
  | 17 => 60
  | 18 => 91
  | 19 => 68
  | 20 => 47
  | 21 => 99
  | 22 => 44
  | 23 => 35
  | 24 => 13
  | 25 => 51
  | 26 => 89
  | 27 => 44
  | 28 => 46
  | 29 => 78
  | 30 => 68
  | 31 => 65
  | 32 => 84
  | 33 => 18
  | 34 => 88
  | 35 => 37
  | 36 => 47
  | 37 => 78
  | 38 => 21
  | 39 => 46
  | 40 => 50
  | 41 => 2
  | 42 => 40
  | 43 => 12
  | 44 => 21
  | 45 => 24
  | 46 => 85
  | 47 => 63
  | _ => 0

def fixedLiteralInvPlusRow_30 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 36
  | 1 => 15
  | 2 => 85
  | 3 => 62
  | 4 => 35
  | 5 => 43
  | 6 => 59
  | 7 => 55
  | 8 => 50
  | 9 => 28
  | 10 => 94
  | 11 => 75
  | 12 => 20
  | 13 => 50
  | 14 => 49
  | 15 => 99
  | 16 => 88
  | 17 => 98
  | 18 => 51
  | 19 => 72
  | 20 => 31
  | 21 => 11
  | 22 => 33
  | 23 => 40
  | 24 => 11
  | 25 => 35
  | 26 => 57
  | 27 => 31
  | 28 => 68
  | 29 => 25
  | 30 => 83
  | 31 => 68
  | 32 => 70
  | 33 => 93
  | 34 => 36
  | 35 => 48
  | 36 => 52
  | 37 => 58
  | 38 => 75
  | 39 => 88
  | 40 => 96
  | 41 => 87
  | 42 => 11
  | 43 => 0
  | 44 => 8
  | 45 => 10
  | 46 => 76
  | 47 => 15
  | _ => 0

def fixedLiteralInvPlusRow_31 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 77
  | 1 => 38
  | 2 => 43
  | 3 => 98
  | 4 => 85
  | 5 => 96
  | 6 => 16
  | 7 => 91
  | 8 => 27
  | 9 => 8
  | 10 => 74
  | 11 => 55
  | 12 => 51
  | 13 => 4
  | 14 => 12
  | 15 => 29
  | 16 => 68
  | 17 => 16
  | 18 => 34
  | 19 => 96
  | 20 => 46
  | 21 => 49
  | 22 => 87
  | 23 => 47
  | 24 => 49
  | 25 => 2
  | 26 => 5
  | 27 => 13
  | 28 => 99
  | 29 => 31
  | 30 => 9
  | 31 => 25
  | 32 => 13
  | 33 => 31
  | 34 => 87
  | 35 => 46
  | 36 => 68
  | 37 => 2
  | 38 => 28
  | 39 => 97
  | 40 => 72
  | 41 => 94
  | 42 => 71
  | 43 => 92
  | 44 => 85
  | 45 => 14
  | 46 => 27
  | 47 => 16
  | _ => 0

def fixedLiteralInvPlusRow_32 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 18
  | 1 => 40
  | 2 => 70
  | 3 => 71
  | 4 => 0
  | 5 => 44
  | 6 => 44
  | 7 => 17
  | 8 => 98
  | 9 => 99
  | 10 => 20
  | 11 => 59
  | 12 => 8
  | 13 => 83
  | 14 => 80
  | 15 => 26
  | 16 => 80
  | 17 => 31
  | 18 => 100
  | 19 => 73
  | 20 => 32
  | 21 => 63
  | 22 => 94
  | 23 => 3
  | 24 => 41
  | 25 => 0
  | 26 => 37
  | 27 => 2
  | 28 => 31
  | 29 => 63
  | 30 => 16
  | 31 => 33
  | 32 => 47
  | 33 => 16
  | 34 => 65
  | 35 => 65
  | 36 => 76
  | 37 => 13
  | 38 => 37
  | 39 => 56
  | 40 => 20
  | 41 => 2
  | 42 => 76
  | 43 => 70
  | 44 => 47
  | 45 => 6
  | 46 => 68
  | 47 => 95
  | _ => 0

def fixedLiteralInvPlusRow_33 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 44
  | 1 => 0
  | 2 => 1
  | 3 => 59
  | 4 => 92
  | 5 => 73
  | 6 => 57
  | 7 => 88
  | 8 => 13
  | 9 => 77
  | 10 => 84
  | 11 => 40
  | 12 => 15
  | 13 => 14
  | 14 => 48
  | 15 => 59
  | 16 => 55
  | 17 => 57
  | 18 => 29
  | 19 => 26
  | 20 => 59
  | 21 => 32
  | 22 => 71
  | 23 => 23
  | 24 => 64
  | 25 => 4
  | 26 => 7
  | 27 => 89
  | 28 => 6
  | 29 => 1
  | 30 => 52
  | 31 => 13
  | 32 => 26
  | 33 => 45
  | 34 => 81
  | 35 => 75
  | 36 => 58
  | 37 => 35
  | 38 => 59
  | 39 => 78
  | 40 => 47
  | 41 => 55
  | 42 => 66
  | 43 => 25
  | 44 => 59
  | 45 => 78
  | 46 => 16
  | 47 => 27
  | _ => 0

def fixedLiteralInvPlusRow_34 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 6
  | 1 => 41
  | 2 => 52
  | 3 => 46
  | 4 => 70
  | 5 => 74
  | 6 => 22
  | 7 => 36
  | 8 => 71
  | 9 => 31
  | 10 => 96
  | 11 => 73
  | 12 => 82
  | 13 => 32
  | 14 => 14
  | 15 => 72
  | 16 => 50
  | 17 => 7
  | 18 => 27
  | 19 => 25
  | 20 => 35
  | 21 => 70
  | 22 => 63
  | 23 => 48
  | 24 => 58
  | 25 => 68
  | 26 => 47
  | 27 => 64
  | 28 => 94
  | 29 => 65
  | 30 => 61
  | 31 => 33
  | 32 => 74
  | 33 => 71
  | 34 => 9
  | 35 => 76
  | 36 => 21
  | 37 => 55
  | 38 => 16
  | 39 => 45
  | 40 => 45
  | 41 => 86
  | 42 => 98
  | 43 => 55
  | 44 => 63
  | 45 => 41
  | 46 => 23
  | 47 => 57
  | _ => 0

def fixedLiteralInvPlusRow_35 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 97
  | 1 => 57
  | 2 => 78
  | 3 => 29
  | 4 => 7
  | 5 => 39
  | 6 => 35
  | 7 => 59
  | 8 => 64
  | 9 => 5
  | 10 => 80
  | 11 => 95
  | 12 => 30
  | 13 => 32
  | 14 => 46
  | 15 => 46
  | 16 => 36
  | 17 => 21
  | 18 => 58
  | 19 => 13
  | 20 => 71
  | 21 => 72
  | 22 => 13
  | 23 => 97
  | 24 => 95
  | 25 => 38
  | 26 => 96
  | 27 => 53
  | 28 => 96
  | 29 => 16
  | 30 => 82
  | 31 => 4
  | 32 => 63
  | 33 => 9
  | 34 => 25
  | 35 => 47
  | 36 => 67
  | 37 => 4
  | 38 => 73
  | 39 => 90
  | 40 => 21
  | 41 => 27
  | 42 => 75
  | 43 => 66
  | 44 => 90
  | 45 => 11
  | 46 => 14
  | 47 => 16
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvPlusRow_36 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 20
  | 1 => 99
  | 2 => 31
  | 3 => 87
  | 4 => 59
  | 5 => 80
  | 6 => 94
  | 7 => 11
  | 8 => 43
  | 9 => 71
  | 10 => 76
  | 11 => 4
  | 12 => 30
  | 13 => 96
  | 14 => 4
  | 15 => 1
  | 16 => 47
  | 17 => 80
  | 18 => 71
  | 19 => 67
  | 20 => 46
  | 21 => 55
  | 22 => 61
  | 23 => 88
  | 24 => 62
  | 25 => 11
  | 26 => 50
  | 27 => 90
  | 28 => 9
  | 29 => 73
  | 30 => 45
  | 31 => 57
  | 32 => 87
  | 33 => 11
  | 34 => 96
  | 35 => 38
  | 36 => 39
  | 37 => 56
  | 38 => 93
  | 39 => 78
  | 40 => 6
  | 41 => 24
  | 42 => 79
  | 43 => 91
  | 44 => 88
  | 45 => 32
  | 46 => 6
  | 47 => 95
  | _ => 0

def fixedLiteralInvPlusRow_37 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 83
  | 1 => 45
  | 2 => 71
  | 3 => 100
  | 4 => 24
  | 5 => 92
  | 6 => 32
  | 7 => 76
  | 8 => 38
  | 9 => 85
  | 10 => 15
  | 11 => 89
  | 12 => 50
  | 13 => 89
  | 14 => 77
  | 15 => 83
  | 16 => 17
  | 17 => 58
  | 18 => 64
  | 19 => 2
  | 20 => 5
  | 21 => 29
  | 22 => 52
  | 23 => 93
  | 24 => 21
  | 25 => 67
  | 26 => 25
  | 27 => 88
  | 28 => 4
  | 29 => 73
  | 30 => 0
  | 31 => 5
  | 32 => 42
  | 33 => 66
  | 34 => 83
  | 35 => 2
  | 36 => 70
  | 37 => 86
  | 38 => 8
  | 39 => 100
  | 40 => 75
  | 41 => 78
  | 42 => 61
  | 43 => 41
  | 44 => 56
  | 45 => 75
  | 46 => 28
  | 47 => 77
  | _ => 0

def fixedLiteralInvPlusRow_38 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 55
  | 1 => 53
  | 2 => 43
  | 3 => 8
  | 4 => 85
  | 5 => 24
  | 6 => 91
  | 7 => 16
  | 8 => 93
  | 9 => 33
  | 10 => 42
  | 11 => 54
  | 12 => 18
  | 13 => 18
  | 14 => 49
  | 15 => 31
  | 16 => 80
  | 17 => 48
  | 18 => 8
  | 19 => 51
  | 20 => 63
  | 21 => 73
  | 22 => 43
  | 23 => 19
  | 24 => 4
  | 25 => 15
  | 26 => 55
  | 27 => 85
  | 28 => 66
  | 29 => 89
  | 30 => 77
  | 31 => 55
  | 32 => 82
  | 33 => 83
  | 34 => 29
  | 35 => 26
  | 36 => 39
  | 37 => 22
  | 38 => 76
  | 39 => 27
  | 40 => 52
  | 41 => 22
  | 42 => 95
  | 43 => 39
  | 44 => 48
  | 45 => 42
  | 46 => 21
  | 47 => 85
  | _ => 0

def fixedLiteralInvPlusRow_39 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 51
  | 1 => 42
  | 2 => 55
  | 3 => 98
  | 4 => 88
  | 5 => 53
  | 6 => 56
  | 7 => 15
  | 8 => 80
  | 9 => 65
  | 10 => 14
  | 11 => 14
  | 12 => 72
  | 13 => 87
  | 14 => 20
  | 15 => 8
  | 16 => 42
  | 17 => 84
  | 18 => 24
  | 19 => 74
  | 20 => 75
  | 21 => 74
  | 22 => 38
  | 23 => 89
  | 24 => 21
  | 25 => 72
  | 26 => 85
  | 27 => 91
  | 28 => 86
  | 29 => 22
  | 30 => 86
  | 31 => 10
  | 32 => 30
  | 33 => 35
  | 34 => 78
  | 35 => 63
  | 36 => 68
  | 37 => 68
  | 38 => 61
  | 39 => 55
  | 40 => 7
  | 41 => 33
  | 42 => 89
  | 43 => 45
  | 44 => 80
  | 45 => 70
  | 46 => 57
  | 47 => 36
  | _ => 0

def fixedLiteralInvPlusRow_40 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 13
  | 1 => 90
  | 2 => 59
  | 3 => 43
  | 4 => 88
  | 5 => 91
  | 6 => 21
  | 7 => 67
  | 8 => 98
  | 9 => 38
  | 10 => 50
  | 11 => 65
  | 12 => 88
  | 13 => 18
  | 14 => 100
  | 15 => 74
  | 16 => 95
  | 17 => 99
  | 18 => 74
  | 19 => 43
  | 20 => 90
  | 21 => 64
  | 22 => 0
  | 23 => 2
  | 24 => 34
  | 25 => 76
  | 26 => 64
  | 27 => 83
  | 28 => 43
  | 29 => 83
  | 30 => 47
  | 31 => 21
  | 32 => 83
  | 33 => 24
  | 34 => 46
  | 35 => 38
  | 36 => 99
  | 37 => 71
  | 38 => 46
  | 39 => 11
  | 40 => 9
  | 41 => 47
  | 42 => 34
  | 43 => 93
  | 44 => 49
  | 45 => 64
  | 46 => 74
  | 47 => 15
  | _ => 0

def fixedLiteralInvPlusRow_41 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 17
  | 1 => 0
  | 2 => 100
  | 3 => 76
  | 4 => 66
  | 5 => 89
  | 6 => 66
  | 7 => 41
  | 8 => 13
  | 9 => 38
  | 10 => 42
  | 11 => 6
  | 12 => 5
  | 13 => 81
  | 14 => 54
  | 15 => 64
  | 16 => 89
  | 17 => 56
  | 18 => 40
  | 19 => 56
  | 20 => 72
  | 21 => 20
  | 22 => 80
  | 23 => 11
  | 24 => 79
  | 25 => 41
  | 26 => 58
  | 27 => 66
  | 28 => 99
  | 29 => 2
  | 30 => 54
  | 31 => 36
  | 32 => 65
  | 33 => 81
  | 34 => 77
  | 35 => 33
  | 36 => 90
  | 37 => 31
  | 38 => 77
  | 39 => 16
  | 40 => 56
  | 41 => 65
  | 42 => 61
  | 43 => 50
  | 44 => 18
  | 45 => 92
  | 46 => 85
  | 47 => 38
  | _ => 0

def fixedLiteralInvPlusRow_42 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 44
  | 1 => 81
  | 2 => 56
  | 3 => 17
  | 4 => 63
  | 5 => 57
  | 6 => 83
  | 7 => 30
  | 8 => 72
  | 9 => 30
  | 10 => 56
  | 11 => 47
  | 12 => 59
  | 13 => 61
  | 14 => 43
  | 15 => 66
  | 16 => 24
  | 17 => 68
  | 18 => 57
  | 19 => 5
  | 20 => 68
  | 21 => 0
  | 22 => 26
  | 23 => 99
  | 24 => 23
  | 25 => 51
  | 26 => 7
  | 27 => 67
  | 28 => 47
  | 29 => 92
  | 30 => 18
  | 31 => 21
  | 32 => 19
  | 33 => 57
  | 34 => 84
  | 35 => 20
  | 36 => 7
  | 37 => 84
  | 38 => 39
  | 39 => 64
  | 40 => 31
  | 41 => 38
  | 42 => 38
  | 43 => 78
  | 44 => 73
  | 45 => 97
  | 46 => 25
  | 47 => 36
  | _ => 0

def fixedLiteralInvPlusRow_43 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 43
  | 1 => 73
  | 2 => 4
  | 3 => 100
  | 4 => 64
  | 5 => 73
  | 6 => 55
  | 7 => 57
  | 8 => 51
  | 9 => 74
  | 10 => 54
  | 11 => 56
  | 12 => 75
  | 13 => 23
  | 14 => 58
  | 15 => 84
  | 16 => 36
  | 17 => 79
  | 18 => 14
  | 19 => 18
  | 20 => 86
  | 21 => 81
  | 22 => 49
  | 23 => 26
  | 24 => 72
  | 25 => 82
  | 26 => 70
  | 27 => 70
  | 28 => 61
  | 29 => 90
  | 30 => 83
  | 31 => 10
  | 32 => 25
  | 33 => 11
  | 34 => 39
  | 35 => 43
  | 36 => 8
  | 37 => 78
  | 38 => 92
  | 39 => 96
  | 40 => 95
  | 41 => 63
  | 42 => 83
  | 43 => 97
  | 44 => 36
  | 45 => 58
  | 46 => 2
  | 47 => 28
  | _ => 0

def fixedLiteralInvPlusRow_44 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 6
  | 1 => 16
  | 2 => 21
  | 3 => 90
  | 4 => 9
  | 5 => 5
  | 6 => 0
  | 7 => 50
  | 8 => 91
  | 9 => 6
  | 10 => 61
  | 11 => 93
  | 12 => 85
  | 13 => 9
  | 14 => 6
  | 15 => 18
  | 16 => 51
  | 17 => 87
  | 18 => 9
  | 19 => 80
  | 20 => 85
  | 21 => 30
  | 22 => 15
  | 23 => 49
  | 24 => 51
  | 25 => 1
  | 26 => 4
  | 27 => 65
  | 28 => 74
  | 29 => 60
  | 30 => 1
  | 31 => 76
  | 32 => 45
  | 33 => 37
  | 34 => 28
  | 35 => 48
  | 36 => 38
  | 37 => 79
  | 38 => 39
  | 39 => 79
  | 40 => 41
  | 41 => 98
  | 42 => 51
  | 43 => 52
  | 44 => 61
  | 45 => 49
  | 46 => 50
  | 47 => 44
  | _ => 0

def fixedLiteralInvPlusRow_45 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 79
  | 1 => 52
  | 2 => 10
  | 3 => 73
  | 4 => 74
  | 5 => 84
  | 6 => 68
  | 7 => 10
  | 8 => 61
  | 9 => 85
  | 10 => 35
  | 11 => 54
  | 12 => 44
  | 13 => 46
  | 14 => 99
  | 15 => 78
  | 16 => 33
  | 17 => 11
  | 18 => 19
  | 19 => 77
  | 20 => 1
  | 21 => 97
  | 22 => 64
  | 23 => 77
  | 24 => 49
  | 25 => 92
  | 26 => 20
  | 27 => 39
  | 28 => 12
  | 29 => 11
  | 30 => 51
  | 31 => 52
  | 32 => 92
  | 33 => 68
  | 34 => 76
  | 35 => 67
  | 36 => 8
  | 37 => 80
  | 38 => 54
  | 39 => 5
  | 40 => 17
  | 41 => 24
  | 42 => 98
  | 43 => 39
  | 44 => 21
  | 45 => 52
  | 46 => 23
  | 47 => 76
  | _ => 0

def fixedLiteralInvPlusRow_46 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 9
  | 1 => 22
  | 2 => 42
  | 3 => 77
  | 4 => 7
  | 5 => 74
  | 6 => 56
  | 7 => 72
  | 8 => 85
  | 9 => 18
  | 10 => 86
  | 11 => 74
  | 12 => 34
  | 13 => 99
  | 14 => 73
  | 15 => 0
  | 16 => 51
  | 17 => 40
  | 18 => 51
  | 19 => 76
  | 20 => 75
  | 21 => 73
  | 22 => 55
  | 23 => 71
  | 24 => 81
  | 25 => 93
  | 26 => 81
  | 27 => 70
  | 28 => 68
  | 29 => 91
  | 30 => 32
  | 31 => 27
  | 32 => 71
  | 33 => 98
  | 34 => 46
  | 35 => 2
  | 36 => 14
  | 37 => 76
  | 38 => 83
  | 39 => 22
  | 40 => 96
  | 41 => 96
  | 42 => 8
  | 43 => 87
  | 44 => 51
  | 45 => 38
  | 46 => 51
  | 47 => 56
  | _ => 0

def fixedLiteralInvPlusRow_47 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 68
  | 1 => 10
  | 2 => 43
  | 3 => 45
  | 4 => 39
  | 5 => 69
  | 6 => 92
  | 7 => 53
  | 8 => 78
  | 9 => 83
  | 10 => 82
  | 11 => 50
  | 12 => 69
  | 13 => 49
  | 14 => 67
  | 15 => 65
  | 16 => 22
  | 17 => 32
  | 18 => 42
  | 19 => 42
  | 20 => 60
  | 21 => 51
  | 22 => 22
  | 23 => 42
  | 24 => 17
  | 25 => 7
  | 26 => 73
  | 27 => 8
  | 28 => 26
  | 29 => 37
  | 30 => 12
  | 31 => 30
  | 32 => 49
  | 33 => 13
  | 34 => 56
  | 35 => 9
  | 36 => 72
  | 37 => 4
  | 38 => 96
  | 39 => 43
  | 40 => 64
  | 41 => 3
  | 42 => 85
  | 43 => 36
  | 44 => 15
  | 45 => 90
  | 46 => 66
  | 47 => 19
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModPlusRow_0 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 33
  | 1 => 94
  | 2 => 24
  | 3 => 37
  | 4 => 26
  | 5 => 98
  | 6 => 97
  | 7 => 45
  | 8 => 72
  | 9 => 76
  | 10 => 10
  | 11 => 96
  | 12 => 43
  | 13 => 71
  | 14 => 92
  | 15 => 91
  | 16 => 28
  | 17 => 36
  | 18 => 63
  | 19 => 81
  | 20 => 70
  | 21 => 84
  | 22 => 26
  | 23 => 93
  | 24 => 49
  | 25 => 50
  | 26 => 31
  | 27 => 28
  | 28 => 46
  | 29 => 66
  | 30 => 6
  | 31 => 44
  | 32 => 32
  | 33 => 32
  | 34 => 6
  | 35 => 98
  | 36 => 39
  | 37 => 27
  | 38 => 45
  | 39 => 34
  | 40 => 79
  | 41 => 31
  | 42 => 40
  | 43 => 96
  | 44 => 64
  | 45 => 60
  | 46 => 83
  | 47 => 45
  | _ => 0

def fixedLiteralModPlusRow_1 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 92
  | 1 => 88
  | 2 => 17
  | 3 => 23
  | 4 => 46
  | 5 => 20
  | 6 => 57
  | 7 => 8
  | 8 => 53
  | 9 => 2
  | 10 => 60
  | 11 => 4
  | 12 => 86
  | 13 => 82
  | 14 => 91
  | 15 => 74
  | 16 => 1
  | 17 => 88
  | 18 => 80
  | 19 => 2
  | 20 => 40
  | 21 => 63
  | 22 => 6
  | 23 => 55
  | 24 => 17
  | 25 => 23
  | 26 => 70
  | 27 => 87
  | 28 => 1
  | 29 => 1
  | 30 => 54
  | 31 => 78
  | 32 => 54
  | 33 => 80
  | 34 => 56
  | 35 => 24
  | 36 => 94
  | 37 => 56
  | 38 => 78
  | 39 => 37
  | 40 => 0
  | 41 => 2
  | 42 => 1
  | 43 => 12
  | 44 => 10
  | 45 => 3
  | 46 => 66
  | 47 => 89
  | _ => 0

def fixedLiteralModPlusRow_2 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 54
  | 1 => 95
  | 2 => 100
  | 3 => 6
  | 4 => 75
  | 5 => 65
  | 6 => 61
  | 7 => 54
  | 8 => 53
  | 9 => 40
  | 10 => 50
  | 11 => 64
  | 12 => 61
  | 13 => 63
  | 14 => 25
  | 15 => 84
  | 16 => 34
  | 17 => 61
  | 18 => 40
  | 19 => 69
  | 20 => 33
  | 21 => 86
  | 22 => 94
  | 23 => 65
  | 24 => 14
  | 25 => 31
  | 26 => 20
  | 27 => 61
  | 28 => 70
  | 29 => 14
  | 30 => 58
  | 31 => 79
  | 32 => 38
  | 33 => 0
  | 34 => 19
  | 35 => 63
  | 36 => 93
  | 37 => 81
  | 38 => 6
  | 39 => 72
  | 40 => 48
  | 41 => 50
  | 42 => 80
  | 43 => 48
  | 44 => 91
  | 45 => 52
  | 46 => 21
  | 47 => 52
  | _ => 0

def fixedLiteralModPlusRow_3 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 8
  | 1 => 10
  | 2 => 16
  | 3 => 40
  | 4 => 81
  | 5 => 88
  | 6 => 97
  | 7 => 100
  | 8 => 79
  | 9 => 27
  | 10 => 82
  | 11 => 6
  | 12 => 86
  | 13 => 25
  | 14 => 57
  | 15 => 60
  | 16 => 67
  | 17 => 10
  | 18 => 73
  | 19 => 44
  | 20 => 52
  | 21 => 51
  | 22 => 49
  | 23 => 53
  | 24 => 69
  | 25 => 5
  | 26 => 15
  | 27 => 57
  | 28 => 81
  | 29 => 22
  | 30 => 87
  | 31 => 37
  | 32 => 15
  | 33 => 53
  | 34 => 91
  | 35 => 11
  | 36 => 19
  | 37 => 13
  | 38 => 87
  | 39 => 72
  | 40 => 36
  | 41 => 20
  | 42 => 82
  | 43 => 48
  | 44 => 37
  | 45 => 88
  | 46 => 88
  | 47 => 10
  | _ => 0

def fixedLiteralModPlusRow_4 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 21
  | 1 => 33
  | 2 => 85
  | 3 => 24
  | 4 => 86
  | 5 => 59
  | 6 => 66
  | 7 => 13
  | 8 => 59
  | 9 => 72
  | 10 => 32
  | 11 => 53
  | 12 => 17
  | 13 => 33
  | 14 => 96
  | 15 => 77
  | 16 => 19
  | 17 => 74
  | 18 => 22
  | 19 => 36
  | 20 => 73
  | 21 => 46
  | 22 => 41
  | 23 => 69
  | 24 => 15
  | 25 => 40
  | 26 => 10
  | 27 => 20
  | 28 => 42
  | 29 => 99
  | 30 => 32
  | 31 => 45
  | 32 => 9
  | 33 => 51
  | 34 => 7
  | 35 => 28
  | 36 => 92
  | 37 => 75
  | 38 => 41
  | 39 => 65
  | 40 => 76
  | 41 => 30
  | 42 => 52
  | 43 => 22
  | 44 => 2
  | 45 => 66
  | 46 => 47
  | 47 => 20
  | _ => 0

def fixedLiteralModPlusRow_5 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 77
  | 1 => 94
  | 2 => 4
  | 3 => 46
  | 4 => 41
  | 5 => 29
  | 6 => 36
  | 7 => 49
  | 8 => 63
  | 9 => 98
  | 10 => 39
  | 11 => 9
  | 12 => 87
  | 13 => 91
  | 14 => 90
  | 15 => 92
  | 16 => 52
  | 17 => 10
  | 18 => 80
  | 19 => 95
  | 20 => 12
  | 21 => 96
  | 22 => 88
  | 23 => 5
  | 24 => 80
  | 25 => 31
  | 26 => 7
  | 27 => 89
  | 28 => 45
  | 29 => 65
  | 30 => 93
  | 31 => 30
  | 32 => 96
  | 33 => 70
  | 34 => 38
  | 35 => 4
  | 36 => 28
  | 37 => 94
  | 38 => 15
  | 39 => 29
  | 40 => 42
  | 41 => 66
  | 42 => 13
  | 43 => 85
  | 44 => 70
  | 45 => 8
  | 46 => 20
  | 47 => 38
  | _ => 0

def fixedLiteralModPlusRow_6 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 35
  | 1 => 88
  | 2 => 58
  | 3 => 92
  | 4 => 8
  | 5 => 80
  | 6 => 86
  | 7 => 89
  | 8 => 18
  | 9 => 50
  | 10 => 20
  | 11 => 51
  | 12 => 17
  | 13 => 69
  | 14 => 25
  | 15 => 43
  | 16 => 43
  | 17 => 72
  | 18 => 89
  | 19 => 26
  | 20 => 69
  | 21 => 8
  | 22 => 61
  | 23 => 40
  | 24 => 62
  | 25 => 17
  | 26 => 6
  | 27 => 22
  | 28 => 46
  | 29 => 92
  | 30 => 30
  | 31 => 83
  | 32 => 10
  | 33 => 97
  | 34 => 52
  | 35 => 22
  | 36 => 78
  | 37 => 79
  | 38 => 68
  | 39 => 65
  | 40 => 16
  | 41 => 36
  | 42 => 72
  | 43 => 67
  | 44 => 92
  | 45 => 93
  | 46 => 35
  | 47 => 52
  | _ => 0

def fixedLiteralModPlusRow_7 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 88
  | 1 => 23
  | 2 => 58
  | 3 => 57
  | 4 => 21
  | 5 => 56
  | 6 => 96
  | 7 => 86
  | 8 => 86
  | 9 => 13
  | 10 => 49
  | 11 => 36
  | 12 => 5
  | 13 => 3
  | 14 => 16
  | 15 => 29
  | 16 => 45
  | 17 => 49
  | 18 => 58
  | 19 => 63
  | 20 => 84
  | 21 => 100
  | 22 => 67
  | 23 => 39
  | 24 => 31
  | 25 => 94
  | 26 => 74
  | 27 => 100
  | 28 => 85
  | 29 => 88
  | 30 => 90
  | 31 => 52
  | 32 => 29
  | 33 => 40
  | 34 => 86
  | 35 => 0
  | 36 => 78
  | 37 => 86
  | 38 => 94
  | 39 => 91
  | 40 => 94
  | 41 => 14
  | 42 => 33
  | 43 => 19
  | 44 => 72
  | 45 => 13
  | 46 => 34
  | 47 => 58
  | _ => 0

def fixedLiteralModPlusRow_8 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 59
  | 1 => 42
  | 2 => 65
  | 3 => 57
  | 4 => 45
  | 5 => 5
  | 6 => 48
  | 7 => 55
  | 8 => 88
  | 9 => 32
  | 10 => 58
  | 11 => 12
  | 12 => 52
  | 13 => 74
  | 14 => 10
  | 15 => 32
  | 16 => 3
  | 17 => 95
  | 18 => 29
  | 19 => 18
  | 20 => 39
  | 21 => 51
  | 22 => 57
  | 23 => 13
  | 24 => 93
  | 25 => 97
  | 26 => 5
  | 27 => 92
  | 28 => 81
  | 29 => 77
  | 30 => 9
  | 31 => 35
  | 32 => 13
  | 33 => 58
  | 34 => 58
  | 35 => 26
  | 36 => 73
  | 37 => 18
  | 38 => 22
  | 39 => 42
  | 40 => 100
  | 41 => 43
  | 42 => 47
  | 43 => 68
  | 44 => 25
  | 45 => 97
  | 46 => 88
  | 47 => 8
  | _ => 0

def fixedLiteralModPlusRow_9 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 29
  | 1 => 3
  | 2 => 18
  | 3 => 75
  | 4 => 81
  | 5 => 99
  | 6 => 51
  | 7 => 96
  | 8 => 33
  | 9 => 92
  | 10 => 17
  | 11 => 35
  | 12 => 79
  | 13 => 87
  | 14 => 89
  | 15 => 74
  | 16 => 84
  | 17 => 63
  | 18 => 23
  | 19 => 56
  | 20 => 81
  | 21 => 95
  | 22 => 37
  | 23 => 84
  | 24 => 33
  | 25 => 82
  | 26 => 100
  | 27 => 74
  | 28 => 29
  | 29 => 55
  | 30 => 30
  | 31 => 91
  | 32 => 92
  | 33 => 58
  | 34 => 29
  | 35 => 97
  | 36 => 13
  | 37 => 28
  | 38 => 53
  | 39 => 47
  | 40 => 2
  | 41 => 70
  | 42 => 64
  | 43 => 69
  | 44 => 52
  | 45 => 7
  | 46 => 31
  | 47 => 58
  | _ => 0

def fixedLiteralModPlusRow_10 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 24
  | 1 => 88
  | 2 => 30
  | 3 => 1
  | 4 => 31
  | 5 => 100
  | 6 => 62
  | 7 => 25
  | 8 => 56
  | 9 => 10
  | 10 => 9
  | 11 => 69
  | 12 => 40
  | 13 => 99
  | 14 => 99
  | 15 => 93
  | 16 => 48
  | 17 => 77
  | 18 => 87
  | 19 => 4
  | 20 => 96
  | 21 => 10
  | 22 => 91
  | 23 => 7
  | 24 => 37
  | 25 => 19
  | 26 => 86
  | 27 => 95
  | 28 => 3
  | 29 => 39
  | 30 => 54
  | 31 => 18
  | 32 => 81
  | 33 => 59
  | 34 => 81
  | 35 => 54
  | 36 => 44
  | 37 => 83
  | 38 => 17
  | 39 => 53
  | 40 => 97
  | 41 => 28
  | 42 => 0
  | 43 => 91
  | 44 => 95
  | 45 => 5
  | 46 => 75
  | 47 => 74
  | _ => 0

def fixedLiteralModPlusRow_11 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 35
  | 1 => 58
  | 2 => 64
  | 3 => 74
  | 4 => 21
  | 5 => 39
  | 6 => 54
  | 7 => 14
  | 8 => 36
  | 9 => 98
  | 10 => 6
  | 11 => 56
  | 12 => 73
  | 13 => 54
  | 14 => 16
  | 15 => 57
  | 16 => 23
  | 17 => 93
  | 18 => 71
  | 19 => 55
  | 20 => 19
  | 21 => 60
  | 22 => 52
  | 23 => 11
  | 24 => 82
  | 25 => 1
  | 26 => 26
  | 27 => 29
  | 28 => 96
  | 29 => 45
  | 30 => 23
  | 31 => 32
  | 32 => 58
  | 33 => 9
  | 34 => 58
  | 35 => 41
  | 36 => 0
  | 37 => 50
  | 38 => 32
  | 39 => 33
  | 40 => 17
  | 41 => 68
  | 42 => 30
  | 43 => 41
  | 44 => 15
  | 45 => 94
  | 46 => 67
  | 47 => 77
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModPlusRow_12 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 63
  | 1 => 61
  | 2 => 81
  | 3 => 50
  | 4 => 9
  | 5 => 100
  | 6 => 10
  | 7 => 5
  | 8 => 58
  | 9 => 79
  | 10 => 11
  | 11 => 5
  | 12 => 11
  | 13 => 49
  | 14 => 31
  | 15 => 82
  | 16 => 60
  | 17 => 91
  | 18 => 11
  | 19 => 50
  | 20 => 88
  | 21 => 32
  | 22 => 92
  | 23 => 93
  | 24 => 67
  | 25 => 83
  | 26 => 42
  | 27 => 13
  | 28 => 64
  | 29 => 41
  | 30 => 64
  | 31 => 87
  | 32 => 3
  | 33 => 82
  | 34 => 65
  | 35 => 87
  | 36 => 75
  | 37 => 97
  | 38 => 12
  | 39 => 11
  | 40 => 70
  | 41 => 1
  | 42 => 52
  | 43 => 77
  | 44 => 78
  | 45 => 9
  | 46 => 39
  | 47 => 92
  | _ => 0

def fixedLiteralModPlusRow_13 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 10
  | 1 => 10
  | 2 => 91
  | 3 => 48
  | 4 => 99
  | 5 => 79
  | 6 => 38
  | 7 => 88
  | 8 => 61
  | 9 => 17
  | 10 => 7
  | 11 => 43
  | 12 => 6
  | 13 => 13
  | 14 => 86
  | 15 => 5
  | 16 => 32
  | 17 => 5
  | 18 => 25
  | 19 => 59
  | 20 => 100
  | 21 => 36
  | 22 => 53
  | 23 => 68
  | 24 => 17
  | 25 => 66
  | 26 => 57
  | 27 => 71
  | 28 => 12
  | 29 => 27
  | 30 => 68
  | 31 => 4
  | 32 => 27
  | 33 => 62
  | 34 => 70
  | 35 => 55
  | 36 => 32
  | 37 => 80
  | 38 => 45
  | 39 => 16
  | 40 => 29
  | 41 => 93
  | 42 => 13
  | 43 => 60
  | 44 => 99
  | 45 => 45
  | 46 => 70
  | 47 => 7
  | _ => 0

def fixedLiteralModPlusRow_14 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 29
  | 1 => 41
  | 2 => 79
  | 3 => 56
  | 4 => 10
  | 5 => 68
  | 6 => 8
  | 7 => 75
  | 8 => 96
  | 9 => 12
  | 10 => 84
  | 11 => 36
  | 12 => 59
  | 13 => 37
  | 14 => 96
  | 15 => 10
  | 16 => 74
  | 17 => 86
  | 18 => 95
  | 19 => 65
  | 20 => 48
  | 21 => 12
  | 22 => 3
  | 23 => 79
  | 24 => 66
  | 25 => 81
  | 26 => 69
  | 27 => 28
  | 28 => 68
  | 29 => 28
  | 30 => 99
  | 31 => 57
  | 32 => 86
  | 33 => 83
  | 34 => 8
  | 35 => 17
  | 36 => 3
  | 37 => 8
  | 38 => 84
  | 39 => 77
  | 40 => 46
  | 41 => 95
  | 42 => 38
  | 43 => 57
  | 44 => 98
  | 45 => 11
  | 46 => 36
  | 47 => 0
  | _ => 0

def fixedLiteralModPlusRow_15 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 97
  | 1 => 8
  | 2 => 32
  | 3 => 13
  | 4 => 21
  | 5 => 98
  | 6 => 88
  | 7 => 81
  | 8 => 72
  | 9 => 8
  | 10 => 5
  | 11 => 50
  | 12 => 44
  | 13 => 79
  | 14 => 63
  | 15 => 91
  | 16 => 54
  | 17 => 79
  | 18 => 84
  | 19 => 65
  | 20 => 36
  | 21 => 13
  | 22 => 8
  | 23 => 53
  | 24 => 71
  | 25 => 8
  | 26 => 71
  | 27 => 19
  | 28 => 29
  | 29 => 79
  | 30 => 90
  | 31 => 73
  | 32 => 2
  | 33 => 23
  | 34 => 76
  | 35 => 21
  | 36 => 93
  | 37 => 89
  | 38 => 19
  | 39 => 78
  | 40 => 89
  | 41 => 55
  | 42 => 99
  | 43 => 24
  | 44 => 23
  | 45 => 19
  | 46 => 62
  | 47 => 92
  | _ => 0

def fixedLiteralModPlusRow_16 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 46
  | 1 => 36
  | 2 => 78
  | 3 => 6
  | 4 => 23
  | 5 => 88
  | 6 => 61
  | 7 => 43
  | 8 => 52
  | 9 => 12
  | 10 => 36
  | 11 => 94
  | 12 => 6
  | 13 => 55
  | 14 => 43
  | 15 => 48
  | 16 => 79
  | 17 => 50
  | 18 => 42
  | 19 => 65
  | 20 => 8
  | 21 => 57
  | 22 => 68
  | 23 => 33
  | 24 => 42
  | 25 => 15
  | 26 => 46
  | 27 => 79
  | 28 => 95
  | 29 => 48
  | 30 => 66
  | 31 => 46
  | 32 => 73
  | 33 => 46
  | 34 => 64
  | 35 => 11
  | 36 => 4
  | 37 => 97
  | 38 => 1
  | 39 => 33
  | 40 => 88
  | 41 => 79
  | 42 => 78
  | 43 => 60
  | 44 => 75
  | 45 => 82
  | 46 => 3
  | 47 => 29
  | _ => 0

def fixedLiteralModPlusRow_17 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 89
  | 1 => 55
  | 2 => 14
  | 3 => 22
  | 4 => 78
  | 5 => 35
  | 6 => 34
  | 7 => 7
  | 8 => 41
  | 9 => 26
  | 10 => 71
  | 11 => 50
  | 12 => 1
  | 13 => 56
  | 14 => 92
  | 15 => 44
  | 16 => 74
  | 17 => 63
  | 18 => 27
  | 19 => 10
  | 20 => 11
  | 21 => 8
  | 22 => 52
  | 23 => 98
  | 24 => 70
  | 25 => 79
  | 26 => 80
  | 27 => 38
  | 28 => 39
  | 29 => 90
  | 30 => 37
  | 31 => 64
  | 32 => 43
  | 33 => 52
  | 34 => 81
  | 35 => 84
  | 36 => 89
  | 37 => 63
  | 38 => 81
  | 39 => 95
  | 40 => 76
  | 41 => 94
  | 42 => 24
  | 43 => 92
  | 44 => 92
  | 45 => 100
  | 46 => 0
  | 47 => 74
  | _ => 0

def fixedLiteralModPlusRow_18 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 53
  | 1 => 94
  | 2 => 46
  | 3 => 35
  | 4 => 50
  | 5 => 95
  | 6 => 8
  | 7 => 37
  | 8 => 49
  | 9 => 100
  | 10 => 50
  | 11 => 20
  | 12 => 60
  | 13 => 72
  | 14 => 65
  | 15 => 34
  | 16 => 0
  | 17 => 87
  | 18 => 64
  | 19 => 78
  | 20 => 88
  | 21 => 20
  | 22 => 1
  | 23 => 27
  | 24 => 92
  | 25 => 56
  | 26 => 67
  | 27 => 96
  | 28 => 31
  | 29 => 18
  | 30 => 79
  | 31 => 1
  | 32 => 63
  | 33 => 21
  | 34 => 83
  | 35 => 15
  | 36 => 70
  | 37 => 8
  | 38 => 67
  | 39 => 5
  | 40 => 63
  | 41 => 6
  | 42 => 18
  | 43 => 44
  | 44 => 81
  | 45 => 71
  | 46 => 95
  | 47 => 9
  | _ => 0

def fixedLiteralModPlusRow_19 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 29
  | 1 => 25
  | 2 => 5
  | 3 => 44
  | 4 => 76
  | 5 => 15
  | 6 => 87
  | 7 => 14
  | 8 => 76
  | 9 => 30
  | 10 => 36
  | 11 => 39
  | 12 => 89
  | 13 => 51
  | 14 => 39
  | 15 => 41
  | 16 => 58
  | 17 => 79
  | 18 => 6
  | 19 => 27
  | 20 => 79
  | 21 => 15
  | 22 => 11
  | 23 => 36
  | 24 => 27
  | 25 => 12
  | 26 => 72
  | 27 => 72
  | 28 => 39
  | 29 => 63
  | 30 => 64
  | 31 => 25
  | 32 => 19
  | 33 => 42
  | 34 => 100
  | 35 => 62
  | 36 => 46
  | 37 => 48
  | 38 => 80
  | 39 => 86
  | 40 => 77
  | 41 => 3
  | 42 => 9
  | 43 => 20
  | 44 => 73
  | 45 => 72
  | 46 => 12
  | 47 => 85
  | _ => 0

def fixedLiteralModPlusRow_20 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 15
  | 1 => 98
  | 2 => 58
  | 3 => 94
  | 4 => 21
  | 5 => 1
  | 6 => 31
  | 7 => 54
  | 8 => 41
  | 9 => 67
  | 10 => 5
  | 11 => 39
  | 12 => 53
  | 13 => 35
  | 14 => 21
  | 15 => 89
  | 16 => 88
  | 17 => 83
  | 18 => 88
  | 19 => 84
  | 20 => 59
  | 21 => 37
  | 22 => 86
  | 23 => 11
  | 24 => 8
  | 25 => 50
  | 26 => 44
  | 27 => 62
  | 28 => 64
  | 29 => 68
  | 30 => 35
  | 31 => 9
  | 32 => 88
  | 33 => 59
  | 34 => 57
  | 35 => 87
  | 36 => 56
  | 37 => 80
  | 38 => 20
  | 39 => 5
  | 40 => 77
  | 41 => 80
  | 42 => 65
  | 43 => 86
  | 44 => 34
  | 45 => 24
  | 46 => 65
  | 47 => 8
  | _ => 0

def fixedLiteralModPlusRow_21 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 55
  | 1 => 92
  | 2 => 61
  | 3 => 85
  | 4 => 30
  | 5 => 61
  | 6 => 76
  | 7 => 66
  | 8 => 6
  | 9 => 51
  | 10 => 28
  | 11 => 78
  | 12 => 36
  | 13 => 35
  | 14 => 58
  | 15 => 69
  | 16 => 61
  | 17 => 79
  | 18 => 46
  | 19 => 10
  | 20 => 75
  | 21 => 29
  | 22 => 86
  | 23 => 1
  | 24 => 49
  | 25 => 88
  | 26 => 89
  | 27 => 52
  | 28 => 43
  | 29 => 100
  | 30 => 72
  | 31 => 11
  | 32 => 30
  | 33 => 78
  | 34 => 53
  | 35 => 100
  | 36 => 62
  | 37 => 36
  | 38 => 10
  | 39 => 55
  | 40 => 46
  | 41 => 63
  | 42 => 75
  | 43 => 69
  | 44 => 32
  | 45 => 9
  | 46 => 55
  | 47 => 33
  | _ => 0

def fixedLiteralModPlusRow_22 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 5
  | 1 => 94
  | 2 => 56
  | 3 => 97
  | 4 => 8
  | 5 => 20
  | 6 => 12
  | 7 => 20
  | 8 => 57
  | 9 => 10
  | 10 => 80
  | 11 => 96
  | 12 => 29
  | 13 => 30
  | 14 => 2
  | 15 => 59
  | 16 => 12
  | 17 => 62
  | 18 => 94
  | 19 => 52
  | 20 => 44
  | 21 => 63
  | 22 => 15
  | 23 => 42
  | 24 => 3
  | 25 => 59
  | 26 => 24
  | 27 => 47
  | 28 => 93
  | 29 => 21
  | 30 => 66
  | 31 => 48
  | 32 => 86
  | 33 => 63
  | 34 => 87
  | 35 => 2
  | 36 => 12
  | 37 => 91
  | 38 => 34
  | 39 => 86
  | 40 => 85
  | 41 => 34
  | 42 => 74
  | 43 => 34
  | 44 => 35
  | 45 => 90
  | 46 => 36
  | 47 => 7
  | _ => 0

def fixedLiteralModPlusRow_23 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 36
  | 2 => 100
  | 3 => 10
  | 4 => 58
  | 5 => 86
  | 6 => 36
  | 7 => 16
  | 8 => 91
  | 9 => 33
  | 10 => 41
  | 11 => 55
  | 12 => 96
  | 13 => 67
  | 14 => 77
  | 15 => 10
  | 16 => 18
  | 17 => 23
  | 18 => 20
  | 19 => 95
  | 20 => 18
  | 21 => 74
  | 22 => 87
  | 23 => 38
  | 24 => 89
  | 25 => 51
  | 26 => 92
  | 27 => 70
  | 28 => 44
  | 29 => 5
  | 30 => 94
  | 31 => 42
  | 32 => 2
  | 33 => 91
  | 34 => 19
  | 35 => 17
  | 36 => 96
  | 37 => 29
  | 38 => 28
  | 39 => 8
  | 40 => 36
  | 41 => 71
  | 42 => 100
  | 43 => 34
  | 44 => 50
  | 45 => 87
  | 46 => 68
  | 47 => 79
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModPlusRow_24 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 49
  | 1 => 25
  | 2 => 49
  | 3 => 42
  | 4 => 22
  | 5 => 29
  | 6 => 9
  | 7 => 21
  | 8 => 80
  | 9 => 78
  | 10 => 53
  | 11 => 13
  | 12 => 94
  | 13 => 95
  | 14 => 14
  | 15 => 71
  | 16 => 3
  | 17 => 22
  | 18 => 99
  | 19 => 81
  | 20 => 88
  | 21 => 76
  | 22 => 46
  | 23 => 51
  | 24 => 23
  | 25 => 62
  | 26 => 48
  | 27 => 62
  | 28 => 49
  | 29 => 7
  | 30 => 55
  | 31 => 85
  | 32 => 29
  | 33 => 95
  | 34 => 32
  | 35 => 79
  | 36 => 16
  | 37 => 37
  | 38 => 67
  | 39 => 29
  | 40 => 24
  | 41 => 98
  | 42 => 52
  | 43 => 82
  | 44 => 67
  | 45 => 76
  | 46 => 31
  | 47 => 42
  | _ => 0

def fixedLiteralModPlusRow_25 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 52
  | 1 => 29
  | 2 => 71
  | 3 => 92
  | 4 => 2
  | 5 => 76
  | 6 => 9
  | 7 => 8
  | 8 => 64
  | 9 => 53
  | 10 => 43
  | 11 => 73
  | 12 => 97
  | 13 => 24
  | 14 => 11
  | 15 => 53
  | 16 => 62
  | 17 => 62
  | 18 => 31
  | 19 => 27
  | 20 => 19
  | 21 => 0
  | 22 => 65
  | 23 => 22
  | 24 => 19
  | 25 => 53
  | 26 => 23
  | 27 => 59
  | 28 => 35
  | 29 => 66
  | 30 => 20
  | 31 => 91
  | 32 => 41
  | 33 => 78
  | 34 => 24
  | 35 => 82
  | 36 => 78
  | 37 => 67
  | 38 => 16
  | 39 => 65
  | 40 => 68
  | 41 => 24
  | 42 => 39
  | 43 => 13
  | 44 => 39
  | 45 => 77
  | 46 => 50
  | 47 => 75
  | _ => 0

def fixedLiteralModPlusRow_26 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 42
  | 1 => 13
  | 2 => 97
  | 3 => 4
  | 4 => 20
  | 5 => 48
  | 6 => 44
  | 7 => 12
  | 8 => 81
  | 9 => 98
  | 10 => 34
  | 11 => 47
  | 12 => 92
  | 13 => 98
  | 14 => 32
  | 15 => 49
  | 16 => 60
  | 17 => 94
  | 18 => 0
  | 19 => 99
  | 20 => 76
  | 21 => 34
  | 22 => 76
  | 23 => 25
  | 24 => 54
  | 25 => 49
  | 26 => 60
  | 27 => 20
  | 28 => 43
  | 29 => 57
  | 30 => 76
  | 31 => 13
  | 32 => 31
  | 33 => 36
  | 34 => 94
  | 35 => 28
  | 36 => 72
  | 37 => 65
  | 38 => 25
  | 39 => 45
  | 40 => 34
  | 41 => 71
  | 42 => 36
  | 43 => 34
  | 44 => 17
  | 45 => 70
  | 46 => 67
  | 47 => 29
  | _ => 0

def fixedLiteralModPlusRow_27 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 77
  | 1 => 73
  | 2 => 51
  | 3 => 24
  | 4 => 20
  | 5 => 37
  | 6 => 5
  | 7 => 35
  | 8 => 68
  | 9 => 48
  | 10 => 26
  | 11 => 8
  | 12 => 89
  | 13 => 32
  | 14 => 65
  | 15 => 79
  | 16 => 6
  | 17 => 79
  | 18 => 32
  | 19 => 2
  | 20 => 62
  | 21 => 10
  | 22 => 54
  | 23 => 73
  | 24 => 65
  | 25 => 74
  | 26 => 47
  | 27 => 92
  | 28 => 98
  | 29 => 14
  | 30 => 58
  | 31 => 24
  | 32 => 16
  | 33 => 63
  | 34 => 45
  | 35 => 7
  | 36 => 89
  | 37 => 76
  | 38 => 87
  | 39 => 88
  | 40 => 44
  | 41 => 78
  | 42 => 45
  | 43 => 8
  | 44 => 8
  | 45 => 20
  | 46 => 63
  | 47 => 48
  | _ => 0

def fixedLiteralModPlusRow_28 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 20
  | 1 => 14
  | 2 => 11
  | 3 => 76
  | 4 => 31
  | 5 => 23
  | 6 => 42
  | 7 => 72
  | 8 => 77
  | 9 => 83
  | 10 => 22
  | 11 => 13
  | 12 => 89
  | 13 => 65
  | 14 => 40
  | 15 => 65
  | 16 => 88
  | 17 => 7
  | 18 => 18
  | 19 => 40
  | 20 => 4
  | 21 => 79
  | 22 => 0
  | 23 => 45
  | 24 => 76
  | 25 => 54
  | 26 => 76
  | 27 => 72
  | 28 => 96
  | 29 => 53
  | 30 => 10
  | 31 => 15
  | 32 => 18
  | 33 => 8
  | 34 => 81
  | 35 => 36
  | 36 => 41
  | 37 => 41
  | 38 => 9
  | 39 => 8
  | 40 => 69
  | 41 => 72
  | 42 => 15
  | 43 => 23
  | 44 => 91
  | 45 => 95
  | 46 => 42
  | 47 => 45
  | _ => 0

def fixedLiteralModPlusRow_29 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 33
  | 1 => 15
  | 2 => 28
  | 3 => 23
  | 4 => 22
  | 5 => 62
  | 6 => 32
  | 7 => 88
  | 8 => 100
  | 9 => 36
  | 10 => 86
  | 11 => 88
  | 12 => 35
  | 13 => 23
  | 14 => 72
  | 15 => 84
  | 16 => 37
  | 17 => 82
  | 18 => 68
  | 19 => 13
  | 20 => 23
  | 21 => 26
  | 22 => 37
  | 23 => 51
  | 24 => 75
  | 25 => 62
  | 26 => 14
  | 27 => 38
  | 28 => 80
  | 29 => 84
  | 30 => 84
  | 31 => 64
  | 32 => 92
  | 33 => 91
  | 34 => 55
  | 35 => 42
  | 36 => 96
  | 37 => 18
  | 38 => 58
  | 39 => 0
  | 40 => 82
  | 41 => 71
  | 42 => 51
  | 43 => 45
  | 44 => 5
  | 45 => 62
  | 46 => 60
  | 47 => 46
  | _ => 0

def fixedLiteralModPlusRow_30 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 94
  | 1 => 16
  | 2 => 76
  | 3 => 29
  | 4 => 15
  | 5 => 81
  | 6 => 17
  | 7 => 79
  | 8 => 34
  | 9 => 61
  | 10 => 13
  | 11 => 74
  | 12 => 42
  | 13 => 46
  | 14 => 12
  | 15 => 8
  | 16 => 86
  | 17 => 92
  | 18 => 95
  | 19 => 92
  | 20 => 89
  | 21 => 91
  | 22 => 71
  | 23 => 64
  | 24 => 66
  | 25 => 66
  | 26 => 48
  | 27 => 91
  | 28 => 62
  | 29 => 20
  | 30 => 80
  | 31 => 72
  | 32 => 39
  | 33 => 47
  | 34 => 44
  | 35 => 68
  | 36 => 34
  | 37 => 42
  | 38 => 32
  | 39 => 90
  | 40 => 25
  | 41 => 78
  | 42 => 40
  | 43 => 47
  | 44 => 66
  | 45 => 87
  | 46 => 37
  | 47 => 79
  | _ => 0

def fixedLiteralModPlusRow_31 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 10
  | 1 => 35
  | 2 => 51
  | 3 => 21
  | 4 => 36
  | 5 => 59
  | 6 => 71
  | 7 => 83
  | 8 => 74
  | 9 => 20
  | 10 => 76
  | 11 => 86
  | 12 => 2
  | 13 => 58
  | 14 => 25
  | 15 => 53
  | 16 => 93
  | 17 => 25
  | 18 => 30
  | 19 => 44
  | 20 => 79
  | 21 => 42
  | 22 => 16
  | 23 => 60
  | 24 => 81
  | 25 => 22
  | 26 => 30
  | 27 => 90
  | 28 => 14
  | 29 => 84
  | 30 => 43
  | 31 => 53
  | 32 => 71
  | 33 => 92
  | 34 => 1
  | 35 => 77
  | 36 => 40
  | 37 => 2
  | 38 => 42
  | 39 => 63
  | 40 => 10
  | 41 => 73
  | 42 => 30
  | 43 => 66
  | 44 => 11
  | 45 => 61
  | 46 => 47
  | 47 => 41
  | _ => 0

def fixedLiteralModPlusRow_32 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 44
  | 1 => 89
  | 2 => 4
  | 3 => 1
  | 4 => 11
  | 5 => 2
  | 6 => 11
  | 7 => 63
  | 8 => 52
  | 9 => 1
  | 10 => 16
  | 11 => 64
  | 12 => 37
  | 13 => 35
  | 14 => 53
  | 15 => 81
  | 16 => 25
  | 17 => 15
  | 18 => 49
  | 19 => 25
  | 20 => 33
  | 21 => 62
  | 22 => 72
  | 23 => 60
  | 24 => 7
  | 25 => 30
  | 26 => 41
  | 27 => 26
  | 28 => 45
  | 29 => 42
  | 30 => 77
  | 31 => 54
  | 32 => 39
  | 33 => 74
  | 34 => 47
  | 35 => 61
  | 36 => 16
  | 37 => 73
  | 38 => 31
  | 39 => 93
  | 40 => 10
  | 41 => 93
  | 42 => 30
  | 43 => 38
  | 44 => 25
  | 45 => 62
  | 46 => 97
  | 47 => 90
  | _ => 0

def fixedLiteralModPlusRow_33 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 42
  | 1 => 12
  | 2 => 41
  | 3 => 61
  | 4 => 85
  | 5 => 4
  | 6 => 79
  | 7 => 44
  | 8 => 21
  | 9 => 54
  | 10 => 11
  | 11 => 13
  | 12 => 92
  | 13 => 47
  | 14 => 8
  | 15 => 49
  | 16 => 23
  | 17 => 78
  | 18 => 41
  | 19 => 95
  | 20 => 34
  | 21 => 59
  | 22 => 100
  | 23 => 66
  | 24 => 53
  | 25 => 23
  | 26 => 51
  | 27 => 46
  | 28 => 85
  | 29 => 61
  | 30 => 21
  | 31 => 19
  | 32 => 12
  | 33 => 34
  | 34 => 9
  | 35 => 87
  | 36 => 98
  | 37 => 59
  | 38 => 32
  | 39 => 56
  | 40 => 46
  | 41 => 16
  | 42 => 48
  | 43 => 96
  | 44 => 13
  | 45 => 40
  | 46 => 1
  | 47 => 76
  | _ => 0

def fixedLiteralModPlusRow_34 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 88
  | 1 => 75
  | 2 => 12
  | 3 => 31
  | 4 => 41
  | 5 => 92
  | 6 => 42
  | 7 => 17
  | 8 => 34
  | 9 => 86
  | 10 => 74
  | 11 => 12
  | 12 => 22
  | 13 => 54
  | 14 => 69
  | 15 => 7
  | 16 => 14
  | 17 => 5
  | 18 => 22
  | 19 => 67
  | 20 => 80
  | 21 => 45
  | 22 => 49
  | 23 => 51
  | 24 => 91
  | 25 => 46
  | 26 => 55
  | 27 => 18
  | 28 => 93
  | 29 => 51
  | 30 => 42
  | 31 => 4
  | 32 => 27
  | 33 => 32
  | 34 => 21
  | 35 => 94
  | 36 => 80
  | 37 => 64
  | 38 => 76
  | 39 => 44
  | 40 => 18
  | 41 => 7
  | 42 => 16
  | 43 => 94
  | 44 => 83
  | 45 => 63
  | 46 => 96
  | 47 => 19
  | _ => 0

def fixedLiteralModPlusRow_35 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 20
  | 1 => 20
  | 2 => 55
  | 3 => 10
  | 4 => 22
  | 5 => 91
  | 6 => 92
  | 7 => 8
  | 8 => 38
  | 9 => 56
  | 10 => 2
  | 11 => 18
  | 12 => 52
  | 13 => 39
  | 14 => 65
  | 15 => 57
  | 16 => 15
  | 17 => 24
  | 18 => 74
  | 19 => 23
  | 20 => 90
  | 21 => 25
  | 22 => 97
  | 23 => 82
  | 24 => 49
  | 25 => 82
  | 26 => 79
  | 27 => 7
  | 28 => 90
  | 29 => 60
  | 30 => 22
  | 31 => 26
  | 32 => 5
  | 33 => 56
  | 34 => 11
  | 35 => 69
  | 36 => 18
  | 37 => 41
  | 38 => 90
  | 39 => 78
  | 40 => 76
  | 41 => 9
  | 42 => 42
  | 43 => 36
  | 44 => 64
  | 45 => 63
  | 46 => 41
  | 47 => 83
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModPlusRow_36 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 25
  | 1 => 10
  | 2 => 28
  | 3 => 60
  | 4 => 66
  | 5 => 45
  | 6 => 13
  | 7 => 8
  | 8 => 65
  | 9 => 62
  | 10 => 9
  | 11 => 19
  | 12 => 95
  | 13 => 87
  | 14 => 50
  | 15 => 57
  | 16 => 98
  | 17 => 88
  | 18 => 96
  | 19 => 17
  | 20 => 91
  | 21 => 16
  | 22 => 58
  | 23 => 27
  | 24 => 67
  | 25 => 14
  | 26 => 44
  | 27 => 60
  | 28 => 64
  | 29 => 92
  | 30 => 90
  | 31 => 72
  | 32 => 93
  | 33 => 42
  | 34 => 36
  | 35 => 5
  | 36 => 90
  | 37 => 26
  | 38 => 100
  | 39 => 29
  | 40 => 16
  | 41 => 61
  | 42 => 34
  | 43 => 14
  | 44 => 32
  | 45 => 32
  | 46 => 7
  | 47 => 65
  | _ => 0

def fixedLiteralModPlusRow_37 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 75
  | 1 => 20
  | 2 => 98
  | 3 => 43
  | 4 => 20
  | 5 => 14
  | 6 => 54
  | 7 => 53
  | 8 => 9
  | 9 => 38
  | 10 => 58
  | 11 => 97
  | 12 => 50
  | 13 => 64
  | 14 => 32
  | 15 => 84
  | 16 => 4
  | 17 => 52
  | 18 => 99
  | 19 => 41
  | 20 => 76
  | 21 => 18
  | 22 => 70
  | 23 => 19
  | 24 => 60
  | 25 => 16
  | 26 => 55
  | 27 => 84
  | 28 => 49
  | 29 => 46
  | 30 => 52
  | 31 => 77
  | 32 => 72
  | 33 => 21
  | 34 => 32
  | 35 => 18
  | 36 => 58
  | 37 => 61
  | 38 => 1
  | 39 => 61
  | 40 => 32
  | 41 => 73
  | 42 => 81
  | 43 => 96
  | 44 => 98
  | 45 => 28
  | 46 => 81
  | 47 => 18
  | _ => 0

def fixedLiteralModPlusRow_38 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 84
  | 1 => 42
  | 2 => 52
  | 3 => 77
  | 4 => 35
  | 5 => 67
  | 6 => 51
  | 7 => 96
  | 8 => 25
  | 9 => 31
  | 10 => 80
  | 11 => 12
  | 12 => 92
  | 13 => 4
  | 14 => 66
  | 15 => 62
  | 16 => 7
  | 17 => 76
  | 18 => 25
  | 19 => 83
  | 20 => 40
  | 21 => 73
  | 22 => 88
  | 23 => 99
  | 24 => 88
  | 25 => 85
  | 26 => 48
  | 27 => 8
  | 28 => 27
  | 29 => 53
  | 30 => 40
  | 31 => 32
  | 32 => 88
  | 33 => 67
  | 34 => 95
  | 35 => 82
  | 36 => 46
  | 37 => 3
  | 38 => 16
  | 39 => 89
  | 40 => 4
  | 41 => 25
  | 42 => 3
  | 43 => 87
  | 44 => 98
  | 45 => 15
  | 46 => 58
  | 47 => 92
  | _ => 0

def fixedLiteralModPlusRow_39 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 18
  | 1 => 74
  | 2 => 64
  | 3 => 66
  | 4 => 84
  | 5 => 49
  | 6 => 93
  | 7 => 17
  | 8 => 68
  | 9 => 18
  | 10 => 5
  | 11 => 78
  | 12 => 14
  | 13 => 32
  | 14 => 94
  | 15 => 85
  | 16 => 12
  | 17 => 77
  | 18 => 15
  | 19 => 41
  | 20 => 78
  | 21 => 24
  | 22 => 85
  | 23 => 48
  | 24 => 47
  | 25 => 61
  | 26 => 96
  | 27 => 10
  | 28 => 92
  | 29 => 13
  | 30 => 44
  | 31 => 85
  | 32 => 45
  | 33 => 8
  | 34 => 39
  | 35 => 79
  | 36 => 64
  | 37 => 36
  | 38 => 84
  | 39 => 77
  | 40 => 85
  | 41 => 68
  | 42 => 64
  | 43 => 92
  | 44 => 69
  | 45 => 73
  | 46 => 98
  | 47 => 1
  | _ => 0

def fixedLiteralModPlusRow_40 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 37
  | 1 => 15
  | 2 => 56
  | 3 => 75
  | 4 => 52
  | 5 => 34
  | 6 => 17
  | 7 => 81
  | 8 => 67
  | 9 => 89
  | 10 => 60
  | 11 => 43
  | 12 => 6
  | 13 => 90
  | 14 => 98
  | 15 => 2
  | 16 => 50
  | 17 => 20
  | 18 => 11
  | 19 => 67
  | 20 => 85
  | 21 => 95
  | 22 => 36
  | 23 => 19
  | 24 => 21
  | 25 => 63
  | 26 => 72
  | 27 => 56
  | 28 => 96
  | 29 => 98
  | 30 => 34
  | 31 => 100
  | 32 => 80
  | 33 => 90
  | 34 => 39
  | 35 => 31
  | 36 => 82
  | 37 => 71
  | 38 => 13
  | 39 => 95
  | 40 => 32
  | 41 => 1
  | 42 => 66
  | 43 => 75
  | 44 => 41
  | 45 => 24
  | 46 => 60
  | 47 => 38
  | _ => 0

def fixedLiteralModPlusRow_41 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 77
  | 1 => 78
  | 2 => 54
  | 3 => 84
  | 4 => 3
  | 5 => 40
  | 6 => 47
  | 7 => 37
  | 8 => 50
  | 9 => 13
  | 10 => 26
  | 11 => 71
  | 12 => 43
  | 13 => 5
  | 14 => 3
  | 15 => 1
  | 16 => 67
  | 17 => 33
  | 18 => 24
  | 19 => 20
  | 20 => 80
  | 21 => 79
  | 22 => 24
  | 23 => 26
  | 24 => 28
  | 25 => 58
  | 26 => 82
  | 27 => 22
  | 28 => 65
  | 29 => 38
  | 30 => 28
  | 31 => 30
  | 32 => 1
  | 33 => 7
  | 34 => 92
  | 35 => 65
  | 36 => 18
  | 37 => 33
  | 38 => 74
  | 39 => 73
  | 40 => 53
  | 41 => 29
  | 42 => 0
  | 43 => 22
  | 44 => 37
  | 45 => 6
  | 46 => 99
  | 47 => 1
  | _ => 0

def fixedLiteralModPlusRow_42 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 8
  | 1 => 48
  | 2 => 47
  | 3 => 56
  | 4 => 95
  | 5 => 36
  | 6 => 6
  | 7 => 8
  | 8 => 77
  | 9 => 0
  | 10 => 5
  | 11 => 53
  | 12 => 54
  | 13 => 57
  | 14 => 14
  | 15 => 72
  | 16 => 10
  | 17 => 30
  | 18 => 98
  | 19 => 1
  | 20 => 8
  | 21 => 57
  | 22 => 75
  | 23 => 1
  | 24 => 64
  | 25 => 66
  | 26 => 24
  | 27 => 52
  | 28 => 87
  | 29 => 15
  | 30 => 69
  | 31 => 41
  | 32 => 9
  | 33 => 26
  | 34 => 26
  | 35 => 78
  | 36 => 1
  | 37 => 16
  | 38 => 68
  | 39 => 91
  | 40 => 75
  | 41 => 51
  | 42 => 100
  | 43 => 64
  | 44 => 32
  | 45 => 56
  | 46 => 71
  | 47 => 55
  | _ => 0

def fixedLiteralModPlusRow_43 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 28
  | 1 => 6
  | 2 => 66
  | 3 => 44
  | 4 => 39
  | 5 => 34
  | 6 => 25
  | 7 => 36
  | 8 => 66
  | 9 => 95
  | 10 => 18
  | 11 => 28
  | 12 => 26
  | 13 => 88
  | 14 => 42
  | 15 => 73
  | 16 => 59
  | 17 => 40
  | 18 => 27
  | 19 => 99
  | 20 => 42
  | 21 => 38
  | 22 => 36
  | 23 => 94
  | 24 => 41
  | 25 => 72
  | 26 => 56
  | 27 => 91
  | 28 => 0
  | 29 => 79
  | 30 => 86
  | 31 => 75
  | 32 => 34
  | 33 => 86
  | 34 => 72
  | 35 => 43
  | 36 => 29
  | 37 => 67
  | 38 => 15
  | 39 => 5
  | 40 => 15
  | 41 => 3
  | 42 => 99
  | 43 => 34
  | 44 => 10
  | 45 => 20
  | 46 => 6
  | 47 => 92
  | _ => 0

def fixedLiteralModPlusRow_44 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 70
  | 1 => 78
  | 2 => 66
  | 3 => 5
  | 4 => 56
  | 5 => 31
  | 6 => 39
  | 7 => 35
  | 8 => 21
  | 9 => 14
  | 10 => 34
  | 11 => 34
  | 12 => 95
  | 13 => 66
  | 14 => 12
  | 15 => 38
  | 16 => 49
  | 17 => 31
  | 18 => 89
  | 19 => 64
  | 20 => 93
  | 21 => 76
  | 22 => 67
  | 23 => 56
  | 24 => 22
  | 25 => 75
  | 26 => 37
  | 27 => 73
  | 28 => 92
  | 29 => 3
  | 30 => 80
  | 31 => 59
  | 32 => 72
  | 33 => 82
  | 34 => 85
  | 35 => 84
  | 36 => 41
  | 37 => 53
  | 38 => 68
  | 39 => 17
  | 40 => 52
  | 41 => 26
  | 42 => 92
  | 43 => 32
  | 44 => 70
  | 45 => 48
  | 46 => 9
  | 47 => 40
  | _ => 0

def fixedLiteralModPlusRow_45 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 82
  | 1 => 20
  | 2 => 49
  | 3 => 37
  | 4 => 8
  | 5 => 75
  | 6 => 73
  | 7 => 16
  | 8 => 20
  | 9 => 22
  | 10 => 19
  | 11 => 6
  | 12 => 33
  | 13 => 19
  | 14 => 35
  | 15 => 52
  | 16 => 36
  | 17 => 26
  | 18 => 75
  | 19 => 88
  | 20 => 13
  | 21 => 29
  | 22 => 4
  | 23 => 47
  | 24 => 27
  | 25 => 43
  | 26 => 6
  | 27 => 12
  | 28 => 74
  | 29 => 20
  | 30 => 48
  | 31 => 62
  | 32 => 71
  | 33 => 54
  | 34 => 100
  | 35 => 92
  | 36 => 34
  | 37 => 51
  | 38 => 23
  | 39 => 63
  | 40 => 20
  | 41 => 97
  | 42 => 1
  | 43 => 1
  | 44 => 3
  | 45 => 41
  | 46 => 21
  | 47 => 90
  | _ => 0

def fixedLiteralModPlusRow_46 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 23
  | 1 => 6
  | 2 => 100
  | 3 => 5
  | 4 => 52
  | 5 => 20
  | 6 => 31
  | 7 => 33
  | 8 => 44
  | 9 => 40
  | 10 => 73
  | 11 => 80
  | 12 => 82
  | 13 => 95
  | 14 => 14
  | 15 => 49
  | 16 => 55
  | 17 => 68
  | 18 => 95
  | 19 => 86
  | 20 => 57
  | 21 => 7
  | 22 => 88
  | 23 => 7
  | 24 => 97
  | 25 => 72
  | 26 => 75
  | 27 => 30
  | 28 => 98
  | 29 => 3
  | 30 => 8
  | 31 => 23
  | 32 => 93
  | 33 => 34
  | 34 => 90
  | 35 => 92
  | 36 => 82
  | 37 => 84
  | 38 => 49
  | 39 => 3
  | 40 => 54
  | 41 => 64
  | 42 => 31
  | 43 => 84
  | 44 => 22
  | 45 => 74
  | 46 => 63
  | 47 => 71
  | _ => 0

def fixedLiteralModPlusRow_47 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 6
  | 1 => 17
  | 2 => 51
  | 3 => 26
  | 4 => 48
  | 5 => 28
  | 6 => 17
  | 7 => 95
  | 8 => 52
  | 9 => 65
  | 10 => 100
  | 11 => 82
  | 12 => 80
  | 13 => 8
  | 14 => 35
  | 15 => 9
  | 16 => 85
  | 17 => 68
  | 18 => 17
  | 19 => 99
  | 20 => 91
  | 21 => 3
  | 22 => 6
  | 23 => 57
  | 24 => 90
  | 25 => 70
  | 26 => 83
  | 27 => 28
  | 28 => 48
  | 29 => 88
  | 30 => 55
  | 31 => 17
  | 32 => 33
  | 33 => 57
  | 34 => 73
  | 35 => 2
  | 36 => 25
  | 37 => 46
  | 38 => 73
  | 39 => 43
  | 40 => 79
  | 41 => 95
  | 42 => 68
  | 43 => 54
  | 44 => 45
  | 45 => 93
  | 46 => 90
  | 47 => 14
  | _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

def fixedLiteralModPlus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralModPlusRow_0
  | 1 => fixedLiteralModPlusRow_1
  | 2 => fixedLiteralModPlusRow_2
  | 3 => fixedLiteralModPlusRow_3
  | 4 => fixedLiteralModPlusRow_4
  | 5 => fixedLiteralModPlusRow_5
  | 6 => fixedLiteralModPlusRow_6
  | 7 => fixedLiteralModPlusRow_7
  | 8 => fixedLiteralModPlusRow_8
  | 9 => fixedLiteralModPlusRow_9
  | 10 => fixedLiteralModPlusRow_10
  | 11 => fixedLiteralModPlusRow_11
  | 12 => fixedLiteralModPlusRow_12
  | 13 => fixedLiteralModPlusRow_13
  | 14 => fixedLiteralModPlusRow_14
  | 15 => fixedLiteralModPlusRow_15
  | 16 => fixedLiteralModPlusRow_16
  | 17 => fixedLiteralModPlusRow_17
  | 18 => fixedLiteralModPlusRow_18
  | 19 => fixedLiteralModPlusRow_19
  | 20 => fixedLiteralModPlusRow_20
  | 21 => fixedLiteralModPlusRow_21
  | 22 => fixedLiteralModPlusRow_22
  | 23 => fixedLiteralModPlusRow_23
  | 24 => fixedLiteralModPlusRow_24
  | 25 => fixedLiteralModPlusRow_25
  | 26 => fixedLiteralModPlusRow_26
  | 27 => fixedLiteralModPlusRow_27
  | 28 => fixedLiteralModPlusRow_28
  | 29 => fixedLiteralModPlusRow_29
  | 30 => fixedLiteralModPlusRow_30
  | 31 => fixedLiteralModPlusRow_31
  | 32 => fixedLiteralModPlusRow_32
  | 33 => fixedLiteralModPlusRow_33
  | 34 => fixedLiteralModPlusRow_34
  | 35 => fixedLiteralModPlusRow_35
  | 36 => fixedLiteralModPlusRow_36
  | 37 => fixedLiteralModPlusRow_37
  | 38 => fixedLiteralModPlusRow_38
  | 39 => fixedLiteralModPlusRow_39
  | 40 => fixedLiteralModPlusRow_40
  | 41 => fixedLiteralModPlusRow_41
  | 42 => fixedLiteralModPlusRow_42
  | 43 => fixedLiteralModPlusRow_43
  | 44 => fixedLiteralModPlusRow_44
  | 45 => fixedLiteralModPlusRow_45
  | 46 => fixedLiteralModPlusRow_46
  | 47 => fixedLiteralModPlusRow_47
  | _ => fun _ => 0

def fixedLiteralInvPlus : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralInvPlusRow_0
  | 1 => fixedLiteralInvPlusRow_1
  | 2 => fixedLiteralInvPlusRow_2
  | 3 => fixedLiteralInvPlusRow_3
  | 4 => fixedLiteralInvPlusRow_4
  | 5 => fixedLiteralInvPlusRow_5
  | 6 => fixedLiteralInvPlusRow_6
  | 7 => fixedLiteralInvPlusRow_7
  | 8 => fixedLiteralInvPlusRow_8
  | 9 => fixedLiteralInvPlusRow_9
  | 10 => fixedLiteralInvPlusRow_10
  | 11 => fixedLiteralInvPlusRow_11
  | 12 => fixedLiteralInvPlusRow_12
  | 13 => fixedLiteralInvPlusRow_13
  | 14 => fixedLiteralInvPlusRow_14
  | 15 => fixedLiteralInvPlusRow_15
  | 16 => fixedLiteralInvPlusRow_16
  | 17 => fixedLiteralInvPlusRow_17
  | 18 => fixedLiteralInvPlusRow_18
  | 19 => fixedLiteralInvPlusRow_19
  | 20 => fixedLiteralInvPlusRow_20
  | 21 => fixedLiteralInvPlusRow_21
  | 22 => fixedLiteralInvPlusRow_22
  | 23 => fixedLiteralInvPlusRow_23
  | 24 => fixedLiteralInvPlusRow_24
  | 25 => fixedLiteralInvPlusRow_25
  | 26 => fixedLiteralInvPlusRow_26
  | 27 => fixedLiteralInvPlusRow_27
  | 28 => fixedLiteralInvPlusRow_28
  | 29 => fixedLiteralInvPlusRow_29
  | 30 => fixedLiteralInvPlusRow_30
  | 31 => fixedLiteralInvPlusRow_31
  | 32 => fixedLiteralInvPlusRow_32
  | 33 => fixedLiteralInvPlusRow_33
  | 34 => fixedLiteralInvPlusRow_34
  | 35 => fixedLiteralInvPlusRow_35
  | 36 => fixedLiteralInvPlusRow_36
  | 37 => fixedLiteralInvPlusRow_37
  | 38 => fixedLiteralInvPlusRow_38
  | 39 => fixedLiteralInvPlusRow_39
  | 40 => fixedLiteralInvPlusRow_40
  | 41 => fixedLiteralInvPlusRow_41
  | 42 => fixedLiteralInvPlusRow_42
  | 43 => fixedLiteralInvPlusRow_43
  | 44 => fixedLiteralInvPlusRow_44
  | 45 => fixedLiteralInvPlusRow_45
  | 46 => fixedLiteralInvPlusRow_46
  | 47 => fixedLiteralInvPlusRow_47
  | _ => fun _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvZeroRow_0 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 18
  | 1 => 6
  | 2 => 41
  | 3 => 61
  | 4 => 75
  | 5 => 60
  | 6 => 96
  | 7 => 27
  | 8 => 22
  | 9 => 70
  | 10 => 0
  | 11 => 46
  | 12 => 55
  | 13 => 69
  | 14 => 13
  | 15 => 5
  | 16 => 26
  | 17 => 29
  | 18 => 78
  | 19 => 14
  | 20 => 0
  | 21 => 62
  | 22 => 24
  | 23 => 19
  | 24 => 81
  | 25 => 21
  | 26 => 28
  | 27 => 72
  | 28 => 38
  | 29 => 34
  | 30 => 92
  | 31 => 55
  | 32 => 36
  | 33 => 20
  | 34 => 27
  | 35 => 70
  | 36 => 27
  | 37 => 68
  | 38 => 0
  | 39 => 34
  | 40 => 43
  | 41 => 100
  | 42 => 60
  | 43 => 89
  | 44 => 20
  | 45 => 91
  | 46 => 64
  | 47 => 54
  | _ => 0

def fixedLiteralInvZeroRow_1 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 45
  | 2 => 54
  | 3 => 32
  | 4 => 85
  | 5 => 49
  | 6 => 49
  | 7 => 17
  | 8 => 91
  | 9 => 1
  | 10 => 64
  | 11 => 67
  | 12 => 27
  | 13 => 37
  | 14 => 20
  | 15 => 10
  | 16 => 95
  | 17 => 65
  | 18 => 20
  | 19 => 63
  | 20 => 30
  | 21 => 20
  | 22 => 10
  | 23 => 93
  | 24 => 77
  | 25 => 15
  | 26 => 41
  | 27 => 19
  | 28 => 7
  | 29 => 59
  | 30 => 4
  | 31 => 10
  | 32 => 70
  | 33 => 2
  | 34 => 79
  | 35 => 42
  | 36 => 36
  | 37 => 14
  | 38 => 73
  | 39 => 71
  | 40 => 84
  | 41 => 30
  | 42 => 99
  | 43 => 84
  | 44 => 49
  | 45 => 41
  | 46 => 80
  | 47 => 15
  | _ => 0

def fixedLiteralInvZeroRow_2 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 57
  | 1 => 24
  | 2 => 21
  | 3 => 89
  | 4 => 88
  | 5 => 4
  | 6 => 15
  | 7 => 36
  | 8 => 41
  | 9 => 24
  | 10 => 39
  | 11 => 37
  | 12 => 90
  | 13 => 12
  | 14 => 26
  | 15 => 65
  | 16 => 98
  | 17 => 15
  | 18 => 42
  | 19 => 31
  | 20 => 95
  | 21 => 23
  | 22 => 40
  | 23 => 41
  | 24 => 63
  | 25 => 73
  | 26 => 1
  | 27 => 94
  | 28 => 49
  | 29 => 8
  | 30 => 84
  | 31 => 51
  | 32 => 82
  | 33 => 25
  | 34 => 56
  | 35 => 4
  | 36 => 81
  | 37 => 63
  | 38 => 46
  | 39 => 89
  | 40 => 15
  | 41 => 40
  | 42 => 51
  | 43 => 85
  | 44 => 7
  | 45 => 54
  | 46 => 71
  | 47 => 40
  | _ => 0

def fixedLiteralInvZeroRow_3 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 31
  | 1 => 96
  | 2 => 24
  | 3 => 7
  | 4 => 82
  | 5 => 66
  | 6 => 17
  | 7 => 87
  | 8 => 17
  | 9 => 70
  | 10 => 65
  | 11 => 16
  | 12 => 12
  | 13 => 50
  | 14 => 6
  | 15 => 71
  | 16 => 91
  | 17 => 67
  | 18 => 9
  | 19 => 92
  | 20 => 50
  | 21 => 40
  | 22 => 46
  | 23 => 6
  | 24 => 12
  | 25 => 73
  | 26 => 28
  | 27 => 14
  | 28 => 47
  | 29 => 19
  | 30 => 22
  | 31 => 91
  | 32 => 72
  | 33 => 11
  | 34 => 61
  | 35 => 25
  | 36 => 84
  | 37 => 29
  | 38 => 19
  | 39 => 53
  | 40 => 12
  | 41 => 70
  | 42 => 60
  | 43 => 25
  | 44 => 85
  | 45 => 90
  | 46 => 41
  | 47 => 81
  | _ => 0

def fixedLiteralInvZeroRow_4 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 85
  | 1 => 29
  | 2 => 94
  | 3 => 59
  | 4 => 75
  | 5 => 87
  | 6 => 82
  | 7 => 17
  | 8 => 29
  | 9 => 85
  | 10 => 34
  | 11 => 0
  | 12 => 66
  | 13 => 63
  | 14 => 23
  | 15 => 18
  | 16 => 21
  | 17 => 8
  | 18 => 3
  | 19 => 23
  | 20 => 91
  | 21 => 6
  | 22 => 13
  | 23 => 38
  | 24 => 68
  | 25 => 8
  | 26 => 79
  | 27 => 33
  | 28 => 86
  | 29 => 14
  | 30 => 94
  | 31 => 20
  | 32 => 88
  | 33 => 48
  | 34 => 24
  | 35 => 12
  | 36 => 33
  | 37 => 4
  | 38 => 91
  | 39 => 23
  | 40 => 23
  | 41 => 65
  | 42 => 81
  | 43 => 93
  | 44 => 69
  | 45 => 76
  | 46 => 3
  | 47 => 85
  | _ => 0

def fixedLiteralInvZeroRow_5 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 85
  | 1 => 87
  | 2 => 75
  | 3 => 80
  | 4 => 62
  | 5 => 11
  | 6 => 56
  | 7 => 35
  | 8 => 99
  | 9 => 27
  | 10 => 99
  | 11 => 61
  | 12 => 83
  | 13 => 96
  | 14 => 50
  | 15 => 73
  | 16 => 58
  | 17 => 39
  | 18 => 83
  | 19 => 91
  | 20 => 35
  | 21 => 93
  | 22 => 90
  | 23 => 38
  | 24 => 49
  | 25 => 91
  | 26 => 29
  | 27 => 50
  | 28 => 92
  | 29 => 94
  | 30 => 83
  | 31 => 63
  | 32 => 52
  | 33 => 66
  | 34 => 10
  | 35 => 39
  | 36 => 88
  | 37 => 3
  | 38 => 34
  | 39 => 91
  | 40 => 25
  | 41 => 49
  | 42 => 1
  | 43 => 2
  | 44 => 31
  | 45 => 33
  | 46 => 14
  | 47 => 75
  | _ => 0

def fixedLiteralInvZeroRow_6 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 98
  | 1 => 13
  | 2 => 79
  | 3 => 20
  | 4 => 87
  | 5 => 100
  | 6 => 2
  | 7 => 86
  | 8 => 74
  | 9 => 45
  | 10 => 77
  | 11 => 43
  | 12 => 56
  | 13 => 17
  | 14 => 62
  | 15 => 0
  | 16 => 22
  | 17 => 52
  | 18 => 7
  | 19 => 8
  | 20 => 31
  | 21 => 50
  | 22 => 56
  | 23 => 40
  | 24 => 2
  | 25 => 33
  | 26 => 46
  | 27 => 96
  | 28 => 15
  | 29 => 53
  | 30 => 56
  | 31 => 90
  | 32 => 94
  | 33 => 47
  | 34 => 23
  | 35 => 36
  | 36 => 98
  | 37 => 7
  | 38 => 33
  | 39 => 70
  | 40 => 55
  | 41 => 46
  | 42 => 58
  | 43 => 70
  | 44 => 53
  | 45 => 29
  | 46 => 66
  | 47 => 61
  | _ => 0

def fixedLiteralInvZeroRow_7 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 45
  | 1 => 99
  | 2 => 31
  | 3 => 28
  | 4 => 63
  | 5 => 77
  | 6 => 72
  | 7 => 9
  | 8 => 85
  | 9 => 48
  | 10 => 35
  | 11 => 43
  | 12 => 35
  | 13 => 62
  | 14 => 85
  | 15 => 30
  | 16 => 52
  | 17 => 40
  | 18 => 82
  | 19 => 61
  | 20 => 90
  | 21 => 25
  | 22 => 69
  | 23 => 59
  | 24 => 31
  | 25 => 16
  | 26 => 32
  | 27 => 49
  | 28 => 60
  | 29 => 35
  | 30 => 4
  | 31 => 7
  | 32 => 41
  | 33 => 95
  | 34 => 99
  | 35 => 29
  | 36 => 13
  | 37 => 44
  | 38 => 21
  | 39 => 15
  | 40 => 28
  | 41 => 3
  | 42 => 49
  | 43 => 24
  | 44 => 47
  | 45 => 68
  | 46 => 46
  | 47 => 43
  | _ => 0

def fixedLiteralInvZeroRow_8 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 43
  | 1 => 19
  | 2 => 91
  | 3 => 35
  | 4 => 57
  | 5 => 28
  | 6 => 64
  | 7 => 90
  | 8 => 98
  | 9 => 71
  | 10 => 27
  | 11 => 46
  | 12 => 34
  | 13 => 1
  | 14 => 23
  | 15 => 83
  | 16 => 46
  | 17 => 37
  | 18 => 28
  | 19 => 56
  | 20 => 66
  | 21 => 30
  | 22 => 8
  | 23 => 29
  | 24 => 46
  | 25 => 5
  | 26 => 40
  | 27 => 85
  | 28 => 35
  | 29 => 10
  | 30 => 16
  | 31 => 30
  | 32 => 55
  | 33 => 57
  | 34 => 55
  | 35 => 75
  | 36 => 94
  | 37 => 60
  | 38 => 8
  | 39 => 16
  | 40 => 1
  | 41 => 6
  | 42 => 1
  | 43 => 92
  | 44 => 55
  | 45 => 91
  | 46 => 29
  | 47 => 84
  | _ => 0

def fixedLiteralInvZeroRow_9 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 73
  | 1 => 47
  | 2 => 27
  | 3 => 32
  | 4 => 77
  | 5 => 67
  | 6 => 37
  | 7 => 51
  | 8 => 7
  | 9 => 13
  | 10 => 98
  | 11 => 96
  | 12 => 19
  | 13 => 66
  | 14 => 64
  | 15 => 67
  | 16 => 90
  | 17 => 43
  | 18 => 49
  | 19 => 28
  | 20 => 4
  | 21 => 79
  | 22 => 37
  | 23 => 74
  | 24 => 91
  | 25 => 36
  | 26 => 40
  | 27 => 46
  | 28 => 23
  | 29 => 76
  | 30 => 54
  | 31 => 4
  | 32 => 66
  | 33 => 89
  | 34 => 37
  | 35 => 32
  | 36 => 1
  | 37 => 26
  | 38 => 93
  | 39 => 29
  | 40 => 86
  | 41 => 1
  | 42 => 3
  | 43 => 26
  | 44 => 41
  | 45 => 80
  | 46 => 57
  | 47 => 97
  | _ => 0

def fixedLiteralInvZeroRow_10 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 0
  | 1 => 65
  | 2 => 43
  | 3 => 93
  | 4 => 75
  | 5 => 73
  | 6 => 37
  | 7 => 24
  | 8 => 19
  | 9 => 48
  | 10 => 99
  | 11 => 32
  | 12 => 97
  | 13 => 45
  | 14 => 34
  | 15 => 25
  | 16 => 99
  | 17 => 86
  | 18 => 67
  | 19 => 9
  | 20 => 36
  | 21 => 50
  | 22 => 62
  | 23 => 44
  | 24 => 42
  | 25 => 98
  | 26 => 67
  | 27 => 19
  | 28 => 88
  | 29 => 76
  | 30 => 70
  | 31 => 63
  | 32 => 97
  | 33 => 0
  | 34 => 38
  | 35 => 28
  | 36 => 37
  | 37 => 68
  | 38 => 35
  | 39 => 59
  | 40 => 44
  | 41 => 79
  | 42 => 37
  | 43 => 5
  | 44 => 8
  | 45 => 33
  | 46 => 5
  | 47 => 0
  | _ => 0

def fixedLiteralInvZeroRow_11 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 13
  | 1 => 23
  | 2 => 92
  | 3 => 3
  | 4 => 44
  | 5 => 44
  | 6 => 29
  | 7 => 37
  | 8 => 16
  | 9 => 16
  | 10 => 34
  | 11 => 14
  | 12 => 20
  | 13 => 71
  | 14 => 37
  | 15 => 89
  | 16 => 69
  | 17 => 7
  | 18 => 77
  | 19 => 35
  | 20 => 67
  | 21 => 7
  | 22 => 36
  | 23 => 91
  | 24 => 95
  | 25 => 58
  | 26 => 29
  | 27 => 6
  | 28 => 4
  | 29 => 27
  | 30 => 27
  | 31 => 42
  | 32 => 94
  | 33 => 30
  | 34 => 51
  | 35 => 67
  | 36 => 20
  | 37 => 19
  | 38 => 18
  | 39 => 57
  | 40 => 9
  | 41 => 98
  | 42 => 9
  | 43 => 26
  | 44 => 0
  | 45 => 31
  | 46 => 84
  | 47 => 3
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvZeroRow_12 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 67
  | 1 => 45
  | 2 => 89
  | 3 => 4
  | 4 => 15
  | 5 => 25
  | 6 => 60
  | 7 => 1
  | 8 => 42
  | 9 => 49
  | 10 => 95
  | 11 => 0
  | 12 => 2
  | 13 => 97
  | 14 => 17
  | 15 => 98
  | 16 => 75
  | 17 => 55
  | 18 => 63
  | 19 => 59
  | 20 => 20
  | 21 => 80
  | 22 => 68
  | 23 => 51
  | 24 => 61
  | 25 => 23
  | 26 => 67
  | 27 => 9
  | 28 => 96
  | 29 => 39
  | 30 => 4
  | 31 => 70
  | 32 => 38
  | 33 => 86
  | 34 => 74
  | 35 => 32
  | 36 => 65
  | 37 => 41
  | 38 => 43
  | 39 => 21
  | 40 => 13
  | 41 => 40
  | 42 => 14
  | 43 => 72
  | 44 => 24
  | 45 => 13
  | 46 => 65
  | 47 => 22
  | _ => 0

def fixedLiteralInvZeroRow_13 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 47
  | 1 => 7
  | 2 => 35
  | 3 => 55
  | 4 => 21
  | 5 => 20
  | 6 => 13
  | 7 => 15
  | 8 => 18
  | 9 => 34
  | 10 => 35
  | 11 => 83
  | 12 => 28
  | 13 => 16
  | 14 => 99
  | 15 => 13
  | 16 => 92
  | 17 => 25
  | 18 => 72
  | 19 => 19
  | 20 => 93
  | 21 => 26
  | 22 => 95
  | 23 => 53
  | 24 => 86
  | 25 => 12
  | 26 => 47
  | 27 => 44
  | 28 => 7
  | 29 => 79
  | 30 => 16
  | 31 => 29
  | 32 => 66
  | 33 => 65
  | 34 => 16
  | 35 => 11
  | 36 => 32
  | 37 => 55
  | 38 => 44
  | 39 => 85
  | 40 => 63
  | 41 => 43
  | 42 => 75
  | 43 => 97
  | 44 => 43
  | 45 => 32
  | 46 => 68
  | 47 => 95
  | _ => 0

def fixedLiteralInvZeroRow_14 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 11
  | 1 => 48
  | 2 => 25
  | 3 => 51
  | 4 => 76
  | 5 => 11
  | 6 => 6
  | 7 => 12
  | 8 => 100
  | 9 => 89
  | 10 => 47
  | 11 => 18
  | 12 => 41
  | 13 => 24
  | 14 => 87
  | 15 => 20
  | 16 => 48
  | 17 => 26
  | 18 => 40
  | 19 => 65
  | 20 => 89
  | 21 => 48
  | 22 => 11
  | 23 => 94
  | 24 => 94
  | 25 => 63
  | 26 => 94
  | 27 => 90
  | 28 => 100
  | 29 => 44
  | 30 => 55
  | 31 => 81
  | 32 => 53
  | 33 => 41
  | 34 => 69
  | 35 => 64
  | 36 => 45
  | 37 => 90
  | 38 => 77
  | 39 => 36
  | 40 => 35
  | 41 => 38
  | 42 => 6
  | 43 => 63
  | 44 => 55
  | 45 => 57
  | 46 => 28
  | 47 => 48
  | _ => 0

def fixedLiteralInvZeroRow_15 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 65
  | 1 => 67
  | 2 => 3
  | 3 => 72
  | 4 => 33
  | 5 => 39
  | 6 => 50
  | 7 => 58
  | 8 => 62
  | 9 => 83
  | 10 => 81
  | 11 => 34
  | 12 => 56
  | 13 => 98
  | 14 => 99
  | 15 => 73
  | 16 => 49
  | 17 => 92
  | 18 => 20
  | 19 => 73
  | 20 => 48
  | 21 => 6
  | 22 => 64
  | 23 => 35
  | 24 => 1
  | 25 => 29
  | 26 => 22
  | 27 => 30
  | 28 => 48
  | 29 => 56
  | 30 => 76
  | 31 => 38
  | 32 => 83
  | 33 => 46
  | 34 => 1
  | 35 => 99
  | 36 => 9
  | 37 => 88
  | 38 => 69
  | 39 => 34
  | 40 => 8
  | 41 => 35
  | 42 => 80
  | 43 => 10
  | 44 => 49
  | 45 => 41
  | 46 => 13
  | 47 => 59
  | _ => 0

def fixedLiteralInvZeroRow_16 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 82
  | 1 => 54
  | 2 => 81
  | 3 => 57
  | 4 => 36
  | 5 => 24
  | 6 => 18
  | 7 => 30
  | 8 => 41
  | 9 => 89
  | 10 => 98
  | 11 => 38
  | 12 => 99
  | 13 => 3
  | 14 => 20
  | 15 => 37
  | 16 => 93
  | 17 => 36
  | 18 => 44
  | 19 => 1
  | 20 => 92
  | 21 => 81
  | 22 => 81
  | 23 => 69
  | 24 => 25
  | 25 => 60
  | 26 => 64
  | 27 => 21
  | 28 => 19
  | 29 => 77
  | 30 => 45
  | 31 => 40
  | 32 => 45
  | 33 => 92
  | 34 => 66
  | 35 => 14
  | 36 => 86
  | 37 => 24
  | 38 => 45
  | 39 => 1
  | 40 => 4
  | 41 => 39
  | 42 => 11
  | 43 => 43
  | 44 => 66
  | 45 => 81
  | 46 => 33
  | 47 => 60
  | _ => 0

def fixedLiteralInvZeroRow_17 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 10
  | 1 => 56
  | 2 => 84
  | 3 => 1
  | 4 => 96
  | 5 => 23
  | 6 => 31
  | 7 => 64
  | 8 => 96
  | 9 => 84
  | 10 => 100
  | 11 => 19
  | 12 => 49
  | 13 => 72
  | 14 => 23
  | 15 => 94
  | 16 => 18
  | 17 => 61
  | 18 => 65
  | 19 => 53
  | 20 => 33
  | 21 => 4
  | 22 => 1
  | 23 => 37
  | 24 => 6
  | 25 => 57
  | 26 => 52
  | 27 => 90
  | 28 => 25
  | 29 => 0
  | 30 => 46
  | 31 => 53
  | 32 => 49
  | 33 => 71
  | 34 => 30
  | 35 => 34
  | 36 => 8
  | 37 => 61
  | 38 => 19
  | 39 => 16
  | 40 => 36
  | 41 => 47
  | 42 => 92
  | 43 => 47
  | 44 => 1
  | 45 => 84
  | 46 => 90
  | 47 => 75
  | _ => 0

def fixedLiteralInvZeroRow_18 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 74
  | 1 => 3
  | 2 => 32
  | 3 => 0
  | 4 => 33
  | 5 => 42
  | 6 => 73
  | 7 => 13
  | 8 => 73
  | 9 => 96
  | 10 => 42
  | 11 => 32
  | 12 => 67
  | 13 => 7
  | 14 => 61
  | 15 => 16
  | 16 => 37
  | 17 => 80
  | 18 => 45
  | 19 => 11
  | 20 => 80
  | 21 => 47
  | 22 => 98
  | 23 => 10
  | 24 => 60
  | 25 => 40
  | 26 => 39
  | 27 => 56
  | 28 => 8
  | 29 => 79
  | 30 => 30
  | 31 => 86
  | 32 => 52
  | 33 => 66
  | 34 => 6
  | 35 => 62
  | 36 => 74
  | 37 => 17
  | 38 => 87
  | 39 => 86
  | 40 => 46
  | 41 => 2
  | 42 => 21
  | 43 => 2
  | 44 => 74
  | 45 => 15
  | 46 => 62
  | 47 => 98
  | _ => 0

def fixedLiteralInvZeroRow_19 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 2
  | 1 => 56
  | 2 => 11
  | 3 => 86
  | 4 => 98
  | 5 => 51
  | 6 => 54
  | 7 => 56
  | 8 => 21
  | 9 => 2
  | 10 => 94
  | 11 => 60
  | 12 => 73
  | 13 => 42
  | 14 => 27
  | 15 => 33
  | 16 => 10
  | 17 => 13
  | 18 => 46
  | 19 => 25
  | 20 => 51
  | 21 => 23
  | 22 => 13
  | 23 => 2
  | 24 => 50
  | 25 => 40
  | 26 => 43
  | 27 => 58
  | 28 => 12
  | 29 => 6
  | 30 => 0
  | 31 => 68
  | 32 => 77
  | 33 => 8
  | 34 => 35
  | 35 => 38
  | 36 => 57
  | 37 => 2
  | 38 => 25
  | 39 => 70
  | 40 => 21
  | 41 => 79
  | 42 => 72
  | 43 => 49
  | 44 => 17
  | 45 => 64
  | 46 => 85
  | 47 => 35
  | _ => 0

def fixedLiteralInvZeroRow_20 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 82
  | 1 => 42
  | 2 => 4
  | 3 => 70
  | 4 => 89
  | 5 => 46
  | 6 => 46
  | 7 => 78
  | 8 => 16
  | 9 => 4
  | 10 => 44
  | 11 => 31
  | 12 => 15
  | 13 => 88
  | 14 => 34
  | 15 => 91
  | 16 => 52
  | 17 => 31
  | 18 => 35
  | 19 => 30
  | 20 => 84
  | 21 => 14
  | 22 => 93
  | 23 => 47
  | 24 => 39
  | 25 => 88
  | 26 => 35
  | 27 => 85
  | 28 => 98
  | 29 => 46
  | 30 => 35
  | 31 => 82
  | 32 => 39
  | 33 => 50
  | 34 => 38
  | 35 => 53
  | 36 => 45
  | 37 => 70
  | 38 => 50
  | 39 => 87
  | 40 => 1
  | 41 => 82
  | 42 => 62
  | 43 => 11
  | 44 => 37
  | 45 => 30
  | 46 => 21
  | 47 => 25
  | _ => 0

def fixedLiteralInvZeroRow_21 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 3
  | 1 => 73
  | 2 => 75
  | 3 => 7
  | 4 => 25
  | 5 => 97
  | 6 => 13
  | 7 => 24
  | 8 => 50
  | 9 => 1
  | 10 => 41
  | 11 => 50
  | 12 => 89
  | 13 => 0
  | 14 => 9
  | 15 => 54
  | 16 => 74
  | 17 => 74
  | 18 => 76
  | 19 => 32
  | 20 => 44
  | 21 => 64
  | 22 => 27
  | 23 => 88
  | 24 => 3
  | 25 => 91
  | 26 => 61
  | 27 => 2
  | 28 => 13
  | 29 => 5
  | 30 => 99
  | 31 => 65
  | 32 => 62
  | 33 => 26
  | 34 => 14
  | 35 => 47
  | 36 => 2
  | 37 => 34
  | 38 => 59
  | 39 => 52
  | 40 => 55
  | 41 => 19
  | 42 => 68
  | 43 => 19
  | 44 => 24
  | 45 => 88
  | 46 => 95
  | 47 => 91
  | _ => 0

def fixedLiteralInvZeroRow_22 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 36
  | 1 => 85
  | 2 => 80
  | 3 => 11
  | 4 => 85
  | 5 => 34
  | 6 => 11
  | 7 => 4
  | 8 => 77
  | 9 => 40
  | 10 => 12
  | 11 => 98
  | 12 => 74
  | 13 => 7
  | 14 => 21
  | 15 => 67
  | 16 => 85
  | 17 => 65
  | 18 => 78
  | 19 => 77
  | 20 => 89
  | 21 => 6
  | 22 => 47
  | 23 => 59
  | 24 => 55
  | 25 => 22
  | 26 => 3
  | 27 => 9
  | 28 => 58
  | 29 => 44
  | 30 => 62
  | 31 => 75
  | 32 => 93
  | 33 => 1
  | 34 => 23
  | 35 => 68
  | 36 => 7
  | 37 => 18
  | 38 => 67
  | 39 => 78
  | 40 => 60
  | 41 => 80
  | 42 => 94
  | 43 => 72
  | 44 => 98
  | 45 => 92
  | 46 => 66
  | 47 => 82
  | _ => 0

def fixedLiteralInvZeroRow_23 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 25
  | 1 => 12
  | 2 => 33
  | 3 => 39
  | 4 => 92
  | 5 => 16
  | 6 => 54
  | 7 => 0
  | 8 => 86
  | 9 => 32
  | 10 => 10
  | 11 => 42
  | 12 => 27
  | 13 => 96
  | 14 => 65
  | 15 => 21
  | 16 => 48
  | 17 => 19
  | 18 => 23
  | 19 => 8
  | 20 => 8
  | 21 => 53
  | 22 => 24
  | 23 => 42
  | 24 => 73
  | 25 => 14
  | 26 => 25
  | 27 => 36
  | 28 => 23
  | 29 => 23
  | 30 => 68
  | 31 => 84
  | 32 => 71
  | 33 => 18
  | 34 => 31
  | 35 => 95
  | 36 => 0
  | 37 => 94
  | 38 => 66
  | 39 => 54
  | 40 => 22
  | 41 => 35
  | 42 => 83
  | 43 => 55
  | 44 => 92
  | 45 => 12
  | 46 => 79
  | 47 => 65
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvZeroRow_24 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 34
  | 1 => 66
  | 2 => 65
  | 3 => 72
  | 4 => 86
  | 5 => 11
  | 6 => 4
  | 7 => 58
  | 8 => 2
  | 9 => 12
  | 10 => 41
  | 11 => 72
  | 12 => 1
  | 13 => 98
  | 14 => 70
  | 15 => 18
  | 16 => 96
  | 17 => 8
  | 18 => 55
  | 19 => 37
  | 20 => 69
  | 21 => 54
  | 22 => 75
  | 23 => 63
  | 24 => 49
  | 25 => 51
  | 26 => 100
  | 27 => 96
  | 28 => 71
  | 29 => 94
  | 30 => 22
  | 31 => 36
  | 32 => 29
  | 33 => 83
  | 34 => 71
  | 35 => 4
  | 36 => 29
  | 37 => 5
  | 38 => 13
  | 39 => 42
  | 40 => 95
  | 41 => 47
  | 42 => 88
  | 43 => 56
  | 44 => 45
  | 45 => 33
  | 46 => 16
  | 47 => 57
  | _ => 0

def fixedLiteralInvZeroRow_25 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 0
  | 1 => 51
  | 2 => 28
  | 3 => 83
  | 4 => 54
  | 5 => 1
  | 6 => 99
  | 7 => 74
  | 8 => 17
  | 9 => 13
  | 10 => 74
  | 11 => 83
  | 12 => 1
  | 13 => 75
  | 14 => 57
  | 15 => 95
  | 16 => 74
  | 17 => 72
  | 18 => 81
  | 19 => 87
  | 20 => 55
  | 21 => 64
  | 22 => 35
  | 23 => 12
  | 24 => 28
  | 25 => 46
  | 26 => 20
  | 27 => 16
  | 28 => 47
  | 29 => 88
  | 30 => 51
  | 31 => 92
  | 32 => 32
  | 33 => 21
  | 34 => 72
  | 35 => 16
  | 36 => 84
  | 37 => 53
  | 38 => 98
  | 39 => 36
  | 40 => 81
  | 41 => 34
  | 42 => 49
  | 43 => 75
  | 44 => 87
  | 45 => 72
  | 46 => 77
  | 47 => 18
  | _ => 0

def fixedLiteralInvZeroRow_26 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 17
  | 1 => 49
  | 2 => 82
  | 3 => 50
  | 4 => 90
  | 5 => 1
  | 6 => 54
  | 7 => 43
  | 8 => 49
  | 9 => 37
  | 10 => 37
  | 11 => 48
  | 12 => 66
  | 13 => 73
  | 14 => 64
  | 15 => 72
  | 16 => 77
  | 17 => 90
  | 18 => 92
  | 19 => 85
  | 20 => 28
  | 21 => 78
  | 22 => 19
  | 23 => 9
  | 24 => 5
  | 25 => 48
  | 26 => 69
  | 27 => 11
  | 28 => 4
  | 29 => 54
  | 30 => 5
  | 31 => 90
  | 32 => 63
  | 33 => 72
  | 34 => 36
  | 35 => 92
  | 36 => 84
  | 37 => 81
  | 38 => 22
  | 39 => 1
  | 40 => 53
  | 41 => 19
  | 42 => 59
  | 43 => 64
  | 44 => 30
  | 45 => 31
  | 46 => 59
  | 47 => 82
  | _ => 0

def fixedLiteralInvZeroRow_27 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 56
  | 1 => 50
  | 2 => 61
  | 3 => 18
  | 4 => 83
  | 5 => 33
  | 6 => 83
  | 7 => 68
  | 8 => 86
  | 9 => 3
  | 10 => 99
  | 11 => 81
  | 12 => 51
  | 13 => 94
  | 14 => 86
  | 15 => 14
  | 16 => 53
  | 17 => 16
  | 18 => 7
  | 19 => 81
  | 20 => 53
  | 21 => 100
  | 22 => 76
  | 23 => 97
  | 24 => 65
  | 25 => 30
  | 26 => 66
  | 27 => 61
  | 28 => 50
  | 29 => 23
  | 30 => 74
  | 31 => 49
  | 32 => 52
  | 33 => 33
  | 34 => 3
  | 35 => 62
  | 36 => 98
  | 37 => 26
  | 38 => 33
  | 39 => 66
  | 40 => 60
  | 41 => 34
  | 42 => 29
  | 43 => 34
  | 44 => 84
  | 45 => 59
  | 46 => 40
  | 47 => 56
  | _ => 0

def fixedLiteralInvZeroRow_28 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 9
  | 1 => 56
  | 2 => 64
  | 3 => 61
  | 4 => 43
  | 5 => 100
  | 6 => 71
  | 7 => 5
  | 8 => 59
  | 9 => 20
  | 10 => 58
  | 11 => 29
  | 12 => 47
  | 13 => 6
  | 14 => 94
  | 15 => 25
  | 16 => 100
  | 17 => 35
  | 18 => 77
  | 19 => 0
  | 20 => 44
  | 21 => 56
  | 22 => 37
  | 23 => 34
  | 24 => 21
  | 25 => 7
  | 26 => 53
  | 27 => 66
  | 28 => 73
  | 29 => 44
  | 30 => 36
  | 31 => 6
  | 32 => 44
  | 33 => 29
  | 34 => 38
  | 35 => 53
  | 36 => 51
  | 37 => 59
  | 38 => 29
  | 39 => 61
  | 40 => 20
  | 41 => 41
  | 42 => 60
  | 43 => 55
  | 44 => 60
  | 45 => 80
  | 46 => 81
  | 47 => 89
  | _ => 0

def fixedLiteralInvZeroRow_29 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 1
  | 1 => 43
  | 2 => 33
  | 3 => 71
  | 4 => 91
  | 5 => 35
  | 6 => 85
  | 7 => 62
  | 8 => 37
  | 9 => 96
  | 10 => 34
  | 11 => 59
  | 12 => 60
  | 13 => 24
  | 14 => 99
  | 15 => 6
  | 16 => 25
  | 17 => 88
  | 18 => 30
  | 19 => 96
  | 20 => 88
  | 21 => 36
  | 22 => 18
  | 23 => 55
  | 24 => 17
  | 25 => 72
  | 26 => 73
  | 27 => 13
  | 28 => 38
  | 29 => 65
  | 30 => 26
  | 31 => 97
  | 32 => 32
  | 33 => 58
  | 34 => 71
  | 35 => 1
  | 36 => 26
  | 37 => 25
  | 38 => 97
  | 39 => 96
  | 40 => 5
  | 41 => 43
  | 42 => 79
  | 43 => 4
  | 44 => 26
  | 45 => 25
  | 46 => 15
  | 47 => 19
  | _ => 0

def fixedLiteralInvZeroRow_30 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 90
  | 1 => 73
  | 2 => 82
  | 3 => 36
  | 4 => 89
  | 5 => 69
  | 6 => 53
  | 7 => 20
  | 8 => 16
  | 9 => 23
  | 10 => 95
  | 11 => 22
  | 12 => 57
  | 13 => 84
  | 14 => 31
  | 15 => 71
  | 16 => 10
  | 17 => 93
  | 18 => 24
  | 19 => 7
  | 20 => 10
  | 21 => 11
  | 22 => 96
  | 23 => 24
  | 24 => 34
  | 25 => 96
  | 26 => 52
  | 27 => 45
  | 28 => 77
  | 29 => 2
  | 30 => 65
  | 31 => 27
  | 32 => 38
  | 33 => 90
  | 34 => 87
  | 35 => 16
  | 36 => 91
  | 37 => 91
  | 38 => 70
  | 39 => 16
  | 40 => 95
  | 41 => 51
  | 42 => 1
  | 43 => 14
  | 44 => 40
  | 45 => 95
  | 46 => 54
  | 47 => 17
  | _ => 0

def fixedLiteralInvZeroRow_31 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 74
  | 1 => 24
  | 2 => 82
  | 3 => 63
  | 4 => 60
  | 5 => 30
  | 6 => 53
  | 7 => 0
  | 8 => 50
  | 9 => 10
  | 10 => 33
  | 11 => 53
  | 12 => 52
  | 13 => 43
  | 14 => 31
  | 15 => 6
  | 16 => 90
  | 17 => 5
  | 18 => 85
  | 19 => 13
  | 20 => 63
  | 21 => 35
  | 22 => 77
  | 23 => 75
  | 24 => 24
  | 25 => 37
  | 26 => 99
  | 27 => 26
  | 28 => 1
  | 29 => 6
  | 30 => 48
  | 31 => 97
  | 32 => 66
  | 33 => 20
  | 34 => 53
  | 35 => 47
  | 36 => 64
  | 37 => 43
  | 38 => 84
  | 39 => 49
  | 40 => 0
  | 41 => 5
  | 42 => 75
  | 43 => 45
  | 44 => 63
  | 45 => 33
  | 46 => 54
  | 47 => 92
  | _ => 0

def fixedLiteralInvZeroRow_32 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 57
  | 1 => 29
  | 2 => 97
  | 3 => 44
  | 4 => 54
  | 5 => 88
  | 6 => 47
  | 7 => 38
  | 8 => 90
  | 9 => 17
  | 10 => 49
  | 11 => 57
  | 12 => 62
  | 13 => 45
  | 14 => 69
  | 15 => 56
  | 16 => 96
  | 17 => 27
  | 18 => 80
  | 19 => 78
  | 20 => 21
  | 21 => 67
  | 22 => 15
  | 23 => 56
  | 24 => 71
  | 25 => 21
  | 26 => 53
  | 27 => 36
  | 28 => 62
  | 29 => 90
  | 30 => 76
  | 31 => 38
  | 32 => 19
  | 33 => 72
  | 34 => 17
  | 35 => 36
  | 36 => 84
  | 37 => 36
  | 38 => 55
  | 39 => 71
  | 40 => 51
  | 41 => 95
  | 42 => 36
  | 43 => 64
  | 44 => 84
  | 45 => 2
  | 46 => 6
  | 47 => 31
  | _ => 0

def fixedLiteralInvZeroRow_33 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 20
  | 1 => 23
  | 2 => 9
  | 3 => 42
  | 4 => 76
  | 5 => 68
  | 6 => 62
  | 7 => 97
  | 8 => 62
  | 9 => 92
  | 10 => 72
  | 11 => 21
  | 12 => 27
  | 13 => 34
  | 14 => 81
  | 15 => 29
  | 16 => 58
  | 17 => 86
  | 18 => 63
  | 19 => 28
  | 20 => 59
  | 21 => 15
  | 22 => 35
  | 23 => 26
  | 24 => 16
  | 25 => 57
  | 26 => 40
  | 27 => 59
  | 28 => 15
  | 29 => 25
  | 30 => 16
  | 31 => 64
  | 32 => 61
  | 33 => 81
  | 34 => 10
  | 35 => 74
  | 36 => 36
  | 37 => 79
  | 38 => 21
  | 39 => 34
  | 40 => 86
  | 41 => 26
  | 42 => 7
  | 43 => 56
  | 44 => 81
  | 45 => 13
  | 46 => 97
  | 47 => 31
  | _ => 0

def fixedLiteralInvZeroRow_34 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 90
  | 1 => 70
  | 2 => 65
  | 3 => 60
  | 4 => 25
  | 5 => 29
  | 6 => 31
  | 7 => 24
  | 8 => 92
  | 9 => 95
  | 10 => 85
  | 11 => 75
  | 12 => 51
  | 13 => 46
  | 14 => 30
  | 15 => 56
  | 16 => 15
  | 17 => 47
  | 18 => 64
  | 19 => 96
  | 20 => 50
  | 21 => 68
  | 22 => 68
  | 23 => 46
  | 24 => 1
  | 25 => 13
  | 26 => 64
  | 27 => 89
  | 28 => 34
  | 29 => 96
  | 30 => 3
  | 31 => 47
  | 32 => 30
  | 33 => 9
  | 34 => 82
  | 35 => 69
  | 36 => 83
  | 37 => 24
  | 38 => 74
  | 39 => 68
  | 40 => 75
  | 41 => 94
  | 42 => 78
  | 43 => 23
  | 44 => 78
  | 45 => 33
  | 46 => 3
  | 47 => 21
  | _ => 0

def fixedLiteralInvZeroRow_35 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 94
  | 1 => 63
  | 2 => 35
  | 3 => 29
  | 4 => 14
  | 5 => 97
  | 6 => 15
  | 7 => 88
  | 8 => 55
  | 9 => 44
  | 10 => 36
  | 11 => 99
  | 12 => 71
  | 13 => 50
  | 14 => 93
  | 15 => 57
  | 16 => 75
  | 17 => 79
  | 18 => 13
  | 19 => 55
  | 20 => 5
  | 21 => 83
  | 22 => 26
  | 23 => 51
  | 24 => 19
  | 25 => 18
  | 26 => 24
  | 27 => 56
  | 28 => 38
  | 29 => 89
  | 30 => 5
  | 31 => 48
  | 32 => 95
  | 33 => 48
  | 34 => 70
  | 35 => 87
  | 36 => 64
  | 37 => 44
  | 38 => 30
  | 39 => 87
  | 40 => 43
  | 41 => 89
  | 42 => 12
  | 43 => 23
  | 44 => 42
  | 45 => 35
  | 46 => 38
  | 47 => 79
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralInvZeroRow_36 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 59
  | 1 => 90
  | 2 => 16
  | 3 => 21
  | 4 => 28
  | 5 => 82
  | 6 => 32
  | 7 => 82
  | 8 => 29
  | 9 => 35
  | 10 => 77
  | 11 => 58
  | 12 => 29
  | 13 => 80
  | 14 => 6
  | 15 => 56
  | 16 => 38
  | 17 => 43
  | 18 => 100
  | 19 => 43
  | 20 => 29
  | 21 => 73
  | 22 => 75
  | 23 => 7
  | 24 => 76
  | 25 => 53
  | 26 => 77
  | 27 => 36
  | 28 => 27
  | 29 => 78
  | 30 => 14
  | 31 => 91
  | 32 => 83
  | 33 => 6
  | 34 => 43
  | 35 => 40
  | 36 => 20
  | 37 => 42
  | 38 => 53
  | 39 => 48
  | 40 => 59
  | 41 => 2
  | 42 => 61
  | 43 => 88
  | 44 => 45
  | 45 => 69
  | 46 => 71
  | 47 => 70
  | _ => 0

def fixedLiteralInvZeroRow_37 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 37
  | 1 => 12
  | 2 => 64
  | 3 => 86
  | 4 => 56
  | 5 => 90
  | 6 => 61
  | 7 => 16
  | 8 => 14
  | 9 => 9
  | 10 => 22
  | 11 => 16
  | 12 => 18
  | 13 => 56
  | 14 => 93
  | 15 => 61
  | 16 => 60
  | 17 => 42
  | 18 => 19
  | 19 => 90
  | 20 => 75
  | 21 => 23
  | 22 => 18
  | 23 => 82
  | 24 => 20
  | 25 => 8
  | 26 => 55
  | 27 => 0
  | 28 => 6
  | 29 => 61
  | 30 => 61
  | 31 => 62
  | 32 => 5
  | 33 => 43
  | 34 => 95
  | 35 => 12
  | 36 => 46
  | 37 => 45
  | 38 => 13
  | 39 => 20
  | 40 => 75
  | 41 => 41
  | 42 => 72
  | 43 => 77
  | 44 => 66
  | 45 => 28
  | 46 => 33
  | 47 => 82
  | _ => 0

def fixedLiteralInvZeroRow_38 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 58
  | 1 => 98
  | 2 => 95
  | 3 => 28
  | 4 => 14
  | 5 => 58
  | 6 => 73
  | 7 => 12
  | 8 => 76
  | 9 => 50
  | 10 => 23
  | 11 => 71
  | 12 => 25
  | 13 => 48
  | 14 => 52
  | 15 => 14
  | 16 => 17
  | 17 => 5
  | 18 => 21
  | 19 => 75
  | 20 => 92
  | 21 => 95
  | 22 => 74
  | 23 => 20
  | 24 => 95
  | 25 => 33
  | 26 => 79
  | 27 => 31
  | 28 => 60
  | 29 => 77
  | 30 => 57
  | 31 => 69
  | 32 => 8
  | 33 => 88
  | 34 => 76
  | 35 => 40
  | 36 => 14
  | 37 => 88
  | 38 => 44
  | 39 => 78
  | 40 => 46
  | 41 => 33
  | 42 => 5
  | 43 => 50
  | 44 => 100
  | 45 => 55
  | 46 => 50
  | 47 => 57
  | _ => 0

def fixedLiteralInvZeroRow_39 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 19
  | 1 => 65
  | 2 => 74
  | 3 => 28
  | 4 => 86
  | 5 => 79
  | 6 => 52
  | 7 => 7
  | 8 => 43
  | 9 => 13
  | 10 => 95
  | 11 => 59
  | 12 => 15
  | 13 => 31
  | 14 => 65
  | 15 => 25
  | 16 => 9
  | 17 => 24
  | 18 => 10
  | 19 => 62
  | 20 => 47
  | 21 => 14
  | 22 => 55
  | 23 => 70
  | 24 => 49
  | 25 => 11
  | 26 => 61
  | 27 => 93
  | 28 => 3
  | 29 => 31
  | 30 => 25
  | 31 => 61
  | 32 => 2
  | 33 => 11
  | 34 => 93
  | 35 => 99
  | 36 => 69
  | 37 => 50
  | 38 => 99
  | 39 => 46
  | 40 => 10
  | 41 => 6
  | 42 => 71
  | 43 => 20
  | 44 => 20
  | 45 => 52
  | 46 => 30
  | 47 => 77
  | _ => 0

def fixedLiteralInvZeroRow_40 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 67
  | 1 => 24
  | 2 => 30
  | 3 => 92
  | 4 => 22
  | 5 => 69
  | 6 => 63
  | 7 => 95
  | 8 => 76
  | 9 => 81
  | 10 => 61
  | 11 => 69
  | 12 => 14
  | 13 => 19
  | 14 => 50
  | 15 => 97
  | 16 => 93
  | 17 => 0
  | 18 => 48
  | 19 => 1
  | 20 => 40
  | 21 => 22
  | 22 => 15
  | 23 => 54
  | 24 => 19
  | 25 => 59
  | 26 => 100
  | 27 => 3
  | 28 => 3
  | 29 => 35
  | 30 => 87
  | 31 => 45
  | 32 => 4
  | 33 => 34
  | 34 => 28
  | 35 => 16
  | 36 => 27
  | 37 => 50
  | 38 => 54
  | 39 => 11
  | 40 => 32
  | 41 => 25
  | 42 => 85
  | 43 => 29
  | 44 => 73
  | 45 => 89
  | 46 => 5
  | 47 => 15
  | _ => 0

def fixedLiteralInvZeroRow_41 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 73
  | 1 => 66
  | 2 => 14
  | 3 => 16
  | 4 => 14
  | 5 => 11
  | 6 => 78
  | 7 => 17
  | 8 => 44
  | 9 => 80
  | 10 => 52
  | 11 => 19
  | 12 => 9
  | 13 => 7
  | 14 => 57
  | 15 => 98
  | 16 => 48
  | 17 => 71
  | 18 => 15
  | 19 => 58
  | 20 => 54
  | 21 => 0
  | 22 => 23
  | 23 => 14
  | 24 => 20
  | 25 => 11
  | 26 => 65
  | 27 => 42
  | 28 => 15
  | 29 => 59
  | 30 => 75
  | 31 => 25
  | 32 => 16
  | 33 => 89
  | 34 => 92
  | 35 => 32
  | 36 => 80
  | 37 => 19
  | 38 => 9
  | 39 => 64
  | 40 => 62
  | 41 => 29
  | 42 => 89
  | 43 => 58
  | 44 => 75
  | 45 => 29
  | 46 => 69
  | 47 => 50
  | _ => 0

def fixedLiteralInvZeroRow_42 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 12
  | 1 => 97
  | 2 => 13
  | 3 => 49
  | 4 => 81
  | 5 => 58
  | 6 => 83
  | 7 => 49
  | 8 => 50
  | 9 => 71
  | 10 => 1
  | 11 => 33
  | 12 => 35
  | 13 => 93
  | 14 => 62
  | 15 => 5
  | 16 => 49
  | 17 => 91
  | 18 => 27
  | 19 => 26
  | 20 => 72
  | 21 => 34
  | 22 => 70
  | 23 => 68
  | 24 => 61
  | 25 => 93
  | 26 => 63
  | 27 => 92
  | 28 => 41
  | 29 => 62
  | 30 => 27
  | 31 => 4
  | 32 => 2
  | 33 => 22
  | 34 => 20
  | 35 => 62
  | 36 => 66
  | 37 => 5
  | 38 => 93
  | 39 => 33
  | 40 => 43
  | 41 => 35
  | 42 => 25
  | 43 => 2
  | 44 => 46
  | 45 => 72
  | 46 => 25
  | 47 => 45
  | _ => 0

def fixedLiteralInvZeroRow_43 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 63
  | 1 => 83
  | 2 => 3
  | 3 => 18
  | 4 => 75
  | 5 => 100
  | 6 => 50
  | 7 => 51
  | 8 => 90
  | 9 => 56
  | 10 => 17
  | 11 => 78
  | 12 => 87
  | 13 => 77
  | 14 => 82
  | 15 => 5
  | 16 => 32
  | 17 => 2
  | 18 => 28
  | 19 => 4
  | 20 => 92
  | 21 => 62
  | 22 => 52
  | 23 => 98
  | 24 => 73
  | 25 => 79
  | 26 => 10
  | 27 => 53
  | 28 => 63
  | 29 => 35
  | 30 => 86
  | 31 => 77
  | 32 => 84
  | 33 => 95
  | 34 => 12
  | 35 => 83
  | 36 => 14
  | 37 => 64
  | 38 => 12
  | 39 => 55
  | 40 => 72
  | 41 => 53
  | 42 => 39
  | 43 => 24
  | 44 => 85
  | 45 => 29
  | 46 => 7
  | 47 => 40
  | _ => 0

def fixedLiteralInvZeroRow_44 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 23
  | 1 => 100
  | 2 => 65
  | 3 => 48
  | 4 => 89
  | 5 => 28
  | 6 => 70
  | 7 => 84
  | 8 => 55
  | 9 => 3
  | 10 => 8
  | 11 => 46
  | 12 => 80
  | 13 => 61
  | 14 => 31
  | 15 => 54
  | 16 => 75
  | 17 => 47
  | 18 => 66
  | 19 => 45
  | 20 => 74
  | 21 => 51
  | 22 => 9
  | 23 => 28
  | 24 => 3
  | 25 => 64
  | 26 => 56
  | 27 => 91
  | 28 => 61
  | 29 => 96
  | 30 => 83
  | 31 => 23
  | 32 => 97
  | 33 => 16
  | 34 => 63
  | 35 => 92
  | 36 => 100
  | 37 => 68
  | 38 => 14
  | 39 => 10
  | 40 => 34
  | 41 => 75
  | 42 => 53
  | 43 => 31
  | 44 => 52
  | 45 => 80
  | 46 => 59
  | 47 => 52
  | _ => 0

def fixedLiteralInvZeroRow_45 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 90
  | 1 => 27
  | 2 => 92
  | 3 => 66
  | 4 => 93
  | 5 => 72
  | 6 => 99
  | 7 => 100
  | 8 => 51
  | 9 => 2
  | 10 => 64
  | 11 => 31
  | 12 => 94
  | 13 => 33
  | 14 => 90
  | 15 => 36
  | 16 => 2
  | 17 => 98
  | 18 => 70
  | 19 => 20
  | 20 => 31
  | 21 => 15
  | 22 => 7
  | 23 => 88
  | 24 => 87
  | 25 => 24
  | 26 => 44
  | 27 => 97
  | 28 => 54
  | 29 => 40
  | 30 => 100
  | 31 => 74
  | 32 => 75
  | 33 => 46
  | 34 => 12
  | 35 => 88
  | 36 => 90
  | 37 => 86
  | 38 => 37
  | 39 => 1
  | 40 => 2
  | 41 => 59
  | 42 => 48
  | 43 => 31
  | 44 => 74
  | 45 => 12
  | 46 => 61
  | 47 => 54
  | _ => 0

def fixedLiteralInvZeroRow_46 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 49
  | 1 => 66
  | 2 => 17
  | 3 => 48
  | 4 => 7
  | 5 => 7
  | 6 => 75
  | 7 => 6
  | 8 => 20
  | 9 => 66
  | 10 => 84
  | 11 => 96
  | 12 => 20
  | 13 => 91
  | 14 => 73
  | 15 => 1
  | 16 => 77
  | 17 => 67
  | 18 => 62
  | 19 => 71
  | 20 => 26
  | 21 => 39
  | 22 => 73
  | 23 => 71
  | 24 => 1
  | 25 => 24
  | 26 => 92
  | 27 => 78
  | 28 => 2
  | 29 => 28
  | 30 => 50
  | 31 => 27
  | 32 => 95
  | 33 => 85
  | 34 => 68
  | 35 => 50
  | 36 => 43
  | 37 => 46
  | 38 => 45
  | 39 => 41
  | 40 => 82
  | 41 => 83
  | 42 => 92
  | 43 => 86
  | 44 => 42
  | 45 => 60
  | 46 => 84
  | 47 => 26
  | _ => 0

def fixedLiteralInvZeroRow_47 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 96
  | 1 => 52
  | 2 => 10
  | 3 => 8
  | 4 => 20
  | 5 => 36
  | 6 => 72
  | 7 => 100
  | 8 => 25
  | 9 => 24
  | 10 => 50
  | 11 => 67
  | 12 => 17
  | 13 => 28
  | 14 => 77
  | 15 => 21
  | 16 => 85
  | 17 => 17
  | 18 => 84
  | 19 => 65
  | 20 => 65
  | 21 => 65
  | 22 => 85
  | 23 => 76
  | 24 => 24
  | 25 => 20
  | 26 => 63
  | 27 => 40
  | 28 => 60
  | 29 => 42
  | 30 => 8
  | 31 => 60
  | 32 => 87
  | 33 => 84
  | 34 => 36
  | 35 => 26
  | 36 => 9
  | 37 => 25
  | 38 => 0
  | 39 => 74
  | 40 => 1
  | 41 => 21
  | 42 => 19
  | 43 => 44
  | 44 => 4
  | 45 => 14
  | 46 => 1
  | 47 => 99
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModZeroRow_0 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 84
  | 1 => 30
  | 2 => 43
  | 3 => 92
  | 4 => 4
  | 5 => 20
  | 6 => 53
  | 7 => 17
  | 8 => 32
  | 9 => 35
  | 10 => 46
  | 11 => 88
  | 12 => 2
  | 13 => 2
  | 14 => 38
  | 15 => 14
  | 16 => 67
  | 17 => 93
  | 18 => 25
  | 19 => 14
  | 20 => 56
  | 21 => 87
  | 22 => 71
  | 23 => 48
  | 24 => 77
  | 25 => 97
  | 26 => 45
  | 27 => 100
  | 28 => 86
  | 29 => 94
  | 30 => 31
  | 31 => 64
  | 32 => 76
  | 33 => 3
  | 34 => 53
  | 35 => 64
  | 36 => 90
  | 37 => 93
  | 38 => 93
  | 39 => 19
  | 40 => 16
  | 41 => 19
  | 42 => 71
  | 43 => 87
  | 44 => 76
  | 45 => 7
  | 46 => 22
  | 47 => 4
  | _ => 0

def fixedLiteralModZeroRow_1 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 50
  | 1 => 64
  | 2 => 82
  | 3 => 46
  | 4 => 22
  | 5 => 78
  | 6 => 44
  | 7 => 28
  | 8 => 40
  | 9 => 41
  | 10 => 65
  | 11 => 8
  | 12 => 41
  | 13 => 69
  | 14 => 54
  | 15 => 77
  | 16 => 62
  | 17 => 44
  | 18 => 38
  | 19 => 67
  | 20 => 14
  | 21 => 98
  | 22 => 56
  | 23 => 45
  | 24 => 73
  | 25 => 54
  | 26 => 87
  | 27 => 29
  | 28 => 61
  | 29 => 73
  | 30 => 76
  | 31 => 81
  | 32 => 57
  | 33 => 29
  | 34 => 54
  | 35 => 34
  | 36 => 50
  | 37 => 35
  | 38 => 53
  | 39 => 15
  | 40 => 63
  | 41 => 12
  | 42 => 70
  | 43 => 9
  | 44 => 89
  | 45 => 53
  | 46 => 61
  | 47 => 41
  | _ => 0

def fixedLiteralModZeroRow_2 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 42
  | 1 => 24
  | 2 => 36
  | 3 => 78
  | 4 => 24
  | 5 => 43
  | 6 => 13
  | 7 => 81
  | 8 => 13
  | 9 => 62
  | 10 => 96
  | 11 => 97
  | 12 => 45
  | 13 => 13
  | 14 => 37
  | 15 => 98
  | 16 => 40
  | 17 => 44
  | 18 => 42
  | 19 => 36
  | 20 => 26
  | 21 => 66
  | 22 => 51
  | 23 => 10
  | 24 => 45
  | 25 => 70
  | 26 => 84
  | 27 => 58
  | 28 => 41
  | 29 => 29
  | 30 => 79
  | 31 => 98
  | 32 => 98
  | 33 => 51
  | 34 => 2
  | 35 => 91
  | 36 => 44
  | 37 => 21
  | 38 => 25
  | 39 => 22
  | 40 => 38
  | 41 => 91
  | 42 => 32
  | 43 => 3
  | 44 => 22
  | 45 => 51
  | 46 => 5
  | 47 => 48
  | _ => 0

def fixedLiteralModZeroRow_3 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 12
  | 1 => 71
  | 2 => 64
  | 3 => 29
  | 4 => 51
  | 5 => 22
  | 6 => 48
  | 7 => 74
  | 8 => 40
  | 9 => 79
  | 10 => 55
  | 11 => 68
  | 12 => 16
  | 13 => 50
  | 14 => 89
  | 15 => 87
  | 16 => 95
  | 17 => 17
  | 18 => 99
  | 19 => 33
  | 20 => 7
  | 21 => 20
  | 22 => 43
  | 23 => 55
  | 24 => 70
  | 25 => 62
  | 26 => 37
  | 27 => 3
  | 28 => 29
  | 29 => 86
  | 30 => 80
  | 31 => 82
  | 32 => 41
  | 33 => 50
  | 34 => 17
  | 35 => 73
  | 36 => 49
  | 37 => 60
  | 38 => 82
  | 39 => 50
  | 40 => 10
  | 41 => 60
  | 42 => 48
  | 43 => 45
  | 44 => 69
  | 45 => 1
  | 46 => 16
  | 47 => 4
  | _ => 0

def fixedLiteralModZeroRow_4 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 97
  | 1 => 40
  | 2 => 53
  | 3 => 11
  | 4 => 30
  | 5 => 66
  | 6 => 49
  | 7 => 26
  | 8 => 39
  | 9 => 49
  | 10 => 27
  | 11 => 39
  | 12 => 70
  | 13 => 76
  | 14 => 69
  | 15 => 74
  | 16 => 73
  | 17 => 94
  | 18 => 75
  | 19 => 11
  | 20 => 45
  | 21 => 31
  | 22 => 6
  | 23 => 99
  | 24 => 100
  | 25 => 44
  | 26 => 79
  | 27 => 54
  | 28 => 52
  | 29 => 37
  | 30 => 7
  | 31 => 56
  | 32 => 75
  | 33 => 3
  | 34 => 74
  | 35 => 39
  | 36 => 71
  | 37 => 54
  | 38 => 5
  | 39 => 22
  | 40 => 26
  | 41 => 61
  | 42 => 34
  | 43 => 3
  | 44 => 69
  | 45 => 87
  | 46 => 72
  | 47 => 6
  | _ => 0

def fixedLiteralModZeroRow_5 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 25
  | 1 => 94
  | 2 => 32
  | 3 => 13
  | 4 => 56
  | 5 => 94
  | 6 => 17
  | 7 => 88
  | 8 => 20
  | 9 => 23
  | 10 => 5
  | 11 => 14
  | 12 => 48
  | 13 => 58
  | 14 => 27
  | 15 => 3
  | 16 => 47
  | 17 => 81
  | 18 => 48
  | 19 => 25
  | 20 => 28
  | 21 => 15
  | 22 => 35
  | 23 => 71
  | 24 => 16
  | 25 => 97
  | 26 => 32
  | 27 => 67
  | 28 => 91
  | 29 => 62
  | 30 => 25
  | 31 => 90
  | 32 => 35
  | 33 => 48
  | 34 => 34
  | 35 => 90
  | 36 => 21
  | 37 => 21
  | 38 => 36
  | 39 => 43
  | 40 => 50
  | 41 => 70
  | 42 => 18
  | 43 => 19
  | 44 => 34
  | 45 => 80
  | 46 => 76
  | 47 => 14
  | _ => 0

def fixedLiteralModZeroRow_6 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 52
  | 1 => 0
  | 2 => 73
  | 3 => 33
  | 4 => 86
  | 5 => 36
  | 6 => 19
  | 7 => 62
  | 8 => 43
  | 9 => 75
  | 10 => 34
  | 11 => 96
  | 12 => 39
  | 13 => 33
  | 14 => 63
  | 15 => 89
  | 16 => 5
  | 17 => 30
  | 18 => 32
  | 19 => 70
  | 20 => 85
  | 21 => 81
  | 22 => 53
  | 23 => 35
  | 24 => 64
  | 25 => 35
  | 26 => 76
  | 27 => 22
  | 28 => 55
  | 29 => 3
  | 30 => 68
  | 31 => 41
  | 32 => 61
  | 33 => 22
  | 34 => 4
  | 35 => 15
  | 36 => 7
  | 37 => 73
  | 38 => 80
  | 39 => 87
  | 40 => 93
  | 41 => 97
  | 42 => 96
  | 43 => 66
  | 44 => 36
  | 45 => 29
  | 46 => 45
  | 47 => 24
  | _ => 0

def fixedLiteralModZeroRow_7 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 84
  | 1 => 88
  | 2 => 86
  | 3 => 59
  | 4 => 23
  | 5 => 44
  | 6 => 67
  | 7 => 27
  | 8 => 76
  | 9 => 76
  | 10 => 87
  | 11 => 56
  | 12 => 79
  | 13 => 36
  | 14 => 63
  | 15 => 55
  | 16 => 38
  | 17 => 42
  | 18 => 57
  | 19 => 57
  | 20 => 85
  | 21 => 28
  | 22 => 8
  | 23 => 5
  | 24 => 99
  | 25 => 83
  | 26 => 31
  | 27 => 0
  | 28 => 92
  | 29 => 89
  | 30 => 63
  | 31 => 42
  | 32 => 50
  | 33 => 75
  | 34 => 48
  | 35 => 7
  | 36 => 71
  | 37 => 6
  | 38 => 89
  | 39 => 79
  | 40 => 24
  | 41 => 40
  | 42 => 77
  | 43 => 1
  | 44 => 56
  | 45 => 64
  | 46 => 91
  | 47 => 28
  | _ => 0

def fixedLiteralModZeroRow_8 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 4
  | 1 => 36
  | 2 => 73
  | 3 => 99
  | 4 => 99
  | 5 => 12
  | 6 => 29
  | 7 => 59
  | 8 => 10
  | 9 => 38
  | 10 => 63
  | 11 => 81
  | 12 => 27
  | 13 => 68
  | 14 => 54
  | 15 => 75
  | 16 => 7
  | 17 => 7
  | 18 => 1
  | 19 => 6
  | 20 => 100
  | 21 => 72
  | 22 => 59
  | 23 => 34
  | 24 => 33
  | 25 => 11
  | 26 => 43
  | 27 => 100
  | 28 => 94
  | 29 => 100
  | 30 => 27
  | 31 => 10
  | 32 => 80
  | 33 => 66
  | 34 => 38
  | 35 => 94
  | 36 => 7
  | 37 => 80
  | 38 => 5
  | 39 => 12
  | 40 => 70
  | 41 => 75
  | 42 => 57
  | 43 => 18
  | 44 => 16
  | 45 => 50
  | 46 => 44
  | 47 => 30
  | _ => 0

def fixedLiteralModZeroRow_9 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 55
  | 1 => 6
  | 2 => 93
  | 3 => 59
  | 4 => 47
  | 5 => 94
  | 6 => 19
  | 7 => 97
  | 8 => 78
  | 9 => 95
  | 10 => 96
  | 11 => 32
  | 12 => 25
  | 13 => 6
  | 14 => 57
  | 15 => 58
  | 16 => 97
  | 17 => 88
  | 18 => 28
  | 19 => 12
  | 20 => 40
  | 21 => 80
  | 22 => 99
  | 23 => 80
  | 24 => 60
  | 25 => 86
  | 26 => 63
  | 27 => 93
  | 28 => 88
  | 29 => 78
  | 30 => 83
  | 31 => 25
  | 32 => 34
  | 33 => 93
  | 34 => 20
  | 35 => 33
  | 36 => 66
  | 37 => 39
  | 38 => 17
  | 39 => 30
  | 40 => 30
  | 41 => 69
  | 42 => 91
  | 43 => 50
  | 44 => 9
  | 45 => 47
  | 46 => 44
  | 47 => 79
  | _ => 0

def fixedLiteralModZeroRow_10 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 75
  | 1 => 98
  | 2 => 26
  | 3 => 16
  | 4 => 34
  | 5 => 5
  | 6 => 32
  | 7 => 100
  | 8 => 56
  | 9 => 98
  | 10 => 22
  | 11 => 3
  | 12 => 54
  | 13 => 81
  | 14 => 32
  | 15 => 16
  | 16 => 88
  | 17 => 76
  | 18 => 96
  | 19 => 44
  | 20 => 41
  | 21 => 15
  | 22 => 39
  | 23 => 4
  | 24 => 74
  | 25 => 97
  | 26 => 37
  | 27 => 82
  | 28 => 42
  | 29 => 78
  | 30 => 48
  | 31 => 66
  | 32 => 58
  | 33 => 66
  | 34 => 9
  | 35 => 64
  | 36 => 48
  | 37 => 90
  | 38 => 36
  | 39 => 17
  | 40 => 73
  | 41 => 1
  | 42 => 74
  | 43 => 19
  | 44 => 43
  | 45 => 61
  | 46 => 88
  | 47 => 80
  | _ => 0

def fixedLiteralModZeroRow_11 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 50
  | 1 => 91
  | 2 => 4
  | 3 => 86
  | 4 => 98
  | 5 => 95
  | 6 => 30
  | 7 => 26
  | 8 => 0
  | 9 => 13
  | 10 => 88
  | 11 => 66
  | 12 => 87
  | 13 => 18
  | 14 => 67
  | 15 => 77
  | 16 => 61
  | 17 => 1
  | 18 => 92
  | 19 => 61
  | 20 => 55
  | 21 => 96
  | 22 => 52
  | 23 => 3
  | 24 => 64
  | 25 => 23
  | 26 => 49
  | 27 => 13
  | 28 => 62
  | 29 => 62
  | 30 => 6
  | 31 => 53
  | 32 => 23
  | 33 => 94
  | 34 => 72
  | 35 => 91
  | 36 => 97
  | 37 => 94
  | 38 => 82
  | 39 => 36
  | 40 => 24
  | 41 => 27
  | 42 => 27
  | 43 => 72
  | 44 => 52
  | 45 => 45
  | 46 => 88
  | 47 => 95
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModZeroRow_12 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 86
  | 1 => 68
  | 2 => 60
  | 3 => 89
  | 4 => 24
  | 5 => 45
  | 6 => 24
  | 7 => 89
  | 8 => 36
  | 9 => 85
  | 10 => 19
  | 11 => 91
  | 12 => 87
  | 13 => 36
  | 14 => 50
  | 15 => 81
  | 16 => 63
  | 17 => 92
  | 18 => 80
  | 19 => 95
  | 20 => 65
  | 21 => 65
  | 22 => 0
  | 23 => 8
  | 24 => 18
  | 25 => 79
  | 26 => 78
  | 27 => 16
  | 28 => 34
  | 29 => 84
  | 30 => 17
  | 31 => 80
  | 32 => 35
  | 33 => 16
  | 34 => 87
  | 35 => 51
  | 36 => 4
  | 37 => 57
  | 38 => 51
  | 39 => 98
  | 40 => 94
  | 41 => 41
  | 42 => 3
  | 43 => 70
  | 44 => 64
  | 45 => 49
  | 46 => 80
  | 47 => 83
  | _ => 0

def fixedLiteralModZeroRow_13 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 78
  | 1 => 94
  | 2 => 21
  | 3 => 62
  | 4 => 86
  | 5 => 55
  | 6 => 87
  | 7 => 17
  | 8 => 22
  | 9 => 95
  | 10 => 93
  | 11 => 15
  | 12 => 25
  | 13 => 13
  | 14 => 82
  | 15 => 1
  | 16 => 98
  | 17 => 100
  | 18 => 32
  | 19 => 56
  | 20 => 23
  | 21 => 68
  | 22 => 92
  | 23 => 85
  | 24 => 49
  | 25 => 4
  | 26 => 65
  | 27 => 98
  | 28 => 30
  | 29 => 58
  | 30 => 47
  | 31 => 7
  | 32 => 69
  | 33 => 66
  | 34 => 79
  | 35 => 36
  | 36 => 71
  | 37 => 40
  | 38 => 62
  | 39 => 14
  | 40 => 77
  | 41 => 61
  | 42 => 49
  | 43 => 7
  | 44 => 14
  | 45 => 61
  | 46 => 60
  | 47 => 9
  | _ => 0

def fixedLiteralModZeroRow_14 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 33
  | 1 => 17
  | 2 => 70
  | 3 => 87
  | 4 => 13
  | 5 => 24
  | 6 => 52
  | 7 => 71
  | 8 => 39
  | 9 => 23
  | 10 => 15
  | 11 => 28
  | 12 => 82
  | 13 => 0
  | 14 => 4
  | 15 => 4
  | 16 => 35
  | 17 => 6
  | 18 => 94
  | 19 => 3
  | 20 => 77
  | 21 => 69
  | 22 => 62
  | 23 => 84
  | 24 => 69
  | 25 => 62
  | 26 => 93
  | 27 => 74
  | 28 => 83
  | 29 => 70
  | 30 => 21
  | 31 => 98
  | 32 => 59
  | 33 => 97
  | 34 => 92
  | 35 => 19
  | 36 => 62
  | 37 => 40
  | 38 => 84
  | 39 => 2
  | 40 => 53
  | 41 => 32
  | 42 => 65
  | 43 => 53
  | 44 => 85
  | 45 => 85
  | 46 => 10
  | 47 => 99
  | _ => 0

def fixedLiteralModZeroRow_15 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 97
  | 1 => 24
  | 2 => 9
  | 3 => 70
  | 4 => 98
  | 5 => 44
  | 6 => 57
  | 7 => 4
  | 8 => 57
  | 9 => 90
  | 10 => 69
  | 11 => 8
  | 12 => 78
  | 13 => 37
  | 14 => 92
  | 15 => 6
  | 16 => 39
  | 17 => 80
  | 18 => 1
  | 19 => 62
  | 20 => 72
  | 21 => 44
  | 22 => 42
  | 23 => 96
  | 24 => 98
  | 25 => 19
  | 26 => 77
  | 27 => 55
  | 28 => 86
  | 29 => 59
  | 30 => 78
  | 31 => 60
  | 32 => 27
  | 33 => 87
  | 34 => 17
  | 35 => 99
  | 36 => 42
  | 37 => 69
  | 38 => 0
  | 39 => 75
  | 40 => 94
  | 41 => 63
  | 42 => 74
  | 43 => 4
  | 44 => 13
  | 45 => 27
  | 46 => 26
  | 47 => 2
  | _ => 0

def fixedLiteralModZeroRow_16 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 0
  | 1 => 85
  | 2 => 23
  | 3 => 44
  | 4 => 24
  | 5 => 54
  | 6 => 31
  | 7 => 77
  | 8 => 15
  | 9 => 19
  | 10 => 37
  | 11 => 42
  | 12 => 67
  | 13 => 42
  | 14 => 72
  | 15 => 85
  | 16 => 15
  | 17 => 100
  | 18 => 83
  | 19 => 3
  | 20 => 65
  | 21 => 70
  | 22 => 67
  | 23 => 58
  | 24 => 74
  | 25 => 90
  | 26 => 95
  | 27 => 65
  | 28 => 44
  | 29 => 20
  | 30 => 12
  | 31 => 13
  | 32 => 76
  | 33 => 37
  | 34 => 59
  | 35 => 23
  | 36 => 51
  | 37 => 20
  | 38 => 19
  | 39 => 3
  | 40 => 96
  | 41 => 93
  | 42 => 25
  | 43 => 20
  | 44 => 10
  | 45 => 93
  | 46 => 36
  | 47 => 90
  | _ => 0

def fixedLiteralModZeroRow_17 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 46
  | 1 => 52
  | 2 => 55
  | 3 => 63
  | 4 => 100
  | 5 => 34
  | 6 => 30
  | 7 => 67
  | 8 => 37
  | 9 => 94
  | 10 => 100
  | 11 => 52
  | 12 => 40
  | 13 => 13
  | 14 => 72
  | 15 => 64
  | 16 => 64
  | 17 => 51
  | 18 => 60
  | 19 => 62
  | 20 => 44
  | 21 => 88
  | 22 => 1
  | 23 => 76
  | 24 => 69
  | 25 => 26
  | 26 => 52
  | 27 => 14
  | 28 => 51
  | 29 => 28
  | 30 => 54
  | 31 => 33
  | 32 => 98
  | 33 => 9
  | 34 => 5
  | 35 => 89
  | 36 => 54
  | 37 => 77
  | 38 => 83
  | 39 => 30
  | 40 => 93
  | 41 => 87
  | 42 => 53
  | 43 => 40
  | 44 => 65
  | 45 => 90
  | 46 => 68
  | 47 => 40
  | _ => 0

def fixedLiteralModZeroRow_18 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 43
  | 1 => 3
  | 2 => 60
  | 3 => 60
  | 4 => 79
  | 5 => 1
  | 6 => 4
  | 7 => 41
  | 8 => 4
  | 9 => 33
  | 10 => 72
  | 11 => 99
  | 12 => 62
  | 13 => 43
  | 14 => 20
  | 15 => 81
  | 16 => 10
  | 17 => 12
  | 18 => 68
  | 19 => 49
  | 20 => 68
  | 21 => 21
  | 22 => 51
  | 23 => 22
  | 24 => 1
  | 25 => 53
  | 26 => 28
  | 27 => 24
  | 28 => 89
  | 29 => 62
  | 30 => 84
  | 31 => 31
  | 32 => 46
  | 33 => 43
  | 34 => 76
  | 35 => 96
  | 36 => 35
  | 37 => 87
  | 38 => 99
  | 39 => 65
  | 40 => 84
  | 41 => 7
  | 42 => 72
  | 43 => 52
  | 44 => 27
  | 45 => 10
  | 46 => 33
  | 47 => 34
  | _ => 0

def fixedLiteralModZeroRow_19 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 10
  | 1 => 91
  | 2 => 87
  | 3 => 76
  | 4 => 72
  | 5 => 94
  | 6 => 4
  | 7 => 97
  | 8 => 45
  | 9 => 67
  | 10 => 79
  | 11 => 22
  | 12 => 99
  | 13 => 29
  | 14 => 45
  | 15 => 54
  | 16 => 91
  | 17 => 75
  | 18 => 97
  | 19 => 29
  | 20 => 20
  | 21 => 100
  | 22 => 51
  | 23 => 5
  | 24 => 91
  | 25 => 3
  | 26 => 39
  | 27 => 72
  | 28 => 43
  | 29 => 57
  | 30 => 96
  | 31 => 71
  | 32 => 17
  | 33 => 79
  | 34 => 7
  | 35 => 20
  | 36 => 35
  | 37 => 22
  | 38 => 69
  | 39 => 41
  | 40 => 80
  | 41 => 100
  | 42 => 47
  | 43 => 93
  | 44 => 54
  | 45 => 61
  | 46 => 62
  | 47 => 76
  | _ => 0

def fixedLiteralModZeroRow_20 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 19
  | 1 => 35
  | 2 => 19
  | 3 => 69
  | 4 => 4
  | 5 => 22
  | 6 => 83
  | 7 => 18
  | 8 => 31
  | 9 => 64
  | 10 => 58
  | 11 => 17
  | 12 => 91
  | 13 => 22
  | 14 => 95
  | 15 => 88
  | 16 => 68
  | 17 => 4
  | 18 => 10
  | 19 => 99
  | 20 => 59
  | 21 => 16
  | 22 => 61
  | 23 => 31
  | 24 => 37
  | 25 => 9
  | 26 => 33
  | 27 => 0
  | 28 => 97
  | 29 => 6
  | 30 => 69
  | 31 => 55
  | 32 => 2
  | 33 => 64
  | 34 => 93
  | 35 => 42
  | 36 => 11
  | 37 => 26
  | 38 => 11
  | 39 => 45
  | 40 => 98
  | 41 => 4
  | 42 => 63
  | 43 => 28
  | 44 => 19
  | 45 => 11
  | 46 => 51
  | 47 => 9
  | _ => 0

def fixedLiteralModZeroRow_21 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 97
  | 1 => 63
  | 2 => 39
  | 3 => 25
  | 4 => 17
  | 5 => 80
  | 6 => 49
  | 7 => 36
  | 8 => 10
  | 9 => 3
  | 10 => 48
  | 11 => 22
  | 12 => 63
  | 13 => 13
  | 14 => 27
  | 15 => 1
  | 16 => 20
  | 17 => 79
  | 18 => 78
  | 19 => 86
  | 20 => 0
  | 21 => 21
  | 22 => 25
  | 23 => 81
  | 24 => 72
  | 25 => 41
  | 26 => 11
  | 27 => 62
  | 28 => 68
  | 29 => 62
  | 30 => 67
  | 31 => 55
  | 32 => 86
  | 33 => 96
  | 34 => 65
  | 35 => 45
  | 36 => 45
  | 37 => 54
  | 38 => 9
  | 39 => 61
  | 40 => 80
  | 41 => 76
  | 42 => 2
  | 43 => 58
  | 44 => 15
  | 45 => 13
  | 46 => 14
  | 47 => 100
  | _ => 0

def fixedLiteralModZeroRow_22 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 59
  | 1 => 29
  | 2 => 22
  | 3 => 60
  | 4 => 13
  | 5 => 82
  | 6 => 27
  | 7 => 30
  | 8 => 97
  | 9 => 48
  | 10 => 81
  | 11 => 56
  | 12 => 74
  | 13 => 22
  | 14 => 31
  | 15 => 68
  | 16 => 41
  | 17 => 0
  | 18 => 69
  | 19 => 25
  | 20 => 75
  | 21 => 8
  | 22 => 61
  | 23 => 21
  | 24 => 78
  | 25 => 47
  | 26 => 78
  | 27 => 91
  | 28 => 76
  | 29 => 38
  | 30 => 5
  | 31 => 57
  | 32 => 45
  | 33 => 83
  | 34 => 89
  | 35 => 55
  | 36 => 17
  | 37 => 83
  | 38 => 1
  | 39 => 95
  | 40 => 67
  | 41 => 88
  | 42 => 73
  | 43 => 11
  | 44 => 17
  | 45 => 97
  | 46 => 41
  | 47 => 34
  | _ => 0

def fixedLiteralModZeroRow_23 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 47
  | 1 => 65
  | 2 => 34
  | 3 => 37
  | 4 => 96
  | 5 => 39
  | 6 => 86
  | 7 => 91
  | 8 => 61
  | 9 => 63
  | 10 => 100
  | 11 => 40
  | 12 => 56
  | 13 => 8
  | 14 => 72
  | 15 => 92
  | 16 => 72
  | 17 => 62
  | 18 => 25
  | 19 => 27
  | 20 => 70
  | 21 => 55
  | 22 => 55
  | 23 => 21
  | 24 => 26
  | 25 => 12
  | 26 => 47
  | 27 => 57
  | 28 => 17
  | 29 => 84
  | 30 => 61
  | 31 => 92
  | 32 => 41
  | 33 => 81
  | 34 => 99
  | 35 => 48
  | 36 => 96
  | 37 => 8
  | 38 => 33
  | 39 => 92
  | 40 => 18
  | 41 => 47
  | 42 => 1
  | 43 => 23
  | 44 => 18
  | 45 => 94
  | 46 => 96
  | 47 => 74
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModZeroRow_24 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 11
  | 1 => 72
  | 2 => 66
  | 3 => 74
  | 4 => 63
  | 5 => 47
  | 6 => 51
  | 7 => 26
  | 8 => 30
  | 9 => 71
  | 10 => 42
  | 11 => 15
  | 12 => 40
  | 13 => 59
  | 14 => 5
  | 15 => 19
  | 16 => 47
  | 17 => 62
  | 18 => 96
  | 19 => 68
  | 20 => 49
  | 21 => 19
  | 22 => 32
  | 23 => 17
  | 24 => 63
  | 25 => 39
  | 26 => 45
  | 27 => 13
  | 28 => 27
  | 29 => 22
  | 30 => 33
  | 31 => 51
  | 32 => 62
  | 33 => 10
  | 34 => 21
  | 35 => 70
  | 36 => 0
  | 37 => 21
  | 38 => 96
  | 39 => 17
  | 40 => 18
  | 41 => 24
  | 42 => 99
  | 43 => 11
  | 44 => 32
  | 45 => 94
  | 46 => 73
  | 47 => 5
  | _ => 0

def fixedLiteralModZeroRow_25 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 38
  | 1 => 54
  | 2 => 84
  | 3 => 69
  | 4 => 60
  | 5 => 83
  | 6 => 59
  | 7 => 96
  | 8 => 50
  | 9 => 7
  | 10 => 11
  | 11 => 99
  | 12 => 54
  | 13 => 36
  | 14 => 9
  | 15 => 52
  | 16 => 57
  | 17 => 61
  | 18 => 3
  | 19 => 13
  | 20 => 39
  | 21 => 57
  | 22 => 14
  | 23 => 34
  | 24 => 61
  | 25 => 23
  | 26 => 3
  | 27 => 49
  | 28 => 22
  | 29 => 86
  | 30 => 22
  | 31 => 34
  | 32 => 68
  | 33 => 85
  | 34 => 11
  | 35 => 9
  | 36 => 16
  | 37 => 16
  | 38 => 72
  | 39 => 12
  | 40 => 6
  | 41 => 74
  | 42 => 54
  | 43 => 71
  | 44 => 35
  | 45 => 83
  | 46 => 59
  | 47 => 37
  | _ => 0

def fixedLiteralModZeroRow_26 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 14
  | 1 => 76
  | 2 => 88
  | 3 => 23
  | 4 => 43
  | 5 => 94
  | 6 => 51
  | 7 => 13
  | 8 => 14
  | 9 => 46
  | 10 => 32
  | 11 => 75
  | 12 => 43
  | 13 => 89
  | 14 => 2
  | 15 => 1
  | 16 => 5
  | 17 => 1
  | 18 => 28
  | 19 => 14
  | 20 => 81
  | 21 => 44
  | 22 => 51
  | 23 => 89
  | 24 => 59
  | 25 => 30
  | 26 => 20
  | 27 => 10
  | 28 => 13
  | 29 => 81
  | 30 => 99
  | 31 => 57
  | 32 => 74
  | 33 => 94
  | 34 => 13
  | 35 => 73
  | 36 => 62
  | 37 => 51
  | 38 => 45
  | 39 => 53
  | 40 => 62
  | 41 => 51
  | 42 => 86
  | 43 => 43
  | 44 => 4
  | 45 => 95
  | 46 => 92
  | 47 => 38
  | _ => 0

def fixedLiteralModZeroRow_27 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 28
  | 1 => 38
  | 2 => 9
  | 3 => 82
  | 4 => 78
  | 5 => 55
  | 6 => 94
  | 7 => 100
  | 8 => 67
  | 9 => 52
  | 10 => 2
  | 11 => 73
  | 12 => 49
  | 13 => 9
  | 14 => 30
  | 15 => 48
  | 16 => 55
  | 17 => 93
  | 18 => 73
  | 19 => 85
  | 20 => 96
  | 21 => 91
  | 22 => 25
  | 23 => 37
  | 24 => 96
  | 25 => 19
  | 26 => 40
  | 27 => 10
  | 28 => 30
  | 29 => 77
  | 30 => 78
  | 31 => 57
  | 32 => 58
  | 33 => 43
  | 34 => 81
  | 35 => 56
  | 36 => 10
  | 37 => 14
  | 38 => 81
  | 39 => 93
  | 40 => 73
  | 41 => 20
  | 42 => 51
  | 43 => 92
  | 44 => 13
  | 45 => 76
  | 46 => 76
  | 47 => 92
  | _ => 0

def fixedLiteralModZeroRow_28 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 49
  | 1 => 35
  | 2 => 42
  | 3 => 43
  | 4 => 43
  | 5 => 83
  | 6 => 12
  | 7 => 36
  | 8 => 1
  | 9 => 97
  | 10 => 24
  | 11 => 36
  | 12 => 40
  | 13 => 23
  | 14 => 35
  | 15 => 31
  | 16 => 52
  | 17 => 87
  | 18 => 60
  | 19 => 18
  | 20 => 67
  | 21 => 20
  | 22 => 29
  | 23 => 36
  | 24 => 70
  | 25 => 55
  | 26 => 7
  | 27 => 82
  | 28 => 68
  | 29 => 38
  | 30 => 81
  | 31 => 68
  | 32 => 59
  | 33 => 20
  | 34 => 65
  | 35 => 52
  | 36 => 79
  | 37 => 62
  | 38 => 6
  | 39 => 96
  | 40 => 72
  | 41 => 58
  | 42 => 95
  | 43 => 17
  | 44 => 96
  | 45 => 45
  | 46 => 88
  | 47 => 57
  | _ => 0

def fixedLiteralModZeroRow_29 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 72
  | 1 => 80
  | 2 => 70
  | 3 => 33
  | 4 => 89
  | 5 => 41
  | 6 => 30
  | 7 => 36
  | 8 => 76
  | 9 => 87
  | 10 => 99
  | 11 => 78
  | 12 => 49
  | 13 => 42
  | 14 => 5
  | 15 => 34
  | 16 => 36
  | 17 => 21
  | 18 => 59
  | 19 => 22
  | 20 => 38
  | 21 => 59
  | 22 => 72
  | 23 => 9
  | 24 => 6
  | 25 => 100
  | 26 => 69
  | 27 => 91
  | 28 => 28
  | 29 => 15
  | 30 => 30
  | 31 => 48
  | 32 => 60
  | 33 => 89
  | 34 => 16
  | 35 => 85
  | 36 => 63
  | 37 => 80
  | 38 => 3
  | 39 => 13
  | 40 => 98
  | 41 => 14
  | 42 => 21
  | 43 => 6
  | 44 => 96
  | 45 => 50
  | 46 => 55
  | 47 => 89
  | _ => 0

def fixedLiteralModZeroRow_30 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 62
  | 1 => 36
  | 2 => 59
  | 3 => 91
  | 4 => 34
  | 5 => 21
  | 6 => 2
  | 7 => 52
  | 8 => 24
  | 9 => 50
  | 10 => 88
  | 11 => 10
  | 12 => 87
  | 13 => 82
  | 14 => 67
  | 15 => 50
  | 16 => 1
  | 17 => 61
  | 18 => 9
  | 19 => 92
  | 20 => 86
  | 21 => 68
  | 22 => 66
  | 23 => 42
  | 24 => 69
  | 25 => 63
  | 26 => 46
  | 27 => 48
  | 28 => 52
  | 29 => 69
  | 30 => 54
  | 31 => 16
  | 32 => 32
  | 33 => 2
  | 34 => 39
  | 35 => 58
  | 36 => 33
  | 37 => 39
  | 38 => 55
  | 39 => 88
  | 40 => 85
  | 41 => 57
  | 42 => 30
  | 43 => 39
  | 44 => 10
  | 45 => 12
  | 46 => 5
  | 47 => 58
  | _ => 0

def fixedLiteralModZeroRow_31 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 32
  | 1 => 81
  | 2 => 17
  | 3 => 39
  | 4 => 82
  | 5 => 60
  | 6 => 15
  | 7 => 27
  | 8 => 10
  | 9 => 11
  | 10 => 26
  | 11 => 64
  | 12 => 56
  | 13 => 65
  | 14 => 46
  | 15 => 59
  | 16 => 85
  | 17 => 31
  | 18 => 86
  | 19 => 0
  | 20 => 3
  | 21 => 23
  | 22 => 5
  | 23 => 22
  | 24 => 98
  | 25 => 3
  | 26 => 2
  | 27 => 43
  | 28 => 10
  | 29 => 52
  | 30 => 26
  | 31 => 56
  | 32 => 7
  | 33 => 45
  | 34 => 5
  | 35 => 10
  | 36 => 1
  | 37 => 3
  | 38 => 78
  | 39 => 2
  | 40 => 41
  | 41 => 21
  | 42 => 10
  | 43 => 8
  | 44 => 56
  | 45 => 75
  | 46 => 32
  | 47 => 21
  | _ => 0

def fixedLiteralModZeroRow_32 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 79
  | 1 => 55
  | 2 => 34
  | 3 => 83
  | 4 => 55
  | 5 => 100
  | 6 => 56
  | 7 => 56
  | 8 => 64
  | 9 => 9
  | 10 => 50
  | 11 => 22
  | 12 => 47
  | 13 => 94
  | 14 => 80
  | 15 => 95
  | 16 => 8
  | 17 => 95
  | 18 => 45
  | 19 => 44
  | 20 => 76
  | 21 => 19
  | 22 => 11
  | 23 => 38
  | 24 => 84
  | 25 => 19
  | 26 => 28
  | 27 => 47
  | 28 => 4
  | 29 => 32
  | 30 => 17
  | 31 => 98
  | 32 => 64
  | 33 => 47
  | 34 => 97
  | 35 => 67
  | 36 => 39
  | 37 => 100
  | 38 => 65
  | 39 => 61
  | 40 => 70
  | 41 => 52
  | 42 => 20
  | 43 => 58
  | 44 => 56
  | 45 => 87
  | 46 => 15
  | 47 => 20
  | _ => 0

def fixedLiteralModZeroRow_33 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 66
  | 1 => 34
  | 2 => 71
  | 3 => 19
  | 4 => 57
  | 5 => 3
  | 6 => 56
  | 7 => 7
  | 8 => 89
  | 9 => 93
  | 10 => 67
  | 11 => 42
  | 12 => 91
  | 13 => 42
  | 14 => 74
  | 15 => 87
  | 16 => 17
  | 17 => 21
  | 18 => 4
  | 19 => 82
  | 20 => 58
  | 21 => 43
  | 22 => 61
  | 23 => 22
  | 24 => 24
  | 25 => 11
  | 26 => 13
  | 27 => 80
  | 28 => 41
  | 29 => 10
  | 30 => 60
  | 31 => 57
  | 32 => 76
  | 33 => 27
  | 34 => 51
  | 35 => 95
  | 36 => 78
  | 37 => 74
  | 38 => 67
  | 39 => 32
  | 40 => 41
  | 41 => 41
  | 42 => 10
  | 43 => 81
  | 44 => 70
  | 45 => 76
  | 46 => 82
  | 47 => 70
  | _ => 0

def fixedLiteralModZeroRow_34 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 77
  | 1 => 79
  | 2 => 71
  | 3 => 42
  | 4 => 28
  | 5 => 1
  | 6 => 23
  | 7 => 37
  | 8 => 33
  | 9 => 62
  | 10 => 45
  | 11 => 72
  | 12 => 1
  | 13 => 5
  | 14 => 35
  | 15 => 63
  | 16 => 6
  | 17 => 57
  | 18 => 37
  | 19 => 13
  | 20 => 77
  | 21 => 16
  | 22 => 39
  | 23 => 44
  | 24 => 29
  | 25 => 12
  | 26 => 38
  | 27 => 67
  | 28 => 44
  | 29 => 51
  | 30 => 62
  | 31 => 63
  | 32 => 37
  | 33 => 7
  | 34 => 59
  | 35 => 93
  | 36 => 20
  | 37 => 86
  | 38 => 66
  | 39 => 24
  | 40 => 5
  | 41 => 76
  | 42 => 38
  | 43 => 15
  | 44 => 44
  | 45 => 65
  | 46 => 20
  | 47 => 6
  | _ => 0

def fixedLiteralModZeroRow_35 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 11
  | 1 => 97
  | 2 => 42
  | 3 => 90
  | 4 => 13
  | 5 => 91
  | 6 => 19
  | 7 => 81
  | 8 => 1
  | 9 => 24
  | 10 => 29
  | 11 => 41
  | 12 => 21
  | 13 => 49
  | 14 => 34
  | 15 => 45
  | 16 => 8
  | 17 => 49
  | 18 => 86
  | 19 => 54
  | 20 => 3
  | 21 => 29
  | 22 => 10
  | 23 => 7
  | 24 => 62
  | 25 => 34
  | 26 => 17
  | 27 => 52
  | 28 => 49
  | 29 => 0
  | 30 => 81
  | 31 => 42
  | 32 => 91
  | 33 => 25
  | 34 => 63
  | 35 => 1
  | 36 => 60
  | 37 => 79
  | 38 => 10
  | 39 => 20
  | 40 => 13
  | 41 => 32
  | 42 => 79
  | 43 => 79
  | 44 => 39
  | 45 => 99
  | 46 => 76
  | 47 => 13
  | _ => 0

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

namespace InternalCatalan

def fixedLiteralModZeroRow_36 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 9
  | 1 => 24
  | 2 => 13
  | 3 => 21
  | 4 => 9
  | 5 => 0
  | 6 => 73
  | 7 => 28
  | 8 => 37
  | 9 => 32
  | 10 => 74
  | 11 => 78
  | 12 => 31
  | 13 => 91
  | 14 => 31
  | 15 => 12
  | 16 => 7
  | 17 => 76
  | 18 => 89
  | 19 => 70
  | 20 => 87
  | 21 => 97
  | 22 => 87
  | 23 => 75
  | 24 => 88
  | 25 => 48
  | 26 => 62
  | 27 => 56
  | 28 => 41
  | 29 => 60
  | 30 => 42
  | 31 => 85
  | 32 => 15
  | 33 => 31
  | 34 => 49
  | 35 => 68
  | 36 => 59
  | 37 => 63
  | 38 => 80
  | 39 => 58
  | 40 => 63
  | 41 => 78
  | 42 => 64
  | 43 => 58
  | 44 => 25
  | 45 => 65
  | 46 => 66
  | 47 => 70
  | _ => 0

def fixedLiteralModZeroRow_37 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 16
  | 1 => 87
  | 2 => 15
  | 3 => 39
  | 4 => 57
  | 5 => 45
  | 6 => 41
  | 7 => 81
  | 8 => 28
  | 9 => 30
  | 10 => 36
  | 11 => 42
  | 12 => 64
  | 13 => 97
  | 14 => 19
  | 15 => 45
  | 16 => 91
  | 17 => 12
  | 18 => 7
  | 19 => 48
  | 20 => 4
  | 21 => 20
  | 22 => 72
  | 23 => 53
  | 24 => 80
  | 25 => 67
  | 26 => 83
  | 27 => 4
  | 28 => 23
  | 29 => 32
  | 30 => 48
  | 31 => 88
  | 32 => 78
  | 33 => 11
  | 34 => 88
  | 35 => 38
  | 36 => 31
  | 37 => 64
  | 38 => 20
  | 39 => 72
  | 40 => 54
  | 41 => 84
  | 42 => 71
  | 43 => 57
  | 44 => 7
  | 45 => 68
  | 46 => 42
  | 47 => 96
  | _ => 0

def fixedLiteralModZeroRow_38 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 59
  | 1 => 34
  | 2 => 83
  | 3 => 4
  | 4 => 64
  | 5 => 70
  | 6 => 13
  | 7 => 73
  | 8 => 82
  | 9 => 8
  | 10 => 22
  | 11 => 55
  | 12 => 87
  | 13 => 68
  | 14 => 13
  | 15 => 39
  | 16 => 14
  | 17 => 40
  | 18 => 92
  | 19 => 94
  | 20 => 72
  | 21 => 99
  | 22 => 99
  | 23 => 67
  | 24 => 81
  | 25 => 50
  | 26 => 73
  | 27 => 80
  | 28 => 26
  | 29 => 14
  | 30 => 4
  | 31 => 90
  | 32 => 95
  | 33 => 10
  | 34 => 45
  | 35 => 81
  | 36 => 27
  | 37 => 98
  | 38 => 82
  | 39 => 90
  | 40 => 79
  | 41 => 90
  | 42 => 10
  | 43 => 39
  | 44 => 91
  | 45 => 61
  | 46 => 39
  | 47 => 23
  | _ => 0

def fixedLiteralModZeroRow_39 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 25
  | 1 => 8
  | 2 => 70
  | 3 => 73
  | 4 => 72
  | 5 => 98
  | 6 => 38
  | 7 => 23
  | 8 => 44
  | 9 => 23
  | 10 => 58
  | 11 => 58
  | 12 => 5
  | 13 => 37
  | 14 => 53
  | 15 => 23
  | 16 => 94
  | 17 => 36
  | 18 => 34
  | 19 => 90
  | 20 => 69
  | 21 => 75
  | 22 => 90
  | 23 => 32
  | 24 => 7
  | 25 => 35
  | 26 => 76
  | 27 => 29
  | 28 => 1
  | 29 => 39
  | 30 => 36
  | 31 => 43
  | 32 => 94
  | 33 => 57
  | 34 => 50
  | 35 => 1
  | 36 => 19
  | 37 => 6
  | 38 => 35
  | 39 => 100
  | 40 => 26
  | 41 => 36
  | 42 => 94
  | 43 => 48
  | 44 => 7
  | 45 => 55
  | 46 => 19
  | 47 => 69
  | _ => 0

def fixedLiteralModZeroRow_40 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 94
  | 1 => 66
  | 2 => 95
  | 3 => 94
  | 4 => 12
  | 5 => 52
  | 6 => 55
  | 7 => 95
  | 8 => 24
  | 9 => 96
  | 10 => 48
  | 11 => 20
  | 12 => 9
  | 13 => 96
  | 14 => 41
  | 15 => 62
  | 16 => 19
  | 17 => 41
  | 18 => 82
  | 19 => 52
  | 20 => 9
  | 21 => 50
  | 22 => 96
  | 23 => 16
  | 24 => 40
  | 25 => 26
  | 26 => 20
  | 27 => 82
  | 28 => 91
  | 29 => 75
  | 30 => 8
  | 31 => 42
  | 32 => 52
  | 33 => 52
  | 34 => 90
  | 35 => 78
  | 36 => 45
  | 37 => 30
  | 38 => 49
  | 39 => 78
  | 40 => 59
  | 41 => 32
  | 42 => 71
  | 43 => 44
  | 44 => 62
  | 45 => 18
  | 46 => 79
  | 47 => 33
  | _ => 0

def fixedLiteralModZeroRow_41 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 44
  | 1 => 50
  | 2 => 62
  | 3 => 82
  | 4 => 40
  | 5 => 83
  | 6 => 63
  | 7 => 87
  | 8 => 43
  | 9 => 94
  | 10 => 12
  | 11 => 23
  | 12 => 98
  | 13 => 95
  | 14 => 57
  | 15 => 41
  | 16 => 31
  | 17 => 80
  | 18 => 30
  | 19 => 15
  | 20 => 76
  | 21 => 45
  | 22 => 41
  | 23 => 3
  | 24 => 82
  | 25 => 37
  | 26 => 52
  | 27 => 75
  | 28 => 5
  | 29 => 23
  | 30 => 26
  | 31 => 58
  | 32 => 28
  | 33 => 38
  | 34 => 50
  | 35 => 54
  | 36 => 37
  | 37 => 41
  | 38 => 65
  | 39 => 17
  | 40 => 74
  | 41 => 70
  | 42 => 96
  | 43 => 31
  | 44 => 80
  | 45 => 6
  | 46 => 82
  | 47 => 5
  | _ => 0

def fixedLiteralModZeroRow_42 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 33
  | 1 => 28
  | 2 => 93
  | 3 => 2
  | 4 => 64
  | 5 => 58
  | 6 => 85
  | 7 => 51
  | 8 => 7
  | 9 => 20
  | 10 => 14
  | 11 => 48
  | 12 => 46
  | 13 => 11
  | 14 => 47
  | 15 => 61
  | 16 => 36
  | 17 => 54
  | 18 => 95
  | 19 => 5
  | 20 => 4
  | 21 => 34
  | 22 => 84
  | 23 => 23
  | 24 => 47
  | 25 => 21
  | 26 => 30
  | 27 => 48
  | 28 => 60
  | 29 => 15
  | 30 => 2
  | 31 => 73
  | 32 => 74
  | 33 => 70
  | 34 => 42
  | 35 => 11
  | 36 => 82
  | 37 => 93
  | 38 => 9
  | 39 => 56
  | 40 => 80
  | 41 => 60
  | 42 => 5
  | 43 => 92
  | 44 => 58
  | 45 => 0
  | 46 => 17
  | 47 => 97
  | _ => 0

def fixedLiteralModZeroRow_43 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 76
  | 1 => 20
  | 2 => 55
  | 3 => 54
  | 4 => 31
  | 5 => 79
  | 6 => 22
  | 7 => 58
  | 8 => 70
  | 9 => 81
  | 10 => 92
  | 11 => 5
  | 12 => 8
  | 13 => 46
  | 14 => 68
  | 15 => 11
  | 16 => 75
  | 17 => 77
  | 18 => 3
  | 19 => 97
  | 20 => 4
  | 21 => 23
  | 22 => 92
  | 23 => 79
  | 24 => 17
  | 25 => 45
  | 26 => 95
  | 27 => 4
  | 28 => 27
  | 29 => 0
  | 30 => 67
  | 31 => 69
  | 32 => 36
  | 33 => 57
  | 34 => 85
  | 35 => 67
  | 36 => 20
  | 37 => 24
  | 38 => 59
  | 39 => 35
  | 40 => 96
  | 41 => 92
  | 42 => 95
  | 43 => 73
  | 44 => 75
  | 45 => 56
  | 46 => 54
  | 47 => 59
  | _ => 0

def fixedLiteralModZeroRow_44 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 53
  | 1 => 87
  | 2 => 11
  | 3 => 91
  | 4 => 8
  | 5 => 56
  | 6 => 3
  | 7 => 79
  | 8 => 97
  | 9 => 14
  | 10 => 27
  | 11 => 23
  | 12 => 18
  | 13 => 42
  | 14 => 75
  | 15 => 62
  | 16 => 85
  | 17 => 64
  | 18 => 24
  | 19 => 2
  | 20 => 38
  | 21 => 15
  | 22 => 45
  | 23 => 15
  | 24 => 24
  | 25 => 27
  | 26 => 62
  | 27 => 87
  | 28 => 74
  | 29 => 79
  | 30 => 19
  | 31 => 6
  | 32 => 99
  | 33 => 29
  | 34 => 88
  | 35 => 77
  | 36 => 9
  | 37 => 43
  | 38 => 57
  | 39 => 71
  | 40 => 20
  | 41 => 12
  | 42 => 4
  | 43 => 62
  | 44 => 36
  | 45 => 65
  | 46 => 53
  | 47 => 33
  | _ => 0

def fixedLiteralModZeroRow_45 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 17
  | 1 => 92
  | 2 => 55
  | 3 => 15
  | 4 => 48
  | 5 => 76
  | 6 => 36
  | 7 => 57
  | 8 => 25
  | 9 => 0
  | 10 => 7
  | 11 => 11
  | 12 => 77
  | 13 => 24
  | 14 => 38
  | 15 => 77
  | 16 => 65
  | 17 => 68
  | 18 => 65
  | 19 => 62
  | 20 => 55
  | 21 => 61
  | 22 => 22
  | 23 => 41
  | 24 => 99
  | 25 => 48
  | 26 => 76
  | 27 => 87
  | 28 => 18
  | 29 => 25
  | 30 => 61
  | 31 => 53
  | 32 => 74
  | 33 => 53
  | 34 => 98
  | 35 => 7
  | 36 => 32
  | 37 => 10
  | 38 => 11
  | 39 => 47
  | 40 => 32
  | 41 => 14
  | 42 => 88
  | 43 => 71
  | 44 => 34
  | 45 => 84
  | 46 => 57
  | 47 => 7
  | _ => 0

def fixedLiteralModZeroRow_46 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 65
  | 1 => 29
  | 2 => 95
  | 3 => 22
  | 4 => 61
  | 5 => 100
  | 6 => 37
  | 7 => 60
  | 8 => 96
  | 9 => 22
  | 10 => 12
  | 11 => 96
  | 12 => 57
  | 13 => 96
  | 14 => 98
  | 15 => 76
  | 16 => 72
  | 17 => 59
  | 18 => 10
  | 19 => 26
  | 20 => 59
  | 21 => 69
  | 22 => 83
  | 23 => 6
  | 24 => 29
  | 25 => 96
  | 26 => 31
  | 27 => 26
  | 28 => 56
  | 29 => 96
  | 30 => 88
  | 31 => 9
  | 32 => 98
  | 33 => 1
  | 34 => 2
  | 35 => 85
  | 36 => 2
  | 37 => 41
  | 38 => 12
  | 39 => 16
  | 40 => 89
  | 41 => 83
  | 42 => 14
  | 43 => 31
  | 44 => 70
  | 45 => 58
  | 46 => 65
  | 47 => 83
  | _ => 0

def fixedLiteralModZeroRow_47 (k : Fin 48) : ZMod 101 :=
  match k.val with
  | 0 => 59
  | 1 => 78
  | 2 => 5
  | 3 => 84
  | 4 => 92
  | 5 => 21
  | 6 => 95
  | 7 => 74
  | 8 => 49
  | 9 => 18
  | 10 => 61
  | 11 => 85
  | 12 => 25
  | 13 => 100
  | 14 => 17
  | 15 => 74
  | 16 => 84
  | 17 => 9
  | 18 => 85
  | 19 => 60
  | 20 => 99
  | 21 => 39
  | 22 => 5
  | 23 => 1
  | 24 => 68
  | 25 => 77
  | 26 => 44
  | 27 => 4
  | 28 => 42
  | 29 => 8
  | 30 => 21
  | 31 => 14
  | 32 => 96
  | 33 => 33
  | 34 => 88
  | 35 => 7
  | 36 => 80
  | 37 => 43
  | 38 => 37
  | 39 => 88
  | 40 => 66
  | 41 => 82
  | 42 => 17
  | 43 => 53
  | 44 => 53
  | 45 => 16
  | 46 => 99
  | 47 => 89
  | _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

def fixedLiteralModZero : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralModZeroRow_0
  | 1 => fixedLiteralModZeroRow_1
  | 2 => fixedLiteralModZeroRow_2
  | 3 => fixedLiteralModZeroRow_3
  | 4 => fixedLiteralModZeroRow_4
  | 5 => fixedLiteralModZeroRow_5
  | 6 => fixedLiteralModZeroRow_6
  | 7 => fixedLiteralModZeroRow_7
  | 8 => fixedLiteralModZeroRow_8
  | 9 => fixedLiteralModZeroRow_9
  | 10 => fixedLiteralModZeroRow_10
  | 11 => fixedLiteralModZeroRow_11
  | 12 => fixedLiteralModZeroRow_12
  | 13 => fixedLiteralModZeroRow_13
  | 14 => fixedLiteralModZeroRow_14
  | 15 => fixedLiteralModZeroRow_15
  | 16 => fixedLiteralModZeroRow_16
  | 17 => fixedLiteralModZeroRow_17
  | 18 => fixedLiteralModZeroRow_18
  | 19 => fixedLiteralModZeroRow_19
  | 20 => fixedLiteralModZeroRow_20
  | 21 => fixedLiteralModZeroRow_21
  | 22 => fixedLiteralModZeroRow_22
  | 23 => fixedLiteralModZeroRow_23
  | 24 => fixedLiteralModZeroRow_24
  | 25 => fixedLiteralModZeroRow_25
  | 26 => fixedLiteralModZeroRow_26
  | 27 => fixedLiteralModZeroRow_27
  | 28 => fixedLiteralModZeroRow_28
  | 29 => fixedLiteralModZeroRow_29
  | 30 => fixedLiteralModZeroRow_30
  | 31 => fixedLiteralModZeroRow_31
  | 32 => fixedLiteralModZeroRow_32
  | 33 => fixedLiteralModZeroRow_33
  | 34 => fixedLiteralModZeroRow_34
  | 35 => fixedLiteralModZeroRow_35
  | 36 => fixedLiteralModZeroRow_36
  | 37 => fixedLiteralModZeroRow_37
  | 38 => fixedLiteralModZeroRow_38
  | 39 => fixedLiteralModZeroRow_39
  | 40 => fixedLiteralModZeroRow_40
  | 41 => fixedLiteralModZeroRow_41
  | 42 => fixedLiteralModZeroRow_42
  | 43 => fixedLiteralModZeroRow_43
  | 44 => fixedLiteralModZeroRow_44
  | 45 => fixedLiteralModZeroRow_45
  | 46 => fixedLiteralModZeroRow_46
  | 47 => fixedLiteralModZeroRow_47
  | _ => fun _ => 0

def fixedLiteralInvZero : Matrix (Fin 48) (Fin 48) (ZMod 101) :=
  fun r => match r.val with
  | 0 => fixedLiteralInvZeroRow_0
  | 1 => fixedLiteralInvZeroRow_1
  | 2 => fixedLiteralInvZeroRow_2
  | 3 => fixedLiteralInvZeroRow_3
  | 4 => fixedLiteralInvZeroRow_4
  | 5 => fixedLiteralInvZeroRow_5
  | 6 => fixedLiteralInvZeroRow_6
  | 7 => fixedLiteralInvZeroRow_7
  | 8 => fixedLiteralInvZeroRow_8
  | 9 => fixedLiteralInvZeroRow_9
  | 10 => fixedLiteralInvZeroRow_10
  | 11 => fixedLiteralInvZeroRow_11
  | 12 => fixedLiteralInvZeroRow_12
  | 13 => fixedLiteralInvZeroRow_13
  | 14 => fixedLiteralInvZeroRow_14
  | 15 => fixedLiteralInvZeroRow_15
  | 16 => fixedLiteralInvZeroRow_16
  | 17 => fixedLiteralInvZeroRow_17
  | 18 => fixedLiteralInvZeroRow_18
  | 19 => fixedLiteralInvZeroRow_19
  | 20 => fixedLiteralInvZeroRow_20
  | 21 => fixedLiteralInvZeroRow_21
  | 22 => fixedLiteralInvZeroRow_22
  | 23 => fixedLiteralInvZeroRow_23
  | 24 => fixedLiteralInvZeroRow_24
  | 25 => fixedLiteralInvZeroRow_25
  | 26 => fixedLiteralInvZeroRow_26
  | 27 => fixedLiteralInvZeroRow_27
  | 28 => fixedLiteralInvZeroRow_28
  | 29 => fixedLiteralInvZeroRow_29
  | 30 => fixedLiteralInvZeroRow_30
  | 31 => fixedLiteralInvZeroRow_31
  | 32 => fixedLiteralInvZeroRow_32
  | 33 => fixedLiteralInvZeroRow_33
  | 34 => fixedLiteralInvZeroRow_34
  | 35 => fixedLiteralInvZeroRow_35
  | 36 => fixedLiteralInvZeroRow_36
  | 37 => fixedLiteralInvZeroRow_37
  | 38 => fixedLiteralInvZeroRow_38
  | 39 => fixedLiteralInvZeroRow_39
  | 40 => fixedLiteralInvZeroRow_40
  | 41 => fixedLiteralInvZeroRow_41
  | 42 => fixedLiteralInvZeroRow_42
  | 43 => fixedLiteralInvZeroRow_43
  | 44 => fixedLiteralInvZeroRow_44
  | 45 => fixedLiteralInvZeroRow_45
  | 46 => fixedLiteralInvZeroRow_46
  | 47 => fixedLiteralInvZeroRow_47
  | _ => fun _ => 0

end InternalCatalan

end

section

namespace InternalCatalan

def fixedLiteralBaseMod (r : Fin 49) (k : Fin 48) : ZMod 101 :=
  match r.val with
  | 0 => fixedLiteralModZeroRow_0 k
  | 1 => fixedLiteralModZeroRow_1 k
  | 2 => fixedLiteralModZeroRow_2 k
  | 3 => fixedLiteralModZeroRow_3 k
  | 4 => fixedLiteralModZeroRow_4 k
  | 5 => fixedLiteralModZeroRow_5 k
  | 6 => fixedLiteralModZeroRow_6 k
  | 7 => fixedLiteralModZeroRow_7 k
  | 8 => fixedLiteralModZeroRow_8 k
  | 9 => fixedLiteralModZeroRow_9 k
  | 10 => fixedLiteralModZeroRow_10 k
  | 11 => fixedLiteralModZeroRow_11 k
  | 12 => fixedLiteralModZeroRow_12 k
  | 13 => fixedLiteralModZeroRow_13 k
  | 14 => fixedLiteralModZeroRow_14 k
  | 15 => fixedLiteralModZeroRow_15 k
  | 16 => fixedLiteralModZeroRow_16 k
  | 17 => fixedLiteralModZeroRow_17 k
  | 18 => fixedLiteralModZeroRow_18 k
  | 19 => fixedLiteralModZeroRow_19 k
  | 20 => fixedLiteralModZeroRow_20 k
  | 21 => fixedLiteralModZeroRow_21 k
  | 22 => fixedLiteralModZeroRow_22 k
  | 23 => fixedLiteralModZeroRow_23 k
  | 24 => fixedLiteralModZeroRow_24 k
  | 25 => fixedLiteralModZeroRow_25 k
  | 26 => fixedLiteralModZeroRow_26 k
  | 27 => fixedLiteralModZeroRow_27 k
  | 28 => fixedLiteralModZeroRow_28 k
  | 29 => fixedLiteralModZeroRow_29 k
  | 30 => fixedLiteralModZeroRow_30 k
  | 31 => fixedLiteralModZeroRow_31 k
  | 32 => fixedLiteralModZeroRow_32 k
  | 33 => fixedLiteralModZeroRow_33 k
  | 34 => fixedLiteralModZeroRow_34 k
  | 35 => fixedLiteralModZeroRow_35 k
  | 36 => fixedLiteralModZeroRow_36 k
  | 37 => fixedLiteralModZeroRow_37 k
  | 38 => fixedLiteralModZeroRow_38 k
  | 39 => fixedLiteralModZeroRow_39 k
  | 40 => fixedLiteralModZeroRow_40 k
  | 41 => fixedLiteralModZeroRow_41 k
  | 42 => fixedLiteralModZeroRow_42 k
  | 43 => fixedLiteralModZeroRow_43 k
  | 44 => fixedLiteralModZeroRow_44 k
  | 45 => fixedLiteralModZeroRow_45 k
  | 46 => fixedLiteralModZeroRow_46 k
  | 47 => fixedLiteralModZeroRow_47 k
  | _ => fixedLiteralModPlusRow_47 k - fixedLiteralModZeroRow_47 k

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

section

namespace InternalCatalan

end InternalCatalan

end

end OAI

end

section

namespace OAI

section

noncomputable section

namespace InternalCatalan

open scoped BigOperators

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

def palindromicPrimeCutoff (z : ℚ) : ℕ := max fixedDeterminantPrimeCutoff z.den

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

end InternalCatalan

end

end

section

noncomputable section

namespace InternalCatalan

end InternalCatalan

end

end

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

def barrierComplex (a b : ℚ) : ℂ := ⟨(a : ℝ), (b : ℝ)⟩

def barrierConjugatePair (z r : ℂ) : List (ℂ × ℂ) :=
  [(z, r), (star z, star r)]

def barrierP2Finite : List ℤ :=
  [45559127, -50750856, -6578767, 13970217, 4786184, -4292433, -576704, 1311615, 671564, -346453]

def barrierV2Finite : List ℤ :=
  [-23910158, 21152432, -2885110, -11558199, 6485289, 1456821, -1912176, -2263524, 2742210, -1162454]

def barrierP1Finite : List ℤ :=
  [11913521, -79993701, -21956443, 37903579, 10744022, -2073193, 570246, -24939103]

def barrierV1Finite : List ℤ :=
  [-89913025, 52874280, 45168341, -30708629, -19269841, 33922112, 9819141, -16992389]

def barrierP2Tail : List (ℂ × ℂ) :=
  [((barrierComplex (85 / 100) 0), (barrierComplex (-9338452 / 100000000) 0))] ++
  [((barrierComplex (94 / 100) 0), (barrierComplex (-2141509 / 100000000) 0))] ++
  barrierConjugatePair (barrierComplex 0 (7 / 10)) (barrierComplex (-66277922 / 200000000) (31907569 / 200000000)) ++
  barrierConjugatePair (barrierComplex 0 (85 / 100)) (barrierComplex (-1231651 / 200000000) (-6002645 / 200000000)) ++
  barrierConjugatePair (barrierComplex (92 / 1000) (92 / 100)) (barrierComplex (-3225918 / 200000000) (-8928234 / 200000000)) ++
  barrierConjugatePair (barrierComplex (-92 / 1000) (92 / 100)) (barrierComplex (-2105536 / 200000000) (9091287 / 200000000))

def barrierV2Tail : List (ℂ × ℂ) :=
  [((barrierComplex (-8 / 10) 0), (barrierComplex (15199211 / 100000000) 0))] ++
  [((barrierComplex (-96 / 100) 0), (barrierComplex (4451662 / 100000000) 0))] ++
  [((barrierComplex (88 / 100) 0), (barrierComplex (2545398 / 100000000) 0))] ++
  [((barrierComplex (95 / 100) 0), (barrierComplex (-4932634 / 100000000) 0))] ++
  [((barrierComplex (984 / 1000) 0), (barrierComplex (11618157 / 100000000) 0))] ++
  barrierConjugatePair (barrierComplex 0 (78 / 100)) (barrierComplex (27238714 / 200000000) (38447936 / 200000000)) ++
  barrierConjugatePair (barrierComplex 0 (9 / 10)) (barrierComplex (-31341084 / 200000000) (30188786 / 200000000)) ++
  barrierConjugatePair (barrierComplex 0 (955 / 1000)) (barrierComplex (-6693542 / 200000000) (-11912254 / 200000000)) ++
  barrierConjugatePair (barrierComplex 0 (984 / 1000)) (barrierComplex (2055213 / 200000000) (21715849 / 200000000))

def barrierLambda2 : ℝ := 0
def barrierLambda1 : ℝ := 247405979 / 100000000

def barrierFiniteCoeff (cs : List ℤ) (k : ℕ) : ℝ :=
  if k = 0 then 0 else (cs.getD (k - 1) 0 : ℝ) / 100000000

def barrierTrial (cs : List ℤ) (tail : List (ℂ × ℂ)) (k : ℕ) : ℝ :=
  if k = 0 then 0 else barrierFiniteCoeff cs k +
    (tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re

def barrierP2 : ℕ → ℝ := barrierTrial barrierP2Finite barrierP2Tail
def barrierV2 : ℕ → ℝ := barrierTrial barrierV2Finite barrierV2Tail
def barrierP1 : ℕ → ℝ := barrierTrial barrierP1Finite []
def barrierV1 : ℕ → ℝ := barrierTrial barrierV1Finite []

open Polynomial

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

section

def barrierTrialNormSq (u : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)

open Polynomial Filter
open scoped BigOperators

def barrierTrialT (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x /
    ((k + 1 : ℕ) : ℝ)

def barrierTrialS (u : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, u (k + 1) * x ^ (k + 1) / ((k + 1 : ℕ) : ℝ)

end

section

open scoped BigOperators

end
section

open Polynomial
open scoped BigOperators

end

section

open Polynomial Set Filter
open scoped BigOperators

end

open Polynomial

open Polynomial
open scoped BigOperators

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Set

end

section

open Polynomial
open scoped BigOperators

end

section

open Polynomial Set
open scoped BigOperators

end

section

open Set
open scoped BigOperators

def realEnergyField (k x : ℝ) : ℝ :=
  (19 / 48 : ℝ) * Real.log |x| + (1 / 12 : ℝ) * Real.log (1 - x) -
    (k / 2 + 17 / 48) * Real.log (1 + x ^ 2)

def realEnergyColumnField (s : ℝ) : ℝ :=
  (7 / 48 : ℝ) * Real.log s + (1 / 12 : ℝ) * Real.log (1 - s)

def realEnergyCaseField (x : ℝ) : ℝ :=
  (1 / 6 : ℝ) - 2 * x ^ 2 / (1 + x ^ 2)

end

section

open scoped BigOperators

end

open Set
open scoped BigOperators

def realEnergyRowTrialField (k lam : ℝ) (p v : ℕ → ℝ) (x : ℝ) : ℝ :=
  realEnergyField k x + lam * realEnergyCaseField x -
    2 * k * barrierTrialT p x - barrierTrialS v x

def realEnergyColumnTrialField (v : ℕ → ℝ) (s : ℝ) : ℝ :=
  realEnergyColumnField s + 2 * barrierTrialT v s

def realEnergyDualConstant (k : ℝ) (p v : ℕ → ℝ) (Bx Bs : ℝ) : ℝ :=
  -(11 / 16 : ℝ) * Real.log 2 + k * barrierTrialNormSq p + barrierTrialNormSq v / 2 + Bx + Bs

open Set
open scoped BigOperators

def realEnergyRowTrialSup (k lam : ℝ) (p v : ℕ → ℝ) : ℝ :=
  sSup (realEnergyRowTrialField k lam p v '' {x : ℝ | x ∈ Ico (-1 : ℝ) 1 ∧ x ≠ 0})

def realEnergyColumnTrialSup (v : ℕ → ℝ) : ℝ :=
  sSup (realEnergyColumnTrialField v '' Ioo (0 : ℝ) 1)

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

end

section

open Polynomial

def barrierBracketLeft (m : ℤ) : ℚ := (m : ℚ) / 10000000000

def barrierBracketRight (m : ℤ) : ℚ := ((m + 2 : ℤ) : ℚ) / 10000000000

end

section

open Polynomial
open scoped BigOperators

end

open Polynomial

open Polynomial

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial

end

section

open Polynomial

def barrierCase2XBrackets : List ℤ :=
  [-9601109148, -8942317572, -7608305633,
   -6503394794, -5185864065, -4015634158,
   -3108806646, -2067921826, -1589849496,
   1531948062, 2072448179, 3208186484,
   4381119427, 5851354199, 7269030693,
   8390277402, 9332614564, 9709786219]

def barrierCase2YBrackets : List ℤ :=
  [176402802, 330649406, 764952882,
   1227250753, 2149465998, 3048189112,
   4322699096, 5564757994, 6801929373,
   8031988371, 8877037851, 9577761832,
   9838463999, 9972727815, 9992037196]

end

open Polynomial

open Polynomial

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section

namespace InternalCatalan

section

def barrierCase2X (x : ℝ) : ℝ :=
  realEnergyField 2 x + barrierLambda2 * realEnergyCaseField x -
    4 * barrierTrialT barrierP2 x - barrierTrialS barrierV2 x

def barrierCase2Y (x : ℝ) : ℝ :=
  realEnergyColumnField x + 2 * barrierTrialT barrierV2 x

end

section

open Set Filter
open scoped Topology

end

section
open scoped BigOperators

end
section

end

section

open scoped ComplexConjugate

end

open Set

end InternalCatalan

end

end OAI

end

section

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace InternalCatalan

def realDeterminantSheetPrefactor (N : ℕ) : ℝ :=
  max ((1 + 10 * Real.exp 12 * (n N : ℝ)) ^ n N)
    ((3 / 2 : ℝ) ^ n N * (n N : ℝ) ^ ((n N : ℝ) / 2))

end InternalCatalan

end

noncomputable section
open Set Filter
open scoped BigOperators

namespace InternalCatalan

end InternalCatalan

end

noncomputable section
open Set Filter
open scoped BigOperators

namespace InternalCatalan

def realDeterminantCertificateSupBound : ℝ :=
  max (realEnergyDualConstant 1 barrierP1 barrierV1
      (realEnergyRowTrialSup 1 barrierLambda1 barrierP1 barrierV1)
      (realEnergyColumnTrialSup barrierV1))
    (realEnergyDualConstant 2 barrierP2 barrierV2
      (realEnergyRowTrialSup 2 0 barrierP2 barrierV2) (realEnergyColumnTrialSup barrierV2))

end InternalCatalan

end

noncomputable section
open Set Filter

namespace InternalCatalan

end InternalCatalan

end

end OAI

end


