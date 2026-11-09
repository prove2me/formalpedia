-- Prove2me | Definitions.Def_CaiZhuInfo_Matrix_matrixProduct
-- name    : CaiZhuInfo_Matrix_matrixProduct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:08.699175+00:00
-- url     : https://prove2.me/theorems/63b49207-2c5e-4226-be11-3c899929d110
-- title:
--   Finite-field matrix multiplication and prediction quantities
-- statement:
--   Let $F$ be any finite field with $q=|F|$. Vectors and matrices are arrays indexed by finite coordinate sets. Matrix multiplication returns the entire matrix
--   $$\mathrm{MM}_{t,s,m}(X,Y)=XY^\top.$$
--   Independent laws are constructed as product distributions, and uniform laws assign equal probability to every element. Scalar prediction error is the probability that $z(Y)$ differs from the target under the product of the two given marginals. The optimal prediction advantage and score are
--   $$\rho_{P_X}(y)=\frac{q\max_a P(X^\top y=a)-1}{q-1},\qquad f_\phi(x)=1-\frac q{q-1}P_Y(x^\top Y\ne\phi(Y)).$$
--   The clipped error coefficient and rank average are computed as
--   $$\alpha_{q,t,s}(\varepsilon)=\max\!\left(1-\frac{q^{ts}}{q^{ts}-1}\varepsilon,0\right),\qquad \kappa_{q,t,s}=\frac1{q^{ts}-1}\sum_{\Lambda\ne0}\frac t{\operatorname{rank}\Lambda}.$$
--   Projection averages are uniform averages over all full-row-rank matrices, applied to the actual pushforward law of the input. The matrix information complexities use independent uniform inputs and the operational protocol infima. No input-rank condition or comparison between the column count and row counts is imposed. All divisions and logarithms in the source domains have positive denominators or arguments.
-- source:
--   Xiaohong Cai, Mingyang Zhu, STOC 2027 submission #616 (October 2026), §1.1, (3)–(5), §5, (22),(24), §6.2, printed pp.2,15–16,20 / PDF pp.3,16–17,21; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/616.pdf

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol

open MeasureTheory
open scoped ENNReal

namespace CaiZhuInfo.Matrix
noncomputable section
open scoped Classical

variable {F : Type} [Field F] [Fintype F]

abbrev Vec (F : Type) (m : ℕ) := Fin m → F
abbrev Mat (F : Type) (t m : ℕ) := _root_.Matrix (Fin t) (Fin m) F

/-- Discrete σ-algebras on the finite matrix/vector alphabets. -/
instance vectorMeasurable (m : ℕ) : MeasurableSpace (Vec F m) := ⊤
instance matrixMeasurable (t m : ℕ) : MeasurableSpace (Mat F t m) := ⊤

/-- The whole output matrix, not an entry or a selected test. Cai–Zhu (3). -/
def matrixProduct {t s m : ℕ} (X : Mat F t m) (Y : Mat F s m) : Mat F t s :=
  X * Y.transpose

def innerProduct {m : ℕ} (x y : Vec F m) : F := ∑ i, x i * y i

def frobenius {d m : ℕ} (A B : Mat F d m) : F := ∑ i, ∑ j, A i j * B i j

def bilinearForm {n m : ℕ} (A : Mat F n m) (x : Vec F n) (y : Vec F m) : F :=
  ∑ i, ∑ j, x i * A i j * y j

/-- Product law explicitly enforces independence; arbitrary marginals are allowed. -/
def independentLaw {A B : Type} (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind fun a => q.map fun b => (a, b)

def uniformLaw (A : Type) [Fintype A] [Nonempty A] : PMF A := PMF.uniformOfFintype A

def predictionError {A B : Type} [Fintype A] [Fintype B]
    (p : PMF A) (q : PMF B) (target : A → B → F) (z : B → F) : ℝ :=
  mean p (fun x => mean q (fun y => if z y = target x y then 0 else 1))

def innerValueMass {m : ℕ} (p : PMF (Vec F m)) (y : Vec F m) (a : F) : ℝ :=
  mass (p.map fun x => innerProduct x y) a

def predictionAdvantage {m : ℕ} (p : PMF (Vec F m)) (y : Vec F m) : ℝ :=
  ((Fintype.card F : ℝ) * (Finset.univ.image (innerValueMass p y)).max' (by simp) - 1) /
    ((Fintype.card F : ℝ) - 1)

def OptimalPredictor {m : ℕ} (p : PMF (Vec F m)) (φ : Vec F m → F) : Prop :=
  ∀ y a, innerValueMass p y a ≤ innerValueMass p y (φ y)

def predictionScore {m : ℕ} (q : PMF (Vec F m)) (φ : Vec F m → F) (x : Vec F m) : ℝ :=
  1 - (Fintype.card F : ℝ) / ((Fintype.card F : ℝ) - 1) *
    mean q (fun y => if innerProduct x y = φ y then 0 else 1)

/-- (4), with real arithmetic and two distinct positive-part operations in the goal. -/
def alpha (F : Type) [Fintype F] (t s : ℕ) (ε : ℝ) : ℝ :=
  max (1 - (Fintype.card F : ℝ) ^ (t * s) /
    ((Fintype.card F : ℝ) ^ (t * s) - 1) * ε) 0

/-- (5), averaged over all nonzero test matrices, including singular ones. -/
def kappa (F : Type) [Field F] [Fintype F] (t s : ℕ) : ℝ :=
  let tests := Finset.univ.filter (fun A : Mat F t s => A ≠ 0)
  (∑ A ∈ tests, (t : ℝ) / (A.rank : ℝ)) / (tests.card : ℝ)

def fullRowRankMatrices (F : Type) [Field F] [Fintype F] (d t : ℕ) : Finset (Mat F d t) :=
  Finset.univ.filter fun T => T.rank = d

/-- Conditional on each fixed independent uniform T, TZ has this pushforward law. -/
def projectedLaw {d t m : ℕ} (T : Mat F d t) (p : PMF (Mat F t m)) : PMF (Mat F d m) :=
  p.map fun Z => T * Z

def projectionMean {d t : ℕ} (f : Mat F d t → ℝ) : ℝ :=
  let ts := fullRowRankMatrices F d t
  (∑ T ∈ ts, f T) / (ts.card : ℝ)

/-- The product-uniform matrix prior. -/
def matrixPrior (F : Type) [Field F] [Fintype F] (t s m : ℕ) : PMF (Mat F t m × Mat F s m) :=
  independentLaw (uniformLaw (Mat F t m)) (uniformLaw (Mat F s m))

def matrixIC (F : Type) [Field F] [Fintype F] (t s m : ℕ) (ε : ℝ)
    (pointwise transcriptOutput : Bool) : ℝ :=
  informationComplexity (matrixPrior F t s m) matrixProduct ε pointwise transcriptOutput

end
end CaiZhuInfo.Matrix


