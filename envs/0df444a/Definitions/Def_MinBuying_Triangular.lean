-- Prove2me | Definitions.Def_MinBuying_Triangular
-- name    : MinBuying_Triangular
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T16:15:18.661276+00:00
-- url     : https://prove2.me/theorems/d3dd93b1-7909-4c38-bc91-b68a0b58e89a
-- title:
--   Concrete triangular probability laws and canonical markets
-- statement:
--   Defines $\operatorname{Tri}(a,v)$ concretely as the image of uniform measure on $(0,1)$ under $u\mapsto\min\{v,au/(1-u)\}$. Positive parameters give the source's cap atom and triangular revenue curve. Defines finite independent triangular families, the continuation recursion from zero, the rejection product, and the canonical joint product law and designated cap-price vector. Distributional and revenue identities are separate theorem obligations.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . Section 4.2 pp.18–20, Eqs.(11)–(13); Lemma EC.1 PDF p.45/ec18.

import Definitions.Def_MinBuying_Model
import Definitions.Def_MinBuying_CanonicalAlgebra

/-! Concrete triangular-revenue probability laws and their canonical market.
The measure is an explicit pushforward; none of its distributional or pricing
properties is inserted as an assumption in the definitions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace MinBuying

/-- Uniform probability measure on the open unit interval. -/
def unitIntervalLaw : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- `Tri(a,v)` from equation (11), for positive `a` and `v`.
An equal-revenue quantile transform is capped at `v`, leaving the stated atom
at the cap. Inclusive affordability accepts that atom at price `v`. -/
def triangularLaw (a v : ℝ) : Measure ℝ :=
  Measure.map (fun u : ℝ => min v (a * u / (1 - u))) unitIntervalLaw

/-- Right CDF of the triangular law. This differs from strict rejection
at the cap: the right CDF is one there, whereas rejection is `v/(v+a)`. -/
def triangularCDF (a v p : ℝ) : ℝ :=
  if p < 0 then 0 else if p < v then p / (p + a) else 1

/-- A finite family of genuine positive-parameter triangular laws.
Empty families are allowed for the rejection-product base case; pricing
theorems require a positive number of items explicitly. -/
structure TriangularInstance (n : ℕ) where
  a : Fin n → ℝ
  cap : Fin n → ℝ
  a_pos : ∀ i, 0 < a i
  cap_pos : ∀ i, 0 < cap i

def triangularMarginals {n : ℕ} (I : TriangularInstance n) : Fin n → Measure ℝ :=
  fun i => triangularLaw (I.a i) (I.cap i)

def triangularJoint {n : ℕ} (I : TriangularInstance n) : JointLaw n :=
  productLaw (triangularMarginals I)

/-- Continuation recursion from zero, when the cap vector is in decreasing
order. The final stage is `k=n`; intermediate stages restrict `k ≤ n`. -/
def triangularContinuation {n : ℕ} (I : TriangularInstance n) (k : ℕ) : ℝ :=
  ((List.finRange n).take k).foldl
    (fun C i => continuationStep (I.a i) (I.cap i) C) 0

/-- Product appearing in Lemma EC.1; it equals actual joint rejection
when the positive common price is at most every cap. -/
def triangularRejectionProduct {n : ℕ} (I : TriangularInstance n) (t : ℝ) : ℝ :=
  ∏ i : Fin n, t / (t + I.a i)

/-- Insert the terminal `Tri(1,P)` item before the additional canonical items.
The ordering here is decreasing cap order, not buyer inspection order. -/
def canonicalParameters (I : CanonicalInstance) : TriangularInstance (I.count + 1) where
  a := Fin.cons 1 I.a
  cap := Fin.cons I.terminalCap I.cap
  a_pos := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact zero_lt_one
    · intro j
      exact I.a_pos j
  cap_pos := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact lt_trans zero_lt_one I.terminal_one_lt
    · intro j
      exact lt_trans zero_lt_one (I.cap_one_lt j)

def canonicalLaw (I : CanonicalInstance) : JointLaw (I.count + 1) :=
  triangularJoint (canonicalParameters I)

def canonicalPrices (I : CanonicalInstance) : Prices (I.count + 1) :=
  Fin.cons I.terminalCap I.cap

end MinBuying


