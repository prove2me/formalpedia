-- Prove2me | Definitions.Def_CappedBaseStock_Window
-- name    : CappedBaseStock_Window
-- status  : Definition
-- author  : @StellaXin
-- created : 2026-09-08T02:23:33.634344+00:00
-- url     : https://prove2.me/theorems/8e5c0208-f0d6-4552-abf0-d2f6c6ff8dcf
-- title:
--   Independent finite-window inventory inputs
-- statement:
--   For a nonnegative integer $n$, an inventory window input consists of a nonnegative initial inventory $I_0$ and $n$ nonnegative deliveries $A_0,\ldots,A_{n-1}$. A window law $W$ is a probability law on this vector with finite first moments for every coordinate. Dependence among its coordinates is allowed.
--
--   Given a fresh i.i.d. demand sequence $(D_k)$ with law $P$, independent of the entire input vector, define
--
--   $$
--   I_{k+1}=(I_k+A_k-D_k)^+,
--   \qquad (x)^+=\max\{x,0\}.
--   $$
--
--   Deliveries are extended by zero after the $n$ specified coordinates. The expected inventory at horizon $m$ is the nonnegative extended expectation $\mathbb E[I_m]$ under the product of the input law and the demand-path law. The common-means condition is
--
--   $$
--   \mathbb E[I_0]=z,\qquad \mathbb E[A_i]=r\quad(0\le i<n).
--   $$
--
--   These definitions expose the independence and moment assumptions needed for finite-window inventory inequalities. They impose no stationarity, policy-cost comparison, or certificate constraint.
-- source:
--   Linwei Xin, Capped Base-Stock Policies: A 2.33-Approximation, user-supplied 2026 manuscript, Proposition 1 (label lemma-lb), source-manuscript.tex lines 253-303; SHA-256 f353793c255e1ebed5f3ec541037284bd926183e3e5b71941f13e79c2d67cb7a. Auxiliary finite-dimensional interface for the proof at lines 277-300; the independence and recursion follow the model and the two unrolled inventory windows. This is a new definition, not a verbatim declaration from the manuscript.

import Definitions.Def_CappedBaseStock_Model

/-!
Independent finite-window inventory inputs for the lower-certificate proof.
The input consists of initial on-hand stock and finitely many committed
deliveries. Its joint law is independent of the fresh demand path by the
explicit product measure below. No stationarity or cost bound is assumed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace CappedBaseStock

abbrev WindowInput (n : ℕ) := ℝ≥0 × (Fin n → ℝ≥0)

/-- An integrable nonnegative inventory/delivery vector with arbitrary
dependence among its coordinates. -/
structure WindowLaw (n : ℕ) where
  law : Measure (WindowInput n)
  probability : IsProbabilityMeasure law
  inventory_integrable : Integrable (fun w : WindowInput n => (w.1 : ℝ)) law
  delivery_integrable : ∀ i : Fin n,
    Integrable (fun w : WindowInput n => (w.2 i : ℝ)) law

attribute [instance] WindowLaw.probability

def WindowMeans {n : ℕ} (W : WindowLaw n) (r z : ℝ) : Prop :=
  (∫ w, (w.1 : ℝ) ∂W.law) = z ∧
    ∀ i : Fin n, (∫ w, (w.2 i : ℝ) ∂W.law) = r

/-- The predetermined delivery in period k, extended by zero outside the window. -/
def windowDelivery {n : ℕ} (w : WindowInput n) (k : ℕ) : ℝ≥0 :=
  if hk : k < n then w.2 ⟨k, hk⟩ else 0

/-- End inventory after k demands, with the initial inventory at k=0. -/
def windowInventory {n : ℕ} (w : WindowInput n) (d : DemandPath) : ℕ → ℝ≥0
  | 0 => w.1
  | k + 1 => windowInventory w d k + windowDelivery w k - d k

/-- Independent fresh demands; within-window input coordinates may be dependent. -/
def windowExpectedInventory (P : DemandLaw) {n : ℕ} (W : WindowLaw n)
    (m : ℕ) : ℝ≥0∞ :=
  ∫⁻ wd : WindowInput n × DemandPath,
    (windowInventory wd.1 wd.2 m : ℝ≥0∞) ∂(W.law.prod (demandPathLaw P))

end CappedBaseStock


