-- Prove2me | Definitions.Def_SupplyChainCarbon_Necessity_Marginals
-- name    : SupplyChainCarbon_Necessity_Marginals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:35:29.972448+00:00
-- url     : https://prove2.me/theorems/78858454-00ec-4b2e-8520-b80b58727e18
-- title:
--   Domain derivatives, influence and marginal carbon accounting
-- statement:
--   Let $a_{i,n,j}(e)$ be the partial derivative of the process footprint $f_i$ with respect to action $j$ of firm $n$, taken within $E$. Let $q_{n,i}(\phi)$ be the derivative of total payment $h_n$ with respect to footprint coordinate $i$, taken within $F$. Define
--
--   $$b_{n,i}(e)=\mathbf1\!\left\{\sum_j a_{i,n,j}(e)<0\right\},\qquad H_i(\phi)=\sum_n q_{n,i}(\phi).$$
--
--   Relevant incidence requires every row and column of $b(e)$ to sum to at least one. Joint carbon production means some column sums to at least two, counting distinct firms. Footprint balance means $H_i(\phi)=p$ for every process and nonnegative footprint; double-counting means $H_i(\phi)>p$ for some such pair.
--
--   The marginal condition is all of equation (14): for every $n,j$,
--
--   $$\sum_i a_{i,n,j}(e)\big(q_{n,i}(f(e))-p\big)=\sum_i a_{i,n,j}(e)\big(q_{n,i}(f(e))-p b_{n,i}(e)\big)=0.$$
--
--   The quantities are computed, rather than supplied as unrestricted independent variables. Fréchet derivatives within the domains are applied to coordinate basis vectors. The technology and payment-rule assumptions ensure differentiability; the theorems use interior effort points. The source suppresses the profile in its definition of influence; the theorem statements explicitly evaluate it at the implementing first best.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, §3.1, pp. 8–9; §3.3, p. 10, Eq. (2) and following definition; Appendix A, p. 24, Eq. (14)

import Definitions.Def_SupplyChainCarbon_Necessity_PaymentRule

noncomputable section

namespace SupplyChainCarbon.Necessity

/-- Within-domain effort derivative applied to a single action coordinate. -/
def effortPartial {N I : ℕ} {m : Fin N → ℕ}
    (C : Technology N I m) (e : Effort N m) (i : Fin I) (n : Fin N) (j : Fin (m n)) : ℝ :=
  fderivWithin ℝ (fun x => C.footprint x i) (effortBox m C.bound) e
    (Pi.single n (Pi.single j 1))

/-- Within-orthant derivative with respect to one process footprint. -/
def paymentPartial {N I : ℕ} {p : ℝ} (R : PaymentRule N I p)
    (φ : Footprint I) (n : Fin N) (i : Fin I) : ℝ :=
  fderivWithin ℝ (R.payment n) (footprintOrthant I) φ (Pi.single i 1)

/-- Influence is derived at the supplied profile, never supplied as unrelated data. -/
def incidence {N I : ℕ} {m : Fin N → ℕ}
    (C : Technology N I m) (e : Effort N m) (n : Fin N) (i : Fin I) : ℕ :=
  if (∑ j, effortPartial C e i n j) < 0 then 1 else 0

def relevantIncidence {N I : ℕ} {m : Fin N → ℕ}
    (C : Technology N I m) (e : Effort N m) : Prop :=
  (∀ n, 1 ≤ ∑ i, incidence C e n i) ∧ (∀ i, 1 ≤ ∑ n, incidence C e n i)

def jointProduction {N I : ℕ} {m : Fin N → ℕ}
    (C : Technology N I m) (e : Effort N m) : Prop :=
  ∃ i, 2 ≤ ∑ n, incidence C e n i

def aggregateMarginal {N I : ℕ} {p : ℝ} (R : PaymentRule N I p)
    (φ : Footprint I) (i : Fin I) : ℝ := ∑ n, paymentPartial R φ n i

def footprintBalanced {N I : ℕ} {p : ℝ} (R : PaymentRule N I p) : Prop :=
  ∀ φ ∈ footprintOrthant I, ∀ i, aggregateMarginal R φ i = p

def doubleCounts {N I : ℕ} {p : ℝ} (R : PaymentRule N I p) : Prop :=
  ∃ φ ∈ footprintOrthant I, ∃ i, p < aggregateMarginal R φ i

/-- The complete chained equation (14), including both sums. -/
def marginalCondition {N I : ℕ} {m : Fin N → ℕ} {p : ℝ}
    (C : Technology N I m) (R : PaymentRule N I p) (e : Effort N m) : Prop :=
  ∀ n j,
    (∑ i, effortPartial C e i n j * (paymentPartial R (C.footprint e) n i - p)) =
      (∑ i, effortPartial C e i n j *
        (paymentPartial R (C.footprint e) n i - p * (incidence C e n i : ℝ))) ∧
    (∑ i, effortPartial C e i n j *
      (paymentPartial R (C.footprint e) n i - p * (incidence C e n i : ℝ))) = 0

end SupplyChainCarbon.Necessity


