-- Prove2me | Definitions.Def_RetailerMarketplace_PositiveFee_Model
-- name    : RetailerMarketplace_PositiveFee_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:45.44838+00:00
-- url     : https://prove2.me/theorems/3c1e1762-a979-4b4c-be4c-5c15077a733b
-- title:
--   §5, p. 7 — Π_M(k, f), the monopolist's profit as a function of the fee f, the value of his Stage-2 allocation problem over all measurable allocations of mass ≤ k
-- statement:
--   This file defines the monopolist's equilibrium profit as a function of the marketplace fee in Hervas-Drane and Shelegia's retailer-led marketplace. It builds on the shared model file of the paper (`RetailerMarketplace.Entry.Model`), which fixes the product distribution $\mu$ (the CDF $G$ of the paper, on $[c,\infty)$), the marketplace products $\mathrm{mp}(c,f)=\{v : v(1-f)\ge c\}$ that the third-party sellers enter (Lemma 1, display (1)), the per-market payoffs of Proposition 1, the admissible allocations (measurable sets $A$ of products with $\mu(A)\le k$) and the monopolist's total profit from an allocation,
--   $$\mathrm{profit}_M(A)=\int_{A\setminus \mathrm{mp}}(v-c)\,d\mu+\int_{A\cap \mathrm{mp}}\pi_M^{SBMT}(f,v)\,d\mu+\int_{\mathrm{mp}\setminus A} fv\,d\mu ,$$
--   with $\pi_M^{SBMT}(f,v)=\lambda(v-c)+(1-\lambda)f\bar p_T$ and $\bar p_T=\dfrac{\lambda v+c(1-\lambda)}{1-f(1-\lambda)}$.
--
--   **The fee-stage value.** For a fee $f$, steering share $\lambda$ and capacity $k$, the monopolist's profit as a function of the fee is the value of his Stage-2 allocation problem:
--   $$\Pi_M(k,f)=\sup\{\mathrm{profit}_M(A) : A \text{ measurable},\ \mu(A)\le k\}.$$
--
--   This is the objective the monopolist maximises in Stage 1 (§5): Stage 3 is solved by Proposition 1, the sellers' Stage-2 entry by Lemma 1, and the monopolist's Stage-2 entry is the optimisation inside $\Pi_M$.
--
--   **Formalization Note.** The paper writes $\Pi_M$ through its closed form (4), whose thresholds $v_L,v_H$ come from Proposition 2; by Proposition 2 the supremum above equals (4), and the supremum form is used because it needs no thresholds. The supremum ranges over all measurable sets of mass at most $k$, not only intervals. The hypotheses on $\mu$ (probability, support in $[c,\infty)$, absolute continuity, $\int|v|\,d\mu<\infty$) are carried by the theorems, not by this file; under them the set of profits is nonempty (the empty allocation) and bounded above, so $\Pi_M$ is a genuine supremum and not Lean's junk value $0$.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 7 (PDF p. 9), §5, display (4)

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model

namespace RetailerMarketplace.PositiveFee

open MeasureTheory

/-- `Π_M(k, f)`: the monopolist's equilibrium profit as a function of the fee `f`, the value of his
Stage-2 allocation problem (supremum of `profitM` over all admissible allocations). -/
noncomputable def PiM (μ : Measure ℝ) (c f lam k : ℝ) : ℝ :=
  sSup (RetailerMarketplace.Entry.profitM μ c f lam '' {A | RetailerMarketplace.Entry.Admissible μ k A})

end RetailerMarketplace.PositiveFee


