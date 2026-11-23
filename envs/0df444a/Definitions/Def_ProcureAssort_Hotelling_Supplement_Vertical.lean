-- Prove2me | Definitions.Def_ProcureAssort_Hotelling_Supplement_Vertical
-- name    : ProcureAssort_Hotelling_Supplement_Vertical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:28:31.466494+00:00
-- url     : https://prove2.me/theorems/52215535-9ffc-4393-840b-5cd3aebd478b
-- title:
--   Vertical quality utilities, active demand, gross surplus and price equations
-- statement:
--   Qualities are strictly increasing. A uniformly distributed consumer $u\in[0,1]$ receives utility $u\alpha_i-p_i$ from product $i$ and buys one unit. A supplier is active when it strictly maximizes utility somewhere on the unit interval. Consecutive active price-to-quality slopes delimit each supplier's consumer interval; absent lower and upper neighbors give interval endpoints zero and one, including unit demand for a singleton assortment.
--
--   $$GCS(x)=\sum_i\int_{\sum_{j<i}x_j}^{\sum_{j\le i}x_j}u\alpha_i\,du.$$
--
--   The price-system predicate records adjacent active price differences equal to their virtual-cost differences and interim price-times-quantity transfers equal to the envelope transfers. It is an object used to describe implementation, not an extra premise of Theorem I.1. No sign restriction is imposed on quality.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), Appendix I, (33)–(35), pp. 60–61

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Supplement_Types

open scoped Classical

namespace ProcureAssort.Hotelling.Supplement

/-- Uniform consumers of type u∈[0,1], serving blocks in increasing quality order.
The integrands are continuous, so the interval integrals have no integrability default. -/
noncomputable def verticalGCS {n : ℕ} (alpha : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∫ u in (∑ j ∈ Finset.univ.filter (· < i), x j)..
      (∑ j ∈ Finset.univ.filter (· ≤ i), x j), u * alpha i

/-- A supplier is active iff it strictly maximizes consumer utility somewhere in [0,1].
Strictly ordered qualities make ties null sets. Appendix I, pp. 60–61. -/
noncomputable def verticalQ {n : ℕ} (alpha p : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∃ u ∈ Set.Icc (0 : ℝ) 1,
    ∀ j, j ≠ i → u * alpha j - p j < u * alpha i - p i)

/-- Demand (34), expressed by the two endpoints of the consumer-type interval.
Missing predecessor/successor means endpoint 0/1; this also gives 1 for a singleton. -/
noncomputable def verticalDemand {n : ℕ} (alpha p : Fin n → ℝ) (i : Fin n) : ℝ :=
  let Q := verticalQ alpha p
  if i ∈ Q then
    (if h : (Q.filter (i < ·)).Nonempty then
      let j := (Q.filter (i < ·)).min' h
      (p j - p i) / (alpha j - alpha i)
    else 1) -
    (if h : (Q.filter (· < i)).Nonempty then
      let j := (Q.filter (· < i)).max' h
      (p i - p j) / (alpha i - alpha j)
    else 0)
  else 0

/-- The adjacent virtual-cost slope in (I.1), with endpoints explicitly in range. -/
noncomputable def qualitySlope {n : ℕ} (alpha p : Fin n → ℝ) (k : ℕ) (hk : k+1 < n) : ℝ :=
  (p ⟨k+1,hk⟩ - p ⟨k,by omega⟩) / (alpha ⟨k+1,hk⟩ - alpha ⟨k,by omega⟩)

/-- The price-difference and interim-transfer system (35). It is a condition on prices,
not an assumption inserted into Theorem I.1. -/
def VerticalPriceSystem {n : ℕ} (alpha : Fin n → ℝ) (Θ : Fin n → Finset ℝ)
    (f : Fin n → ℝ → ℝ) (p : Profile Θ → Fin n → ℝ) : Prop :=
  let x := fun θ : Profile Θ => verticalDemand alpha (vvec Θ f θ)
  (∀ θ, ∀ i ∈ verticalQ alpha (vvec Θ f θ),
    ∀ j ∈ verticalQ alpha (vvec Θ f θ), i < j →
      (∀ k ∈ verticalQ alpha (vvec Θ f θ), ¬ (i < k ∧ k < j)) →
      p θ j - p θ i = virtualCost Θ f j (θ j) - virtualCost Θ f i (θ i)) ∧
  (∀ i, ∀ c ∈ Θ i,
    interim f (fun θ => p θ i * x θ i) i c =
      interim f (fun θ => tstar Θ x θ i) i c)

end ProcureAssort.Hotelling.Supplement


