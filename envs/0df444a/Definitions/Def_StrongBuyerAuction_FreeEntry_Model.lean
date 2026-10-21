-- Prove2me | Definitions.Def_StrongBuyerAuction_FreeEntry_Model
-- name    : StrongBuyerAuction_FreeEntry_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:11:13.946012+00:00
-- url     : https://prove2.me/theorems/09768f82-2c82-4e60-81a1-1c1ae2e63dae
-- title:
--   §2–§5, pp. 9–14 — value laws, FOSD, regular-buyer profit, seller revenue and free entry
-- statement:
--   Let $F$ be the value distribution function of each regular buyer and $G$ that of the strong buyer. Each is the cumulative distribution function of a probability law concentrated on $[0,1]$. A law $G$ **strictly dominates** $F$ in the paper's first-order sense when $G(z)\le F(z)$ throughout $(0,1)$, with strict inequality on a set of positive Lebesgue measure. The positive-measure predicate `StrictWhereOpen` additionally requires $G'(z)<G(z)$ at values where $F(z)<1$; `ProfitNondegenerate` requires $G(z)>0$ and $F(z)<1$ on a positive-measure set.
--
--   For real $N$, the gross profit of a regular buyer, the seller's expected revenue, and the free-entry condition are
--
--   $$
--   \pi(N\mid G)=\int_0^1(1-F(z))G(z)F(z)^{N-1}\,dz,\qquad
--   R(N\mid G)=1-\int_0^1F(z)^N\,dz-N\pi(N\mid G),\qquad
--   \pi(N\mid G)=c,\quad N\ge1.
--   $$
--
--   These definitions fix the common model for the comparative statics and the main revenue result.
--
--   **Formalization Note** The inequalities involving a distribution function use its CDF, not its measure directly. The extra strictness predicates expose the nondegeneracy used by the paper's strict claims. The interval integrals are Lebesgue integrals over $[0,1]$; atoms at either endpoint do not change them. At $F(z)=0$, real powers and $F(z)^N\log F(z)$ use the standard zero convention.
-- source:
--   Marquez & Singh, Selling assets: Are sellers better off with strong buyers?, SSRN working paper 3949699 (October 2021), pp. 9–14 (PDF 10–15), §2, eq. (1), (3), (4)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace StrongBuyerAuction.FreeEntry

/-- A value distribution supported on the normalized interval. -/
def IsValueLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Icc 0 1) = 1

/-- The first law dominates the second in the paper's strict FOSD sense. -/
def FOSD (G F : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Ioo (0 : ℝ) 1, G x ≤ F x) ∧
    0 < volume {x ∈ Set.Ioo (0 : ℝ) 1 | G x < F x}

/-- Dominance changes regular-buyer profit on a positive-measure set. -/
def StrictWhereOpen (F G' G : ℝ → ℝ) : Prop :=
  0 < volume {x ∈ Set.Ioo (0 : ℝ) 1 | G' x < G x ∧ F x < 1}

/-- A positive-measure set on which adding a regular buyer strictly lowers profit. -/
def ProfitNondegenerate (F G : ℝ → ℝ) : Prop :=
  0 < volume {x ∈ Set.Ioo (0 : ℝ) 1 | 0 < G x ∧ F x < 1}

/-- Equation (1): gross expected profit of any one regular bidder. -/
noncomputable def piReg (F G : ℝ → ℝ) (N : ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..1, (1 - F z) * G z * F z ^ (N - 1)

/-- Equation (3) and the proof of Lemma 1: the seller's expected revenue. -/
noncomputable def rev (F G : ℝ → ℝ) (N : ℝ) : ℝ :=
  1 - (∫ z in (0 : ℝ)..1, F z ^ N) - N * piReg F G N

/-- Equation (4) and the standing assumption that at least one regular bidder enters. -/
def IsFreeEntry (F G : ℝ → ℝ) (c N : ℝ) : Prop :=
  piReg F G N = c ∧ 1 ≤ N

end StrongBuyerAuction.FreeEntry


