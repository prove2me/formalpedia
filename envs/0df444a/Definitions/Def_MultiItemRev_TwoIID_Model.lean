-- Prove2me | Definitions.Def_MultiItemRev_TwoIID_Model
-- name    : MultiItemRev_TwoIID_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:56.134599+00:00
-- url     : https://prove2.me/theorems/d4a5ab33-27d2-4005-be1e-4dc00a0057e0
-- title:
--   §2.1 and Appendix A.1 — single-buyer mechanisms, revenues, and symmetry
-- statement:
--   A buyer has a nonnegative value for each good, and values a collection additively. A direct mechanism assigns each reported valuation vector $x$ an allocation probability $q_i(x)$ for every good and a real payment $s(x)$. Its truthful payoff is
--
--   $$b(x)=\sum_i q_i(x)x_i-s(x).$$
--
--   Feasibility means $0\le q_i(x)\le1$. Incentive compatibility means truthful reporting maximizes the buyer's payoff; individual rationality means $b(x)\ge0$; no positive transfer means $s(x)\ge0$. The expected payment is $R(\mu;X)$, and $\operatorname{Rev}(X)$ is the supremum of expected payments over feasible, incentive-compatible, individually rational mechanisms. $\operatorname{Rev}_1$ is the one-good value; $\operatorname{SRev}$ sums marginal one-good values, and $\operatorname{BRev}$ is the one-good value of the total valuation.
--
--   For two goods, swapping coordinates, symmetry, averaging a mechanism with its swapped copy, and the diagonal valuation $(t,t)$ are defined for the proof of Theorem B.
--
--   **Formalization Note** Valuations are functions into $\mathbb R_{\ge0}$, random valuations are represented by their laws, and expected payment is an extended real number so it can be negative or infinite. Payment measurability is included in admissibility, following footnote 12. Optimal revenue clips a single mechanism's negative revenue at zero before taking the supremum; this leaves the supremum unchanged because the zero mechanism is admissible.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, pp. 11–14, §2.1; p. 32, proof of Theorem B

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.TwoIID

def IsAdmissible {ι : Type*} [Fintype ι] [MeasurableSpace (ι → ℝ≥0)]
    (M : MultiItemRev.Decomp.Mechanism ι) : Prop :=
  MultiItemRev.Decomp.IsFeasible M ∧ MultiItemRev.Decomp.IsIC M ∧ MultiItemRev.Decomp.IsIR M ∧ Measurable M.s

noncomputable def expRevenue {ι : Type*} [MeasurableSpace (ι → ℝ≥0)]
    (μ : Measure (ι → ℝ≥0)) (M : MultiItemRev.Decomp.Mechanism ι) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (M.s x) ∂μ : ℝ≥0∞) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (-M.s x) ∂μ : ℝ≥0∞) : EReal)

noncomputable def Rev {ι : Type*} [Fintype ι] [MeasurableSpace (ι → ℝ≥0)]
    (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  ⨆ (M : MultiItemRev.Decomp.Mechanism ι) (_ : IsAdmissible M), (expRevenue μ M).toENNReal

noncomputable def SRev {ι : Type*} [Fintype ι] [MeasurableSpace (ι → ℝ≥0)]
    (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  ∑ i, MultiItemRev.Decomp.Rev1 (μ.map (fun x => x i))

noncomputable def BRev {ι : Type*} [Fintype ι] [MeasurableSpace (ι → ℝ≥0)]
    (μ : Measure (ι → ℝ≥0)) : ℝ≥0∞ :=
  MultiItemRev.Decomp.Rev1 (μ.map (fun x => ∑ i, x i))

def swap2 (x : Fin 2 → ℝ≥0) : Fin 2 → ℝ≥0 :=
  x ∘ Equiv.swap 0 1

def IsSymmetric (M : MultiItemRev.Decomp.Mechanism (Fin 2)) : Prop :=
  ∀ x, M.q x 0 = M.q (swap2 x) 1 ∧ M.s x = M.s (swap2 x)

noncomputable def symmetrize (M : MultiItemRev.Decomp.Mechanism (Fin 2)) : MultiItemRev.Decomp.Mechanism (Fin 2) where
  q x i := (M.q x i + M.q (swap2 x) (Equiv.swap 0 1 i)) / 2
  s x := (M.s x + M.s (swap2 x)) / 2

def diag (t : ℝ≥0) : Fin 2 → ℝ≥0 := fun _ => t

end MultiItemRev.TwoIID


