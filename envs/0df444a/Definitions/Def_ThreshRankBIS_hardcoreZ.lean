-- Prove2me | Definitions.Def_ThreshRankBIS_hardcoreZ
-- name    : ThreshRankBIS_hardcoreZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:58:29.816901+00:00
-- url     : https://prove2.me/theorems/69c5ce17-784e-4a40-bd1a-d63fa0dd51bb
-- title:
--   Hard-core partition function $Z_G(\lambda)$, Gibbs law $\mu_{G,\lambda}$, total variation
-- statement:
--   Let $\mathcal I(G)$ be the family of independent sets of the bipartite graph $G$. The **hard-core partition function** at fugacity $\lambda$ is
--
--   $$
--   Z_G(\lambda)=\sum_{I\in\mathcal I(G)}\lambda^{|I|},
--   $$
--
--   and the **Gibbs distribution** is $\mu_{G,\lambda}(I)=\lambda^{|I|}/Z_G(\lambda)$. At $\lambda=1$, $Z_G(1)$ is the number of independent sets (#BIS). The module also defines maximal independent sets and the **total variation distance** $\|\mu-\nu\|_{TV}=\tfrac12\sum_\omega|\mu(\omega)-\nu(\omega)|$ of two functions on a finite set.
--
--   These are the quantities the paper approximates (counting) and samples (Corollary 2, Corollary 13).
--
--   **Formalization Note** The Gibbs law is a function on the outcomes "a vertex set" or "no valid output" (`none`), with mass $0$ on non-independent sets and on `none`, so a sampler that outputs anything else is penalized in total variation. $\lambda$ is real; the hypothesis $\lambda>0$ is stated in each theorem.
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), §1, p.2; §1.1, p.3

import Mathlib
import Definitions.Def_ThreshRankBIS_IsRegular
set_option autoImplicit false

namespace ThreshRankBIS

open Finset

/-- `I ⊆ V(G)` is independent in `HiddenPartition.bip E`. -/
def IsIndep {n : ℕ} (E : Fin n → Fin n → Bool) (I : Finset (V n)) : Prop :=
  (HiddenPartition.bip E).IsIndepSet (I : Set (V n))

/-- `I` is a maximal independent set: independent, and adding any vertex outside `I` destroys
independence. -/
def IsMaxIndep {n : ℕ} (E : Fin n → Fin n → Bool) (I : Finset (V n)) : Prop :=
  IsIndep E I ∧ ∀ v, v ∉ I → ¬ IsIndep E (insert v I)

/-- **The hard-core partition function** `Z_G(λ) = ∑_{I ∈ 𝓘(G)} λ^{|I|}`, the sum over the
independent sets of `G` (p.2).

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), §1, p.2; Gibbs law
and total variation §1.1, p.3.

The module also defines the Gibbs distribution `µ_{G,λ}(I) = λ^{|I|}/Z_G(λ)` (p.3) on the
outcomes `Option (Finset (V n))` (with mass `0` on non-independent sets and on `none`, the
"undecodable output" outcome) and the total variation distance
`‖µ − ν‖_TV = ½ ∑_ω |µ(ω) − ν(ω)|` (p.3) of two functions on a finite type.

**Formalization Note.** `λ` is a real number; the paper's `λ > 0` is a hypothesis of each
statement. The platform's `ExpanderBIS.HardCore.hardcoreZ` is the same object on a different
graph type; it is redefined here on `HiddenPartition.bip E`. -/
noncomputable def hardcoreZ {n : ℕ} (E : Fin n → Fin n → Bool) (lam : ℝ) : ℝ := by
  classical
  exact ∑ I ∈ univ.filter (fun I : Finset (V n) => IsIndep E I), lam ^ #I

/-- The Gibbs distribution `µ_{G,λ}(I) = λ^{|I|}/Z_G(λ)` on independent sets (p.3), extended by
`0` to non-independent sets and to the outcome `none`. -/
noncomputable def gibbs {n : ℕ} (E : Fin n → Fin n → Bool) (lam : ℝ) :
    Option (Finset (V n)) → ℝ := by
  classical
  exact fun o => match o with
    | none => 0
    | some I => if IsIndep E I then lam ^ #I / hardcoreZ E lam else 0

/-- Total variation distance `½ ∑_ω |µ(ω) − ν(ω)|` (p.3) of two functions on a finite type. -/
noncomputable def tv {β : Type} [Fintype β] (μ ν : β → ℝ) : ℝ :=
  (1 / 2) * ∑ o, |μ o - ν o|

end ThreshRankBIS


