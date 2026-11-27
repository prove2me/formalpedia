-- Prove2me | Definitions.Def_MPBSelect_Supplement_Favorable
-- name    : MPBSelect_Supplement_Favorable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:45:35.721048+00:00
-- url     : https://prove2.me/theorems/1b7a2c21-aada-4328-80a0-f9a5ae132b01
-- title:
--   Favorable-set OCBA objectives and balance systems
-- statement:
--   Let $\Xi^{\mathrm{adv}}=\{(i^*,\theta_b):\theta_b\notin\Theta_{i^*}\}$ and consider the active pairs $\Xi\cup\Xi^{\mathrm{adv}}$. This bundle defines the accuracy and false-negative balance weights $W_i^{\mathrm{ACC}}(\theta_b)$ and $W_i^{\mathrm{FN}}(\theta_b)$ in (30), the two lower-rate objectives optimized in (28) and (29), their optimality predicates, and the global and pairwise balance systems of Theorem 6.
--
--   The global balance sums over every $i\ne i^b$, including $i^*$. The paper's $+\infty$ weights off $\Xi\cup\Xi^{\mathrm{adv}}$ are represented by restricting both objectives and pairwise balance to that active finite set.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, favorable-set events (24)-(27), problems (28)-(29), and weights (30), pp.24-26

import Mathlib
import Definitions.Def_MPBSelect_feasibleSet
import Definitions.Def_MPBSelect_Problem_Xi
import Definitions.Def_MPBSelect_Problem_W
import Definitions.Def_MPBSelect_Problem_G

noncomputable section

namespace MPBSelect.Supplement

/-- The adversarial MPB pairs `Ξ^adv = {(i*,θ_b) : θ_b ∈ Θ^c_{i*}}` (p.14). -/
def xiAdv {k B : ℕ} (P : MPBSelect.Problem k B) : Finset (Fin k × Fin B) :=
  Finset.univ.filter fun x => x.1 = P.istar ∧ P.ib x.2 ≠ P.istar

/-- The active pairs in the favorable-set objectives (28) and (29). -/
def favorablePairs {k B : ℕ} (P : MPBSelect.Problem k B) : Finset (Fin k × Fin B) :=
  P.Xi ∪ xiAdv P

/-- Public bundle name for the favorable-set OCBA objects (28)--(30). -/
abbrev Favorable {k B : ℕ} (P : MPBSelect.Problem k B) := favorablePairs P

theorem favorablePairs_nonempty {k B : ℕ} (P : MPBSelect.Problem k B) :
    (favorablePairs P).Nonempty :=
  P.Xi_nonempty.mono (Finset.subset_union_left)

/-- The accuracy balance weight `W^ACC` in (30), on all pairs. The theorem and objectives
evaluate it only on `Ξ ∪ Ξ^adv`; the paper's `+∞` value off that set is therefore represented by
the domain restriction rather than a fake real value. -/
def wAcc {k B : ℕ} (P : MPBSelect.Problem k B) (i : Fin k) (b : Fin B) : ℝ :=
  if P.ib b = P.istar ∨ (i = P.istar ∧ P.ib b ≠ P.istar) then 1 else P.W i b

/-- The false-negative balance weight `W^FN` in (30), on `Ξ ∪ Ξ^adv`. -/
def wFN {k B : ℕ} (P : MPBSelect.Problem k B) (i : Fin k) (b : Fin B) : ℝ :=
  if (i, b) ∈ P.Xi then P.W i b else 1

/-- The global balance used by both favorable-set programs: unlike Theorem 3, the sum contains
every solution other than the conditional optimum, including `i*`. -/
def GlobalBalanceAll {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) : Prop :=
  ∀ b : Fin B, α (P.ib b) b ^ 2 / P.lam (P.ib b) b ^ 2 =
    ∑ i ∈ Finset.univ.filter (fun i : Fin k => i ≠ P.ib b),
      α i b ^ 2 / P.lam i b ^ 2

/-- Pairwise balance for the accuracy objective (28). -/
def PairwiseBalanceAcc {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) : Prop :=
  ∀ x ∈ favorablePairs P, ∀ x' ∈ favorablePairs P,
    wAcc P x.1 x.2 * P.G α x.1 x.2 = wAcc P x'.1 x'.2 * P.G α x'.1 x'.2

/-- Pairwise balance for the false-negative objective (29). -/
def PairwiseBalanceFN {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) : Prop :=
  ∀ x ∈ favorablePairs P, ∀ x' ∈ favorablePairs P,
    wFN P x.1 x.2 * P.G α x.1 x.2 = wFN P x'.1 x'.2 * P.G α x'.1 x'.2

/-- The rate lower bound `LDR_ACC` optimized in (28). -/
def ldrAcc {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) : ℝ :=
  (favorablePairs P).inf' (favorablePairs_nonempty P)
    fun x => wAcc P x.1 x.2 * P.G α x.1 x.2

/-- The rate lower bound `LDR_FN` optimized in (29). -/
def ldrFN {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) : ℝ :=
  (favorablePairs P).inf' (favorablePairs_nonempty P)
    fun x => wFN P x.1 x.2 * P.G α x.1 x.2

/-- Optimality for the favorable-set accuracy OCBA problem (28). -/
def IsOptimalAcc {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) : Prop :=
  α ∈ MPBSelect.feasibleSet k B ∧
    ∀ α' ∈ MPBSelect.feasibleSet k B, ldrAcc P α' ≤ ldrAcc P α

/-- Optimality for the favorable-set false-negative OCBA problem (29). -/
def IsOptimalFN {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) : Prop :=
  α ∈ MPBSelect.feasibleSet k B ∧
    ∀ α' ∈ MPBSelect.feasibleSet k B, ldrFN P α' ≤ ldrFN P α

end MPBSelect.Supplement


