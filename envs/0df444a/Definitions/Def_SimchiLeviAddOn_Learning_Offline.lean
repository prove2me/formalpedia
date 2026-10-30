-- Prove2me | Definitions.Def_SimchiLeviAddOn_Learning_Offline
-- name    : SimchiLeviAddOn_Learning_Offline
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T01:58:19.385033+00:00
-- url     : https://prove2.me/theorems/c2d15c95-6c12-4994-96c7-0f9b33a08456
-- title:
--   Algorithm 1: supportive maximization, ranking, rounding and DP recovery
-- statement:
--   For each grid value j/K, maximize each ordinary supportive score over every original price and each discounted score over strictly feasible original-discount pairs. Retain price witnesses, rank the differences decreasingly, and select positive differences among the first S ranks. Round every core mean to a nearest multiple of 1/K. Compute the backward DP on remaining core products, starting at rounded demand zero, and recover maximizing decisions. At the terminal grid demand use the supportive price witnesses. Every nearest-rounding, sorting and maximizing tie is retained. The ordinary maximization remains unrestricted as printed, and an output is not assumed feasible for (1). An unused discount label is arbitrary and affects no revenue or feedback. Approximation error is measured using the actual revenue polynomial, not the DP value.
-- source:
--   Simchi-Levi, Sun and Zhang, arXiv:2005.00947v1 (2 May 2020), https://arxiv.org/abs/2005.00947v1, Algorithm 1, p. 12 (PDF 12), and Lemma 3 preamble, p. 13

import Definitions.Def_SimchiLeviAddOn_Learning_Model

open scoped BigOperators

namespace SimchiLeviAddOn.Learning

/-- Maximizer witnesses and a permutation, retaining every sorting and price tie. -/
structure SupportWitness (X : Market) where
  ordinary : Fin X.M → Fin X.ns
  original : Fin X.M → Fin X.ns
  discount : Fin X.M → Fin X.na
  rank : Equiv.Perm (Fin X.M)

noncomputable def ordinaryScore (X : Market) (d : Tables X) (γ : ℝ)
    (m : Fin X.M) (s : Fin X.ns) : ℝ :=
  d (.primary m s) * X.original s + γ * d (.ordinary m s) * X.original s

noncomputable def discountScore (X : Market) (d : Tables X) (γ : ℝ)
    (m : Fin X.M) (s : Fin X.ns) (a : Fin X.na) : ℝ :=
  d (.primary m s) * X.original s + γ * d (.discounted m a) * X.discount a

noncomputable def gain (X : Market) (d : Tables X) (γ : ℝ)
    (w : SupportWitness X) (m : Fin X.M) : ℝ :=
  discountScore X d γ m (w.original m) (w.discount m) -
    ordinaryScore X d γ m (w.ordinary m)

noncomputable def chosen (X : Market) (d : Tables X) (γ : ℝ)
    (w : SupportWitness X) (m : Fin X.M) : Bool := by
  classical
  exact decide (0 < gain X d γ w m ∧ (w.rank.symm m).val < X.S)

def IsSupportWitness (X : Market) (d : Tables X) (γ : ℝ)
    (w : SupportWitness X) : Prop :=
  (∀ m s, ordinaryScore X d γ m s ≤ ordinaryScore X d γ m (w.ordinary m)) ∧
  (∀ m, X.discount (w.discount m) < X.original (w.original m)) ∧
  (∀ m s a, X.discount a < X.original s →
    discountScore X d γ m s a ≤ discountScore X d γ m (w.original m) (w.discount m)) ∧
  (∀ i j : Fin X.M, i.val ≤ j.val → gain X d γ w (w.rank j) ≤ gain X d γ w (w.rank i))

noncomputable def gridSupport (X : Market) (d : Tables X) (γ : ℝ)
    (w : SupportWitness X) : ℝ :=
  ∑ m, (ordinaryScore X d γ m (w.ordinary m) +
    (if chosen X d γ w m then gain X d γ w m else 0))

/-- Only the grid 0,...,NK is consulted in a run from the initial state. -/
structure OfflineChoices (X : Market) (K : ℕ) where
  rounded : Fin X.N → Fin X.nc → Fin (K + 1)
  support : ℕ → SupportWitness X

def IsOfflineChoices (X : Market) (d : Tables X) (K : ℕ)
    (w : OfflineChoices X K) : Prop :=
  (∀ (n : Fin X.N) (p : Fin X.nc) (q : Fin (K + 1)),
    |d (.core n p) - (w.rounded n p : ℕ) / (K : ℝ)| ≤
      |d (.core n p) - (q : ℕ) / (K : ℝ)|) ∧
  (∀ j, j ≤ X.N * K → IsSupportWitness X d ((j : ℝ) / K) (w.support j))

/-- Backward recursion on the remaining core products. -/
noncomputable def dp (X : Market) (d : Tables X) (K : ℕ)
    (w : OfflineChoices X K) : List (Fin X.N) → ℕ → ℝ
  | [], j => gridSupport X d ((j : ℝ) / K) (w.support j)
  | n :: ns, j => sSup (Set.range (fun p : Fin X.nc =>
      d (.core n p) * X.core p + dp X d K w ns (j + (w.rounded n p).val)))

noncomputable def gridBefore (X : Market) (K : ℕ) (w : OfflineChoices X K)
    (p : Policy X) (i : ℕ) : ℕ :=
  ∑ n : Fin X.N, if n.val < i then (w.rounded n (p.core n)).val else 0

/-- Algorithm 1, including recovery from maximizing DP transitions and the supportive witnesses.
Unused discount labels may be arbitrary: no feasibility assertion is imposed on the output. -/
def IsOfflineOutput (X : Market) (d : Tables X) (K : ℕ) (p : Policy X) : Prop :=
  ∃ w : OfflineChoices X K, IsOfflineChoices X d K w ∧
    (∀ n : Fin X.N,
      dp X d K w ((List.finRange X.N).drop n.val) (gridBefore X K w p n.val) =
        d (.core n (p.core n)) * X.core (p.core n) +
          dp X d K w ((List.finRange X.N).drop (n.val + 1))
            (gridBefore X K w p n.val + (w.rounded n (p.core n)).val)) ∧
    (let j := gridBefore X K w p X.N
     let γ := (j : ℝ) / K
     let z := w.support j
     ∀ m, p.selected m = chosen X d γ z m ∧
       p.original m = (if chosen X d γ z m then z.original m else z.ordinary m) ∧
       (p.selected m = true → p.discount m = z.discount m))

end SimchiLeviAddOn.Learning


