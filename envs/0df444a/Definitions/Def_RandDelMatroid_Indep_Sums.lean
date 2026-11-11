-- Prove2me | Definitions.Def_RandDelMatroid_Indep_Sums
-- name    : RandDelMatroid_Indep_Sums
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:28:30.116303+00:00
-- url     : https://prove2.me/theorems/8303be0e-4ea7-4040-8e58-fc50d26d7994
-- title:
--   Cycles, sums of binary matroids, and 1-, 2-, 3-sums (Definitions 9, 10)
-- statement:
--   A **cycle** of a matroid is a (possibly empty) disjoint union of circuits (p. 13).
--
--   **Sum (Definition 9).** Let $M_1=(E_1,\mathcal I_1)$ and $M_2=(E_2,\mathcal I_2)$ be binary matroids and $S=E_1\cap E_2$. The sum $M_1\triangle M_2$ is the matroid on $E_1\triangle E_2$ whose circuits are the inclusion-wise minimal nonempty sets of the form $C_1\triangle C_2$, where $C_i$ is a cycle of $M_i$ and $C_1\cap S=C_2\cap S$.
--
--   **1-, 2- and 3-sums (Definition 10).** The sum $M_1\triangle M_2$ is
--
--   1. a **1-sum** if $|S|=0$;
--   2. a **2-sum** if $|S|=1$, $S$ is not a circuit of $M_1$, $M_2$, $M_1^*$ or $M_2^*$, and $|E_1|,|E_2|\ge 3$;
--   3. a **3-sum** if $|S|=3$, $S$ is a circuit of $M_1$ and of $M_2$, $S$ contains no cocircuit of $M_1$ or of $M_2$, and $|E_1|,|E_2|\ge 7$.
--
--   These are the gluing operations of Seymour's decomposition and of the decomposition trees of the mission.
--
--   **Formalization Note** `IsSum M₁ M₂ N` says that `N` has ground set `E₁ △ E₂` and exactly these circuits (a matroid is determined by its circuits). `IsOneSumPair`, `IsTwoSumPair`, `IsThreeSumPair` are the conditions of Definition 10 on the pair, `IsOneSum` etc. add `IsSum`, and `IsSumPair` is "1-, 2- or 3-sum". Duals are Mathlib's `M✶`. Binarity is a hypothesis of the lemmas that use sums, not part of `IsSum`.
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), pp. 10–11, Definitions 9 and 10; p. 13 (cycles)

import Mathlib

set_option autoImplicit false

namespace RandDelMatroid.Indep

variable {β : Type}

/-- p. 13: a *cycle* of `M` is a (possibly empty) disjoint union of circuits of `M`. -/
def IsCycle (M : Matroid β) (C : Set β) : Prop :=
  ∃ 𝒞 : Set (Set β), (∀ D ∈ 𝒞, M.IsCircuit D) ∧ 𝒞.PairwiseDisjoint id ∧ C = ⋃₀ 𝒞

/-- Definition 9 (p. 10). With `S = E₁ ∩ E₂`, the matroid `N` is the sum `M₁ △ M₂`: its ground set
is `E₁ △ E₂` and its circuits are the inclusion-wise minimal nonempty sets of the form `C₁ △ C₂`,
where `Cᵢ` is a cycle of `Mᵢ` and `C₁ ∩ S = C₂ ∩ S`. -/
def IsSum (M₁ M₂ N : Matroid β) : Prop :=
  N.E = symmDiff M₁.E M₂.E ∧
    ∀ C : Set β, N.IsCircuit C ↔
      Minimal (fun X : Set β => X.Nonempty ∧ ∃ C₁ C₂ : Set β, IsCycle M₁ C₁ ∧ IsCycle M₂ C₂ ∧
        C₁ ∩ (M₁.E ∩ M₂.E) = C₂ ∩ (M₁.E ∩ M₂.E) ∧ X = symmDiff C₁ C₂) C

/-- Definition 10 (p. 11), item 1, condition on the pair: `|S| = 0`. -/
def IsOneSumPair (M₁ M₂ : Matroid β) : Prop :=
  M₁.E ∩ M₂.E = ∅

/-- Definition 10 (p. 11), item 2, condition on the pair: `|S| = 1`, `S` is not a circuit of
`M₁`, `M₂`, `M₁*` or `M₂*`, and `|E₁|, |E₂| ≥ 3`. -/
def IsTwoSumPair (M₁ M₂ : Matroid β) : Prop :=
  (M₁.E ∩ M₂.E).ncard = 1 ∧
    ¬ M₁.IsCircuit (M₁.E ∩ M₂.E) ∧ ¬ M₂.IsCircuit (M₁.E ∩ M₂.E) ∧
    ¬ M₁✶.IsCircuit (M₁.E ∩ M₂.E) ∧ ¬ M₂✶.IsCircuit (M₁.E ∩ M₂.E) ∧
    3 ≤ M₁.E.ncard ∧ 3 ≤ M₂.E.ncard

/-- Definition 10 (p. 11), item 3, condition on the pair: `|S| = 3`, `S` is a circuit of `M₁` and
of `M₂`, `S` contains no cocircuit of `M₁` or of `M₂`, and `|E₁|, |E₂| ≥ 7`. -/
def IsThreeSumPair (M₁ M₂ : Matroid β) : Prop :=
  (M₁.E ∩ M₂.E).ncard = 3 ∧
    M₁.IsCircuit (M₁.E ∩ M₂.E) ∧ M₂.IsCircuit (M₁.E ∩ M₂.E) ∧
    (∀ D : Set β, D ⊆ M₁.E ∩ M₂.E → ¬ M₁✶.IsCircuit D ∧ ¬ M₂✶.IsCircuit D) ∧
    7 ≤ M₁.E.ncard ∧ 7 ≤ M₂.E.ncard

/-- Definition 10: `N = M₁ △ M₂` is a 1-sum. -/
def IsOneSum (M₁ M₂ N : Matroid β) : Prop := IsSum M₁ M₂ N ∧ IsOneSumPair M₁ M₂

/-- Definition 10: `N = M₁ △ M₂` is a 2-sum. -/
def IsTwoSum (M₁ M₂ N : Matroid β) : Prop := IsSum M₁ M₂ N ∧ IsTwoSumPair M₁ M₂

/-- Definition 10: `N = M₁ △ M₂` is a 3-sum. -/
def IsThreeSum (M₁ M₂ N : Matroid β) : Prop := IsSum M₁ M₂ N ∧ IsThreeSumPair M₁ M₂

/-- The sum of `M₁` and `M₂` is a 1-, 2- or 3-sum (the conditions of Definition 10 on the pair). -/
def IsSumPair (M₁ M₂ : Matroid β) : Prop :=
  IsOneSumPair M₁ M₂ ∨ IsTwoSumPair M₁ M₂ ∨ IsThreeSumPair M₁ M₂

end RandDelMatroid.Indep


