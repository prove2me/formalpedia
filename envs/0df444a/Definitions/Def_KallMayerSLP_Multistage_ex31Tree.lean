-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_ex31Tree
-- name    : KallMayerSLP_Multistage_ex31Tree
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:18:08.032983+00:00
-- url     : https://prove2.me/theorems/442e3c6b-b9e2-4a65-8117-f406c174d29d
-- title:
--   Example 3.1: the scenario tree of the discretization
-- statement:
--   The scenario tree of the discretization of Example 3.1: a path through stages 1 and 2, followed by two children for the partition $\{[0,\tfrac12),[\tfrac12,1]\}$ of $\Xi^3$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, Example 3.1, p.259 (PDF 268)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_ScenarioTree
import Definitions.Def_KallMayerSLP_Multistage_ex31Cell

namespace KallMayerSLP.Multistage

private theorem ex31_mem (y : Fin 1 → ℝ) (J : Set ℝ) : (∀ i, y i ∈ J) ↔ y 0 ∈ J :=
  Fin.forall_fin_one

private theorem ex31_isInterval (J : Set ℝ) (hJ : J.OrdConnected) :
    IsInterval {v : Fin 1 → ℝ | ∀ i, v i ∈ J} :=
  ⟨fun _ => J, fun _ => hJ, Set.ext fun _ => ⟨fun h i _ => h i, fun h i => h i trivial⟩⟩

private theorem ex31_cond_subset (v : Bool) {a : ℝ}
    (h : a ∈ cond v (Set.Icc (1 / 2 : ℝ) 1) (Set.Ico (0 : ℝ) (1 / 2))) : a ∈ Set.Icc (0 : ℝ) 1 := by
  cases v
  · exact ⟨h.1, by have := h.2; linarith⟩
  · exact ⟨by have := h.1; linarith, h.2⟩

/-- The scenario tree of the discretization of Example 3.1 (Kall & Mayer, *Stochastic Linear
Programming* (2005), Chapter 3, Example 3.1, p.259, PDF 268): a path through stages 1 and 2, then
two children for the partition `{[0, 1/2), [1/2, 1]}` of `Ξ^3`. -/
def ex31Tree : ScenarioTree ex31Data ex31Support where
  Node := ex31Node
  fintypeNode := ex31Node.instFintype
  uniqueRoot := inferInstanceAs (Unique Unit)
  parent := fun t n =>
    match t, n with
    | 0, _ => PUnit.unit
    | 1, _ => PUnit.unit
    | 2, _ => PUnit.unit
    | _ + 3, n => (n : Empty).elim
  cell := ex31Cell
  isInterval_cell := by
    intro t h2 h3 n
    have ht : t ≤ 3 := h3
    interval_cases t
    · exact ex31_isInterval _ Set.ordConnected_Icc
    · revert n
      change ∀ n : Bool, _
      intro n
      cases n
      · exact ex31_isInterval _ Set.ordConnected_Ico
      · exact ex31_isInterval _ Set.ordConnected_Icc
  disjoint_cell := by
    intro t h1 h3 u v hp hne
    clear hp
    have ht : t < 3 := h3
    interval_cases t
    · exact absurd rfl hne
    · revert u v
      change ∀ u v : Bool, u ≠ v → _
      intro u v hne
      rw [Set.disjoint_left]
      intro x hu hv
      have hu0 := (ex31_mem x _).1 hu
      have hv0 := (ex31_mem x _).1 hv
      cases u <;> cases v
      · exact hne rfl
      · exact absurd hv0.1 (not_le.2 hu0.2)
      · exact absurd hu0.1 (not_le.2 hv0.2)
      · exact hne rfl
  iUnion_cell := by
    intro t h1 h3 h
    have ht : t < 3 := h3
    interval_cases t
    · ext x
      simp only [Set.mem_iUnion]
      exact ⟨fun ⟨_, _, hv⟩ => hv, fun hx => ⟨PUnit.unit, rfl, hx⟩⟩
    · ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨v, -, hv⟩
        exact (ex31_mem x _).2 (ex31_cond_subset v ((ex31_mem x _).1 hv))
      · intro hx
        have hx0 := (ex31_mem x _).1 hx
        by_cases hlt : x (0 : Fin 1) < 1 / 2
        · exact ⟨(false : Bool), rfl, (ex31_mem x _).2 ⟨hx0.1, hlt⟩⟩
        · exact ⟨(true : Bool), rfl, (ex31_mem x _).2 ⟨not_lt.1 hlt, hx0.2⟩⟩

end KallMayerSLP.Multistage


