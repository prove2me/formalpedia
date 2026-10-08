-- Prove2me | Definitions.Def_SingleMachinePrec_IntervalChromatic_CanonicalOrder
-- name    : SingleMachinePrec_IntervalChromatic_CanonicalOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:19:44.165979+00:00
-- url     : https://prove2.me/theorems/6e46088e-0c59-4bf6-be30-a967fa8312e9
-- title:
--   Canonical interval orders and colorability
-- statement:
--   For an integer $n\ge2$, the **canonical interval order** $I_n$ consists of every closed interval with two distinct endpoints in $[n]$. Write an interval as its two-element endpoint set $S$. For intervals $S$ and $T$,
--
--   $$
--   S\le_{I_n}T\iff S=T\ \text{or}\ \max S<\min T.
--   $$
--
--   The relation is a partial order. The predicate $\operatorname{Colorable}(n,k)$ means that the graph $G_{I_n}$ of ordered incomparable pairs has a proper vertex coloring using colors from a set of size $k$. This definition makes the chromatic conclusion a finite-coloring statement and permits $k=0$ on an empty graph.
--
--   **Formalization Note** The endpoint set is `Fin n`, indexed from $0$ to $n-1$; shifting every endpoint by one gives the paper's $[n]$. The definitions exist at smaller $n$ too, but the mission's statements use the paper's domain $n\ge2$.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 658, §4.2; DOI 10.1287/moor.1110.0512

import Definitions.Def_SingleMachinePrec_IntervalChromatic_IncomparableGraph

namespace SingleMachinePrec.IntervalChromatic

/-- Closed intervals with distinct endpoints in `[n]`, represented by their endpoints. -/
def Interval (n : ℕ) : Type :=
  {s : Finset (Fin n) // s.card = 2}

/-- The canonical interval order: a closed interval precedes another when it ends
strictly before the other begins, or when the two intervals coincide. -/
def I (n : ℕ) (s t : Interval n) : Prop :=
  s = t ∨ ∀ a ∈ s.1, ∀ b ∈ t.1, a < b

/-- The displayed relation really is a partial order, including at small `n`. -/
instance canonicalPartialOrder (n : ℕ) : IsPartialOrder (Interval n) (I n) where
  refl := by
    intro s
    exact Or.inl rfl
  trans := by
    intro s t u hst htu
    rcases hst with rfl | hst
    · exact htu
    rcases htu with rfl | htu
    · exact Or.inr hst
    right
    intro a ha c hc
    obtain ⟨b, hb⟩ : t.1.Nonempty := Finset.card_pos.mp (by rw [t.2]; omega)
    exact lt_trans (hst a ha b hb) (htu b hb c hc)
  antisymm := by
    intro s t hst hts
    rcases hst with heq | hst
    · exact heq
    rcases hts with heq | hts
    · exact heq.symm
    obtain ⟨a, ha⟩ : s.1.Nonempty := Finset.card_pos.mp (by rw [s.2]; omega)
    obtain ⟨b, hb⟩ : t.1.Nonempty := Finset.card_pos.mp (by rw [t.2]; omega)
    exact False.elim ((lt_asymm (hst a ha b hb)) (hts b hb a ha))

/-- The interval whose endpoints are `a < b`. -/
def endpointPair {n : ℕ} (a b : Fin n) (h : a < b) : Interval n :=
  ⟨{a, b}, by simp [ne_of_lt h]⟩

/-- Proper vertex coloring of the graph of incomparable pairs of `I n`. -/
def Colorable (n k : ℕ) : Prop :=
  ∃ color : IncomparablePair (I n) → Fin k,
    ∀ u v, G (I n) u v → color u ≠ color v

end SingleMachinePrec.IntervalChromatic


