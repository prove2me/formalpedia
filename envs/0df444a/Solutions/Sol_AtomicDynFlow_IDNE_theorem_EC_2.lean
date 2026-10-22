-- Prove2me | solution 1 for AtomicDynFlow.IDNE.theorem_EC_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T07:55:30.602657+00:00
-- url     : https://prove2.me/submissions/c245b511-c314-4157-aae5-274e997e2443
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model
import Definitions.Def_AtomicDynFlow_IDNE_Equilibrium
import Definitions.Def_AtomicDynFlow_IDNE_Selection
import Theorems.Thm_AtomicDynFlow_IDNE_lemma_EC_2

open AtomicDynFlow.IDNE

private lemma prefixProfile_eq {E A : Type} [DecidableEq A] (p : A → List E) :
    ∀ (L : List (A × List E)), (∀ y ∈ L, y.2 = p y.1) → ∀ x,
      prefixProfile L x = if x ∈ L.map Prod.fst then some (p x) else none := by
  intro L
  induction L with
  | nil => intro _ x; simp [prefixProfile]
  | cons y L ih =>
    intro hL x
    obtain ⟨b, P⟩ := y
    have hb : P = p b := hL (b, P) (by simp)
    have ih' := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy)) x
    by_cases hxb : x = b
    · subst hxb; simp [prefixProfile, hb]
    · have e1 : prefixProfile ((b, P) :: L) x = prefixProfile L x := by
        simp [prefixProfile, hxb]
      have e2 : (x ∈ ((b, P) :: L).map Prod.fst) ↔ x ∈ L.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons, hxb, false_or]
      rw [e1, ih']
      exact if_congr e2.symm rfl rfl

theorem solution {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [DecidableEq A] (G : Instance V E A) (σ : A → ℕ) (p : A → List E)
    (h : G.IsSpecialSeq σ p) : G.IsIDNEWith σ p := by
  classical
  obtain ⟨hinj, hdown, hsel⟩ := h
  refine ⟨fun a => (hsel a).2.1, hinj, hdown, ?_⟩
  intro a v hv q hq hqp
  -- the agent of index `m`
  let g : ℕ → A := fun m => if hm : ∃ b, σ b = m then Classical.choose hm else a
  have hg : ∀ m, m < σ a → σ (g m) = m := by
    intro m hm
    have hex : ∃ b, σ b = m := hdown a m hm
    simp only [g, dif_pos hex]
    exact Classical.choose_spec hex
  let Lm : ℕ → List (A × List E) := fun m => (List.range m).map (fun i => (g i, p (g i)))
  have hLm_val : ∀ m, ∀ y ∈ Lm m, y.2 = p y.1 := by
    intro m y hy
    simp only [Lm, List.mem_map] at hy
    obtain ⟨i, _, rfl⟩ := hy
    rfl
  have hLm_mem : ∀ m, m ≤ σ a → ∀ x, x ∈ (Lm m).map Prod.fst ↔ σ x < m := by
    intro m hm x
    simp only [Lm, List.map_map, List.mem_map, List.mem_range, Function.comp_def]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rw [hg i (lt_of_lt_of_le hi hm)]; exact hi
    · intro hx
      refine ⟨σ x, hx, ?_⟩
      apply hinj
      exact hg (σ x) (lt_of_lt_of_le hx hm)
  have hprof : ∀ m, m ≤ σ a →
      prefixProfile (Lm m) = fun b => if σ b < m then some (p b) else none := by
    intro m hm
    funext x
    rw [prefixProfile_eq p (Lm m) (hLm_val m) x]
    simp only [hLm_mem m hm x]
  set L := Lm (σ a) with hLdef
  have hLspecial : G.IsSpecialPrefix L := by
    intro n hn
    have hlen : L.length = σ a := by simp [L, Lm]
    have hn' : n < σ a := hlen ▸ hn
    have htake : L.take n = Lm n := by
      simp only [L, Lm, ← List.map_take, List.take_range, min_eq_left hn'.le]
    have hget : L[n]'hn = (g n, p (g n)) := by
      simp [L, Lm]
    rw [htake, hget, hprof n hn'.le]
    have := hsel (g n)
    rw [hg n hn'] at this
    exact this
  have hLprof : prefixProfile L = fun b => if σ b < σ a then some (p b) else none :=
    hprof (σ a) le_rfl
  have hka : G.IsSelected (prefixProfile L) a (p a) := by
    rw [hLprof]; exact hsel a
  let S : Set A := {b | σ a ≤ σ b}
  have hS : ∀ b ∈ S, b ∉ L.map Prod.fst := by
    intro b hb hmem
    rw [hLm_mem (σ a) le_rfl] at hmem
    exact absurd hb (not_le.mpr hmem)
  have haS : a ∈ S := le_refl (σ a)
  -- left-hand side
  have hL1 : overlay (prefixProfile (L ++ [(a, p a)])) (restrictTo q (S \ {a})) =
      fun b => some (q b) := by
    funext x
    have hval : ∀ y ∈ L ++ [(a, p a)], y.2 = p y.1 := by
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact hLm_val _ y hy
      · simp at hy; subst hy; rfl
    have hmemx : x ∈ (L ++ [(a, p a)]).map Prod.fst ↔ σ x < σ a ∨ x = a := by
      rw [List.map_append, List.mem_append, hLm_mem (σ a) le_rfl x]
      simp
    have hpp := prefixProfile_eq p _ hval x
    simp only [overlay]
    by_cases h1 : σ x < σ a
    · rw [hpp, if_pos (hmemx.2 (Or.inl h1)), hqp x h1.le]
    · by_cases h2 : x = a
      · rw [hpp, if_pos (hmemx.2 (Or.inr h2)), hqp x (by rw [h2])]
      · have hxS : x ∈ S \ {a} := ⟨not_lt.1 h1, h2⟩
        rw [hpp, if_neg (by rw [hmemx]; tauto)]
        simp [restrictTo, hxS]
  have key := lemma_EC_2 G L hLspecial a (p a) hka S hS a haS v hv q hq
  rw [hL1] at key
  rw [key.1]
  apply le_antisymm
  · apply le_iInf; intro j; apply le_iInf; intro hj; apply le_iInf; intro r
    apply le_iInf; intro hr
    have hjS : j ∈ S := hj
    have k2 := (lemma_EC_2 G L hLspecial a (p a) hka S hS j hjS v hv r hr.1).2
    have hprof2 : overlay (prefixProfile L) (restrictTo r S) = fun b => some (r b) := by
      funext x
      simp only [overlay, hLprof]
      by_cases h1 : σ x < σ a
      · simp [h1, hr.2 x h1]
      · have hxS : x ∈ S := not_lt.1 h1
        simp [h1, restrictTo, hxS]
    rw [hprof2] at k2
    exact k2
  · have h1 := key.1
    rw [← key.1]
    exact iInf₂_le_of_le a le_rfl (iInf₂_le_of_le q ⟨hq, fun b hb => hqp b hb.le⟩ le_rfl)
