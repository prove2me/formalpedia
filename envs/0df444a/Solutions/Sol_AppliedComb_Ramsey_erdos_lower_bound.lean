-- Prove2me | solution 1 for AppliedComb.Ramsey.erdos_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:19:05.424491+00:00
-- url     : https://prove2.me/submissions/35cee2f8-3e63-4a41-9266-ae42720e0d2a

import Mathlib
import Definitions.Def_AppliedComb_Ramsey_ramseyNumber

open Finset

namespace ErdosRamseyAux

/-! ### Part A: existence of Ramsey bounds (finite Ramsey theorem) -/

/-- Ramsey's theorem relative to a finite vertex subset `S`. -/
lemma ramsey_exists_aux : ∀ (m n : ℕ), ∃ N : ℕ, ∀ (V : Type) (G : SimpleGraph V) (S : Finset V),
    N ≤ S.card → (∃ s ⊆ S, G.IsNClique m s) ∨ (∃ s ⊆ S, G.IsNIndepSet n s) := by
  classical
  intro m
  induction m with
  | zero =>
    intro n
    exact ⟨0, fun V G S _ => Or.inl ⟨∅, Finset.empty_subset _, by simp⟩⟩
  | succ m ihm =>
    intro n
    induction n with
    | zero =>
      exact ⟨0, fun V G S _ => Or.inr ⟨∅, Finset.empty_subset _,
        (SimpleGraph.isNClique_compl G).1 (by simp)⟩⟩
    | succ n ihn =>
      obtain ⟨N1, h1⟩ := ihm (n + 1)
      obtain ⟨N2, h2⟩ := ihn
      refine ⟨N1 + N2 + 1, fun V G S hS => ?_⟩
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨v, hv⟩ := hne
      set A := (S.erase v).filter (fun w => G.Adj v w) with hA
      set B := (S.erase v).filter (fun w => ¬ G.Adj v w) with hB
      have hcard : A.card + B.card = S.card - 1 := by
        rw [hA, hB, Finset.card_filter_add_card_filter_not, Finset.card_erase_of_mem hv]
      have hAS : A ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hBS : B ⊆ S := (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
      have hvA : v ∉ A := fun h => by
        have := (Finset.mem_filter.1 h).1
        simp at this
      have hvB : v ∉ B := fun h => by
        have := (Finset.mem_filter.1 h).1
        simp at this
      by_cases hA' : N1 ≤ A.card
      · rcases h1 V G A hA' with ⟨s, hsA, hs⟩ | ⟨s, hsA, hs⟩
        · left
          refine ⟨insert v s, Finset.insert_subset hv (hsA.trans hAS), ?_⟩
          rw [SimpleGraph.isNClique_iff, Finset.coe_insert]
          refine ⟨SimpleGraph.isClique_insert.2 ⟨hs.isClique, fun b hb _ =>
            (Finset.mem_filter.1 (hsA (Finset.mem_coe.1 hb))).2⟩, ?_⟩
          rw [Finset.card_insert_of_notMem (fun h => hvA (hsA h)), hs.card_eq]
        · exact Or.inr ⟨s, hsA.trans hAS, hs⟩
      · have hB' : N2 ≤ B.card := by omega
        rcases h2 V G B hB' with ⟨s, hsB, hs⟩ | ⟨s, hsB, hs⟩
        · exact Or.inl ⟨s, hsB.trans hBS, hs⟩
        · right
          refine ⟨insert v s, Finset.insert_subset hv (hsB.trans hBS), ?_⟩
          rw [← SimpleGraph.isNClique_compl G, SimpleGraph.isNClique_iff, Finset.coe_insert]
          have hs' : Gᶜ.IsNClique n s := (SimpleGraph.isNClique_compl G).2 hs
          refine ⟨SimpleGraph.isClique_insert.2 ⟨hs'.isClique, fun b hb hvb => ?_⟩, ?_⟩
          · rw [SimpleGraph.compl_adj]
            exact ⟨hvb, (Finset.mem_filter.1 (hsB (Finset.mem_coe.1 hb))).2⟩
          · rw [Finset.card_insert_of_notMem (fun h => hvB (hsB h)), hs'.card_eq]

lemma ramsey_set_nonempty (n : ℕ) :
    ∃ N : ℕ, 0 < N ∧ AppliedComb.Ramsey.IsRamseyBound n n N := by
  obtain ⟨N, h⟩ := ramsey_exists_aux n n
  refine ⟨N + 1, Nat.succ_pos _, ?_⟩
  intro V _ hV G
  have := h V G Finset.univ (by rw [Finset.card_univ]; omega)
  rcases this with ⟨s, -, hs⟩ | ⟨s, -, hs⟩
  · exact Or.inl ⟨s, hs⟩
  · exact Or.inr ⟨s, hs⟩

/-! ### Part B: the counting argument -/

/-- The graph on `Fin N` with edge set `F` (a family of two-element subsets). -/
def gr (N : ℕ) (F : Finset (Finset (Fin N))) : SimpleGraph (Fin N) where
  Adj x y := x ≠ y ∧ ({x, y} : Finset (Fin N)) ∈ F
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [Finset.pair_comm]; exact h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

lemma gr_adj {N : ℕ} {F : Finset (Finset (Fin N))} {x y : Fin N} :
    (gr N F).Adj x y ↔ x ≠ y ∧ ({x, y} : Finset (Fin N)) ∈ F := Iff.rfl

lemma pow2_subset_of_clique {N n : ℕ} {F : Finset (Finset (Fin N))} {S : Finset (Fin N)}
    (h : (gr N F).IsNClique n S) : S.powersetCard 2 ⊆ F := by
  intro T hT
  rw [Finset.mem_powersetCard] at hT
  obtain ⟨hTS, hT2⟩ := hT
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hT2
  have hx : x ∈ S := hTS (by simp)
  have hy : y ∈ S := hTS (by simp)
  exact (gr_adj.1 (h.isClique hx hy hxy)).2

lemma disjoint_of_indep {N n : ℕ} {F : Finset (Finset (Fin N))} {S : Finset (Fin N)}
    (h : (gr N F).IsNIndepSet n S) : Disjoint F (S.powersetCard 2) := by
  rw [Finset.disjoint_left]
  intro T hTF hTS
  rw [Finset.mem_powersetCard] at hTS
  obtain ⟨hTS, hT2⟩ := hTS
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hT2
  have hx : x ∈ S := hTS (by simp)
  have hy : y ∈ S := hTS (by simp)
  exact h.isIndepSet hx hy hxy (gr_adj.2 ⟨hxy, hTF⟩)

lemma exists_good_graph (N n : ℕ) (h : 2 * N.choose n < 2 ^ (n.choose 2)) :
    ∃ G : SimpleGraph (Fin N),
      (∀ s : Finset (Fin N), ¬ G.IsNClique n s) ∧ ∀ s : Finset (Fin N), ¬ G.IsNIndepSet n s := by
  classical
  by_contra hcon
  have key : ∀ G : SimpleGraph (Fin N),
      (∃ s, G.IsNClique n s) ∨ ∃ s, G.IsNIndepSet n s := fun G => by
    by_contra h'
    exact hcon ⟨G, fun s hs => h' (Or.inl ⟨s, hs⟩), fun s hs => h' (Or.inr ⟨s, hs⟩)⟩
  set E : Finset (Finset (Fin N)) := (Finset.univ : Finset (Fin N)).powersetCard 2 with hE
  have hEcard : E.card = N.choose 2 := by
    rw [hE, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  -- bad families for a given `n`-set
  let Bc : Finset (Fin N) → Finset (Finset (Finset (Fin N))) :=
    fun S => E.powerset.filter (fun F => S.powersetCard 2 ⊆ F)
  let Bi : Finset (Fin N) → Finset (Finset (Finset (Fin N))) :=
    fun S => E.powerset.filter (fun F => Disjoint F (S.powersetCard 2))
  have hcover : E.powerset ⊆ (Finset.univ.powersetCard n).biUnion (fun S => Bc S ∪ Bi S) := by
    intro F hF
    rw [Finset.mem_biUnion]
    rcases key (gr N F) with ⟨S, hS⟩ | ⟨S, hS⟩
    · refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.card_eq⟩, ?_⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hF, pow2_subset_of_clique hS⟩)
    · refine ⟨S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS.card_eq⟩, ?_⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hF, disjoint_of_indep hS⟩)
  have hBc : ∀ S : Finset (Fin N), S.card = n →
      (Bc S).card ≤ 2 ^ (E.card - n.choose 2) := by
    intro S hS
    have hsub : S.powersetCard 2 ⊆ E := Finset.powersetCard_mono (Finset.subset_univ S)
    have hES : (S.powersetCard 2).card = n.choose 2 := by rw [Finset.card_powersetCard, hS]
    calc (Bc S).card ≤ ((E \ S.powersetCard 2).powerset).card := by
          refine Finset.card_le_card_of_injOn (fun F => F \ S.powersetCard 2) ?_ ?_
          · intro F hF
            simp only [Finset.mem_coe, Bc, Finset.mem_filter, Finset.mem_powerset] at hF ⊢
            exact Finset.sdiff_subset_sdiff hF.1 (le_refl _)
          · intro F hF G hG hFG
            simp only [Finset.mem_coe, Bc, Finset.mem_filter] at hF hG
            have := congrArg (· ∪ S.powersetCard 2) hFG
            simp only [Finset.sdiff_union_of_subset hF.2, Finset.sdiff_union_of_subset hG.2] at this
            exact this
      _ = 2 ^ (E.card - n.choose 2) := by
          rw [Finset.card_powerset, Finset.card_sdiff_of_subset hsub, hES]
  have hBi : ∀ S : Finset (Fin N), S.card = n →
      (Bi S).card ≤ 2 ^ (E.card - n.choose 2) := by
    intro S hS
    have hsub : S.powersetCard 2 ⊆ E := Finset.powersetCard_mono (Finset.subset_univ S)
    have hES : (S.powersetCard 2).card = n.choose 2 := by rw [Finset.card_powersetCard, hS]
    calc (Bi S).card ≤ ((E \ S.powersetCard 2).powerset).card := by
          refine Finset.card_le_card ?_
          intro F hF
          simp only [Bi, Finset.mem_filter, Finset.mem_powerset] at hF ⊢
          exact Finset.subset_sdiff.2 ⟨hF.1, hF.2⟩
      _ = 2 ^ (E.card - n.choose 2) := by
          rw [Finset.card_powerset, Finset.card_sdiff_of_subset hsub, hES]
  have hbound : 2 ^ E.card ≤ N.choose n * (2 * 2 ^ (E.card - n.choose 2)) := by
    calc 2 ^ E.card = E.powerset.card := (Finset.card_powerset E).symm
      _ ≤ ((Finset.univ.powersetCard n).biUnion (fun S => Bc S ∪ Bi S)).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ S ∈ Finset.univ.powersetCard n, (Bc S ∪ Bi S).card := Finset.card_biUnion_le
      _ ≤ ∑ S ∈ Finset.univ.powersetCard n, (2 * 2 ^ (E.card - n.choose 2)) := by
          refine Finset.sum_le_sum fun S hS => ?_
          have hSn : S.card = n := (Finset.mem_powersetCard.1 hS).2
          calc (Bc S ∪ Bi S).card ≤ (Bc S).card + (Bi S).card := Finset.card_union_le _ _
            _ ≤ 2 ^ (E.card - n.choose 2) + 2 ^ (E.card - n.choose 2) :=
                add_le_add (hBc S hSn) (hBi S hSn)
            _ = 2 * 2 ^ (E.card - n.choose 2) := by ring
      _ = N.choose n * (2 * 2 ^ (E.card - n.choose 2)) := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
  rcases lt_or_ge N n with hNn | hnN
  · rw [Nat.choose_eq_zero_of_lt hNn, zero_mul] at hbound
    exact absurd hbound (not_le.2 (by positivity))
  · have ha : n.choose 2 ≤ E.card := by rw [hEcard]; exact Nat.choose_le_choose 2 hnN
    have h1 : 2 ^ (E.card - n.choose 2) * 2 ^ (n.choose 2) ≤
        2 ^ (E.card - n.choose 2) * (2 * N.choose n) := by
      calc 2 ^ (E.card - n.choose 2) * 2 ^ (n.choose 2) = 2 ^ E.card := by
            rw [← pow_add, Nat.sub_add_cancel ha]
        _ ≤ N.choose n * (2 * 2 ^ (E.card - n.choose 2)) := hbound
        _ = 2 ^ (E.card - n.choose 2) * (2 * N.choose n) := by ring
    have h2 := Nat.le_of_mul_le_mul_left h1 (by positivity)
    omega

/-! ### Part C: the numerical inequality -/

lemma numeric (n N : ℕ) (hn : 0 < n)
    (hlt : (N : ℝ) < (n : ℝ) / (Real.exp 1 * Real.sqrt 2) * (2 : ℝ) ^ ((n : ℝ) / 2)) :
    2 * N.choose n < 2 ^ (n.choose 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hpow : (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2) = Real.sqrt 2 ^ (k + 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    push_cast
    ring
  have hX : ((k + 1 : ℕ) : ℝ) / (Real.exp 1 * Real.sqrt 2) * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) / 2) =
      ((k + 1 : ℕ) : ℝ) / Real.exp 1 * Real.sqrt 2 ^ k := by
    rw [hpow, pow_succ]
    field_simp
  rw [hX] at hlt
  obtain ⟨j, hj⟩ := Nat.even_mul_succ_self k
  have hc2 : (k + 1).choose 2 = j := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, mul_comm, hj]
    omega
  set a : ℝ := (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) with ha
  have ha0 : 0 < a := by positivity
  have hXpow : (((k + 1 : ℕ) : ℝ) / Real.exp 1 * Real.sqrt 2 ^ k) ^ (k + 1) = a * 2 ^ j := by
    rw [mul_pow, ← pow_mul, show k * (k + 1) = 2 * j by omega, pow_mul, hsq]
  have h1 : (N : ℝ) ^ (k + 1) < a * 2 ^ j := by
    rw [← hXpow]
    exact pow_lt_pow_left₀ hlt (Nat.cast_nonneg _) (Nat.succ_ne_zero k)
  have hF : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hchoose : ((N.choose (k + 1) : ℕ) : ℝ) * ((k + 1).factorial : ℝ) ≤ (N : ℝ) ^ (k + 1) :=
    (le_div_iff₀ hF).1 (Nat.choose_le_pow_div (k + 1) N)
  have hst : 2 * a ≤ ((k + 1).factorial : ℝ) := by
    have h := Stirling.le_factorial_stirling (k + 1)
    have h2 : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi * ((k + 1 : ℕ) : ℝ)) := by
      refine (Real.le_sqrt' (by norm_num)).2 ?_
      have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ k + 1 := by omega
        exact_mod_cast this
      nlinarith [Real.pi_gt_three]
    calc 2 * a ≤ Real.sqrt (2 * Real.pi * ((k + 1 : ℕ) : ℝ)) * a :=
          mul_le_mul_of_nonneg_right h2 ha0.le
      _ ≤ _ := h
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hlin : 2 * ((N.choose (k + 1) : ℕ) : ℝ) * ((k + 1).factorial : ℝ) <
      2 ^ j * ((k + 1).factorial : ℝ) := by
    have h3 : 2 * a * 2 ^ j ≤ ((k + 1).factorial : ℝ) * 2 ^ j :=
      mul_le_mul_of_nonneg_right hst h2j.le
    nlinarith
  have hres : 2 * ((N.choose (k + 1) : ℕ) : ℝ) < 2 ^ j := lt_of_mul_lt_mul_right hlin hF.le
  rw [hc2]
  exact_mod_cast hres

end ErdosRamseyAux

/-- Erdős' lower bound for the diagonal Ramsey number. -/
theorem solution (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / (Real.exp 1 * Real.sqrt 2) * (2 : ℝ) ^ ((n : ℝ) / 2) ≤
      (AppliedComb.Ramsey.ramseyNumber n n : ℝ) := by
  have hset := ErdosRamseyAux.ramsey_set_nonempty n
  have hR : AppliedComb.Ramsey.ramseyNumber n n ∈
      {N : ℕ | 0 < N ∧ AppliedComb.Ramsey.IsRamseyBound n n N} := Nat.sInf_mem hset
  obtain ⟨hRpos, hRb⟩ := hR
  by_contra hcon
  have hcon' := not_le.1 hcon
  have hnum := ErdosRamseyAux.numeric n (AppliedComb.Ramsey.ramseyNumber n n) hn hcon'
  obtain ⟨G, hG1, hG2⟩ := ErdosRamseyAux.exists_good_graph _ n hnum
  have := hRb (Fin (AppliedComb.Ramsey.ramseyNumber n n)) (le_of_eq (Fintype.card_fin _).symm) G
  rcases this with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact hG1 s hs
  · exact hG2 s hs
