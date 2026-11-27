-- Prove2me | solution 1 for AlonMilman.PropertyT.Supplement.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:19.544866+00:00
-- url     : https://prove2.me/submissions/a3e1dabf-38ce-40d3-befb-14a7f19d3745

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_Supplement_concentrationFun
import Definitions.Def_AlonMilman_PropertyT_Supplement_IsConcentrated
import Definitions.Def_AlonMilman_PropertyT_Supplement_boxPi

open AlonMilman
open AlonMilman.PropertyT
open AlonMilman.PropertyT.Supplement

/-- Theorem 3.2 (Alon–Milman 1985, p. 81). Let `H` be any fixed finite connected simple graph.
For `i ≥ 1` let `G_i` be the Cartesian product of `i` copies of `H`. Then `{G_i}_{i ≥ 1}` is a
concentrated family of graphs. -/
theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (hH : H.Connected) :
    IsConcentrated (fun i : ℕ+ => Fin (i : ℕ) → V) (fun i => cartesianPower H (i : ℕ)) := by
      set D : ℕ := (Finset.univ : Finset (V × V)).sup (fun p => H.dist p.1 p.2) + 1
        with hDdef
      have hD : ∀ a b : V, H.dist a b ≤ D := by
        intro a b
        have : H.dist a b ≤ (Finset.univ : Finset (V × V)).sup
            (fun p => H.dist p.1 p.2) :=
          Finset.le_sup (f := fun p : V × V => H.dist p.1 p.2) (Finset.mem_univ (a, b))
        omega
      have hDpos : (0:ℝ) < D := by rw [hDdef]; positivity
      have main : ∀ l : ℝ, 0 ≤ l →
        ∀ n : ℕ, ∀ A : Finset (Fin n → V), ∃ f : (Fin n → V) → ℕ, A.Nonempty →
          (∀ x, ∃ a ∈ A, (cartesianPower H n).Reachable a x ∧ (cartesianPower H n).dist a x ≤ f x) ∧
          (A.card : ℝ) * ∑ x, Real.exp (l * f x) ≤
            ((Real.exp (l * D) + 1) ^ 2 / (4 * Real.exp (l * D))) ^ n *
              ((Fintype.card V : ℝ) ^ n) ^ 2 := by
        intro l hl
        have hsum : ∀ n : ℕ, ∀ g : (Fin (n+1) → V) → ℝ,
            ∑ x, g x = ∑ ω : V, ∑ y : Fin n → V, g (Fin.cons ω y) := by
          intro n g
          rw [← (Fin.consEquiv fun _ => V).sum_comp, Fintype.sum_prod_type]
          rfl
        set E := Real.exp (l * D) with hE
        have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by positivity)
        set K := (E + 1) ^ 2 / (4 * E) with hK
        set M : ℝ := (Fintype.card V : ℝ) with hM
        intro n
        induction n with
        | zero =>
          intro A
          refine ⟨fun _ => 0, fun hA => ⟨fun x => ?_, ?_⟩⟩
          · obtain ⟨a, ha⟩ := hA
            refine ⟨a, ha, ?_, ?_⟩
            · rw [Subsingleton.elim a x]
            · rw [Subsingleton.elim a x, SimpleGraph.dist_self]
          · have hc : A.card ≤ 1 := by
              calc A.card ≤ Fintype.card (Fin 0 → V) := Finset.card_le_univ _
                _ = 1 := by simp
            have : (A.card : ℝ) ≤ 1 := by exact_mod_cast hc
            simp only [CharP.cast_eq_zero, mul_zero, Real.exp_zero, Finset.sum_const, Finset.card_univ,
              pow_zero, one_pow, mul_one]
            simp
            exact_mod_cast hc
        | succ n ih =>
          choose F hF using ih
          intro A
          -- homs
          let φ : V → (cartesianPower H n →g cartesianPower H (n+1)) := fun ω =>
            ⟨fun y => (Fin.cons ω y : Fin (n+1) → V), by
              intro y y' hyy
              obtain ⟨j, hj, hj'⟩ := hyy
              refine ⟨j.succ, by simpa using hj, ?_⟩
              intro j' hne
              refine Fin.cases ?_ (fun k hk => ?_) j' hne
              · intro _; rfl
              · simp only [Fin.cons_succ]
                exact hj' k (fun h => hk (by rw [h]))⟩
          let ψ : (Fin n → V) → (H →g cartesianPower H (n+1)) := fun y =>
            ⟨fun ω => (Fin.cons ω y : Fin (n+1) → V), by
              intro ω ω' hωω
              refine ⟨0, by simpa using hωω, ?_⟩
              intro j' hne
              refine Fin.cases ?_ (fun k hk => ?_) j' hne
              · intro h; exact absurd rfl h
              · simp⟩
          let sec : V → Finset (Fin n → V) := fun ω =>
            Finset.univ.filter (fun y => (Fin.cons ω y : Fin (n+1) → V) ∈ A)
          let B : Finset (Fin n → V) :=
            Finset.univ.filter (fun y => ∃ ω, (Fin.cons ω y : Fin (n+1) → V) ∈ A)
          let T : V → ℝ := fun ω => ∑ y, Real.exp (l * F (sec ω) y)
          let U : ℝ := ∑ y, Real.exp (l * F B y)
          let ch : V → Prop := fun ω => (sec ω).Nonempty ∧ T ω ≤ E * U
          classical
          let f : (Fin (n+1) → V) → ℕ := fun x =>
            if ch (x 0) then F (sec (x 0)) (Fin.tail x) else D + F B (Fin.tail x)
          have hf : ∀ ω y, f (Fin.cons ω y) =
              if ch ω then F (sec ω) y else D + F B y := by
            intro ω y; simp [f]
          refine ⟨f, fun hA => ?_⟩
          have hBne : B.Nonempty := by
            obtain ⟨a, ha⟩ := hA
            refine ⟨Fin.tail a, Finset.mem_filter.2 ⟨Finset.mem_univ _, a 0, ?_⟩⟩
            simpa using ha
          have hsecB : ∀ ω, sec ω ⊆ B := by
            intro ω y hy
            simp only [sec, B, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
            exact ⟨ω, hy⟩
          obtain ⟨hFB1, hFB2⟩ := hF B hBne
          constructor
          · intro x
            obtain ⟨ω, y, rfl⟩ : ∃ ω y, x = (Fin.cons ω y : Fin (n+1) → V) :=
              ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
            rw [hf]
            split_ifs with hc
            · obtain ⟨a', ha', hr, hd⟩ := (hF (sec ω) hc.1).1 y
              refine ⟨Fin.cons ω a', (Finset.mem_filter.1 ha').2, ?_, ?_⟩
              · exact hr.map (φ ω)
              · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
                calc (cartesianPower H (n+1)).dist (Fin.cons ω a') (Fin.cons ω y)
                    ≤ (p.map (φ ω)).length := SimpleGraph.dist_le _
                  _ = _ := by rw [SimpleGraph.Walk.length_map, hp]
                  _ ≤ _ := hd
            · obtain ⟨b, hb, hr, hd⟩ := hFB1 y
              obtain ⟨ω', hω'⟩ := (Finset.mem_filter.1 hb).2
              obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
              obtain ⟨q, hq⟩ := (hH.preconnected ω' ω).exists_walk_length_eq_dist
              let w := (q.map (ψ b)).append (p.map (φ ω))
              refine ⟨Fin.cons ω' b, hω', ⟨w⟩, ?_⟩
              calc (cartesianPower H (n+1)).dist (Fin.cons ω' b) (Fin.cons ω y)
                  ≤ w.length := SimpleGraph.dist_le _
                _ = H.dist ω' ω + (cartesianPower H n).dist b y := by
                  simp only [w, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_map, hp, hq]
                _ ≤ D + F B y := Nat.add_le_add (hD _ _) hd
          · have scal : ∀ a b S X : ℝ, 0 ≤ a → a ≤ b → 0 < b → 0 ≤ X → 0 ≤ S →
                b * S ≤ E * X → (0 < a → a * S ≤ X) → S * b ^ 2 ≤ X * (b * (E + 1) - E * a) := by
              intro a b S X ha hab hb hX hS h1 h2
              by_cases hEa : b ≤ E * a
              · have ha0 : 0 < a := by
                  by_contra hc
                  have : a = 0 := le_antisymm (not_lt.1 hc) ha
                  rw [this, mul_zero] at hEa; linarith
                have h3 := h2 ha0
                have key : a * (S * b ^ 2) ≤ a * (X * (b * (E + 1) - E * a)) := by
                  have e1 : a * (S * b ^ 2) ≤ X * b ^ 2 := by
                    have := mul_le_mul_of_nonneg_right h3 (sq_nonneg b); linarith
                  have e2 : 0 ≤ X * ((b - a) * (E * a - b)) :=
                    mul_nonneg hX (mul_nonneg (by linarith) (by linarith))
                  nlinarith
                exact le_of_mul_le_mul_left key ha0
              · push_neg at hEa
                have e1 : S * b ^ 2 ≤ b * (E * X) := by
                  have := mul_le_mul_of_nonneg_left h1 hb.le; nlinarith
                have e2 : 0 ≤ X * (b - E * a) := mul_nonneg hX (by linarith)
                nlinarith
            set X := K ^ n * (M ^ n) ^ 2 with hXdef
            have hX : 0 ≤ X := by
              have : 0 ≤ K := by rw [hK]; positivity
              positivity
            let S : V → ℝ := fun ω => if ch ω then T ω else E * U
            have h1 : ∑ x, Real.exp (l * f x) = ∑ ω, S ω := by
              rw [hsum]
              refine Finset.sum_congr rfl (fun ω _ => ?_)
              by_cases hc : ch ω
              · simp only [hf, hc, if_true, S, T]
              · simp only [hf, hc, if_false, S, U, Nat.cast_add, mul_add, Real.exp_add, E,
                  Finset.mul_sum]
            have h2 : (A.card : ℝ) = ∑ ω, ((sec ω).card : ℝ) := by
              have e : (A.card : ℝ) = ∑ x : Fin (n+1) → V, if x ∈ A then (1:ℝ) else 0 := by
                rw [Finset.sum_boole]; simp
              rw [e, hsum]
              refine Finset.sum_congr rfl (fun ω _ => ?_)
              rw [Finset.sum_boole]
            have hb : (0 : ℝ) < B.card := by exact_mod_cast hBne.card_pos
            have hU0 : 0 ≤ U := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
            have hT0 : ∀ ω, 0 ≤ T ω := fun ω => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
            have hper : ∀ ω, S ω * (B.card : ℝ) ^ 2 ≤
                X * ((B.card : ℝ) * (E + 1) - E * (sec ω).card) := by
              intro ω
              have hab : ((sec ω).card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card (hsecB ω)
              have hSU : S ω ≤ E * U := by
                by_cases hc : ch ω
                · simp only [S, hc, if_true]; exact hc.2
                · simp only [S, hc, if_false]; exact le_rfl
              refine scal _ _ _ _ (Nat.cast_nonneg _) hab hb hX ?_ ?_ ?_
              · by_cases hc : ch ω
                · simp only [S, hc, if_true]; exact hT0 ω
                · simp only [S, hc, if_false]; exact mul_nonneg (by linarith) hU0
              · calc (B.card : ℝ) * S ω ≤ B.card * (E * U) := mul_le_mul_of_nonneg_left hSU hb.le
                  _ = E * (B.card * U) := by ring
                  _ ≤ E * X := mul_le_mul_of_nonneg_left hFB2 (by linarith)
              · intro ha0
                have hne : (sec ω).Nonempty := Finset.card_pos.1 (by exact_mod_cast ha0)
                have hT := (hF (sec ω) hne).2
                have hST : S ω ≤ T ω := by
                  by_cases hc : ch ω
                  · simp only [S, hc, if_true]; exact le_rfl
                  · simp only [S, hc, if_false]
                    have : ¬ T ω ≤ E * U := fun h => hc ⟨hne, h⟩
                    push_neg at this; exact this.le
                calc ((sec ω).card : ℝ) * S ω ≤ (sec ω).card * T ω :=
                      mul_le_mul_of_nonneg_left hST (Nat.cast_nonneg _)
                  _ ≤ X := hT
            have hsumS : (∑ ω, S ω) * (B.card : ℝ) ^ 2 ≤
                X * (M * (B.card : ℝ) * (E + 1) - E * A.card) := by
              rw [Finset.sum_mul, h2]
              calc ∑ ω, S ω * (B.card : ℝ) ^ 2 ≤ ∑ ω, X * ((B.card : ℝ) * (E + 1) - E * (sec ω).card) :=
                    Finset.sum_le_sum (fun ω _ => hper ω)
                _ = X * (M * (B.card : ℝ) * (E + 1) - E * ∑ ω, ((sec ω).card : ℝ)) := by
                  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
                    Finset.card_univ, hM]
                  simp only [nsmul_eq_mul, ← Finset.mul_sum]; ring
            have hS0 : 0 ≤ ∑ ω, S ω := by
              rw [← h1]; exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
            have hA0 : (0:ℝ) ≤ A.card := Nat.cast_nonneg _
            have hE0 : 0 < E := by linarith
            rw [h1]
            have hfin : (A.card : ℝ) * (∑ ω, S ω) * (B.card : ℝ) ^ 2 ≤
                (X * (M ^ 2 * K)) * (B.card : ℝ) ^ 2 := by
              have e1 : (A.card : ℝ) * (∑ ω, S ω) * (B.card : ℝ) ^ 2 ≤
                  A.card * (X * (M * (B.card : ℝ) * (E + 1) - E * A.card)) := by
                rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hsumS hA0
              have e2 : (A.card : ℝ) * (M * (B.card : ℝ) * (E + 1) - E * A.card) * (4 * E) ≤
                  M ^ 2 * (B.card : ℝ) ^ 2 * (E + 1) ^ 2 := by
                nlinarith [sq_nonneg (M * (B.card : ℝ) * (E + 1) - 2 * E * A.card)]
              have e3 : (A.card : ℝ) * (M * (B.card : ℝ) * (E + 1) - E * A.card) ≤
                  M ^ 2 * K * (B.card : ℝ) ^ 2 := by
                rw [hK, div_eq_mul_inv]
                have h4E : 0 < 4 * E := by linarith
                have := mul_le_mul_of_nonneg_right e2 (inv_nonneg.2 h4E.le)
                rw [mul_assoc, mul_inv_cancel₀ h4E.ne', mul_one] at this
                linarith [this]
              calc (A.card : ℝ) * (∑ ω, S ω) * (B.card : ℝ) ^ 2
                  ≤ A.card * (X * (M * (B.card : ℝ) * (E + 1) - E * A.card)) := e1
                _ = X * ((A.card : ℝ) * (M * (B.card : ℝ) * (E + 1) - E * A.card)) := by ring
                _ ≤ X * (M ^ 2 * K * (B.card : ℝ) ^ 2) := mul_le_mul_of_nonneg_left e3 hX
                _ = (X * (M ^ 2 * K)) * (B.card : ℝ) ^ 2 := by ring
            have := le_of_mul_le_mul_right hfin (by positivity)
            calc (A.card : ℝ) * (∑ ω, S ω) ≤ X * (M ^ 2 * K) := this
              _ = K ^ (n + 1) * (M ^ (n + 1)) ^ 2 := by rw [hXdef]; ring
      have hdiam : ∀ n : ℕ, (cartesianPower H n).diam = 0 ∨ n ≤ (cartesianPower H n).diam := by
        intro n
        by_cases hV : ∃ a b : V, a ≠ b
        · right
          obtain ⟨a, b, hab⟩ := hV
          haveI : Nonempty (Fin n → V) := ⟨fun _ => a⟩
          have hconn : (cartesianPower H n).Connected := by
            obtain ⟨f, hf⟩ := main 0 le_rfl n {fun _ => a}
            have hr := (hf ⟨_, Finset.mem_singleton_self _⟩).1
            refine ⟨fun x y => ?_⟩
            obtain ⟨a1, ha1, hx, -⟩ := hr x
            obtain ⟨a2, ha2, hy, -⟩ := hr y
            rw [Finset.mem_singleton] at ha1 ha2
            subst ha1; subst ha2
            exact hx.symm.trans hy
          have hham : ∀ (u v : Fin n → V) (p : (cartesianPower H n).Walk u v),
              (Finset.univ.filter (fun j => u j ≠ v j)).card ≤ p.length := by
            intro u v p
            induction p with
            | nil => simp
            | @cons u' w v' hadj p ih =>
              rw [SimpleGraph.Walk.length_cons]
              obtain ⟨j0, -, hj0⟩ := hadj
              calc (Finset.univ.filter (fun j => u' j ≠ v' j)).card
                  ≤ (insert j0 (Finset.univ.filter (fun j => w j ≠ v' j))).card := by
                    apply Finset.card_le_card
                    intro j hj
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hj ⊢
                    by_cases hjj : j = j0
                    · left; exact hjj
                    · right; rw [← hj0 j hjj]; exact hj
                _ ≤ (Finset.univ.filter (fun j => w j ≠ v' j)).card + 1 := Finset.card_insert_le _ _
                _ ≤ p.length + 1 := by omega
          have hne := SimpleGraph.connected_iff_ediam_ne_top.1 hconn
          obtain ⟨p, hp⟩ :=
            (hconn.preconnected (fun _ => a) (fun _ => b)).exists_walk_length_eq_dist
          have h1 : n ≤ p.length := by
            have := hham _ _ p
            simpa [hab] using this
          have h3 := SimpleGraph.dist_le_diam hne (u := fun _ => a) (v := fun _ => b)
          omega
        · left
          push_neg at hV
          haveI : Subsingleton V := ⟨hV⟩
          simp [SimpleGraph.diam, SimpleGraph.ediam_eq_zero_of_subsingleton]
      refine ⟨2 * Real.exp (1/4), 1 / D, by positivity, by positivity, ?_⟩
      intro i ρ hρ
      show concentrationFun (cartesianPower H (i:ℕ)) ρ ≤ 2 * Real.exp (1/4) *
        Real.exp (-(⌊1 / (D:ℝ) * ρ / Real.sqrt ((cartesianPower H (i:ℕ)).diam : ℝ)⌋₊ : ℝ))
      have hn1' : 1 ≤ (i:ℕ) := i.pos
      generalize (i:ℕ) = n at hn1' ⊢
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn1'
      set l : ℝ := 1 / (D * Real.sqrt n) with hl
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
      have hl0 : 0 < l := by positivity
      have hKb : ((Real.exp (l * D) + 1) ^ 2 / (4 * Real.exp (l * D))) ^ n ≤ Real.exp (1/4) := by
        have ht : l * D = 1 / Real.sqrt n := by rw [hl]; field_simp
        set t := l * D
        have hK1 : (Real.exp t + 1) ^ 2 / (4 * Real.exp t) = Real.cosh (t/2) ^ 2 := by
          rw [Real.cosh_eq]
          have e : Real.exp t = Real.exp (t/2) ^ 2 := by
            rw [← Real.exp_nat_mul]; push_cast; ring_nf
          have e2 : Real.exp (-(t/2)) = (Real.exp (t/2))⁻¹ := Real.exp_neg _
          rw [e, e2]
          have := Real.exp_pos (t/2)
          field_simp
          ring
        have hK2 : Real.cosh (t/2) ^ 2 ≤ Real.exp (t^2/4) := by
          have h := Real.cosh_le_exp_half_sq (t/2)
          have h0 : 0 ≤ Real.cosh (t/2) := (Real.cosh_pos _).le
          calc Real.cosh (t/2) ^ 2 ≤ Real.exp ((t/2)^2/2) ^ 2 := pow_le_pow_left₀ h0 h 2
            _ = Real.exp (t^2/4) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have ht2 : t^2 = 1 / n := by rw [ht, div_pow, Real.sq_sqrt (by linarith)]; ring
        rw [hK1]
        calc (Real.cosh (t/2) ^ 2) ^ n ≤ Real.exp (t^2/4) ^ n :=
              pow_le_pow_left₀ (by positivity) hK2 n
          _ = Real.exp (n * (t^2/4)) := (Real.exp_nat_mul _ _).symm
          _ = Real.exp (1/4) := by congr 1; rw [ht2]; field_simp
      have hmainb : concentrationFun (cartesianPower H n) ρ ≤
          2 * Real.exp (1/4) * Real.exp (-(l * ρ)) := by
        unfold concentrationFun
        split_ifs with h0
        · positivity
        · apply Finset.sup'_le
          intro A hA
          have hA2 := (Finset.mem_filter.1 hA).2
          have hNpos : (0:ℝ) < (Fintype.card (Fin n → V) : ℝ) := by
            have := Nat.pos_of_ne_zero h0; exact_mod_cast this
          have hAne : A.Nonempty := by
            rw [← Finset.card_pos]
            have : (0:ℝ) < A.card := by linarith
            exact_mod_cast this
          obtain ⟨f, hf⟩ := main l hl0.le n A
          obtain ⟨hf1, hf2⟩ := hf hAne
          set En := enlargement (cartesianPower H n) A ρ with hEn
          have hcard : (En.card : ℝ) + (Enᶜ.card : ℝ) = (Fintype.card (Fin n → V) : ℝ) := by
            exact_mod_cast Finset.card_add_card_compl _
          have hfx : ∀ x ∈ Enᶜ, ρ < f x := by
            intro x hx
            rw [Finset.mem_compl] at hx
            by_contra hc
            push_neg at hc
            obtain ⟨a, ha, hr, hd⟩ := hf1 x
            apply hx
            rw [hEn]
            unfold enlargement
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨a, ha, hr, le_trans (by exact_mod_cast hd) hc⟩
          have hs0 : 0 ≤ ∑ x, Real.exp (l * f x) :=
            Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
          have hCsum : (Enᶜ.card : ℝ) * Real.exp (l * ρ) ≤ ∑ x, Real.exp (l * f x) := by
            calc (Enᶜ.card : ℝ) * Real.exp (l * ρ) = ∑ x ∈ Enᶜ, Real.exp (l * ρ) := by
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ ∑ x ∈ Enᶜ, Real.exp (l * f x) := Finset.sum_le_sum (fun x hx =>
                  Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hfx x hx).le hl0.le))
              _ ≤ ∑ x, Real.exp (l * f x) := Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)
          have hcardN : (Fintype.card (Fin n → V) : ℝ) = (Fintype.card V : ℝ) ^ n := by simp
          have hS : (A.card : ℝ) * ∑ x, Real.exp (l * f x) ≤
              Real.exp (1/4) * (Fintype.card (Fin n → V) : ℝ) ^ 2 := by
            refine hf2.trans ?_
            rw [hcardN]
            exact mul_le_mul_of_nonneg_right hKb (by positivity)
          set N : ℝ := (Fintype.card (Fin n → V) : ℝ)
          set c' : ℝ := (Enᶜ.card : ℝ)
          have k1 : c' * Real.exp (l * ρ) * N ≤ 2 * (Real.exp (1/4) * N ^ 2) := by
            calc c' * Real.exp (l * ρ) * N ≤ (∑ x, Real.exp (l * f x)) * (2 * A.card) :=
                  mul_le_mul hCsum hA2 hNpos.le hs0
              _ = 2 * (A.card * ∑ x, Real.exp (l * f x)) := by ring
              _ ≤ 2 * (Real.exp (1/4) * N ^ 2) := by linarith
          have hee : Real.exp (-(l * ρ)) * Real.exp (l * ρ) = 1 := by
            rw [← Real.exp_add]; simp
          have k2 : c' ≤ 2 * Real.exp (1/4) * Real.exp (-(l * ρ)) * N := by
            have hpos : 0 < Real.exp (l * ρ) * N := by positivity
            refine le_of_mul_le_mul_right ?_ hpos
            calc c' * (Real.exp (l * ρ) * N) = c' * Real.exp (l * ρ) * N := by ring
              _ ≤ 2 * (Real.exp (1/4) * N ^ 2) := k1
              _ = 2 * Real.exp (1/4) * (Real.exp (-(l * ρ)) * Real.exp (l * ρ)) * N * N := by
                  rw [hee]; ring
              _ = 2 * Real.exp (1/4) * Real.exp (-(l * ρ)) * N * (Real.exp (l * ρ) * N) := by ring
          have : 1 - (En.card : ℝ) / N = c' / N := by
            field_simp
            linarith
          rw [this, div_le_iff₀ hNpos]
          exact k2
      have hfl : (⌊1 / (D:ℝ) * ρ / Real.sqrt ((cartesianPower H n).diam : ℝ)⌋₊ : ℝ) ≤ l * ρ := by
        rcases hdiam n with h0 | hge
        · rw [h0]; simp; positivity
        · have hge' : (n:ℝ) ≤ (cartesianPower H n).diam := by exact_mod_cast hge
          have hs : Real.sqrt n ≤ Real.sqrt ((cartesianPower H n).diam) := Real.sqrt_le_sqrt hge'
          have hx0 : 0 ≤ 1 / (D:ℝ) * ρ / Real.sqrt ((cartesianPower H n).diam : ℝ) := by positivity
          refine (Nat.floor_le hx0).trans ?_
          calc 1 / (D:ℝ) * ρ / Real.sqrt ((cartesianPower H n).diam : ℝ)
              = ρ / (D * Real.sqrt ((cartesianPower H n).diam : ℝ)) := by ring
            _ ≤ ρ / (D * Real.sqrt n) := div_le_div_of_nonneg_left hρ.le (by positivity)
                (mul_le_mul_of_nonneg_left hs hDpos.le)
            _ = l * ρ := by rw [hl]; ring
      calc concentrationFun (cartesianPower H n) ρ ≤ 2 * Real.exp (1/4) * Real.exp (-(l * ρ)) := hmainb
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
