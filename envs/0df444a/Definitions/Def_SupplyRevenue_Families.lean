-- Prove2me | Definitions.Def_SupplyRevenue_Families
-- name    : SupplyRevenue_Families
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:40.068526+00:00
-- url     : https://prove2.me/theorems/cd8a7965-a1e7-4ea1-b3cc-485f50466e4d
-- title:
--   The lower-bound instances of §9
-- statement:
--   Four instances. In each, a number of active items is fixed and the remaining items of $M$ are worthless.
--
--   1. **Family (17):** $k=4^L$ and $k^2$ active items. Each of $n$ buyers independently draws a uniform $k$-subset $A$ of the active items and a uniform $s\in\{2,4,\dots,2^L\}$, with value $v_{A,s}(Q)=\max\{(t+1)|Q\cap A|,\ (1+k/s)\min\{|Q|,ts\}\}$.
--   2. **Rare item:** one buyer valuing one item at one with probability $q$.
--   3. **Clique-star market:** items are the edges of a complete graph on $d+1$ vertices, placed among $M$ by an injection. Buyer $i$ values at one exactly the bundles containing its whole incident star.
--   4. **Dyadic additive buyer:** $s$ uniform on $\{0,\dots,L\}$, then a uniform $2^s$-subset $A$ of the $2^L$ active items, with additive coefficient $2^{-s}$ on $A$ and zero elsewhere.
--
--   They supply all the matching lower bounds of the goal.
--
--   **Formalization Note** $|Q|$ in (17) counts active items, so $m=k^2$ is the page's instance. The clique value tests nonemptiness of the star, which matters only at $d=0$, where it keeps the value normalized; the page has $d\ge1$.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §9, pp.17–19, (17)

import Mathlib
import Definitions.Def_SupplyRevenue_Buyer

namespace SupplyRevenue

/-!
# The lower-bound instances of §9

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§9, pp.17–19: the family (17), the single rare item (p.18), the clique-star market (§9.1) and the dyadic additive family
(§9.2).

**Formalization Note** Padding ("worthless hidden items", p.18) is built in. The active items are `activeItems m N`, the
first `N` items of `Fin m`, and a value reads only `Q ∩ activeItems m N`, so `m = N` is the page's instance. The
family's parameter `k` is `4 ^ L`, and `N = k²`. The level `s ∈ {2, 4, …, 2^L}` is `2 ^ (ℓ + 1)`, `ℓ : Fin L`. The
clique-star market takes the placement of edges among the items as an injection `e`; the edges of `K_{d+1}` are the
non-diagonal elements of `Sym2 (Fin (d + 1))`. `k/s` and `2^{−s}` use real division.
-/

/-- The first `N` items of `Fin m`. -/
def activeItems (m N : ℕ) : Finset (Fin m) := Finset.univ.filter fun j => j.val < N

theorem card_activeItems {m N : ℕ} (h : N ≤ m) : (activeItems m N).card = N := by
  classical
  have : (activeItems m N) = (Finset.range N).attachFin (fun i hi => by
      have := Finset.mem_range.mp hi; omega) := by
    ext j; simp [activeItems]
  rw [this, Finset.card_attachFin, Finset.card_range]

/-- The types of the family (17): a `k`-subset `A` of the active items and a level `ℓ : Fin L`, `s = 2^(ℓ+1)`. -/
abbrev CoreType (L m : ℕ) :=
  {A : Finset (Fin m) // A ⊆ activeItems m (4 ^ L * 4 ^ L) ∧ A.card = 4 ^ L} × Fin L

/-- The value (17), `v_{A,s}(Q) = max{(t+1)|Q ∩ A|, (1 + k/s) min{|Q|, ts}}`, with `k = 4^L` and `|Q|` counting active
items. -/
noncomputable def coreValue (L t m : ℕ) (A : Finset (Fin m)) (s : ℕ) (Q : Finset (Fin m)) : ℝ :=
  max (((t : ℝ) + 1) * ((Q ∩ A).card : ℝ))
    ((1 + ((4 ^ L : ℕ) : ℝ) / (s : ℝ)) *
      ((min (Q ∩ activeItems m (4 ^ L * 4 ^ L)).card (t * s) : ℕ) : ℝ))

theorem coreValue_valuation (L t m : ℕ) (A : Finset (Fin m)) (s : ℕ) :
    IsValuation (coreValue L t m A s) := by
  constructor
  · simp [coreValue]
  · intro Q Q' h
    have hc : (Q ∩ A).card ≤ (Q' ∩ A).card :=
      Finset.card_le_card (Finset.inter_subset_inter_right h)
    have ha : (Q ∩ activeItems m (4 ^ L * 4 ^ L)).card ≤ (Q' ∩ activeItems m (4 ^ L * 4 ^ L)).card :=
      Finset.card_le_card (Finset.inter_subset_inter_right h)
    apply max_le_max
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hc) (by positivity)
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_min_right _ ha) (by positivity)

/-- A uniform buyer over a finite nonempty type set. -/
noncomputable def uniformBuyer {m : ℕ} {Θ : Type} [Fintype Θ] [Nonempty Θ]
    (val : Θ → Finset (Fin m) → ℝ) (hv : ∀ θ, IsValuation (val θ)) : Buyer m :=
  Buyer.ofFintype (fun _ => 1 / (Fintype.card Θ : ℝ)) val (fun _ => by positivity)
    (by
      have : (Fintype.card Θ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp [Finset.card_univ, this])
    hv

theorem coreType_nonempty {L m : ℕ} (hL : 1 ≤ L) (hm : 4 ^ L * 4 ^ L ≤ m) :
    Nonempty (CoreType L m) := by
  have hk : 4 ^ L ≤ (activeItems m (4 ^ L * 4 ^ L)).card := by
    rw [card_activeItems hm]; exact Nat.le_mul_of_pos_right _ (by positivity)
  obtain ⟨A, hA, hc⟩ := Finset.exists_subset_card_eq hk
  exact ⟨(⟨A, hA, hc⟩, ⟨0, hL⟩)⟩

/-- The instance of (17): `n` independent buyers, each drawing a uniform `k`-subset `A` of the `k²` active items and a
uniform `s ∈ {2, 4, …, 2^L}`. -/
noncomputable def coreFamily (L n t m : ℕ) (hL : 1 ≤ L) (hm : 4 ^ L * 4 ^ L ≤ m) : Instance n m :=
  fun _ =>
    haveI := coreType_nonempty hL hm
    uniformBuyer (Θ := CoreType L m)
      (fun θ => coreValue L t m θ.1.1 (2 ^ (θ.2.val + 1)))
      (fun θ => coreValue_valuation L t m θ.1.1 _)

/-- A single buyer valuing one item (item `0`) at one with probability `q`, and nothing otherwise (p.18). All other
items are worthless. -/
noncomputable def rareItem (m : ℕ) (hm : 0 < m) (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Instance 1 m :=
  fun _ => Buyer.ofFintype (Θ := Bool)
    (fun b => if b then q else 1 - q)
    (fun b Q => if b ∧ (⟨0, hm⟩ : Fin m) ∈ Q then 1 else 0)
    (fun b => by cases b <;> simp [h0, h1])
    (by simp)
    (fun b => by
      constructor
      · simp
      · intro Q Q' h
        by_cases hb : b = true
        · by_cases hQ : (⟨0, hm⟩ : Fin m) ∈ Q
          · have : (⟨0, hm⟩ : Fin m) ∈ Q' := h hQ
            simp [hb, hQ, this]
          · simp only [hb, hQ, true_and, if_false]
            split_ifs <;> norm_num
        · simp [hb])

/-- The edges of the complete graph on `d + 1` vertices. -/
abbrev CliqueEdge (d : ℕ) := {s : Sym2 (Fin (d + 1)) // ¬ s.IsDiag}

/-- The star `T_i`: the items at the edges incident to vertex `i`. -/
def cliqueStar {d m : ℕ} (e : CliqueEdge d ↪ Fin m) (i : Fin (d + 1)) : Finset (Fin m) :=
  (Finset.univ.filter fun s : CliqueEdge d => i ∈ s.1).map e

/-- The clique-star market (§9.1): `d + 1` deterministic buyers, buyer `i` valuing at one exactly the bundles containing
its whole star. Items outside the image of `e` are worthless. The nonemptiness test matters only at `d = 0`, where the
star is empty and the value must still be normalized; the page has `d ≥ 1`. -/
noncomputable def cliqueMarket {d m : ℕ} (e : CliqueEdge d ↪ Fin m) : Instance (d + 1) m :=
  fun i => Buyer.ofFintype (Θ := Unit) (fun _ => 1)
    (fun _ Q => if (cliqueStar e i).Nonempty ∧ cliqueStar e i ⊆ Q then 1 else 0)
    (fun _ => zero_le_one)
    (by simp)
    (fun _ => by
      constructor
      · have hne : ¬ ((cliqueStar e i).Nonempty ∧ cliqueStar e i ⊆ ∅) := by
          rintro ⟨h, h'⟩
          rw [Finset.subset_empty] at h'
          exact h.ne_empty h'
        exact if_neg hne
      · intro Q Q' h
        by_cases hQ : (cliqueStar e i).Nonempty ∧ cliqueStar e i ⊆ Q
        · have : (cliqueStar e i).Nonempty ∧ cliqueStar e i ⊆ Q' := ⟨hQ.1, hQ.2.trans h⟩
          simp [hQ, this]
        · simp only [hQ, if_false]
          split_ifs <;> norm_num)

/-- The types of the dyadic family (§9.2): a level `s ∈ {0, …, L}` and a `2^s`-subset of the `2^L` active items. -/
abbrev DyadicType (L m : ℕ) :=
  Σ s : Fin (L + 1), {A : Finset (Fin m) // A ⊆ activeItems m (2 ^ L) ∧ A.card = 2 ^ s.val}

theorem dyadicType_nonempty {L m : ℕ} (hm : 2 ^ L ≤ m) (s : Fin (L + 1)) :
    Nonempty {A : Finset (Fin m) // A ⊆ activeItems m (2 ^ L) ∧ A.card = 2 ^ s.val} := by
  have hk : 2 ^ s.val ≤ (activeItems m (2 ^ L)).card := by
    rw [card_activeItems hm]
    exact Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp s.isLt)
  obtain ⟨A, hA, hc⟩ := Finset.exists_subset_card_eq hk
  exact ⟨⟨A, hA, hc⟩⟩

/-- The dyadic additive buyer (§9.2): `s` uniform on `{0, …, L}`, then a uniform `2^s`-subset `A` of the `2^L` active
items, with additive coefficient `2^{−s}` on `A` and zero elsewhere. -/
noncomputable def dyadicFamily (L m : ℕ) (hm : 2 ^ L ≤ m) : Instance 1 m :=
  fun _ => Buyer.ofFintype (Θ := DyadicType L m)
    (fun θ => (1 / ((L : ℝ) + 1)) *
      (1 / (Fintype.card {A : Finset (Fin m) // A ⊆ activeItems m (2 ^ L) ∧ A.card = 2 ^ θ.1.val} : ℝ)))
    (fun θ Q => (1 / (2 : ℝ) ^ θ.1.val) * ((Q ∩ θ.2.1).card : ℝ))
    (fun _ => by positivity)
    (by
      rw [Fintype.sum_sigma]
      have : ∀ s : Fin (L + 1),
          ∑ _A : {A : Finset (Fin m) // A ⊆ activeItems m (2 ^ L) ∧ A.card = 2 ^ s.val},
            (1 / ((L : ℝ) + 1)) * (1 / (Fintype.card
              {A : Finset (Fin m) // A ⊆ activeItems m (2 ^ L) ∧ A.card = 2 ^ s.val} : ℝ)) =
            1 / ((L : ℝ) + 1) := by
        intro s
        have := dyadicType_nonempty hm s
        have hc : (Fintype.card
            {A : Finset (Fin m) // A ⊆ activeItems m (2 ^ L) ∧ A.card = 2 ^ s.val} : ℝ) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
      simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : ((L : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp)
    (fun θ => by
      constructor
      · simp
      · intro Q Q' h
        exact mul_le_mul_of_nonneg_left
          (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_right h))
          (by positivity))

end SupplyRevenue


