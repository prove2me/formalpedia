-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForestAux
-- name    : BCFGJPSSV26_Stable_LocalSearch_StarForestAux
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:14.266697+00:00
-- url     : https://prove2.me/theorems/0a1bd659-ae5c-40ac-a971-4d1bb8f6ca1a
-- title:
--   BCFGJPSSV26.Stable.LocalSearch.StarForestAux — Combinatorics for the swap families on star forests
-- statement:
--   This is module `BCFGJPSSV26.Stable.LocalSearch.StarForestAux` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Generic counting lemmas for `BCFGJPSSV26.Stable.BiGraph.exists_swap_families`
--   (`BCFGJPSSV26/Stable/LocalSearch/StarForest.lean`):
--
--   * **Ranks** (`BCFGJPSSV26.Stable.StarForestAux.exists_rank`): an injective position function on a
--     finite set, compatible with a key, the elements of smaller key first.
--   * **Cuts** (`BCFGJPSSV26.Stable.StarForestAux.exists_cut`): a cyclic sequence of positions of
--     weight `0` or `1`, with no two consecutive positions of weight `0`, cut from any offset into
--     consecutive blocks of prescribed weights, each at most twice as long as its weight.
--   * **Cyclic blocks** (`BCFGJPSSV26.Stable.StarForestAux.exists_cycle_blocks`): the left leaves of
--     the right stars in a cyclic order with the leaves of each star consecutive, cut into blocks of
--     prescribed weights from every offset; a block of weight `w` has `w` more leaves than stars, up
--     to one, and over all offsets each leaf is in at most `M + 2 (∑ w - E)` blocks.
--   * **Pieces** (`BCFGJPSSV26.Stable.StarForestAux.exists_pieces`): the right leaves cut into pieces
--     of at most `3 N` leaves, keeping the leaves of every small left star together.
--   * Counting residues over all shifts of a window
--     (`BCFGJPSSV26.Stable.StarForestAux.sum_card_mod_le`) and blocks hitting a set
--     (`BCFGJPSSV26.Stable.StarForestAux.card_blocks_le`).
--
--   **Contents.** The module is published as a whole: 12 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForestAux`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LocalSearch/StarForestAux.lean

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.LocalSearch.StarForestAux` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Combinatorics for the swap families on star forests

Generic counting lemmas for `BCFGJPSSV26.Stable.BiGraph.exists_swap_families`
(`BCFGJPSSV26/Stable/LocalSearch/StarForest.lean`):

* **Ranks** (`BCFGJPSSV26.Stable.StarForestAux.exists_rank`): an injective position function on a
  finite set, compatible with a key, the elements of smaller key first.
* **Cuts** (`BCFGJPSSV26.Stable.StarForestAux.exists_cut`): a cyclic sequence of positions of
  weight `0` or `1`, with no two consecutive positions of weight `0`, cut from any offset into
  consecutive blocks of prescribed weights, each at most twice as long as its weight.
* **Cyclic blocks** (`BCFGJPSSV26.Stable.StarForestAux.exists_cycle_blocks`): the left leaves of
  the right stars in a cyclic order with the leaves of each star consecutive, cut into blocks of
  prescribed weights from every offset; a block of weight `w` has `w` more leaves than stars, up
  to one, and over all offsets each leaf is in at most `M + 2 (∑ w - E)` blocks.
* **Pieces** (`BCFGJPSSV26.Stable.StarForestAux.exists_pieces`): the right leaves cut into pieces
  of at most `3 N` leaves, keeping the leaves of every small left star together.
* Counting residues over all shifts of a window
  (`BCFGJPSSV26.Stable.StarForestAux.sum_card_mod_le`) and blocks hitting a set
  (`BCFGJPSSV26.Stable.StarForestAux.card_blocks_le`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable.StarForestAux

open Finset

/-- A ranking of a finite set by a key: an injective position function, with the elements of
smaller key first. -/
theorem exists_rank {γ : Type*} (s : Finset γ) (κ : γ → ℕ) :
    ∃ pos : γ → ℕ, Set.InjOn pos s ∧ ∀ x ∈ s,
      #{y ∈ s | κ y < κ x} ≤ pos x ∧ pos x < #{y ∈ s | κ y ≤ κ x} := by
  classical
  let e : γ → ℕ := fun x ↦ if hx : x ∈ s then (s.equivFin ⟨x, hx⟩ : ℕ) else 0
  have he : Set.InjOn e s := by
    intro x hx y hy h
    have hx' : x ∈ s := hx
    have hy' : y ∈ s := hy
    simp only [e, hx', hy', ↓reduceDIte] at h
    exact congrArg Subtype.val (s.equivFin.injective (Fin.ext h))
  have key : ∀ x ∈ s, ∀ y ∈ s, (κ x < κ y ∨ (κ x = κ y ∧ e x < e y)) →
      #{z ∈ s | κ z < κ x ∨ (κ z = κ x ∧ e z < e x)} <
        #{z ∈ s | κ z < κ y ∨ (κ z = κ y ∧ e z < e y)} := by
    intro x hx y hy hxy
    apply card_lt_card
    refine ⟨fun z hz ↦ ?_, fun hsub ↦ ?_⟩
    · simp only [mem_filter] at hz ⊢
      exact ⟨hz.1, by omega⟩
    · have := hsub (mem_filter.2 ⟨hx, hxy⟩)
      simp only [mem_filter] at this
      omega
  refine ⟨fun x ↦ #{y ∈ s | κ y < κ x ∨ (κ y = κ x ∧ e y < e x)}, ?_, ?_⟩
  · intro x hx y hy h
    by_contra hne
    rcases lt_trichotomy (κ x) (κ y) with h1 | h1 | h1
    · exact absurd h (ne_of_lt (key x hx y hy (Or.inl h1)))
    · rcases lt_trichotomy (e x) (e y) with h2 | h2 | h2
      · exact absurd h (ne_of_lt (key x hx y hy (Or.inr ⟨h1, h2⟩)))
      · exact hne (he hx hy h2)
      · exact absurd h (ne_of_gt (key y hy x hx (Or.inr ⟨h1.symm, h2⟩)))
    · exact absurd h (ne_of_gt (key y hy x hx (Or.inl h1)))
  · intro x hx
    constructor
    · exact card_le_card fun z hz ↦ by
        simp only [mem_filter] at hz ⊢
        exact ⟨hz.1, Or.inl hz.2⟩
    · apply card_lt_card
      refine ⟨fun z hz ↦ ?_, fun hsub ↦ ?_⟩
      · simp only [mem_filter] at hz ⊢
        exact ⟨hz.1, by omega⟩
      · have := hsub (mem_filter.2 ⟨hx, le_rfl⟩)
        simp only [mem_filter] at this
        omega

/-- `t ↦ t % M` is injective on intervals of length at most `M`. -/
theorem eq_of_mod_eq {M t t' : ℕ} (h1 : t ≤ t') (h2 : t' < t + M) (h : t % M = t' % M) :
    t = t' := by
  have hd : M ∣ t' - t := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h.symm)
  have : t' - t = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
  omega

/-- The same, in either order. -/
theorem eq_of_mod_eq' {M t t' : ℕ} (h1 : t' < t + M) (h2 : t < t' + M)
    (h : t % M = t' % M) : t = t' := by
  rcases le_total t t' with h3 | h3
  · exact eq_of_mod_eq h3 h1 h
  · exact (eq_of_mod_eq h3 h2 h.symm).symm

/-- Every residue appears in every interval of length `M`. -/
theorem exists_mod_eq {M : ℕ} (hM : 0 < M) (r : ℕ) {i : ℕ} (hi : i < M) :
    ∃ t, r ≤ t ∧ t < r + M ∧ t % M = i := by
  have := surjOn_of_injOn_of_card_le (s := Ico r (r + M)) (t := range M) (fun t ↦ t % M)
    (fun t _ ↦ by simpa using Nat.mod_lt t hM)
    (fun t ht t' ht' h ↦ by
      simp only [coe_Ico, Set.mem_Ico] at ht ht'
      exact eq_of_mod_eq' (by omega) (by omega) h)
    (by simp) (by simpa using hi)
  obtain ⟨t, ht, h⟩ := this
  simp only [coe_Ico, Set.mem_Ico] at ht
  exact ⟨t, ht.1, ht.2, h⟩

/-- Counting residues over all shifts of a window. -/
theorem sum_card_mod_le (M L : ℕ) {i : ℕ} :
    ∑ r ∈ range M, #{t ∈ Ico r (r + L) | t % M = i} ≤ L := by
  have h1 : ∀ r, #{t ∈ Ico r (r + L) | t % M = i} =
      ∑ j ∈ range L, if (r + j) % M = i then 1 else 0 := by
    intro r
    rw [card_filter, sum_Ico_eq_sum_range]
    simp
  simp_rw [h1]
  rw [sum_comm]
  calc ∑ j ∈ range L, ∑ r ∈ range M, (if (r + j) % M = i then 1 else 0)
      ≤ ∑ _j ∈ range L, (1 : ℕ) := sum_le_sum fun j _ ↦ by
        rw [← card_filter]
        refine card_le_one.2 fun r hr r' hr' ↦ ?_
        simp only [mem_filter, mem_range] at hr hr'
        have h : (r + j) % M = (r' + j) % M := hr.2.trans hr'.2.symm
        have := eq_of_mod_eq' (by omega) (by omega) h
        omega
    _ = L := by simp only [sum_const, card_range, smul_eq_mul, mul_one]

/-- Disjoint consecutive blocks hit a set of points at most as often as their union does. -/
theorem card_blocks_le (a : ℕ → ℕ) (ha : Monotone a) (P : ℕ → Prop) [DecidablePred P] (s : ℕ) :
    #{q ∈ range s | ({t ∈ Ico (a q) (a (q + 1)) | P t}).Nonempty} ≤
      #{t ∈ Ico (a 0) (a s) | P t} := by
  classical
  induction s with
  | zero => simp
  | succ s ih =>
    rw [range_add_one, filter_insert]
    have hU : Ico (a 0) (a (s + 1)) = Ico (a 0) (a s) ∪ Ico (a s) (a (s + 1)) :=
      (Ico_union_Ico_eq_Ico (ha (Nat.zero_le s)) (ha (Nat.le_succ s))).symm
    rw [hU, filter_union, card_union_of_disjoint (disjoint_filter_filter
      (Ico_disjoint_Ico_consecutive _ _ _))]
    split_ifs with h
    · have h2 : 0 < #{t ∈ Ico (a s) (a (s + 1)) | P t} := card_pos.2 h
      have := card_insert_le s
        (filter (fun q ↦ ({t ∈ Ico (a q) (a (q + 1)) | P t}).Nonempty) (range s))
      omega
    · omega

/-- A point of `[a 0, a s)` lies in one of the blocks `[a q, a (q + 1))`. -/
theorem exists_block (a : ℕ → ℕ) {t : ℕ} (s : ℕ) (h0 : a 0 ≤ t) (hs : t < a s) :
    ∃ q < s, a q ≤ t ∧ t < a (q + 1) := by
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases h : t < a s
    · obtain ⟨q, hq, h1, h2⟩ := ih h
      exact ⟨q, by omega, h1, h2⟩
    · exact ⟨s, by omega, by omega, hs⟩

/-- **Cutting a cyclic sequence into blocks of given weight.** Positions `t` with `Z (t % M)`
have weight `0`, the others weight `1`; no two consecutive positions have weight `0`. `cut r c`
is the end of the shortest block from `r` of weight `c`. -/
theorem exists_cut {M : ℕ} (Z : ℕ → Prop) [DecidablePred Z]
    (hZ : ∀ t, Z (t % M) → ¬ Z ((t + 1) % M)) :
    ∃ cut : ℕ → ℕ → ℕ, ∀ r c c', c ≤ c' →
      cut r 0 = r ∧ cut r c ≤ cut r c' ∧
      cut r c' - cut r c = (c' - c) + #{t ∈ Ico (cut r c) (cut r c') | Z (t % M)} ∧
      cut r c' ≤ cut r c + 2 * (c' - c) ∧
      (#{t ∈ range M | ¬ Z t} < c' → r + M ≤ cut r c') ∧
      (#{t ∈ range M | ¬ Z t} ≤ c' →
        cut r c' ≤ r + M + 2 * (c' - #{t ∈ range M | ¬ Z t})) := by
  classical
  set E := #{t ∈ range M | ¬ Z t} with hE
  set F : ℕ → ℕ := fun t ↦ #{u ∈ range t | ¬ Z (u % M)} with hF
  have hFs : ∀ t, F (t + 1) = F t + if Z (t % M) then 0 else 1 := by
    intro t
    simp only [hF, range_add_one, filter_insert]
    by_cases h : Z (t % M)
    · simp [h]
    · simp only [h, not_false_eq_true, ↓reduceIte]
      rw [card_insert_of_notMem (by simp)]
  have hF1 : ∀ t, F (t + 1) ≤ F t + 1 := fun t ↦ by rw [hFs]; split_ifs <;> omega
  have hFmono : Monotone F := monotone_nat_of_le_succ fun t ↦ by rw [hFs]; omega
  have hF2 : ∀ t c, F t + c ≤ F (t + 2 * c) := by
    intro t c
    induction c with
    | zero => simp
    | succ c ih =>
      have h1 := hFs (t + 2 * c)
      have h2 := hFs (t + 2 * c + 1)
      have h3 := hZ (t + 2 * c)
      rw [show t + 2 * (c + 1) = t + 2 * c + 1 + 1 by omega, h2, h1]
      by_cases h4 : Z ((t + 2 * c) % M)
      · have h5 := h3 h4
        simp only [h4, h5, ↓reduceIte]
        omega
      · simp only [h4, ↓reduceIte]
        split_ifs <;> omega
  have hFM : ∀ t, F (t + M) = F t + E := by
    intro t
    induction t with
    | zero =>
      simp only [zero_add, hF, hE, range_zero, filter_empty, card_empty]
      exact congrArg card (filter_congr fun u hu ↦ by rw [Nat.mod_eq_of_lt (mem_range.1 hu)])
    | succ t ih =>
      rw [show t + 1 + M = t + M + 1 by omega, hFs, hFs, ih, Nat.add_mod_right]
      omega
  have hFlen : ∀ a b, a ≤ b → F b + #{t ∈ Ico a b | Z (t % M)} = F a + (b - a) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      rw [hFs, Nat.Ico_succ_right_eq_insert_Ico hab, filter_insert]
      split_ifs with h
      · rw [card_insert_of_notMem (by simp)]
        omega
      · omega
  have hex : ∀ r c, ∃ t, F r + c ≤ F (r + t) := fun r c ↦ ⟨2 * c, hF2 r c⟩
  have hcutF : ∀ r c, F (r + Nat.find (hex r c)) = F r + c := by
    intro r c
    refine le_antisymm ?_ (Nat.find_spec (hex r c))
    rcases hk : Nat.find (hex r c) with _ | k
    · have := Nat.find_spec (hex r c)
      rw [hk] at this
      simp only [add_zero] at this ⊢
      omega
    · have h1 := Nat.find_min (hex r c) (show k < Nat.find (hex r c) by omega)
      have h2 := hF1 (r + k)
      rw [← add_assoc]
      omega
  refine ⟨fun r c ↦ r + Nat.find (hex r c), fun r c c' hcc' ↦ ?_⟩
  beta_reduce
  have hmono : Nat.find (hex r c) ≤ Nat.find (hex r c') :=
    Nat.find_mono fun t ht ↦ le_trans (by omega) ht
  have hc := hcutF r c
  have hc' := hcutF r c'
  refine ⟨?_, by omega, ?_, ?_, ?_, ?_⟩
  · simp only [add_eq_left, Nat.find_eq_zero]
    simp
  · have := hFlen (r + Nat.find (hex r c)) (r + Nat.find (hex r c')) (by omega)
    omega
  · have : Nat.find (hex r c') ≤ Nat.find (hex r c) + 2 * (c' - c) := by
      refine Nat.find_min' (hex r c') ?_
      have := hF2 (r + Nat.find (hex r c)) (c' - c)
      rw [← add_assoc]
      omega
    omega
  · intro h
    by_contra h'
    have := hFmono (show r + Nat.find (hex r c') ≤ r + M by omega)
    have := hFM r
    omega
  · intro h
    have : Nat.find (hex r c') ≤ M + 2 * (c' - E) := by
      refine Nat.find_min' (hex r c') ?_
      have := hF2 (r + M) (c' - E)
      have := hFM r
      rw [← add_assoc]
      omega
    omega

/-- The successor of a position, away from the end of the cycle. -/
theorem succ_mod_of_lt {M t : ℕ} (h : t % M + 1 < M) : (t + 1) % M = t % M + 1 := by
  have h1 := Nat.div_add_mod t M
  have : t + 1 = (t % M + 1) + M * (t / M) := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

/-- The predecessor of a position, away from the start of the cycle. -/
theorem pred_mod_of_pos {M t : ℕ} (hM : 0 < M) (h : 0 < t % M) : (t - 1) % M = t % M - 1 := by
  have h1 := Nat.div_add_mod t M
  have h2 := Nat.mod_lt t hM
  have : t - 1 = (t % M - 1) + M * (t / M) := by omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- **Blocks of a cyclic order of the left leaves.** The leaves `LF` are put in a cyclic order in
which the leaves of every hub `x ∈ HR` (each hub has at least two) are consecutive. For weights
`w q` with total more than `E` (one less than the number of positions, up to hubs), and every
offset `r`, consecutive blocks `Y r q` from `r` have: `w q` leaves more than hubs, up to one, at
most `2 w q` leaves, together cover all leaves, and each leaf is in at most
`M + 2 (∑ w - E)` blocks over all offsets `r < M`. -/
theorem exists_cycle_blocks {α β : Type*} [DecidableEq α]
    (LF : Finset α) (HR : Finset β) (rel : α → β → Prop)
    (hrel1 : ∀ u ∈ LF, ∀ x ∈ HR, ∀ x' ∈ HR, rel u x → rel u x' → x = x')
    (hrel2 : ∀ x ∈ HR, ∃ u ∈ LF, ∃ u' ∈ LF, u ≠ u' ∧ rel u x ∧ rel u' x)
    (hM : 0 < LF.card) :
    ∃ E : ℕ, LF.card ≤ E + HR.card ∧ E ≤ LF.card ∧
      ∀ (w : ℕ → ℕ) (s : ℕ), (∀ q < s, 2 * w q ≤ LF.card) → E < ∑ q ∈ range s, w q →
      ∃ Y : ℕ → ℕ → Finset α,
        (∀ r q, Y r q ⊆ LF) ∧
        (∀ r q, q < s → ∀ H : Finset β, (∀ x ∈ H, x ∈ HR ∧ ∃ u ∈ Y r q, rel u x) →
          H.card + w q ≤ (Y r q).card + 1) ∧
        (∀ r q, q < s → (Y r q).card ≤ 2 * w q) ∧
        (∀ r, ∀ u ∈ LF, ∃ q < s, u ∈ Y r q) ∧
        (∀ u ∈ LF, ∑ r ∈ range LF.card, #{q ∈ range s | u ∈ Y r q} ≤
            LF.card + 2 * (∑ q ∈ range s, w q - E)) := by
  classical
  set M := LF.card with hMdef
  set h := HR.card with hh
  obtain ⟨u₀, hu₀⟩ := card_pos.1 hM
  have : Nonempty α := ⟨u₀⟩
  -- the hubs are numbered
  obtain ⟨idx, hidx, hidx'⟩ := exists_rank HR (fun _ ↦ 0)
  have hidxlt : ∀ x ∈ HR, idx x < h := fun x hx ↦ by simpa using (hidx' x hx).2
  -- the key of a leaf is the number of its hub, or `h`
  let κ : α → ℕ := fun u ↦ if hu : ∃ x ∈ HR, rel u x then idx hu.choose else h
  have hκ1 : ∀ u ∈ LF, ∀ x ∈ HR, rel u x → κ u = idx x := by
    intro u hu x hx hux
    have hex : ∃ x ∈ HR, rel u x := ⟨x, hx, hux⟩
    simp only [κ, hex, ↓reduceDIte]
    rw [hrel1 u hu _ hex.choose_spec.1 x hx hex.choose_spec.2 hux]
  have hκ2 : ∀ u ∈ LF, κ u < h → ∃ x ∈ HR, rel u x ∧ κ u = idx x := by
    intro u hu hlt
    by_cases hex : ∃ x ∈ HR, rel u x
    · obtain ⟨x, hx, hux⟩ := hex
      exact ⟨x, hx, hux, hκ1 u hu x hx hux⟩
    · simp only [κ, hex, ↓reduceDIte] at hlt
      omega
  -- positions of the leaves, sorted by key
  obtain ⟨pos, hpos, hpos'⟩ := exists_rank LF κ
  have hposlt : ∀ u ∈ LF, pos u < M := fun u hu ↦
    (hpos' u hu).2.trans_le (card_le_card (filter_subset _ _))
  have hsurj : ∀ t < M, ∃ u ∈ LF, pos u = t := by
    intro t ht
    obtain ⟨u, hu, hut⟩ := surjOn_of_injOn_of_card_le (s := LF) (t := range M) pos
      (fun u hu ↦ by simpa using hposlt u hu) hpos (by simp [hMdef]) (by simpa using ht)
    exact ⟨u, hu, hut⟩
  choose! lf hlf using hsurj
  have hlf_pos : ∀ u ∈ LF, lf (pos u) = u := fun u hu ↦
    hpos (hlf _ (hposlt u hu)).1 hu (hlf _ (hposlt u hu)).2
  have hlfM : ∀ t, lf (t % M) ∈ LF := fun t ↦ (hlf _ (Nat.mod_lt t hM)).1
  have hmono : ∀ t t', t ≤ t' → t' < M → κ (lf t) ≤ κ (lf t') := by
    intro t t' htt' ht'
    obtain ⟨h1, h2⟩ := hlf t (by omega)
    obtain ⟨h1', h2'⟩ := hlf t' ht'
    by_contra hlt
    push Not at hlt
    have a1 := (hpos' _ h1).1
    have a2 := (hpos' _ h1').2
    have a3 : #{y ∈ LF | κ y ≤ κ (lf t')} ≤ #{y ∈ LF | κ y < κ (lf t)} :=
      card_le_card fun y hy ↦ by
        simp only [mem_filter] at hy ⊢
        exact ⟨hy.1, by omega⟩
    omega
  -- the positions of weight `0`: the first leaf of each hub
  let Z : ℕ → Prop := fun t ↦ t < M ∧ κ (lf t) < h ∧ (t = 0 ∨ κ (lf (t - 1)) ≠ κ (lf t))
  have hZ' : ∀ t, Z t → t + 1 < M ∧ ¬ Z (t + 1) := by
    rintro t ⟨htM, hκt, h0⟩
    obtain ⟨x, hx, hrx, hκx⟩ := hκ2 _ (hlf t htM).1 hκt
    obtain ⟨v, hv, hvne, hrv⟩ : ∃ v ∈ LF, v ≠ lf t ∧ rel v x := by
      obtain ⟨u, hu, u', hu', hne, hru, hru'⟩ := hrel2 x hx
      by_cases hut : u = lf t
      · exact ⟨u', hu', fun h' ↦ hne (hut.trans h'.symm), hru'⟩
      · exact ⟨u, hu, hut, hru⟩
    have hκv : κ v = κ (lf t) := by rw [hκ1 v hv x hx hrv, hκx]
    have ht'M := hposlt v hv
    have ht't : pos v ≠ t := fun h' ↦ hvne (by rw [← hlf_pos v hv, h'])
    rcases lt_or_gt_of_ne ht't with hlt | hgt
    · have hm1 := hmono (pos v) (t - 1) (by omega) (by omega)
      have hm2 := hmono (t - 1) t (by omega) htM
      rw [hlf_pos v hv, hκv] at hm1
      rcases h0 with h0 | h0
      · omega
      · exact absurd (le_antisymm hm2 hm1) h0
    · refine ⟨by omega, fun ⟨_, _, h1⟩ ↦ ?_⟩
      have hm1 := hmono t (t + 1) (by omega) (by omega)
      have hm2 := hmono (t + 1) (pos v) (by omega) ht'M
      rw [hlf_pos v hv, hκv] at hm2
      rcases h1 with h1 | h1
      · omega
      · simp only [Nat.add_sub_cancel] at h1
        exact h1 (le_antisymm hm1 hm2)
  have hZ : ∀ t, Z (t % M) → ¬ Z ((t + 1) % M) := by
    intro t hz hz'
    obtain ⟨h1, h2⟩ := hZ' _ hz
    rw [succ_mod_of_lt h1] at hz'
    exact h2 hz'
  -- at most one zero per hub
  have hZne : ∀ t t', Z t → Z t' → t < t' → κ (lf t) ≠ κ (lf t') := by
    rintro t t' ⟨-, -, -⟩ ⟨ht'M, -, h0'⟩ htt' heq
    have hm1 := hmono t (t' - 1) (by omega) (by omega)
    have hm2 := hmono (t' - 1) t' (by omega) ht'M
    rcases h0' with h0' | h0'
    · omega
    · exact h0' (le_antisymm hm2 (heq ▸ hm1))
  have hZcard : #{t ∈ range M | Z t} ≤ h := by
    have := card_le_card_of_injOn (s := {t ∈ range M | Z t}) (t := range h) (fun t ↦ κ (lf t))
      (fun t ht ↦ by
        simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ht
        simpa using ht.2.2.1)
      (fun t ht t' ht' heq ↦ by
        simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ht ht'
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hZne t t' ht.2 ht'.2 hlt heq
        · exact hZne t' t ht'.2 ht.2 hgt heq.symm)
    simpa using this
  set E := #{t ∈ range M | ¬ Z t} with hE
  have hME : #{t ∈ range M | Z t} + E = M := by
    rw [hE, card_filter_add_card_filter_not]
    simp
  -- the hubs of an interval of positions: one more than the zeros
  have hKL : ∀ a b, ∀ H : Finset β, (∀ x ∈ H, x ∈ HR ∧ ∃ t ∈ Ico a b, rel (lf (t % M)) x) →
      H.card ≤ #{t ∈ Ico a b | Z (t % M)} + 1 := by
    intro a b H hH
    let g : β → ℕ := fun x ↦
      if hx : ∃ t, t ∈ Ico a b ∧ rel (lf (t % M)) x then Nat.find hx else 0
    have hg : ∀ x ∈ H, g x ∈ Ico a b ∧ rel (lf (g x % M)) x ∧
        ∀ t ∈ Ico a b, t < g x → ¬ rel (lf (t % M)) x := by
      intro x hx
      have hx' : ∃ t, t ∈ Ico a b ∧ rel (lf (t % M)) x := by
        obtain ⟨-, t, ht, hr⟩ := hH x hx
        exact ⟨t, ht, hr⟩
      simp only [g, hx', ↓reduceDIte]
      exact ⟨(Nat.find_spec hx').1, (Nat.find_spec hx').2,
        fun t ht htlt hr ↦ Nat.find_min hx' htlt ⟨ht, hr⟩⟩
    have hginj : Set.InjOn g H := by
      intro x hx x' hx' heq
      obtain ⟨-, hr, -⟩ := hg x hx
      obtain ⟨-, hr', -⟩ := hg x' hx'
      rw [heq] at hr
      exact hrel1 _ (hlfM _) x (hH x hx).1 x' (hH x' hx').1 hr hr'
    have h0 : (H.filter fun x ↦ g x = a).card ≤ 1 := by
      refine card_le_one.2 fun x hx x' hx' ↦ ?_
      rw [mem_filter] at hx hx'
      exact hginj hx.1 hx'.1 (hx.2.trans hx'.2.symm)
    have h1 : (H.filter fun x ↦ ¬ g x = a).card ≤ #{t ∈ Ico a b | Z (t % M)} := by
      refine card_le_card_of_injOn g (fun x hx ↦ ?_)
        (hginj.mono (coe_subset.2 (filter_subset _ _)))
      simp only [coe_filter, Set.mem_ofPred_eq] at hx
      obtain ⟨hgab, hr, hmin⟩ := hg x hx.1
      have hxR := (hH x hx.1).1
      simp only [coe_filter, Set.mem_ofPred_eq]
      refine ⟨hgab, Nat.mod_lt _ hM, ?_, ?_⟩
      · rw [hκ1 _ (hlfM _) x hxR hr]
        exact hidxlt x hxR
      · by_cases h0 : g x % M = 0
        · exact Or.inl h0
        · right
          intro heq
          have hgt : a < g x := lt_of_le_of_ne (mem_Ico.1 hgab).1 (Ne.symm hx.2)
          have hlt : κ (lf (g x % M - 1)) < h := by
            rw [heq, hκ1 _ (hlfM _) x hxR hr]
            exact hidxlt x hxR
          obtain ⟨x', hx', hr', hκ'⟩ := hκ2 _ (hlf _ (by have := Nat.mod_lt (g x) hM; omega)).1
            hlt
          have : x' = x := by
            refine hidx hx' hxR ?_
            rw [← hκ', heq, hκ1 _ (hlfM _) x hxR hr]
          rw [this, ← pred_mod_of_pos hM (Nat.pos_of_ne_zero h0)] at hr'
          exact hmin (g x - 1) (mem_Ico.2 ⟨by omega, by have := (mem_Ico.1 hgab).2; omega⟩)
            (by omega) hr'
    have := card_filter_add_card_filter_not (s := H) (fun x ↦ g x = a)
    omega
  obtain ⟨cut, hcut⟩ := exists_cut Z hZ
  refine ⟨E, by omega, by omega, fun w s hw hEs ↦ ?_⟩
  set C : ℕ → ℕ := fun q ↦ ∑ q' ∈ range q, w q' with hCdef
  have hC : ∀ q, C (q + 1) = C q + w q := fun q ↦ sum_range_succ _ _
  have hCmono : Monotone C := monotone_nat_of_le_succ fun q ↦ by rw [hC]; omega
  set A : ℕ → ℕ → ℕ := fun r q ↦ cut r (C q) with hAdef
  have hAmono : ∀ r, Monotone (A r) := fun r q q' hqq' ↦
    (hcut r (C q) (C q') (hCmono hqq')).2.1
  have hA0 : ∀ r, A r 0 = r := fun r ↦ (hcut r 0 0 le_rfl).1
  have hAs : ∀ r, r + M ≤ A r s := fun r ↦ (hcut r 0 (C s) (Nat.zero_le _)).2.2.2.2.1 hEs
  have hAs' : ∀ r, A r s ≤ r + M + 2 * (C s - E) := fun r ↦
    (hcut r 0 (C s) (Nat.zero_le _)).2.2.2.2.2 hEs.le
  have hblock : ∀ r q, A r (q + 1) - A r q = w q + #{t ∈ Ico (A r q) (A r (q + 1)) | Z (t % M)}
      ∧ A r (q + 1) ≤ A r q + 2 * w q := by
    intro r q
    have h := hcut r (C q) (C (q + 1)) (hCmono (Nat.le_succ q))
    simp only [hC, Nat.add_sub_cancel_left] at h
    simp only [hAdef, hC]
    exact ⟨h.2.2.1, h.2.2.2.1⟩
  refine ⟨fun r q ↦ (Ico (A r q) (A r (q + 1))).image (fun t ↦ lf (t % M)), ?_, ?_, ?_, ?_, ?_⟩
  · intro r q u hu
    obtain ⟨t, -, rfl⟩ := mem_image.1 hu
    exact hlfM t
  · intro r q hq H hH
    obtain ⟨hlen, hup⟩ := hblock r q
    have hmono' := hAmono r (Nat.le_succ q)
    have hinj : Set.InjOn (fun t ↦ lf (t % M)) (Ico (A r q) (A r (q + 1))) := by
      intro t ht t' ht' heq
      simp only [coe_Ico, Set.mem_Ico] at ht ht'
      have h1 : pos (lf (t % M)) = pos (lf (t' % M)) := congrArg pos heq
      rw [(hlf _ (Nat.mod_lt t hM)).2, (hlf _ (Nat.mod_lt t' hM)).2] at h1
      have := hw q hq
      exact eq_of_mod_eq' (by omega) (by omega) h1
    rw [card_image_of_injOn hinj, Nat.card_Ico]
    have := hKL (A r q) (A r (q + 1)) H fun x hx ↦ by
      obtain ⟨hxR, u, hu, hr⟩ := hH x hx
      obtain ⟨t, ht, rfl⟩ := mem_image.1 hu
      exact ⟨hxR, t, ht, hr⟩
    omega
  · intro r q hq
    obtain ⟨hlen, hup⟩ := hblock r q
    refine card_image_le.trans ?_
    rw [Nat.card_Ico]
    omega
  · intro r u hu
    obtain ⟨t, ht1, ht2, htu⟩ := exists_mod_eq hM r (hposlt u hu)
    obtain ⟨q, hq, h1, h2⟩ := exists_block (A r) s (t := t) (by rw [hA0]; exact ht1)
      (by have := hAs r; omega)
    refine ⟨q, hq, mem_image.2 ⟨t, mem_Ico.2 ⟨h1, h2⟩, ?_⟩⟩
    rw [htu, hlf_pos u hu]
  · intro u hu
    have hr : ∀ r, #{q ∈ range s | u ∈ (Ico (A r q) (A r (q + 1))).image
        (fun t ↦ lf (t % M))} ≤ #{t ∈ Ico r (r + (M + 2 * (C s - E))) | t % M = pos u} := by
      intro r
      calc #{q ∈ range s | u ∈ (Ico (A r q) (A r (q + 1))).image (fun t ↦ lf (t % M))}
          ≤ #{q ∈ range s | ({t ∈ Ico (A r q) (A r (q + 1)) | t % M = pos u}).Nonempty} := by
            refine card_le_card fun q hq ↦ ?_
            simp only [mem_filter, mem_image] at hq ⊢
            obtain ⟨hq, t, ht, htu⟩ := hq
            refine ⟨hq, t, mem_filter.2 ⟨ht, ?_⟩⟩
            rw [← htu, (hlf _ (Nat.mod_lt t hM)).2]
        _ ≤ #{t ∈ Ico (A r 0) (A r s) | t % M = pos u} := card_blocks_le (A r) (hAmono r) _ s
        _ ≤ _ := by
            refine card_le_card fun t ht ↦ ?_
            simp only [mem_filter, mem_Ico] at ht ⊢
            rw [hA0] at ht
            have := hAs' r
            exact ⟨⟨ht.1.1, by omega⟩, ht.2⟩
    calc _ ≤ ∑ r ∈ range M, #{t ∈ Ico r (r + (M + 2 * (C s - E))) | t % M = pos u} :=
          sum_le_sum fun r _ ↦ hr r
      _ ≤ M + 2 * (C s - E) := sum_card_mod_le M _

/-- **Pieces**: the right leaves `RF` are cut into pieces (`φR` gives the piece of a leaf) of at
most `3 N` leaves, keeping the neighbourhood `nb u` of every small hub `u ∈ HS` in one piece
(the piece `φH u`). -/
theorem exists_pieces {α β : Type*} {N : ℕ} (hN : 0 < N) (RF : Finset β)
    (HS : Finset α) (nb : α → Finset β)
    (hdisj : ∀ u ∈ HS, ∀ u' ∈ HS, u ≠ u' → Disjoint (nb u) (nb u'))
    (hsz : ∀ u ∈ HS, (nb u).card < 2 * N) :
    ∃ φR : β → ℕ, ∃ φH : α → ℕ,
      (∀ v ∈ RF, φR v ≤ RF.card / N) ∧
      (∀ u ∈ HS, ∀ v ∈ nb u, φR v = φH u) ∧
      (∀ q, #{v ∈ RF | φR v = q} ≤ 3 * N) := by
  classical
  obtain ⟨idxS, hidxS, hidxS'⟩ := exists_rank HS (fun _ ↦ 0)
  have hidxSlt : ∀ u ∈ HS, idxS u < HS.card := fun u hu ↦ by simpa using (hidxS' u hu).2
  obtain ⟨idxR, hidxR, -⟩ := exists_rank RF (fun _ ↦ 0)
  let ρ : β → ℕ := fun v ↦
    if hv : ∃ u ∈ HS, v ∈ nb u then idxS hv.choose else HS.card + idxR v
  have hρ1 : ∀ u ∈ HS, ∀ v ∈ nb u, ρ v = idxS u := by
    intro u hu v hv
    have hex : ∃ u ∈ HS, v ∈ nb u := ⟨u, hu, hv⟩
    simp only [ρ, hex, ↓reduceDIte]
    have h1 := hex.choose_spec
    have : hex.choose = u := by
      by_contra h'
      exact disjoint_left.1 (hdisj _ h1.1 u hu h') h1.2 hv
    rw [this]
  have hρ2 : ∀ v, (¬ ∃ u ∈ HS, v ∈ nb u) → ρ v = HS.card + idxR v := by
    intro v hv
    simp only [ρ, hv, ↓reduceDIte]
  have hclass : ∀ v ∈ RF, #{v' ∈ RF | ρ v' = ρ v} < 2 * N := by
    intro v hv
    by_cases hex : ∃ u ∈ HS, v ∈ nb u
    · obtain ⟨u, hu, hvu⟩ := hex
      refine lt_of_le_of_lt (card_le_card fun v' hv' ↦ ?_) (hsz u hu)
      rw [mem_filter, hρ1 u hu v hvu] at hv'
      by_contra hv'u
      by_cases hex' : ∃ u' ∈ HS, v' ∈ nb u'
      · obtain ⟨u', hu', hv'u'⟩ := hex'
        rw [hρ1 u' hu' v' hv'u'] at hv'
        have := hidxS hu' hu hv'.2
        subst this
        exact hv'u hv'u'
      · rw [hρ2 v' hex'] at hv'
        have := hidxSlt u hu
        omega
    · have key : ∀ v' ∈ RF, ρ v' = ρ v → v' = v := by
        intro v' hv' h
        rw [hρ2 v hex] at h
        by_cases hex' : ∃ u' ∈ HS, v' ∈ nb u'
        · obtain ⟨u', hu', hv'u'⟩ := hex'
          rw [hρ1 u' hu' v' hv'u'] at h
          have := hidxSlt u' hu'
          omega
        · rw [hρ2 v' hex'] at h
          exact hidxR hv' hv (by omega)
      refine lt_of_le_of_lt (card_le_one.2 fun v₁ h₁ v₂ h₂ ↦ ?_) (by omega)
      rw [mem_filter] at h₁ h₂
      rw [key v₁ h₁.1 h₁.2, key v₂ h₂.1 h₂.2]
  obtain ⟨pos, hpos, hpos'⟩ := exists_rank RF ρ
  refine ⟨fun v ↦ #{v' ∈ RF | ρ v' < ρ v} / N, fun u ↦ #{v' ∈ RF | ρ v' < idxS u} / N,
    fun v _ ↦ Nat.div_le_div_right (card_le_card (filter_subset _ _)),
    fun u hu v hv ↦ by simp only [hρ1 u hu v hv], fun q ↦ ?_⟩
  refine (card_le_card_of_injOn pos (t := Ico (N * q) (N * q + 3 * N)) (fun v hv ↦ ?_)
    (hpos.mono (coe_subset.2 (filter_subset _ _)))).trans (by simp)
  simp only [coe_filter, Set.mem_ofPred_eq] at hv
  obtain ⟨hvR, hq⟩ := hv
  have h1 := hpos' v hvR
  have h2 : #{v' ∈ RF | ρ v' ≤ ρ v} = #{v' ∈ RF | ρ v' < ρ v} + #{v' ∈ RF | ρ v' = ρ v} := by
    rw [← card_union_of_disjoint (disjoint_filter.2 fun _ _ h1 h2 ↦ by omega), ← filter_or]
    exact congrArg card (filter_congr fun _ _ ↦ le_iff_lt_or_eq)
  have h3 := hclass v hvR
  have h4 := Nat.div_add_mod (#{v' ∈ RF | ρ v' < ρ v}) N
  have h5 := Nat.mod_lt (#{v' ∈ RF | ρ v' < ρ v}) hN
  rw [hq] at h4
  simp only [coe_Ico, Set.mem_Ico]
  generalize N * q = y at *
  omega

end BCFGJPSSV26.Stable.StarForestAux


