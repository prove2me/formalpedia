-- Prove2me | Definitions.Def_CirclePackingConstants_SixteenGlue
-- name    : CirclePackingConstants_SixteenGlue
-- status  : Definition
-- author  : @vebis
-- created : 2026-10-06T15:13:34.225187+00:00
-- url     : https://prove2.me/theorems/0d15b9f4-2114-49bb-8972-77f396041050
-- title:
--   Glue lemmas for the sixteen-point occupancy and rigidity statements
-- statement:
--   This file provides the glue between the certified box checker (`CirclePackingConstants_BoxChecker`) and the geometry of the $4\times4$ cells.
--
--   (1) *Entries and placements.* For a library entry (a list of triples $(x,y,m)$) the slot list `expandEnt` repeats each cell $m$ times; `initS` packs the boxes of the slots; `nogood_apply` shows: if a checker certificate for the slot list exists and the placed pattern is dominated by the occupation counts of sixteen labelled points with pairwise squared distances $>\tfrac19$, then we get a contradiction. The proof chooses distinct points for the slots (ordered by $x$ inside a multiply occupied cell), maps them back to the canonical position by an isometry of the plane (a symmetry of the square followed by a translation by whole cells) and applies the box checker. `nogood_batch` packages this for a batch of library entries.
--
--   (2) *Covering.* `cov3` is a depth-first search over partial assignments of the cell counts $n_i\in\{0,1,2\}$ with lower and upper bounds for the total; `cov3_sound` shows that a successful search implies that every count vector with total $16$ that is not all ones contains a placed library pattern.
--
--   (3) *Local rigidity.* `local_grid` shows: if sixteen points lie within $1/200$ of the points $(i/3,j/3)$ of the $4\times4$ grid of spacing $\tfrac13$, inside the unit square, then two of them are at squared distance at most $\tfrac19$; the proof is a second-order argument (each row and column loses at most $60\rho^2$, where $\rho$ is the maximal offset). `struct_main` combines this with the checker certificate for the quarter-cell problem.
--
--   **Formalization Note.** Definitions and proofs are in one file; only the axioms `propext`, `Classical.choice` and `Quot.sound` are used.
-- source:
--   G. Wengerodt, Die dichteste Packung von 16 Kreisen in einem Quadrat, Beitraege zur Algebra und Geometrie 16 (1983), 173-190 (optimality of the 4x4 grid); the occupancy-pattern decomposition, the pattern library and the certificates are computer generated for this formalization.

import Definitions.Def_CirclePackingConstants
import Definitions.Def_CirclePackingConstants_SixteenOcc
import Definitions.Def_CirclePackingConstants_BoxChecker

open CirclePackingConstants CirclePackingConstants.Sixteen

open CirclePackingConstants


namespace CPQ

def ordsOf (sc : List (Nat × Nat)) : List (Nat × Nat) :=
  ((List.range (sc.length - 1)).filter (fun k => decide (sc[k]? = sc[k + 1]?))).map (fun k => (k, k + 1))

theorem mem_ordsOf {sc : List (Nat × Nat)} {a b : Nat} (h : (a, b) ∈ ordsOf sc) :
    b = a + 1 ∧ a + 1 < sc.length ∧ sc[a]? = sc[a + 1]? := by
  unfold ordsOf at h
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, Prod.mk.injEq] at h
  obtain ⟨k, ⟨hk, hk2⟩, rfl, rfl⟩ := h
  exact ⟨rfl, by omega, hk2⟩

def slotField (c : Nat × Nat) (i : Nat) : Nat :=
  if i = 0 then c.1 * M / 4 else if i = 1 then (c.1 + 1) * M / 4
  else if i = 2 then c.2 * M / 4 else (c.2 + 1) * M / 4

def slotPack (c : Nat × Nat) : Nat :=
  slotField c 0 + FW * (slotField c 1 + FW * (slotField c 2 + FW * slotField c 3))

def initS : List (Nat × Nat) → Nat
  | [] => 0
  | c :: t => slotPack c + FW ^ 4 * initS t

theorem M_lt_FW : M < FW := by unfold M FW; norm_num

theorem slotField_lt (c : Nat × Nat) (h1 : c.1 ≤ 3) (h2 : c.2 ≤ 3) (i : Nat) : slotField c i < FW := by
  have hM := M_lt_FW
  have key : ∀ x : Nat, x ≤ 4 → x * M / 4 < FW := by
    intro x hx
    have : x * M ≤ 4 * M := Nat.mul_le_mul_right _ hx
    have : x * M / 4 ≤ M := by omega
    omega
  unfold slotField
  split_ifs
  · exact key _ (by omega)
  · exact key _ (by omega)
  · exact key _ (by omega)
  · exact key _ (by omega)

theorem pack4_lt (a b c d : Nat) (ha : a < FW) (hb : b < FW) (hc : c < FW) (hd : d < FW) :
    a + FW * (b + FW * (c + FW * d)) < FW ^ 4 := by
  have hFW := FW_pos
  have h1 : c + FW * d < FW * FW := by nlinarith
  have h2 : b + FW * (c + FW * d) < FW * (FW * FW) := by nlinarith
  have h3 : a + FW * (b + FW * (c + FW * d)) < FW * (FW * (FW * FW)) := by nlinarith
  calc _ < _ := h3
    _ = FW ^ 4 := by ring

theorem fld_pack4 (a b c d : Nat) (ha : a < FW) (hb : b < FW) (hc : c < FW) (hd : d < FW) :
    fld (a + FW * (b + FW * (c + FW * d))) 0 = a ∧ fld (a + FW * (b + FW * (c + FW * d))) 1 = b ∧
    fld (a + FW * (b + FW * (c + FW * d))) 2 = c ∧ fld (a + FW * (b + FW * (c + FW * d))) 3 = d := by
  have hFW := FW_pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : a + FW * (b + FW * (c + FW * d)) = 0 + FW ^ 0 * (a + FW * (b + FW * (c + FW * d))) := by ring
    rw [e, fld_decomp_val _ _ _ _ _ (by simp) ha]
    simp
  · have e : a + FW * (b + FW * (c + FW * d)) = a + FW ^ 1 * (b + FW * (c + FW * d)) := by ring
    rw [e, fld_decomp_val _ _ _ _ _ (by simpa using ha) hb]
    simp
  · have e : a + FW * (b + FW * (c + FW * d)) = (a + FW * b) + FW ^ 2 * (c + FW * d) := by ring
    have hab : a + FW * b < FW ^ 2 := by nlinarith
    rw [e, fld_decomp_val _ _ _ _ _ hab hc]
    simp
  · have e : a + FW * (b + FW * (c + FW * d)) = (a + FW * b + FW ^ 2 * c) + FW ^ 3 * (d + FW * 0) := by ring
    have habc : a + FW * b + FW ^ 2 * c < FW ^ 3 := by nlinarith
    rw [e, fld_decomp_val _ _ _ _ _ habc hd]
    simp

theorem fld_slotPack (c : Nat × Nat) (h1 : c.1 ≤ 3) (h2 : c.2 ≤ 3) (i : Nat) (hi : i < 4) :
    fld (slotPack c) i = slotField c i := by
  have l0 := slotField_lt c h1 h2 0
  have l1 := slotField_lt c h1 h2 1
  have l2 := slotField_lt c h1 h2 2
  have l3 := slotField_lt c h1 h2 3
  obtain ⟨f0, f1, f2, f3⟩ := fld_pack4 _ _ _ _ l0 l1 l2 l3
  unfold slotPack
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · exact f0
  · exact f1
  · exact f2
  · exact f3

theorem slotPack_lt (c : Nat × Nat) (h1 : c.1 ≤ 3) (h2 : c.2 ≤ 3) : slotPack c < FW ^ 4 :=
  pack4_lt _ _ _ _ (slotField_lt c h1 h2 0) (slotField_lt c h1 h2 1) (slotField_lt c h1 h2 2) (slotField_lt c h1 h2 3)

theorem fld_cons (A T j : Nat) (hA : A < FW ^ 4) :
    fld (A + FW ^ 4 * T) j = if j < 4 then fld A j else fld T (j - 4) := by
  have hFW := FW_pos
  rw [fld_eq]
  split_ifs with hj
  · obtain ⟨d, hd⟩ : ∃ d, 4 = j + d + 1 := ⟨3 - j, by omega⟩
    have e : FW ^ 4 = FW ^ j * (FW ^ d * FW) := by rw [hd, pow_succ, pow_add, mul_assoc]
    have h1 : (A + FW ^ 4 * T) / FW ^ j = A / FW ^ j + FW ^ d * FW * T := by
      rw [e, mul_assoc, Nat.add_mul_div_left _ _ (by positivity)]
    rw [h1, show FW ^ d * FW * T = FW * (FW ^ d * T) by ring, Nat.add_mul_mod_self_left, fld_eq]
  · obtain ⟨m, hm⟩ : ∃ m, j = 4 + m := ⟨j - 4, by omega⟩
    subst hm
    rw [pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by positivity),
      Nat.div_eq_of_lt hA, zero_add, fld_eq]
    simp

theorem fld_initS (sc : List (Nat × Nat)) (hsc : ∀ c ∈ sc, c.1 ≤ 3 ∧ c.2 ≤ 3) :
    ∀ (k : Nat) (hk : k < sc.length) (i : Nat), i < 4 → fld (initS sc) (4 * k + i) = slotField sc[k] i := by
  induction sc with
  | nil => intro k hk; simp at hk
  | cons c t ih =>
    intro k hk i hi
    have hc := hsc c (by simp)
    have ht : ∀ c ∈ t, c.1 ≤ 3 ∧ c.2 ≤ 3 := fun c' h => hsc c' (by simp [h])
    unfold initS
    rw [fld_cons _ _ _ (slotPack_lt c hc.1 hc.2)]
    cases k with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add]
      rw [if_pos hi, fld_slotPack c hc.1 hc.2 i hi]
      simp
    | succ k' =>
      have : ¬ (4 * (k' + 1) + i < 4) := by omega
      rw [if_neg this]
      have e : 4 * (k' + 1) + i - 4 = 4 * k' + i := by omega
      rw [e, ih ht k' (by simpa using hk) i hi]
      simp

/-- closed quarter cell Q(c) = [x/4,(x+1)/4] × [y/4,(y+1)/4] -/
def InQ (c : Nat × Nat) (a : ℝ × ℝ) : Prop :=
  (c.1 : ℝ) / 4 ≤ a.1 ∧ a.1 ≤ ((c.1 : ℝ) + 1) / 4 ∧ (c.2 : ℝ) / 4 ≤ a.2 ∧ a.2 ≤ ((c.2 : ℝ) + 1) / 4

theorem M_dvd4' : (4 : Nat) ∣ M := by unfold M; norm_num

theorem cast_quarter (x : Nat) : ((x * M / 4 : Nat) : ℝ) = (x : ℝ) * M / 4 := by
  rw [Nat.cast_div (dvd_mul_of_dvd_right M_dvd4' x) (by norm_num)]
  push_cast; ring

theorem slotField_cast (c : Nat × Nat) :
    ((slotField c 0 : Nat) : ℝ) = (c.1 : ℝ) * M / 4 ∧ ((slotField c 1 : Nat) : ℝ) = ((c.1 : ℝ) + 1) * M / 4 ∧
    ((slotField c 2 : Nat) : ℝ) = (c.2 : ℝ) * M / 4 ∧ ((slotField c 3 : Nat) : ℝ) = ((c.2 : ℝ) + 1) * M / 4 := by
  unfold slotField
  simp only [if_true, one_ne_zero, if_false, OfNat.ofNat_ne_zero, show (2 : Nat) ≠ 0 from by omega,
    show (2 : Nat) ≠ 1 from by omega, show (3 : Nat) ≠ 0 from by omega, show (3 : Nat) ≠ 1 from by omega,
    show (3 : Nat) ≠ 2 from by omega, show (1 : Nat) ≠ 0 from by omega]
  refine ⟨cast_quarter _, ?_, cast_quarter _, ?_⟩
  · rw [cast_quarter]; push_cast; ring
  · rw [cast_quarter]; push_cast; ring

theorem sat_init (sc : List (Nat × Nat)) (hsc : ∀ c ∈ sc, c.1 ≤ 3 ∧ c.2 ≤ 3) (pt : Nat → ℝ × ℝ)
    (hcell : ∀ k (h : k < sc.length), InQ sc[k] (pt k))
    (hsep : ∀ k l, k < sc.length → l < sc.length → k ≠ l → (1 : ℝ) / 9 < sqDist (pt k) (pt l))
    (hord : ∀ k, k + 1 < sc.length → sc[k]? = sc[k + 1]? → (pt k).1 ≤ (pt (k + 1)).1) :
    Sat sc.length (ordsOf sc) (initS sc) pt := by
  have hM := M_pos
  refine ⟨?_, hsep, ?_⟩
  · intro k hk
    have hq := hcell k hk
    obtain ⟨q1, q2, q3, q4⟩ := hq
    obtain ⟨s0, s1, s2, s3⟩ := slotField_cast sc[k]
    unfold InS
    have f0 := fld_initS sc hsc k hk 0 (by norm_num)
    have f1 := fld_initS sc hsc k hk 1 (by norm_num)
    have f2 := fld_initS sc hsc k hk 2 (by norm_num)
    have f3 := fld_initS sc hsc k hk 3 (by norm_num)
    simp only [Nat.add_zero] at f0
    rw [f0, f1, f2, f3, s0, s1, s2, s3]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := mul_le_mul_of_nonneg_right q1 hM.le; linarith
    · have := mul_le_mul_of_nonneg_right q2 hM.le; linarith
    · have := mul_le_mul_of_nonneg_right q3 hM.le; linarith
    · have := mul_le_mul_of_nonneg_right q4 hM.le; linarith
  · intro a b hab
    obtain ⟨hb, hlt, heq⟩ := mem_ordsOf hab
    subst hb
    exact hord a hlt heq

/-- the real affine isometry sending actual points back to canonical coordinates -/
noncomputable def tmap (s tx ty : Nat) (a : ℝ × ℝ) : ℝ × ℝ :=
  let u := a.1 - ((tx : ℝ) - 3) / 4
  let v := a.2 - ((ty : ℝ) - 3) / 4
  let pq : ℝ × ℝ := if s / 4 % 2 = 1 then (v, u) else (u, v)
  (if s % 2 = 1 then 1 / 4 - pq.1 else pq.1, if s / 2 % 2 = 1 then 1 / 4 - pq.2 else pq.2)

theorem tmap_sqDist (s tx ty : Nat) (a b : ℝ × ℝ) : sqDist (tmap s tx ty a) (tmap s tx ty b) = sqDist a b := by
  unfold tmap
  dsimp only
  split_ifs <;> simp only [sqDist] <;> ring

/-- closed cell with integer index -/
def InQI (z : Int × Int) (a : ℝ × ℝ) : Prop :=
  (z.1 : ℝ) / 4 ≤ a.1 ∧ a.1 ≤ ((z.1 : ℝ) + 1) / 4 ∧ (z.2 : ℝ) / 4 ≤ a.2 ∧ a.2 ≤ ((z.2 : ℝ) + 1) / 4

theorem tmap_cell (s tx ty : Nat) (c : Nat × Nat) (a : ℝ × ℝ) (h : InQI (place s tx ty c) a) :
    InQ c (tmap s tx ty a) := by
  unfold InQI place at h
  unfold InQ tmap
  dsimp only at h ⊢
  by_cases h1 : s % 2 = 1 <;> by_cases h2 : s / 2 % 2 = 1 <;> by_cases h3 : s / 4 % 2 = 1 <;>
    simp only [h1, h2, h3, if_true, if_false] at h ⊢ <;> push_cast at h ⊢ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem inQ_toNat (z : Int × Int) (h1 : 0 ≤ z.1) (h2 : 0 ≤ z.2) (a : ℝ × ℝ)
    (h : InQ (z.1.toNat, z.2.toNat) a) : InQI z a := by
  unfold InQ at h
  unfold InQI
  have e1 : ((z.1.toNat : Nat) : ℝ) = (z.1 : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h1]
  have e2 : ((z.2.toNat : Nat) : ℝ) = (z.2 : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h2]
  simp only [e1, e2] at h
  exact h

end CPQ


namespace CPQ

theorem assign_exists {α : Type} [DecidableEq α] (cl : Fin 16 → α) (κ : Fin 16 → ℝ) :
    ∀ (L : List α) (U : Finset (Fin 16)),
      (∀ x, L.countP (fun y => decide (y = x)) + (U.filter (fun k => cl k = x)).card ≤ (Finset.univ.filter (fun k => cl k = x)).card) →
      ∃ A : List (Fin 16), A.length = L.length ∧ A.Nodup ∧ (∀ y ∈ A, y ∉ U) ∧
        (∀ i, i < L.length → L[i]? = some (cl (A.getD i 0))) ∧
        (∀ i, i + 1 < L.length → L[i]? = L[i + 1]? → κ (A.getD i 0) ≤ κ (A.getD (i + 1) 0)) := by
  intro L
  induction L with
  | nil =>
    intro U _
    exact ⟨[], rfl, List.nodup_nil, by simp, by simp, by simp⟩
  | cons x L ih =>
    intro U hU
    -- pick the available point with label x of smallest κ
    have hx := hU x
    simp only [List.countP_cons, decide_true, if_true] at hx
    have hne : (Finset.univ.filter (fun k => cl k = x ∧ k ∉ U)).Nonempty := by
      by_contra hcon
      rw [Finset.not_nonempty_iff_eq_empty] at hcon
      have hsub : Finset.univ.filter (fun k => cl k = x) ⊆ U.filter (fun k => cl k = x) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        by_contra hk2
        have : k ∈ Finset.univ.filter (fun k => cl k = x ∧ k ∉ U) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hk, fun hh => hk2 ⟨hh, hk⟩⟩
        rw [hcon] at this; simp at this
      have := Finset.card_le_card hsub
      omega
    obtain ⟨k, hkS, hkmin⟩ := Finset.exists_min_image _ κ hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkS
    obtain ⟨hkx, hkU⟩ := hkS
    have hU' : ∀ y, L.countP (fun z => decide (z = y)) + ((insert k U).filter (fun j => cl j = y)).card ≤
        (Finset.univ.filter (fun j => cl j = y)).card := by
      intro y
      have h := hU y
      rw [Finset.filter_insert]
      by_cases hy : cl k = y
      · rw [if_pos hy, Finset.card_insert_of_notMem (by simp [hkU])]
        have hxy : x = y := by rw [← hkx, hy]
        subst hxy
        simp only [List.countP_cons, decide_true, if_true] at h
        omega
      · rw [if_neg hy]
        have hxy : ¬ (x = y) := by intro e; apply hy; rw [← e, hkx]
        have : (x :: L).countP (fun z => decide (z = y)) = L.countP (fun z => decide (z = y)) := by
          rw [List.countP_cons]; simp [hxy]
        omega
    obtain ⟨A, hlen, hnd, hU2, hlab, hord⟩ := ih (insert k U) hU'
    refine ⟨k :: A, by simp [hlen], ?_, ?_, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨?_, hnd⟩
      intro hk; exact hU2 k hk (by simp)
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hkU
      · intro h; exact hU2 y hy (Finset.mem_insert_of_mem h)
    · intro i hi
      cases i with
      | zero => simp [hkx]
      | succ j =>
        have := hlab j (by simpa using hi)
        simpa using this
    · intro i hi heq
      cases i with
      | zero =>
        -- L[0]? = x
        have hL : 0 < L.length := by simpa using hi
        have h1 : L[0]? = some x := by
          have := heq; simp at this
          exact this.symm
        have h2 := hlab 0 hL
        rw [h1] at h2
        have hA : 0 < A.length := by omega
        have hcl : cl (A.getD 0 0) = x := by
          have := Option.some.inj h2; exact this.symm
        have hmem : A.getD 0 0 ∈ A := by
          rw [List.getD_eq_getElem _ _ hA]; exact List.getElem_mem hA
        have hk'U : A.getD 0 0 ∉ U := fun h => hU2 _ hmem (Finset.mem_insert_of_mem h)
        have hh := hkmin (A.getD 0 0) (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hcl, hk'U⟩)
        simpa using hh
      | succ j =>
        have := hord j (by simpa using hi) (by simpa using heq)
        simpa using this

end CPQ



namespace CPQ

theorem place_inj (s tx ty : Nat) (c c' : Nat × Nat) (h : place s tx ty c = place s tx ty c') : c = c' := by
  unfold place at h
  dsimp only at h
  by_cases h1 : s % 2 = 1 <;> by_cases h2 : s / 2 % 2 = 1 <;> by_cases h3 : s / 4 % 2 = 1 <;>
    simp only [h1, h2, h3, if_true, if_false, Prod.mk.injEq] at h <;>
    refine Prod.ext ?_ ?_ <;> omega

/-- target label of a canonical cell -/
def tgt (s tx ty : Nat) (c : Nat × Nat) : Nat × Nat :=
  ((place s tx ty c).1.toNat, (place s tx ty c).2.toNat)

theorem inGrid_nonneg {z : Int × Int} (h : inGrid z = true) : 0 ≤ z.1 ∧ z.1 ≤ 3 ∧ 0 ≤ z.2 ∧ z.2 ≤ 3 := by
  unfold inGrid at h
  simpa using h

theorem tgt_inj (s tx ty : Nat) (c c' : Nat × Nat) (h1 : inGrid (place s tx ty c) = true)
    (h2 : inGrid (place s tx ty c') = true) (h : tgt s tx ty c = tgt s tx ty c') : c = c' := by
  have a1 := inGrid_nonneg h1
  have a2 := inGrid_nonneg h2
  unfold tgt at h
  simp only [Prod.mk.injEq] at h
  apply place_inj s tx ty
  refine Prod.ext ?_ ?_
  · omega
  · omega

theorem nogood_apply
    (sc : List (Nat × Nat)) (hsc : ∀ c ∈ sc, c.1 ≤ 3 ∧ c.2 ≤ 3)
    (hnoSat : ∀ pt : Nat → ℝ × ℝ, Sat sc.length (ordsOf sc) (initS sc) pt → False)
    (p : Fin 16 → ℝ × ℝ) (cl : Fin 16 → Nat × Nat) (hcl : ∀ k, InQ (cl k) (p k))
    (hsep : ∀ i j, i ≠ j → (1 : ℝ) / 9 < sqDist (p i) (p j))
    (s tx ty : Nat)
    (hmult : ∀ c ∈ sc, inGrid (place s tx ty c) = true ∧
      sc.count c ≤ (Finset.univ.filter (fun k : Fin 16 => cl k = ((place s tx ty c).1.toNat, (place s tx ty c).2.toNat))).card) :
    False := by
  classical
  -- counting hypothesis for the target labels
  have hcount : ∀ x, (sc.map (tgt s tx ty)).countP (fun y => decide (y = x)) +
      ((∅ : Finset (Fin 16)).filter (fun k => cl k = x)).card ≤ (Finset.univ.filter (fun k => cl k = x)).card := by
    intro x
    simp only [Finset.filter_empty, Finset.card_empty, add_zero]
    by_cases hx : ∃ c ∈ sc, tgt s tx ty c = x
    · obtain ⟨c, hc, rfl⟩ := hx
      have e : (sc.map (tgt s tx ty)).countP (fun y => decide (y = tgt s tx ty c)) = sc.count c := by
        rw [List.countP_map, List.count_eq_countP]
        apply List.countP_congr
        intro c' hc'
        simp only [Function.comp, beq_iff_eq, decide_eq_true_eq]
        constructor
        · intro h; exact tgt_inj s tx ty c' c (hmult c' hc').1 (hmult c hc).1 h
        · intro h; rw [h]
      rw [e]
      exact (hmult c hc).2
    · push Not at hx
      have : (sc.map (tgt s tx ty)).countP (fun y => decide (y = x)) = 0 := by
        rw [List.countP_eq_zero]
        intro a ha
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ha
        simpa using hx c hc
      omega
  obtain ⟨A, hlen, hnd, -, hlab, hord⟩ := assign_exists cl (fun k => (tmap s tx ty (p k)).1)
    (sc.map (tgt s tx ty)) ∅ hcount
  have hlen' : A.length = sc.length := by simpa using hlen
  -- the transported points
  let pt : Nat → ℝ × ℝ := fun i => tmap s tx ty (p (A.getD i 0))
  have hlabel : ∀ k (hk : k < sc.length), cl (A.getD k 0) = tgt s tx ty sc[k] := by
    intro k hk
    have := hlab k (by simpa using hk)
    simp only [List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, Option.some.injEq] at this
    exact this.symm
  have hSat : Sat sc.length (ordsOf sc) (initS sc) pt := by
    apply sat_init sc hsc pt
    · intro k hk
      have hl := hlabel k hk
      have hq := hcl (A.getD k 0)
      rw [hl] at hq
      have hg := inGrid_nonneg (hmult sc[k] (List.getElem_mem hk)).1
      have hI := inQ_toNat (place s tx ty sc[k]) hg.1 hg.2.2.1 _ hq
      exact tmap_cell s tx ty sc[k] _ hI
    · intro k l hk hl hkl
      have hkA : k < A.length := by omega
      have hlA : l < A.length := by omega
      have hne : A.getD k 0 ≠ A.getD l 0 := by
        rw [List.getD_eq_getElem _ _ hkA, List.getD_eq_getElem _ _ hlA]
        intro h
        exact hkl ((hnd.getElem_inj_iff).1 h)
      show (1 : ℝ) / 9 < sqDist (tmap s tx ty (p (A.getD k 0))) (tmap s tx ty (p (A.getD l 0)))
      rw [tmap_sqDist]
      exact hsep _ _ hne
    · intro k hk heq
      apply hord k (by simpa using hk)
      simp only [List.getElem?_map, heq]
  exact hnoSat _ hSat

end CPQ

namespace CPQ

def expandEnt (ent : List (Nat × Nat × Nat)) : List (Nat × Nat) :=
  ent.flatMap (fun t => List.replicate t.2.2 (t.1, t.2.1))

def entValid (ent : List (Nat × Nat × Nat)) : Bool :=
  ent.all (fun t => Nat.ble t.1 3 && Nat.ble t.2.1 3 && Nat.ble 1 t.2.2 && Nat.ble t.2.2 3) &&
    decide ((ent.map (fun t => (t.1, t.2.1))).Nodup)

theorem mem_expandEnt {ent : List (Nat × Nat × Nat)} {c : Nat × Nat} (h : c ∈ expandEnt ent) :
    ∃ t ∈ ent, c = (t.1, t.2.1) := by
  unfold expandEnt at h
  rw [List.mem_flatMap] at h
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, ht, List.eq_of_mem_replicate hc⟩

theorem count_expandEnt (ent : List (Nat × Nat × Nat)) (hnd : (ent.map (fun t => (t.1, t.2.1))).Nodup)
    (t : Nat × Nat × Nat) (ht : t ∈ ent) : (expandEnt ent).count (t.1, t.2.1) = t.2.2 := by
  induction ent with
  | nil => simp at ht
  | cons u rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    unfold expandEnt at *
    simp only [List.flatMap_cons, List.count_append, List.count_replicate]
    rcases List.mem_cons.1 ht with h | h
    · subst h
      have : (rest.flatMap (fun t => List.replicate t.2.2 (t.1, t.2.1))).count (t.1, t.2.1) = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro hm
        rw [List.mem_flatMap] at hm
        obtain ⟨w, hw, hwc⟩ := hm
        have := List.eq_of_mem_replicate hwc
        exact hnd.1 (List.mem_map.2 ⟨w, hw, this.symm⟩)
      rw [this]; simp
    · have hne : (u.1, u.2.1) ≠ (t.1, t.2.1) := by
        intro heq
        exact hnd.1 (List.mem_map.2 ⟨t, h, heq.symm⟩)
      have := ih hnd.2 h
      have hb : ((u.1, u.2.1) == (t.1, t.2.1)) = false := beq_eq_false_iff_ne.2 hne
      rw [hb]
      simpa using this

def unpack20 (g : Nat) : List Nat :=
  [g % 4096, g / 2 ^ 12 % 4096, g / 2 ^ 24 % 4096, g / 2 ^ 36 % 4096, g / 2 ^ 48 % 4096, g / 2 ^ 60 % 4096,
   g / 2 ^ 72 % 4096, g / 2 ^ 84 % 4096, g / 2 ^ 96 % 4096, g / 2 ^ 108 % 4096, g / 2 ^ 120 % 4096, g / 2 ^ 132 % 4096,
   g / 2 ^ 144 % 4096, g / 2 ^ 156 % 4096, g / 2 ^ 168 % 4096, g / 2 ^ 180 % 4096, g / 2 ^ 192 % 4096, g / 2 ^ 204 % 4096,
   g / 2 ^ 216 % 4096, g / 2 ^ 228 % 4096]

def unpackAll20 : List Nat → List Nat
  | [] => []
  | g :: t => unpack20 g ++ unpackAll20 t

def streamOK (sc : List (Nat × Nat)) (st : List Nat) : Bool :=
  (checkS (fun _ => false) sc.length (ordsOf sc) 1000 (unpackAll20 st) (initS sc)).isSome

theorem streamOK_sound (sc : List (Nat × Nat)) (st : List Nat) (h : streamOK sc st = true) :
    ∀ pt : Nat → ℝ × ℝ, Sat sc.length (ordsOf sc) (initS sc) pt → False := by
  intro pt hs
  unfold streamOK at h
  rcases hr : checkS (fun _ => false) sc.length (ordsOf sc) 1000 (unpackAll20 st) (initS sc) with _ | rest
  · rw [hr] at h; simp at h
  · exact checkS_sound (pt := pt) (fun _ => false) (fun S h => by simp at h) 1000 _ _ rest hr hs

theorem nogood_entry (st : List Nat) (ent : List (Nat × Nat × Nat)) (hv : entValid ent = true)
    (hchk : streamOK (expandEnt ent) st = true)
    (p : Fin 16 → ℝ × ℝ) (cl : Fin 16 → Nat × Nat) (hcl : ∀ k, InQ (cl k) (p k))
    (hsep : ∀ i j, i ≠ j → (1 : ℝ) / 9 < sqDist (p i) (p j)) (s tx ty : Nat)
    (hm : ∀ t ∈ ent, inGrid (place s tx ty (t.1, t.2.1)) = true ∧
      t.2.2 ≤ (Finset.univ.filter (fun k : Fin 16 => cl k = ((place s tx ty (t.1, t.2.1)).1.toNat,
        (place s tx ty (t.1, t.2.1)).2.toNat))).card) : False := by
  unfold entValid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hv1, hnd⟩ := hv
  have hsc : ∀ c ∈ expandEnt ent, c.1 ≤ 3 ∧ c.2 ≤ 3 := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := mem_expandEnt hc
    have := List.all_eq_true.1 hv1 t ht
    simp only [Bool.and_eq_true, Nat.ble_eq] at this
    exact ⟨this.1.1.1, this.1.1.2⟩
  refine nogood_apply (expandEnt ent) hsc (streamOK_sound _ st hchk) p cl hcl hsep s tx ty ?_
  intro c hc
  obtain ⟨t, ht, rfl⟩ := mem_expandEnt hc
  obtain ⟨h1, h2⟩ := hm t ht
  refine ⟨h1, ?_⟩
  rw [count_expandEnt ent hnd t ht]
  exact h2

def libCheckAt (lo : Nat) (streams : List (List Nat)) (e : Nat) : Bool :=
  match sixteenLib[e]?, streams[e - lo]? with
  | some ent, some st => entValid ent && streamOK (expandEnt ent) st
  | _, _ => false

def libBatchOK (lo cnt : Nat) (streams : List (List Nat)) : Bool := (List.range' lo cnt).all (libCheckAt lo streams)

theorem nogood_batch (lo cnt : Nat) (streams : List (List Nat)) (hall : libBatchOK lo cnt streams = true)
    (e : Nat) (he1 : lo ≤ e) (he2 : e < lo + cnt) (ent : List (Nat × Nat × Nat)) (hent : sixteenLib[e]? = some ent)
    (p : Fin 16 → ℝ × ℝ) (cl : Fin 16 → Nat × Nat) (hcl : ∀ k, InQ (cl k) (p k))
    (hsep : ∀ i j, i ≠ j → (1 : ℝ) / 9 < sqDist (p i) (p j)) (s tx ty : Nat)
    (hm : ∀ t ∈ ent, inGrid (place s tx ty (t.1, t.2.1)) = true ∧
      t.2.2 ≤ (Finset.univ.filter (fun k : Fin 16 => cl k = ((place s tx ty (t.1, t.2.1)).1.toNat,
        (place s tx ty (t.1, t.2.1)).2.toNat))).card) : False := by
  have h1 := List.all_eq_true.1 hall e (List.mem_range'_1.2 ⟨he1, he2⟩)
  unfold libCheckAt at h1
  rw [hent] at h1
  rcases htr : streams[e - lo]? with _ | st
  · rw [htr] at h1; simp at h1
  · rw [htr] at h1
    simp only [Bool.and_eq_true] at h1
    exact nogood_entry st ent h1.1 h1.2 p cl hcl hsep s tx ty hm

end CPQ

namespace CPQ

structure PL where
  cells : List (Nat × Nat)
  e : Nat
  s : Nat
  tx : Nat
  ty : Nat

/-- placed cell list (index, multiplicity) of library entry `e` under placement (s,tx,ty); empty if not entirely inside the grid -/
def placedCells (lib : Lib) (e s tx ty : Nat) : List (Nat × Nat) :=
  match lib[e]? with
  | none => []
  | some ent =>
    bif ent.all (fun t => inGrid (place s tx ty (t.1, t.2.1))) then
      ent.map (fun t => (cellIdx (place s tx ty (t.1, t.2.1)), t.2.2))
    else []

def plOK (lib : Lib) (p : PL) : Bool := decide (p.cells = placedCells lib p.e p.s p.tx p.ty)

def tabOK (lib : Lib) (tab : List (List PL)) : Bool := tab.all fun c => c.all fun p => plOK lib p

def tabGet (tab : List (List PL)) (j : Nat) : Option PL :=
  match tab[j / 80]? with
  | none => none
  | some c => (c.drop (j % 80)).head?


theorem placedCells_sound (lib : Lib) (e s tx ty : Nat) (n : Nat → Nat)
    (hne : placedCells lib e s tx ty ≠ [])
    (hm : ∀ c ∈ placedCells lib e s tx ty, c.2 ≤ n c.1) : Matches lib n e s tx ty := by
  unfold placedCells at hne hm
  rcases hl : lib[e]? with _ | ent
  · rw [hl] at hne; simp at hne
  · rw [hl] at hne hm
    dsimp only at hne hm
    by_cases hg : (ent.all (fun t => inGrid (place s tx ty (t.1, t.2.1)))) = true
    · rw [hg] at hm
      simp only [cond_true] at hm
      refine ⟨ent, hl, ?_⟩
      intro t ht
      refine ⟨List.all_eq_true.1 hg t ht, ?_⟩
      exact hm _ (List.mem_map.2 ⟨t, ht, rfl⟩)
    · rw [Bool.eq_false_iff.2 hg] at hne
      simp at hne


theorem tabGet_ok (lib : Lib) (tab : List (List PL)) (h : tabOK lib tab = true) (j : Nat) (p : PL)
    (hp : tabGet tab j = some p) : p.cells = placedCells lib p.e p.s p.tx p.ty := by
  unfold tabGet at hp
  rcases hc : tab[j / 80]? with _ | c
  · rw [hc] at hp; simp at hp
  · rw [hc] at hp
    simp only at hp
    have hmem : c ∈ tab := List.mem_of_getElem? hc
    have h1 := List.all_eq_true.1 h c hmem
    have hpm : p ∈ c := List.mem_of_mem_drop (List.mem_of_mem_head? (Option.mem_def.2 hp))
    have h2 := List.all_eq_true.1 h1 p hpm
    unfold plOK at h2
    simpa using h2


end CPQ

namespace CPQ

def cellsMatch3 (asg : List Nat) (cells : List (Nat × Nat)) : Bool :=
  cells.all fun c => Nat.ble (c.1 + 1) 16 && Nat.ble c.2 (asg.getD c.1 3) && Nat.ble (asg.getD c.1 3) 2

/-- dynamic-order covering checker. Partial assignment `asg` (3 = unassigned), lo/hi = lower/upper bound of the total.
    tokens: t ≤ 15: branch on cell t; 16: all assigned and all ones; 17 + j: prune with table entry j. -/
def cov3 (tab : List (List PL)) : Nat → List Nat → List Nat → Nat → Nat → Option (List Nat)
  | 0, _, _, _, _ => none
  | f+1, [], _, _, _ => none
  | f+1, t :: rest, asg, lo, hi =>
    bif Nat.ble t 15 then
      bif Nat.beq (asg.getD t 3) 3 then
        match (bif Nat.ble (lo + 0) 16 && Nat.ble 18 (hi + 0) then
            cov3 tab f rest (asg.set t 0) (lo + 0) (hi + 0 - 2) else some rest) with
        | none => none
        | some r1 =>
          match (bif Nat.ble (lo + 1) 16 && Nat.ble 18 (hi + 1) then
              cov3 tab f r1 (asg.set t 1) (lo + 1) (hi + 1 - 2) else some r1) with
          | none => none
          | some r2 =>
            bif Nat.ble (lo + 2) 16 && Nat.ble 18 (hi + 2) then
              cov3 tab f r2 (asg.set t 2) (lo + 2) (hi + 2 - 2) else some r2
      else none
    else bif Nat.beq t 16 then
      bif decide (asg = List.replicate 16 1) then some rest else none
    else
      match tabGet tab (t - 17) with
      | none => none
      | some p => bif (!p.cells.isEmpty) && cellsMatch3 asg p.cells then some rest else none

end CPQ

namespace CPQ

theorem getD_set' (l : List Nat) (c d v dflt : Nat) (hc : c < l.length) :
    (l.set c v).getD d dflt = if d = c then v else l.getD d dflt := by
  induction l generalizing c d with
  | nil => simp at hc
  | cons a t ih =>
    cases c with
    | zero =>
      cases d with
      | zero => simp
      | succ d => simp
    | succ c =>
      cases d with
      | zero => simp
      | succ d =>
        simp only [List.set_cons_succ, List.getD_cons_succ]
        rw [ih c d (by simpa using hc)]
        simp

def lowF (asg : List Nat) (c : Nat) : Nat := if asg.getD c 3 ≤ 2 then asg.getD c 3 else 0
def upF (asg : List Nat) (c : Nat) : Nat := if asg.getD c 3 ≤ 2 then asg.getD c 3 else 2

def Inv3 (n : Nat → Nat) (asg : List Nat) (lo hi : Nat) : Prop :=
  asg.length = 16 ∧ (∀ c < 16, asg.getD c 3 ≤ 2 → n c = asg.getD c 3) ∧
  lo = ∑ c ∈ Finset.range 16, lowF asg c ∧ hi = ∑ c ∈ Finset.range 16, upF asg c

theorem inv3_bounds (n : Nat → Nat) (asg : List Nat) (lo hi : Nat) (h : Inv3 n asg lo hi)
    (hn2 : ∀ i, n i ≤ 2) : lo ≤ ∑ c ∈ Finset.range 16, n c ∧ ∑ c ∈ Finset.range 16, n c ≤ hi := by
  obtain ⟨_, hag, hlo, hhi⟩ := h
  constructor
  · rw [hlo]
    apply Finset.sum_le_sum
    intro c hc
    have hc16 := Finset.mem_range.1 hc
    unfold lowF
    split_ifs with h1
    · rw [hag c hc16 h1]
    · exact Nat.zero_le _
  · rw [hhi]
    apply Finset.sum_le_sum
    intro c hc
    have hc16 := Finset.mem_range.1 hc
    unfold upF
    split_ifs with h1
    · rw [hag c hc16 h1]
    · exact hn2 c

theorem inv3_set (n : Nat → Nat) (asg : List Nat) (lo hi t v : Nat) (h : Inv3 n asg lo hi)
    (ht : t < 16) (hu : asg.getD t 3 = 3) (hv : v ≤ 2) (hnt : n t = v) :
    Inv3 n (asg.set t v) (lo + v) (hi + v - 2) := by
  obtain ⟨hlen, hag, hlo, hhi⟩ := h
  have hgd : ∀ d, (asg.set t v).getD d 3 = if d = t then v else asg.getD d 3 :=
    fun d => getD_set' asg t d v 3 (by omega)
  have htmem : t ∈ Finset.range 16 := Finset.mem_range.2 ht
  refine ⟨by simpa using hlen, ?_, ?_, ?_⟩
  · intro c hc hle
    rw [hgd c] at hle ⊢
    by_cases hct : c = t
    · subst hct; simp; exact hnt
    · simp only [hct, if_false] at hle ⊢
      exact hag c hc hle
  · rw [hlo, ← Finset.add_sum_erase _ _ htmem, ← Finset.add_sum_erase _ _ htmem]
    have e1 : lowF (asg.set t v) t = v := by unfold lowF; rw [hgd t]; simp [hv]
    have e2 : lowF asg t = 0 := by unfold lowF; rw [hu]; simp
    have e3 : ∑ c ∈ (Finset.range 16).erase t, lowF (asg.set t v) c = ∑ c ∈ (Finset.range 16).erase t, lowF asg c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hct : c ≠ t := (Finset.mem_erase.1 hc).1
      unfold lowF; rw [hgd c]; simp [hct]
    rw [e1, e2, e3]; ring
  · rw [hhi, ← Finset.add_sum_erase _ _ htmem, ← Finset.add_sum_erase _ _ htmem]
    have e1 : upF (asg.set t v) t = v := by unfold upF; rw [hgd t]; simp [hv]
    have e2 : upF asg t = 2 := by unfold upF; rw [hu]; simp
    have e3 : ∑ c ∈ (Finset.range 16).erase t, upF (asg.set t v) c = ∑ c ∈ (Finset.range 16).erase t, upF asg c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hct : c ≠ t := (Finset.mem_erase.1 hc).1
      unfold upF; rw [hgd c]; simp [hct]
    rw [e1, e2, e3]; omega

end CPQ

namespace CPQ

theorem cellsMatch3_sound (asg : List Nat) (cells : List (Nat × Nat)) (h : cellsMatch3 asg cells = true)
    (n : Nat → Nat) (hag : ∀ c < 16, asg.getD c 3 ≤ 2 → n c = asg.getD c 3) :
    ∀ c ∈ cells, c.2 ≤ n c.1 := by
  intro c hc
  have := List.all_eq_true.1 h c hc
  simp only [Bool.and_eq_true, Nat.ble_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  rw [hag c.1 (by omega) h3]; exact h2

theorem cov3_sound (lib : Lib) (tab : List (List PL)) (htab : tabOK lib tab = true) :
    ∀ (f : Nat) (toks : List Nat) (asg : List Nat) (lo hi : Nat) (rest : List Nat),
      cov3 tab f toks asg lo hi = some rest →
      ∀ n : Nat → Nat, Inv3 n asg lo hi → (∀ i, n i ≤ 2) →
        (∑ i ∈ Finset.range 16, n i = 16) → (∃ i < 16, n i ≠ 1) →
        ∃ e s tx ty, Matches lib n e s tx ty := by
  intro f
  induction f with
  | zero => intro toks asg lo hi rest h; simp [cov3] at h
  | succ f ih =>
    intro toks asg lo hi rest h n hinv hn2 hs16 hne
    cases toks with
    | nil => simp [cov3] at h
    | cons t ts =>
      unfold cov3 at h
      by_cases h0 : Nat.ble t 15 = true
      · rw [h0] at h
        simp only [cond_true] at h
        have ht15 : t ≤ 15 := Nat.le_of_ble_eq_true h0
        by_cases hu : Nat.beq (asg.getD t 3) 3 = true
        · rw [hu] at h
          simp only [cond_true] at h
          have hu' : asg.getD t 3 = 3 := Nat.eq_of_beq_eq_true hu
          have hfe : ∀ v, v ≤ 2 → n t = v → (lo + v ≤ 16 ∧ 18 ≤ hi + v) := by
            intro v hv hnt
            have hi3 := inv3_set n asg lo hi t v hinv (by omega) hu' hv hnt
            have hb := inv3_bounds n _ _ _ hi3 hn2
            have hhi2 : 2 ≤ hi := by
              obtain ⟨_, _, _, hhi⟩ := hinv
              rw [hhi, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by omega : t < 16))]
              have : upF asg t = 2 := by unfold upF; rw [hu']; simp
              omega
            omega
          rcases hA : (bif Nat.ble (lo + 0) 16 && Nat.ble 18 (hi + 0) then
              cov3 tab f ts (asg.set t 0) (lo + 0) (hi + 0 - 2) else some ts) with _ | r1
          · rw [hA] at h; simp at h
          rw [hA] at h
          simp only at h
          rcases hB : (bif Nat.ble (lo + 1) 16 && Nat.ble 18 (hi + 1) then
              cov3 tab f r1 (asg.set t 1) (lo + 1) (hi + 1 - 2) else some r1) with _ | r2
          · rw [hB] at h; simp at h
          rw [hB] at h
          simp only at h
          rcases (by have := hn2 t; omega : n t = 0 ∨ n t = 1 ∨ n t = 2) with hv | hv | hv
          · have hf := hfe 0 (by omega) hv
            have hc : (Nat.ble (lo + 0) 16 && Nat.ble 18 (hi + 0)) = true := by
              simp only [Bool.and_eq_true, Nat.ble_eq]; exact hf
            rw [hc] at hA
            simp only [cond_true] at hA
            exact ih ts _ _ _ r1 hA n (inv3_set n asg lo hi t 0 hinv (by omega) hu' (by omega) hv) hn2 hs16 hne
          · have hf := hfe 1 (by omega) hv
            have hc : (Nat.ble (lo + 1) 16 && Nat.ble 18 (hi + 1)) = true := by
              simp only [Bool.and_eq_true, Nat.ble_eq]; exact hf
            rw [hc] at hB
            simp only [cond_true] at hB
            exact ih r1 _ _ _ r2 hB n (inv3_set n asg lo hi t 1 hinv (by omega) hu' (by omega) hv) hn2 hs16 hne
          · have hf := hfe 2 (by omega) hv
            have hc : (Nat.ble (lo + 2) 16 && Nat.ble 18 (hi + 2)) = true := by
              simp only [Bool.and_eq_true, Nat.ble_eq]; exact hf
            rw [hc] at h
            simp only [cond_true] at h
            exact ih r2 _ _ _ rest h n (inv3_set n asg lo hi t 2 hinv (by omega) hu' (by omega) hv) hn2 hs16 hne
        · rw [Bool.eq_false_iff.2 hu] at h; simp at h
      · have h0' : Nat.ble t 15 = false := Bool.eq_false_iff.2 h0
        rw [h0'] at h
        simp only [cond_false] at h
        by_cases h16 : Nat.beq t 16 = true
        · rw [h16] at h
          simp only [cond_true] at h
          by_cases hc : decide (asg = List.replicate 16 1) = true
          · exfalso
            have heq : asg = List.replicate 16 1 := of_decide_eq_true hc
            obtain ⟨_, hag, _, _⟩ := hinv
            obtain ⟨i, hi16, hi1⟩ := hne
            apply hi1
            have hge : asg.getD i 3 = 1 := by
              rw [heq, List.getD_eq_getElem?_getD, List.getElem?_replicate]; simp [hi16]
            rw [hag i hi16 (by omega), hge]
          · rw [Bool.eq_false_iff.2 hc] at h; simp at h
        · have h16' : Nat.beq t 16 = false := Bool.eq_false_iff.2 h16
          rw [h16'] at h
          simp only [cond_false] at h
          rcases hg : tabGet tab (t - 17) with _ | p
          · rw [hg] at h; simp at h
          · rw [hg] at h
            simp only at h
            by_cases hc : ((!p.cells.isEmpty) && cellsMatch3 asg p.cells) = true
            · simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
              obtain ⟨hne', hm⟩ := hc
              have hcells := tabGet_ok lib tab htab _ p hg
              have hne2 : placedCells lib p.e p.s p.tx p.ty ≠ [] := by
                rw [← hcells]
                intro hh; rw [hh] at hne'; simp at hne'
              refine ⟨p.e, p.s, p.tx, p.ty, placedCells_sound lib _ _ _ _ n hne2 ?_⟩
              rw [← hcells]
              exact cellsMatch3_sound asg p.cells hm n hinv.2.1
            · rw [Bool.eq_false_iff.2 hc] at h; simp at h

end CPQ

namespace CPQ

def unpack18 (g : Nat) : List Nat :=
  [g % 4096, g / 4096 % 4096, g / 2 ^ 24 % 4096, g / 2 ^ 36 % 4096, g / 2 ^ 48 % 4096, g / 2 ^ 60 % 4096,
   g / 2 ^ 72 % 4096, g / 2 ^ 84 % 4096, g / 2 ^ 96 % 4096, g / 2 ^ 108 % 4096, g / 2 ^ 120 % 4096, g / 2 ^ 132 % 4096,
   g / 2 ^ 144 % 4096, g / 2 ^ 156 % 4096, g / 2 ^ 168 % 4096, g / 2 ^ 180 % 4096, g / 2 ^ 192 % 4096, g / 2 ^ 204 % 4096]

def unpackAll18 : List Nat → List Nat
  | [] => []
  | g :: t => unpack18 g ++ unpackAll18 t

theorem inv3_init (n : Nat → Nat) (a b : Nat) (h0 : n 0 = a) (h1 : n 1 = b) (ha : a ≤ 2) (hb : b ≤ 2) :
    Inv3 n [a, b, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] (a + b) (a + b + 28) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro c hc hle
    interval_cases c <;> simp_all [List.getD]
  · simp [Finset.sum_range_succ, lowF, List.getD, ha, hb]
  · simp [Finset.sum_range_succ, upF, List.getD, ha, hb]

/-- piece check: starting from the preassigned cells 0 and 1 -/
def pieceOK (tab : List (List PL)) (toks : List Nat) (a b : Nat) : Bool :=
  (cov3 tab 400000 (unpackAll18 toks) [a, b, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] (a + b) (a + b + 28)).isSome

theorem piece_sound (lib : Lib) (tab : List (List PL)) (htab : tabOK lib tab = true) (toks : List Nat) (a b : Nat)
    (hp : pieceOK tab toks a b = true) (ha : a ≤ 2) (hb : b ≤ 2)
    (n : Nat → Nat) (hn : ∀ i, n i ≤ 2) (hsum : ∑ i ∈ Finset.range 16, n i = 16) (hne : ∃ i < 16, n i ≠ 1)
    (h0 : n 0 = a) (h1 : n 1 = b) : ∃ e s tx ty, Matches lib n e s tx ty := by
  unfold pieceOK at hp
  rcases hr : cov3 tab 400000 (unpackAll18 toks) [a, b, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3] (a + b) (a + b + 28) with _ | rest
  · rw [hr] at hp; simp at hp
  · exact cov3_sound lib tab htab _ _ _ _ _ rest hr n (inv3_init n a b h0 h1 ha hb) hn hsum hne

end CPQ

namespace CPQ

theorem key_edge (r u w : ℝ) (hu : |u| ≤ 2 * r) (hw : |w| ≤ 2 * r)
    (hs : (1 : ℝ) / 9 < (1 / 3 + u) ^ 2 + w ^ 2) : -(12 * r ^ 2) < u := by
  have hu' := abs_le.1 hu
  have hw' := abs_le.1 hw
  have h1 : u ^ 2 ≤ 4 * r ^ 2 := by nlinarith [hu'.1, hu'.2]
  have h2 : w ^ 2 ≤ 4 * r ^ 2 := by nlinarith [hw'.1, hw'.2]
  have e : (1 / 3 + u) ^ 2 = 1 / 9 + 2 / 3 * u + u ^ 2 := by ring
  linarith

theorem line_lemma (f0 f1 f2 f3 g0 g1 g2 g3 r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 200)
    (hf0 : |f0| ≤ r) (hf1 : |f1| ≤ r) (hf2 : |f2| ≤ r) (hf3 : |f3| ≤ r)
    (hg0 : |g0| ≤ r) (hg1 : |g1| ≤ r) (hg2 : |g2| ≤ r) (hg3 : |g3| ≤ r)
    (hlo : 0 ≤ f0) (hhi : f3 ≤ 0)
    (s0 : (1 : ℝ) / 9 < (1 / 3 + (f1 - f0)) ^ 2 + (g1 - g0) ^ 2)
    (s1 : (1 : ℝ) / 9 < (1 / 3 + (f2 - f1)) ^ 2 + (g2 - g1) ^ 2)
    (s2 : (1 : ℝ) / 9 < (1 / 3 + (f3 - f2)) ^ 2 + (g3 - g2) ^ 2) :
    |f0| ≤ 60 * r ^ 2 ∧ |f1| ≤ 60 * r ^ 2 ∧ |f2| ≤ 60 * r ^ 2 ∧ |f3| ≤ 60 * r ^ 2 := by
  have a0 := abs_le.1 hf0
  have a1 := abs_le.1 hf1
  have a2 := abs_le.1 hf2
  have a3 := abs_le.1 hf3
  have b0 := abs_le.1 hg0
  have b1 := abs_le.1 hg1
  have b2 := abs_le.1 hg2
  have b3 := abs_le.1 hg3
  have u0 := key_edge r (f1 - f0) (g1 - g0) (by rw [abs_le]; constructor <;> linarith [a0.1, a0.2, a1.1, a1.2]) (by rw [abs_le]; constructor <;> linarith [b0.1, b0.2, b1.1, b1.2]) s0
  have u1 := key_edge r (f2 - f1) (g2 - g1) (by rw [abs_le]; constructor <;> linarith [a2.1, a2.2, a1.1, a1.2]) (by rw [abs_le]; constructor <;> linarith [b2.1, b2.2, b1.1, b1.2]) s1
  have u2 := key_edge r (f3 - f2) (g3 - g2) (by rw [abs_le]; constructor <;> linarith [a2.1, a2.2, a3.1, a3.2]) (by rw [abs_le]; constructor <;> linarith [b2.1, b2.2, b3.1, b3.2]) s2
  clear s0 s1 s2 hf0 hf1 hf2 hf3 hg0 hg1 hg2 hg3
  generalize r ^ 2 = t at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

theorem contract_le (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 200) : 60 * r ^ 2 ≤ 3 / 10 * r := by
  nlinarith

end CPQ

namespace CPQ

noncomputable def gx (i : Fin 4) : ℝ := (i.val : ℝ) / 3

def Pr (p : Fin 4 → Fin 4 → ℝ × ℝ) (r : ℝ) : Prop :=
  ∀ i j, |(p i j).1 - gx i| ≤ r ∧ |(p i j).2 - gx j| ≤ r

theorem edge_x (p : Fin 4 → Fin 4 → ℝ × ℝ)
    (hsep : ∀ i j k l, (i, j) ≠ (k, l) → (1 : ℝ) / 9 < sqDist (p i j) (p k l))
    (i i' j : Fin 4) (hi : i'.val = i.val + 1) :
    (1 : ℝ) / 9 < (1 / 3 + (((p i' j).1 - gx i') - ((p i j).1 - gx i))) ^ 2 +
      (((p i' j).2 - gx j) - ((p i j).2 - gx j)) ^ 2 := by
  have hne : (i, j) ≠ (i', j) := by
    intro h; have := congrArg (fun x => x.1.val) h; simp at this; omega
  have h := hsep i j i' j hne
  have hg : gx i' = gx i + 1 / 3 := by unfold gx; rw [hi]; push_cast; ring
  unfold sqDist at h
  have key : (1 / 3 + (((p i' j).1 - gx i') - ((p i j).1 - gx i))) ^ 2 +
      (((p i' j).2 - gx j) - ((p i j).2 - gx j)) ^ 2 =
      ((p i j).1 - (p i' j).1) ^ 2 + ((p i j).2 - (p i' j).2) ^ 2 := by rw [hg]; ring
  rw [key]; exact h

theorem edge_y (p : Fin 4 → Fin 4 → ℝ × ℝ)
    (hsep : ∀ i j k l, (i, j) ≠ (k, l) → (1 : ℝ) / 9 < sqDist (p i j) (p k l))
    (i j j' : Fin 4) (hj : j'.val = j.val + 1) :
    (1 : ℝ) / 9 < (1 / 3 + (((p i j').2 - gx j') - ((p i j).2 - gx j))) ^ 2 +
      (((p i j').1 - gx i) - ((p i j).1 - gx i)) ^ 2 := by
  have hne : (i, j) ≠ (i, j') := by
    intro h; have := congrArg (fun x => x.2.val) h; simp at this; omega
  have h := hsep i j i j' hne
  have hg : gx j' = gx j + 1 / 3 := by unfold gx; rw [hj]; push_cast; ring
  unfold sqDist at h
  have key : (1 / 3 + (((p i j').2 - gx j') - ((p i j).2 - gx j))) ^ 2 +
      (((p i j').1 - gx i) - ((p i j).1 - gx i)) ^ 2 =
      ((p i j).2 - (p i j').2) ^ 2 + ((p i j).1 - (p i j').1) ^ 2 := by rw [hg]; ring
  rw [key]; linarith [h]

end CPQ

namespace CPQ

theorem gx0 : gx 0 = 0 := by unfold gx; norm_num
theorem gx3 : gx 3 = 1 := by unfold gx; norm_num

theorem step_Pr (p : Fin 4 → Fin 4 → ℝ × ℝ)
    (hlo : ∀ j, 0 ≤ (p 0 j).1) (hhi : ∀ j, (p 3 j).1 ≤ 1)
    (hlo' : ∀ i, 0 ≤ (p i 0).2) (hhi' : ∀ i, (p i 3).2 ≤ 1)
    (hsep : ∀ i j k l, (i, j) ≠ (k, l) → (1 : ℝ) / 9 < sqDist (p i j) (p k l))
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 200) (h : Pr p r) : Pr p (3 / 10 * r) := by
  have hc := contract_le r hr0 hr
  have hrow : ∀ j, |(p 0 j).1 - gx 0| ≤ 60 * r ^ 2 ∧ |(p 1 j).1 - gx 1| ≤ 60 * r ^ 2 ∧
      |(p 2 j).1 - gx 2| ≤ 60 * r ^ 2 ∧ |(p 3 j).1 - gx 3| ≤ 60 * r ^ 2 := by
    intro j
    exact line_lemma _ _ _ _ (((p 0 j).2 - gx j)) (((p 1 j).2 - gx j)) (((p 2 j).2 - gx j)) (((p 3 j).2 - gx j)) r hr0 hr
      (h 0 j).1 (h 1 j).1 (h 2 j).1 (h 3 j).1 (h 0 j).2 (h 1 j).2 (h 2 j).2 (h 3 j).2
      (by rw [gx0]; have := hlo j; linarith) (by rw [gx3]; have := hhi j; linarith)
      (edge_x p hsep 0 1 j (by decide)) (edge_x p hsep 1 2 j (by decide)) (edge_x p hsep 2 3 j (by decide))
  have hcol : ∀ i, |(p i 0).2 - gx 0| ≤ 60 * r ^ 2 ∧ |(p i 1).2 - gx 1| ≤ 60 * r ^ 2 ∧
      |(p i 2).2 - gx 2| ≤ 60 * r ^ 2 ∧ |(p i 3).2 - gx 3| ≤ 60 * r ^ 2 := by
    intro i
    exact line_lemma _ _ _ _ (((p i 0).1 - gx i)) (((p i 1).1 - gx i)) (((p i 2).1 - gx i)) (((p i 3).1 - gx i)) r hr0 hr
      (h i 0).2 (h i 1).2 (h i 2).2 (h i 3).2 (h i 0).1 (h i 1).1 (h i 2).1 (h i 3).1
      (by rw [gx0]; have := hlo' i; linarith) (by rw [gx3]; have := hhi' i; linarith)
      (edge_y p hsep i 0 1 (by decide)) (edge_y p hsep i 1 2 (by decide)) (edge_y p hsep i 2 3 (by decide))
  intro i j
  refine ⟨?_, ?_⟩
  · have := hrow j
    fin_cases i
    · exact this.1.trans hc
    · exact this.2.1.trans hc
    · exact this.2.2.1.trans hc
    · exact this.2.2.2.trans hc
  · have := hcol i
    fin_cases j
    · exact this.1.trans hc
    · exact this.2.1.trans hc
    · exact this.2.2.1.trans hc
    · exact this.2.2.2.trans hc

end CPQ

namespace CPQ

theorem local_grid (p : Fin 4 → Fin 4 → ℝ × ℝ)
    (hlo : ∀ j, 0 ≤ (p 0 j).1) (hhi : ∀ j, (p 3 j).1 ≤ 1)
    (hlo' : ∀ i, 0 ≤ (p i 0).2) (hhi' : ∀ i, (p i 3).2 ≤ 1)
    (hsep : ∀ i j k l, (i, j) ≠ (k, l) → (1 : ℝ) / 9 < sqDist (p i j) (p k l))
    (h0 : Pr p (1 / 200)) : False := by
  have iter : ∀ n : ℕ, Pr p ((3 / 10 : ℝ) ^ n / 200) := by
    intro n
    induction n with
    | zero => simpa using h0
    | succ n ih =>
      have hle : ((3 / 10 : ℝ) ^ n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have := step_Pr p hlo hhi hlo' hhi' hsep ((3 / 10 : ℝ) ^ n / 200) (by positivity)
        (by linarith) ih
      have e : (3 / 10 : ℝ) ^ (n + 1) / 200 = 3 / 10 * ((3 / 10 : ℝ) ^ n / 200) := by ring
      rw [e]; exact this
  have zero : ∀ i j, (p i j).1 = gx i ∧ (p i j).2 = gx j := by
    intro i j
    have key : ∀ x : ℝ, (∀ n : ℕ, |x| ≤ (3 / 10 : ℝ) ^ n / 200) → x = 0 := by
      intro x hx
      by_contra hne
      have hpos : 0 < |x| := abs_pos.2 hne
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 200 * |x| by positivity) (show (3 / 10 : ℝ) < 1 by norm_num)
      have := hx n
      linarith
    constructor
    · have := key ((p i j).1 - gx i) (fun n => (iter n i j).1)
      linarith
    · have := key ((p i j).2 - gx j) (fun n => (iter n i j).2)
      linarith
  have h00 := zero 0 0
  have h10 := zero 1 0
  have hs := hsep 0 0 1 0 (by simp)
  unfold sqDist at hs
  rw [h00.1, h00.2, h10.1, h10.2] at hs
  unfold gx at hs
  norm_num at hs

end CPQ

namespace CPQ

theorem s2_M_dvd3 : (3 : Nat) ∣ M := by unfold M; norm_num

theorem s2_cast_third (i : Nat) : ((i * M / 3 : Nat) : ℝ) = (i : ℝ) * M / 3 := by
  rw [Nat.cast_div (dvd_mul_of_dvd_right s2_M_dvd3 i) (by norm_num)]; push_cast; ring

noncomputable def ptOf (p : Fin 4 → Fin 4 → ℝ × ℝ) (k : Nat) : ℝ × ℝ :=
  if h : k < 16 then p ⟨k / 4, by omega⟩ ⟨k % 4, by omega⟩ else (0, 0)

theorem ptOf_idx (p : Fin 4 → Fin 4 → ℝ × ℝ) (i j : Fin 4) : ptOf p (4 * i.val + j.val) = p i j := by
  have hi := i.isLt
  have hj := j.isLt
  have h16 : 4 * i.val + j.val < 16 := by omega
  unfold ptOf
  rw [dif_pos h16]
  congr 2 <;> omega

/-- scaled version of the offset bound: xl ≤ x*M ≤ xh, grid point i/3 -/
theorem s2_off_bound (i xl xh R : Nat) (x : ℝ) (h1 : i * M / 3 ≤ xl + R) (h2 : xh ≤ i * M / 3 + R)
    (hR : (R : ℝ) ≤ M / 200) (hx1 : (xl : ℝ) ≤ x * M) (hx2 : x * M ≤ (xh : ℝ)) :
    |x - (i : ℝ) / 3| ≤ 1 / 200 := by
  have hM := M_pos
  have e := s2_cast_third i
  have c1 : ((i * M / 3 : Nat) : ℝ) ≤ (xl : ℝ) + R := by exact_mod_cast h1
  have c2 : (xh : ℝ) ≤ ((i * M / 3 : Nat) : ℝ) + R := by exact_mod_cast h2
  rw [e] at c1 c2
  rw [abs_le]
  constructor
  · by_contra hc
    have hc' := not_le.1 hc
    nlinarith
  · by_contra hc
    have hc' := not_le.1 hc
    nlinarith

end CPQ

namespace CPQ

def sc16 : List (Nat × Nat) := (List.range 16).map (fun k => (k / 4, k % 4))

theorem sc16_len : sc16.length = 16 := by simp [sc16]

theorem sc16_get (k : Nat) (hk : k < 16) : sc16[k]? = some (k / 4, k % 4) := by
  simp [sc16, hk]

theorem leaf_extract (S : Nat) (h : leafOK S = true) (k : Nat) (hk : k < 16) :
    (k / 4 * M / 3 ≤ fld S (4 * k) + M / 200) ∧ (fld S (4 * k + 1) ≤ k / 4 * M / 3 + M / 200) ∧
    (k % 4 * M / 3 ≤ fld S (4 * k + 2) + M / 200) ∧ (fld S (4 * k + 3) ≤ k % 4 * M / 3 + M / 200) ∧
    fld S (4 * k + 1) ≤ M ∧ fld S (4 * k + 3) ≤ M := by
  unfold leafOK at h
  have := List.all_eq_true.1 h k (List.mem_range.2 hk)
  simp only [Bool.and_eq_true, Nat.ble_eq] at this
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := this
  exact ⟨a, b, c, d, e, f⟩

theorem struct_hlk (p : Fin 4 → Fin 4 → ℝ × ℝ)
    (hd : ∀ i j k l, (i, j) ≠ (k, l) → (1 : ℝ) / 9 < sqDist (p i j) (p k l)) :
    ∀ S, leafOK S = true → Sat sc16.length (ordsOf sc16) S (ptOf p) → False := by
  intro S h hs
  have hM := M_pos
  have hR : (((M / 200 : Nat)) : ℝ) ≤ M / 200 := by
    have := Nat.cast_div_le (α := ℝ) (m := M) (n := 200)
    simpa using this
  have fact : ∀ i j : Fin 4, |(p i j).1 - gx i| ≤ 1 / 200 ∧ |(p i j).2 - gx j| ≤ 1 / 200 ∧
      0 ≤ (p i j).1 ∧ (p i j).1 ≤ 1 ∧ 0 ≤ (p i j).2 ∧ (p i j).2 ≤ 1 := by
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    have hk : 4 * i.val + j.val < 16 := by omega
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := leaf_extract S h (4 * i.val + j.val) hk
    have hin := hs.1 (4 * i.val + j.val) (by rw [sc16_len]; exact hk)
    rw [ptOf_idx] at hin
    obtain ⟨x1, x2, y1, y2⟩ := hin
    have e1 : (4 * i.val + j.val) / 4 = i.val := by omega
    have e2 : (4 * i.val + j.val) % 4 = j.val := by omega
    rw [e1] at g1 g2
    rw [e2] at g3 g4
    have hx0 : (0 : ℝ) ≤ (p i j).1 * M := le_trans (Nat.cast_nonneg _) x1
    have hy0 : (0 : ℝ) ≤ (p i j).2 * M := le_trans (Nat.cast_nonneg _) y1
    have hxM : (p i j).1 * M ≤ M := le_trans x2 (by exact_mod_cast g5)
    have hyM : (p i j).2 * M ≤ M := le_trans y2 (by exact_mod_cast g6)
    refine ⟨s2_off_bound i.val _ _ _ _ g1 g2 hR x1 x2, s2_off_bound j.val _ _ _ _ g3 g4 hR y1 y2, ?_, ?_, ?_, ?_⟩
    · by_contra hc; have := not_le.1 hc; nlinarith
    · by_contra hc; have := not_le.1 hc; nlinarith
    · by_contra hc; have := not_le.1 hc; nlinarith
    · by_contra hc; have := not_le.1 hc; nlinarith
  apply local_grid p
  · intro j; exact (fact 0 j).2.2.1
  · intro j; exact (fact 3 j).2.2.2.1
  · intro i; exact (fact i 0).2.2.2.2.1
  · intro i; exact (fact i 3).2.2.2.2.2
  · exact hd
  · intro i j; exact ⟨(fact i j).1, (fact i j).2.1⟩

theorem struct_main (p : Fin 4 → Fin 4 → ℝ × ℝ)
    (hc : ∀ i j, (i.val : ℝ) / 4 ≤ (p i j).1 ∧ (p i j).1 ≤ ((i.val : ℝ) + 1) / 4 ∧
      (j.val : ℝ) / 4 ≤ (p i j).2 ∧ (p i j).2 ≤ ((j.val : ℝ) + 1) / 4)
    (hd : ∀ i j k l, (i, j) ≠ (k, l) → (1 : ℝ) / 9 < sqDist (p i j) (p k l))
    (st : List Nat) (rest : List Nat)
    (hchk : checkS leafOK sc16.length (ordsOf sc16) 1000 (unpackAll20 st) (initS sc16) = some rest) : False := by
  have hsc : ∀ c ∈ sc16, c.1 ≤ 3 ∧ c.2 ≤ 3 := by
    intro c hc
    simp only [sc16, List.mem_map, List.mem_range] at hc
    obtain ⟨k, hk, rfl⟩ := hc
    omega
  have hSat : Sat sc16.length (ordsOf sc16) (initS sc16) (ptOf p) := by
    refine sat_init sc16 hsc (ptOf p) ?_ ?_ ?_
    · intro k hk
      have hk16 : k < 16 := by rw [sc16_len] at hk; exact hk
      have hk4 : k / 4 < 4 := by omega
      have hk4' : k % 4 < 4 := by omega
      have hpt : ptOf p k = p ⟨k / 4, hk4⟩ ⟨k % 4, hk4'⟩ := by unfold ptOf; rw [dif_pos hk16]
      have hsc16 : sc16[k] = (k / 4, k % 4) := by simp [sc16]
      rw [hpt]
      have key := hc ⟨k / 4, hk4⟩ ⟨k % 4, hk4'⟩
      exact hsc16.symm ▸ key
    · intro k l hk hl hkl
      have hk16 : k < 16 := by rw [sc16_len] at hk; exact hk
      have hl16 : l < 16 := by rw [sc16_len] at hl; exact hl
      have e1 : ptOf p k = p ⟨k / 4, by omega⟩ ⟨k % 4, by omega⟩ := by unfold ptOf; rw [dif_pos hk16]
      have e2 : ptOf p l = p ⟨l / 4, by omega⟩ ⟨l % 4, by omega⟩ := by unfold ptOf; rw [dif_pos hl16]
      rw [e1, e2]
      apply hd
      intro h
      apply hkl
      have h1 := congrArg (fun x => x.1.val) h
      have h2 := congrArg (fun x => x.2.val) h
      simp at h1 h2
      omega
    · intro k hk heq
      exfalso
      have hk16 : k + 1 < 16 := by rw [sc16_len] at hk; exact hk
      rw [sc16_get k (by omega), sc16_get (k + 1) hk16] at heq
      have h1 := Option.some.inj heq
      have h2 := congrArg (fun x => x.1 * 4 + x.2) h1
      simp only at h2
      omega
  exact checkS_sound (pt := ptOf p) leafOK (struct_hlk p hd) 1000 _ _ rest hchk hSat

end CPQ


