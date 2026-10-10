-- Prove2me | solution 1 for ArtinPrimitiveRoots.rootIL_eq_baseline_mul_memMomentD
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:32:36.214984+00:00
-- url     : https://prove2.me/submissions/7cec40dc-8e40-4263-aa0b-44fa76665c42

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

end ArtinPrimitiveRoots
end

section
/-! # L102D_MemDefs — alias of the bundle `Def_ArtinMemoryModel` (round 5)

The memory model (root coordinates, `pathPhi`, `rootIL`, the memory space, `ghostOp`, `edgeOp`,
`memMomentD`, `dyadParams`, and `MemParams.RootIn`) now lives in
`Definitions/Def_ArtinMemoryModel.lean` (same declarations, same names). -/
end

section
/-! # L102F: basic facts for the memory identity (D7a)

Per-prime statuses of a memory state (`PSt`: unborn, active, pending with a line, dead), the
encoding `enc` of a status assignment as an augmented memory state, the particle ↔ (prime, line)
equivalence (`ptE`, disjoint groups), and the projective-line facts (`lineOf_lt`,
`lineOf_eq_of_dvd`). -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

/-- The status of one group prime in a memory state. -/
inductive PSt
  | U
  | A
  | P (L : ℕ)
  | D
  deriving DecidableEq

section Basic

variable (P : MemParams)

/-- The group primes as a type. -/
abbrev GP := {p // p ∈ P.gPrimes}

lemma mem_gPrimes {p : ℕ} : p ∈ P.gPrimes ↔ ∃ i, p ∈ P.grp i := by
  simp [MemParams.gPrimes, groupPrimes, MemParams.grp]

lemma mem_gPrimes_of_grp {i : Fin P.K} {p : ℕ} (h : p ∈ P.grp i) : p ∈ P.gPrimes :=
  (mem_gPrimes P).2 ⟨i, h⟩

lemma prime_of_grp {i : Fin P.K} {p : ℕ} (h : p ∈ P.grp i) : p.Prime := by
  unfold MemParams.grp primeGroup at h
  exact (mem_filter.1 h).2.1

lemma prime_of_gPrimes {p : ℕ} (h : p ∈ P.gPrimes) : p.Prime := by
  obtain ⟨i, hi⟩ := (mem_gPrimes P).1 h
  exact prime_of_grp P hi

lemma pos_of_gPrimes {p : ℕ} (h : p ∈ P.gPrimes) : 0 < p := (prime_of_gPrimes P h).pos

/-- The group of a group prime. -/
noncomputable def gi (p : GP P) : Fin P.K := ((mem_gPrimes P).1 p.2).choose

lemma gi_spec (p : GP P) : p.1 ∈ P.grp (gi P p) := ((mem_gPrimes P).1 p.2).choose_spec

lemma gi_eq (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {p : GP P} {i : Fin P.K}
    (h : p.1 ∈ P.grp i) : gi P p = i := by
  by_contra hne
  exact disjoint_left.1 (hdisj _ _ hne) (gi_spec P p) h

lemma mem_partSet {y : Fin P.K × ℕ × ℕ} :
    y ∈ P.partSet ↔ y.2.1 ∈ P.grp y.1 ∧ y.2.2 < y.2.1 + 1 := by
  obtain ⟨i, p, L⟩ := y
  simp only [MemParams.partSet, mem_biUnion, mem_univ, true_and, mem_image, mem_range,
    Prod.mk.injEq]
  constructor
  · rintro ⟨i', p', hp', L', hL', rfl, rfl, rfl⟩
    exact ⟨hp', hL'⟩
  · rintro ⟨hp, hL⟩
    exact ⟨i, p, hp, L, hL, rfl, rfl, rfl⟩

/-- Particles are pairs (group prime, line). -/
noncomputable def ptE (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) :
    P.PT ≃ Σ p : GP P, Fin (p.1 + 1) where
  toFun y := ⟨⟨y.1.2.1, mem_gPrimes_of_grp P ((mem_partSet P).1 y.2).1⟩,
    ⟨y.1.2.2, ((mem_partSet P).1 y.2).2⟩⟩
  invFun q := ⟨(gi P q.1, q.1.1, q.2.1), (mem_partSet P).2 ⟨gi_spec P q.1, q.2.2⟩⟩
  left_inv y := by
    obtain ⟨⟨i, p, L⟩, hy⟩ := y
    have h := (mem_partSet P).1 hy
    apply Subtype.ext
    simp only
    rw [gi_eq P hdisj h.1]
  right_inv q := by
    obtain ⟨⟨p, hp⟩, L⟩ := q
    rfl

/-- The particle of the prime `p` with line `L`. -/
noncomputable abbrev pt (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) (p : GP P)
    (L : Fin (p.1 + 1)) : P.PT :=
  (ptE P hdisj).symm ⟨p, L⟩

lemma pt_val (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) (p : GP P)
    (L : Fin (p.1 + 1)) : (pt P hdisj p L).1 = (gi P p, p.1, L.1) := rfl

lemma prod_PT (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {M : Type*}
    [CommMonoid M] (F : P.PT → M) :
    ∏ y, F y = ∏ p : GP P, ∏ L : Fin (p.1 + 1), F (pt P hdisj p L) := by
  rw [← Fintype.prod_sigma (fun q : Σ p : GP P, Fin (p.1 + 1) => F ((ptE P hdisj).symm q))]
  exact Fintype.prod_equiv (ptE P hdisj) _ _ fun y => by simp

lemma sum_PT (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {M : Type*}
    [AddCommMonoid M] (F : P.PT → M) :
    ∑ y, F y = ∑ p : GP P, ∑ L : Fin (p.1 + 1), F (pt P hdisj p L) := by
  rw [← Fintype.sum_sigma (fun q : Σ p : GP P, Fin (p.1 + 1) => F ((ptE P hdisj).symm q))]
  exact Fintype.sum_equiv (ptE P hdisj) _ _ fun y => by simp

/-- Two particles with the same prime and line are equal (disjoint groups). -/
lemma pt_ext (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {y y' : P.PT}
    (hp : y.1.2.1 = y'.1.2.1) (hL : y.1.2.2 = y'.1.2.2) : y = y' := by
  obtain ⟨⟨i, p, L⟩, hy⟩ := y
  obtain ⟨⟨i', p', L'⟩, hy'⟩ := y'
  simp only at hp hL
  subst hp hL
  have h1 := ((mem_partSet P).1 hy).1
  have h2 := ((mem_partSet P).1 hy').1
  have : i = i' := by
    by_contra hne
    exact disjoint_left.1 (hdisj _ _ hne) h1 h2
  subst this
  rfl

end Basic

/-! ## Projective lines -/

lemma lineOf_lt {p : ℕ} (hp : 0 < p) (z : ℤ × ℤ) : lineOf p z < p + 1 := by
  unfold lineOf
  split_ifs
  · exact Nat.lt_succ_self p
  · have : NeZero p := ⟨hp.ne'⟩
    exact Nat.lt_succ_of_lt (ZMod.val_lt _)

lemma not_dvd_of_gcd {p : ℕ} (hp : p.Prime) {z : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1)
    (h1 : (p : ℤ) ∣ z.1) : ¬ (p : ℤ) ∣ z.2 := by
  intro h2
  have := Int.dvd_gcd h1 h2
  rw [hz] at this
  have h3 : p ∣ 1 := by exact_mod_cast this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

/-- A prime dividing `det(z, z')` of two primitive vectors sees the same line. -/
lemma lineOf_eq_of_dvd {p : ℕ} (hp : p.Prime) {z z' : ℤ × ℤ} (hz : Int.gcd z.1 z.2 = 1)
    (hz' : Int.gcd z'.1 z'.2 = 1) (hd : (p : ℤ) ∣ detZ z z') : lineOf p z = lineOf p z' := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  unfold detZ at hd
  unfold lineOf
  by_cases h1 : (p : ℤ) ∣ z.1
  · have h2 : (p : ℤ) ∣ z.2 * z'.1 := by
      have : (p : ℤ) ∣ z.1 * z'.2 := dvd_mul_of_dvd_left h1 _
      have := dvd_sub this hd
      simpa using this
    have h3 : (p : ℤ) ∣ z'.1 := by
      rcases hpz.dvd_or_dvd h2 with h | h
      · exact absurd h (not_dvd_of_gcd hp hz h1)
      · exact h
    rw [if_pos h1, if_pos h3]
  · have h3 : ¬ (p : ℤ) ∣ z'.1 := by
      intro h3
      have h4 : (p : ℤ) ∣ z.1 * z'.2 := by
        have : (p : ℤ) ∣ z.2 * z'.1 := dvd_mul_of_dvd_right h3 _
        have := dvd_add hd this
        simpa using this
      rcases hpz.dvd_or_dvd h4 with h | h
      · exact h1 h
      · exact not_dvd_of_gcd hp hz' h3 h
    rw [if_neg h1, if_neg h3]
    have : Fact p.Prime := ⟨hp⟩
    congr 1
    have e1 : (z.1 : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h1
    have e2 : (z'.1 : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h3
    have e3 : ((z.1 * z'.2 - z.2 * z'.1 : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hd
    push_cast at e3
    field_simp
    linear_combination -e3

/-! ## Encoding status assignments as memory states -/

section Enc

variable (P : MemParams)

/-- The memory of a status assignment: one copy of the particle `(i, p, L)` iff `p` is pending
with line `L`. -/
def encMem (st : ℕ → PSt) : P.Mem := fun y => if st y.1.2.1 = PSt.P y.1.2.2 then 1 else 0

/-- The born primes: the group primes that are not unborn. -/
noncomputable def encBorn (st : ℕ → PSt) : Finset ℕ := P.gPrimes.filter fun p => st p ≠ PSt.U

/-- The augmented memory state at position `z` with lists `ℓ` and statuses `st`. -/
noncomputable def enc (z : ℤ × ℤ) (ℓ : P.Lst) (st : ℕ → PSt) : P.MState × Finset ℕ :=
  ((z, ℓ, encMem P st), encBorn P st)

/-- A valid status assignment for the lists `ℓ`. -/
structure Valid (ℓ : P.Lst) (st : ℕ → PSt) : Prop where
  lc : ∀ i k, ℓ i k ∈ P.grp i
  act : ∀ p ∈ P.gPrimes, (st p = PSt.A ↔ ∃ i k, ℓ i k = p)
  pend : ∀ p ∈ P.gPrimes, ∀ L, st p = PSt.P L → L < p + 1

variable (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
include hdisj

lemma encMem_pt (st : ℕ → PSt) (p : GP P) (L : Fin (p.1 + 1)) :
    encMem P st (pt P hdisj p L) = if st p.1 = PSt.P L.1 then 1 else 0 := rfl

lemma isHit_pt (z : ℤ × ℤ) (p : GP P) (L : Fin (p.1 + 1)) :
    P.IsHit z (pt P hdisj p L) ↔ L.1 = lineOf p.1 z := Iff.rfl

/-- The point `lineOf p z` of `Fin (p + 1)`. -/
def lnF (p : GP P) (z : ℤ × ℤ) : Fin (p.1 + 1) := ⟨lineOf p.1 z, lineOf_lt (pos_of_gPrimes P p.2) z⟩

omit hdisj in
lemma sum_fin_ite_line {M : Type*} [AddCommMonoid M] (p : GP P) (z : ℤ × ℤ) (g : ℕ → M) :
    ∑ L : Fin (p.1 + 1), (if L.1 = lineOf p.1 z then g L.1 else 0) = g (lineOf p.1 z) := by
  rw [sum_eq_single (lnF P p z)]
  · simp [lnF]
  · intro L _ hL
    rw [if_neg]
    intro h; exact hL (Fin.ext h)
  · simp

lemma hitCount_enc (z : ℤ × ℤ) (st : ℕ → PSt) :
    P.hitCount z (encMem P st) = ∑ p : GP P, if st p.1 = PSt.P (lineOf p.1 z) then 1 else 0 := by
  classical
  unfold MemParams.hitCount
  rw [sum_PT P hdisj]
  refine sum_congr rfl fun p _ => ?_
  have := sum_fin_ite_line P p z (fun L => if st p.1 = PSt.P L then 1 else 0)
  rw [← this]
  refine sum_congr rfl fun L _ => ?_
  simp only [isHit_pt P hdisj, encMem_pt P hdisj]

lemma memSize_enc (st : ℕ → PSt) :
    P.memSize (encMem P st) = ∑ p : GP P, ∑ L : Fin (p.1 + 1),
      if st p.1 = PSt.P L.1 then 1 else 0 := by
  unfold MemParams.memSize
  rw [sum_PT P hdisj]
  rfl

omit hdisj in
lemma sum_fin_st_le_one (s : PSt) (n : ℕ) :
    ∑ L : Fin n, (if s = PSt.P L.1 then 1 else 0) ≤ 1 := by
  by_cases h : ∃ L : Fin n, s = PSt.P L.1
  · obtain ⟨L, hL⟩ := h
    rw [sum_eq_single L]
    · simp [hL]
    · intro L' _ hL'
      rw [if_neg]
      intro h'
      rw [hL] at h'
      exact hL' (Fin.ext (PSt.P.inj h').symm)
    · simp
  · simp only [not_exists] at h
    simp [h]

lemma memSize_enc_le (st : ℕ → PSt) : P.memSize (encMem P st) ≤ P.gPrimes.card := by
  classical
  rw [memSize_enc P hdisj]
  calc ∑ p : GP P, ∑ L : Fin (p.1 + 1), (if st p.1 = PSt.P L.1 then 1 else 0)
      ≤ ∑ _p : GP P, 1 := sum_le_sum fun p _ => sum_fin_st_le_one _ _
    _ = P.gPrimes.card := by simp

omit hdisj in
lemma encMem_le_one (st : ℕ → PSt) (y : P.PT) : encMem P st y ≤ 1 := by
  unfold encMem; split_ifs <;> simp

lemma encMem_mem (st : ℕ → PSt) (hB : P.gPrimes.card ≤ P.B) : encMem P st ∈ P.memSet := by
  unfold MemParams.memSet
  rw [mem_filter, Fintype.mem_piFinset]
  refine ⟨fun y => ?_, (memSize_enc_le P hdisj st).trans hB⟩
  rw [mem_range]
  by_cases h : encMem P st y = 0
  · rw [h]; omega
  · have h1 := encMem_le_one P st y
    have hy : y.1.2.1 ∈ P.gPrimes := mem_gPrimes_of_grp P ((mem_partSet P).1 y.2).1
    have : 1 ≤ P.gPrimes.card := card_pos.2 ⟨_, hy⟩
    omega

omit hdisj in
lemma mem_bornPrimes (b : P.Mem) (q : ℕ) :
    q ∈ P.bornPrimes b ↔ ∃ y, b y ≠ 0 ∧ y.1.2.1 = q := by
  unfold MemParams.bornPrimes
  simp only [Multiset.mem_sum, mem_univ, true_and, Multiset.mem_nsmul, Multiset.mem_singleton]
  exact exists_congr fun y => and_congr_right fun _ => eq_comm

omit hdisj in
lemma count_bornPrimes (b : P.Mem) (q : ℕ) :
    (P.bornPrimes b).count q = ∑ y, if y.1.2.1 = q then b y else 0 := by
  classical
  unfold MemParams.bornPrimes
  rw [Multiset.count_sum']
  refine sum_congr rfl fun y _ => ?_
  rw [Multiset.count_nsmul, Multiset.count_singleton]
  by_cases h : y.1.2.1 = q
  · simp [h]
  · rw [if_neg (Ne.symm h), if_neg h, mul_zero]

omit hdisj in
lemma le_count_bornPrimes (b : P.Mem) (y : P.PT) : b y ≤ (P.bornPrimes b).count y.1.2.1 := by
  classical
  rw [count_bornPrimes]
  have := single_le_sum (s := univ) (f := fun y' : P.PT => if y'.1.2.1 = y.1.2.1 then b y' else 0)
    (fun _ _ => Nat.zero_le _) (mem_univ y)
  simpa using this

lemma count_bornPrimes_enc_le (st : ℕ → PSt) (q : ℕ) :
    (P.bornPrimes (encMem P st)).count q ≤ 1 := by
  classical
  rw [count_bornPrimes, sum_PT P hdisj]
  by_cases hq : q ∈ P.gPrimes
  · rw [sum_eq_single ⟨q, hq⟩]
    · simp only [pt_val, if_true, encMem_pt P hdisj]
      exact sum_fin_st_le_one _ _
    · intro p _ hp
      refine sum_eq_zero fun L _ => ?_
      rw [pt_val, if_neg]
      intro h; exact hp (Subtype.ext h)
    · simp
  · refine (sum_eq_zero fun p _ => sum_eq_zero fun L _ => ?_).le.trans zero_le_one
    rw [pt_val, if_neg]
    intro h; exact hq (h ▸ p.2)

lemma nodup_bornPrimes_enc (st : ℕ → PSt) : (P.bornPrimes (encMem P st)).Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  exact fun q => count_bornPrimes_enc_le P hdisj st q

end Enc

/-! ## Line types and the physical tail with fixed lines -/

section Types

variable (P : MemParams)

/-- The types of a group prime: a line `some L` (`L ≤ p`) or `none` ("dead"). -/
def tyS (p : GP P) : Finset (Option ℕ) := insertNone (range (p.1 + 1))

/-- The divisibility oracle of a type assignment. -/
def dT (τ : GP P → Option ℕ) : ℕ → ℤ × ℤ → Prop :=
  fun p z => ∃ h : p ∈ P.gPrimes, τ ⟨p, h⟩ = some (lineOf p z)

open Classical in
/-- The prime factor at visit `j` for the type `o`. -/
noncomputable def pfT (j p : ℕ) (s : (ℤ × ℤ) × P.Lst) (o : Option ℕ) : ℝ :=
  if ∃ i k, s.2 i k = p then (if o = some (lineOf p s.1) then 1 else 0)
  else (if o = some (lineOf p s.1) then P.qv j else 1)

lemma visitFac_dT (τ : GP P → Option ℕ) (j : ℕ) (s : (ℤ × ℤ) × P.Lst) :
    P.visitFac (dT P τ) j s = ∏ p : GP P, pfT P j p.1 s (τ p) := by
  classical
  unfold MemParams.visitFac
  rw [← prod_coe_sort P.gPrimes]
  refine prod_congr rfl fun p _ => ?_
  have hd : dT P τ p.1 s.1 ↔ τ p = some (lineOf p.1 s.1) :=
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨p.2, h⟩⟩
  unfold MemParams.primeFac pfT
  simp only [hd]

/-! ## The coefficients -/

/-- `b'_p[t, N] = 1 − ∑_{t ≤ j ≤ N} η'_j/(p+1)`. -/
noncomputable def btail (t p : ℕ) : ℝ := 1 - (∑ j ∈ Ico t (P.N + 1), P.etav j) / ((p : ℝ) + 1)

/-- The coefficient of an unborn prime. -/
noncomputable def cU (t p : ℕ) (o : Option ℕ) : ℂ :=
  if o = none then ((1 - btail P t p / P.bprime p : ℝ) : ℂ)
  else ((1 / (((p : ℝ) + 1) * P.bprime p) : ℝ) : ℂ)

/-- The coefficient of a status before the ghost at visit `t`, position `z`. -/
noncomputable def cf (t : ℕ) (z : ℤ × ℤ) (p : ℕ) : PSt → Option ℕ → ℂ
  | PSt.U, o => cU P t p o
  | PSt.A, o => if o = some (lineOf p z) then 1 else 0
  | PSt.P L, o => (if L = lineOf p z then ((memRho⁻¹ : ℝ) : ℂ) else 1) *
      ((if o = some L then 1 else 0) - (if o = none then 1 else 0))
  | PSt.D, o => if o = none then 1 else 0

/-- The coefficient of a status after the ghost at visit `t` (before the edge `t`). -/
noncomputable def cg (t : ℕ) (z : ℤ × ℤ) (p : ℕ) : PSt → Option ℕ → ℂ
  | PSt.U, o => cU P (t + 1) p o
  | PSt.A, o => if o = some (lineOf p z) then 1 else 0
  | PSt.P L, o => (if L = lineOf p z then ((memRho : ℝ) : ℂ) else 1) *
      ((if o = some L then 1 else 0) - (if o = none then 1 else 0))
  | PSt.D, o => if o = none then 1 else 0

end Types

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: the ghost step of the memory identity

The ghost `G_t` on an encoded state factors over the group primes: an unborn prime may be born
at its current line (weight `−η'_t Vᵢ νᵢ(p)/ρ`), a pending prime that hits may be deleted
(`−η'_t/ρ`) or survive (`q_t/ρ²`); nothing else changes. Against the coefficients `cg` after the
ghost this reproduces `cf` times the visit factor of the type (`ghost_local`). -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

section Local

variable (P : MemParams)

lemma btail_succ (t p : ℕ) (ht : t ≤ P.N) :
    btail P t p = btail P (t + 1) p - P.etav t / ((p : ℝ) + 1) := by
  unfold btail
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : t < P.N + 1)]
  ring

lemma qv_eq (t : ℕ) : P.qv t = 1 - P.etav t := by unfold MemParams.etav; ring

/-- The local ghost choice is available: unborn, or pending and hitting. -/
def gAct (z : ℤ × ℤ) (p : ℕ) (s : PSt) : Prop := s = PSt.U ∨ s = PSt.P (lineOf p z)

instance (z : ℤ × ℤ) (p : ℕ) (s : PSt) : Decidable (gAct z p s) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The status after the local ghost choice `b`. -/
def gNew (z : ℤ × ℤ) (p : ℕ) (s : PSt) (b : Bool) : PSt :=
  if b then (if s = PSt.U then PSt.P (lineOf p z) else PSt.D) else s

/-- The local ghost weight. -/
noncomputable def gW (t : ℕ) (z : ℤ × ℤ) (i : Fin P.K) (p : ℕ) (s : PSt) (b : Bool) : ℂ :=
  if s = PSt.U then (if b then ((-P.etav t * P.Vg i * P.nu i p / memRho : ℝ) : ℂ) else 1)
  else if s = PSt.P (lineOf p z) then
    (if b then ((-P.etav t / memRho : ℝ) : ℂ) else ((P.qv t / memRho ^ 2 : ℝ) : ℂ))
  else 1

lemma memRho_ne : (memRho : ℝ) ≠ 0 := by unfold memRho; norm_num

/-- **The local ghost identity.** -/
lemma ghost_local (t : ℕ) (ht : t ≤ P.N) (z : ℤ × ℤ) (i : Fin P.K) (p : ℕ) (hVi : P.Vg i ≠ 0)
    (hbp : P.bprime p ≠ 0) (s : PSt) (act : Prop) [Decidable act] (hact : s = PSt.A ↔ act)
    (o : Option ℕ) :
    (if gAct z p s then
      gW P t z i p s true * cg P t z p (gNew z p s true) o +
        gW P t z i p s false * cg P t z p (gNew z p s false) o
      else cg P t z p s o) =
    cf P t z p s o * ((if act then (if o = some (lineOf p z) then 1 else 0)
      else (if o = some (lineOf p z) then P.qv t else 1) : ℝ) : ℂ) := by
  have hρ : ((memRho : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 memRho_ne
  have hp1 : ((p : ℂ) + 1) ≠ 0 := by
    have : ((p : ℝ) + 1 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hVc : ((P.Vg i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hVi
  have hbc : ((P.bprime p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hbp
  have hbt := btail_succ P t p ht
  have hq := qv_eq P t
  rcases s with _ | _ | L | _
  · -- unborn
    have hna : ¬ act := fun h => by have := hact.2 h; cases this
    simp only [gAct, gNew, gW, cg, cf, cU, if_true, true_or, if_false, Bool.false_eq_true,
      if_neg hna]
    rcases o with _ | L'
    · simp only [reduceCtorEq, if_false, if_true, mul_one]
      rw [hbt]
      simp only [MemParams.nu]
      push_cast
      field_simp
      ring
    · simp only [reduceCtorEq, if_false, Option.some.injEq]
      by_cases hL : L' = lineOf p z
      · simp only [hL, if_true, mul_one, sub_zero]
        rw [hq]
        simp only [MemParams.nu]
        push_cast
        field_simp
        ring
      · simp only [hL, if_false, mul_zero, sub_zero, zero_add, one_mul, mul_one]
        simp
  · -- active
    have ha : act := hact.1 rfl
    simp only [gAct, reduceCtorEq, or_self, if_false, cg, cf, if_pos ha]
    split_ifs <;> simp
  · -- pending with line L
    have hna : ¬ act := fun h => by have := hact.2 h; cases this
    simp only [if_neg hna]
    by_cases hL : L = lineOf p z
    · subst hL
      simp only [gAct, gNew, gW, cg, cf, reduceCtorEq, false_or, if_true, if_false,
        Bool.false_eq_true]
      rcases o with _ | L'
      · simp only [reduceCtorEq, if_false, if_true]
        rw [hq]
        push_cast
        field_simp
        ring
      · simp only [reduceCtorEq, if_false, Option.some.injEq, sub_zero]
        by_cases hL' : L' = lineOf p z
        · subst hL'
          simp only [if_true]
          push_cast
          field_simp
          ring
        · simp [hL', Ne.symm hL']
    · have hg : ¬ gAct z p (PSt.P L) := by
        unfold gAct; simp only [reduceCtorEq, false_or, PSt.P.injEq]; exact hL
      rw [if_neg hg]
      simp only [cg, cf, if_neg hL, one_mul]
      rcases o with _ | L'
      · simp
      · simp only [reduceCtorEq, if_false, Option.some.injEq, sub_zero]
        by_cases hL' : L' = lineOf p z
        · subst hL'
          rw [if_neg (Ne.symm hL)]; simp
        · simp [hL']
  · -- dead
    have hna : ¬ act := fun h => by have := hact.2 h; cases this
    simp only [gAct, reduceCtorEq, or_self, if_false, cg, cf, if_neg hna]
    rcases o with _ | L'
    · simp
    · simp

end Local

section Step

variable (P : MemParams)

/-- Allowed local ghost choices. -/
def gS (z : ℤ × ℤ) (st : ℕ → PSt) (p : GP P) : Finset Bool :=
  if gAct z p.1 (st p.1) then univ else {false}

/-- The statuses after the ghost choices `χ`. -/
noncomputable def stG (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) : ℕ → PSt :=
  fun q => if h : q ∈ P.gPrimes then gNew z q (st q) (χ ⟨q, h⟩) else st q

/-- The deleted particles, as a status function. -/
noncomputable def stD (st : ℕ → PSt) (χ : GP P → Bool) : ℕ → PSt :=
  fun q => if h : q ∈ P.gPrimes then
    (if χ ⟨q, h⟩ = true ∧ st q ≠ PSt.U then st q else PSt.U) else PSt.U

/-- The born particles, as a status function. -/
noncomputable def stB (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) : ℕ → PSt :=
  fun q => if h : q ∈ P.gPrimes then
    (if χ ⟨q, h⟩ = true ∧ st q = PSt.U then PSt.P (lineOf q z) else PSt.U) else PSt.U

lemma stG_gp (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) (p : GP P) :
    stG P z st χ p.1 = gNew z p.1 (st p.1) (χ p) := by
  unfold stG; rw [dif_pos p.2]

lemma chi_act {z : ℤ × ℤ} {st : ℕ → PSt} {χ : GP P → Bool}
    (hχ : χ ∈ Fintype.piFinset (gS P z st)) {p : GP P} (h : χ p = true) :
    gAct z p.1 (st p.1) := by
  have := Fintype.mem_piFinset.1 hχ p
  unfold gS at this
  split_ifs at this with hg
  · exact hg
  · simp at this; rw [this] at h; exact absurd h (by simp)

lemma valid_stG {z : ℤ × ℤ} {ℓ : P.Lst} {st : ℕ → PSt} (hv : Valid P ℓ st) {χ : GP P → Bool}
    (hχ : χ ∈ Fintype.piFinset (gS P z st)) : Valid P ℓ (stG P z st χ) := by
  refine ⟨hv.lc, fun p hp => ?_, fun p hp L hL => ?_⟩
  · rw [← hv.act p hp]
    have e := stG_gp P z st χ ⟨p, hp⟩
    simp only at e
    rw [e]
    unfold gNew
    cases hc : χ ⟨p, hp⟩
    · simp
    · have hg := chi_act P hχ hc
      unfold gAct at hg
      simp only [if_true]
      rcases hg with h | h <;> rw [h] <;> simp
  · have e := stG_gp P z st χ ⟨p, hp⟩
    simp only at e
    rw [e] at hL
    unfold gNew at hL
    cases hc : χ ⟨p, hp⟩
    · rw [hc] at hL; exact hv.pend p hp L hL
    · rw [hc] at hL
      simp only [if_true] at hL
      split_ifs at hL
      · cases hL; exact lineOf_lt (pos_of_gPrimes P hp) z

lemma stB_of_mem (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) {q : ℕ} (hq : q ∈ P.gPrimes) :
    stB P z st χ q =
      if χ ⟨q, hq⟩ = true ∧ st q = PSt.U then PSt.P (lineOf q z) else PSt.U := by
  unfold stB; rw [dif_pos hq]

lemma stD_of_mem (st : ℕ → PSt) (χ : GP P → Bool) {q : ℕ} (hq : q ∈ P.gPrimes) :
    stD P st χ q = if χ ⟨q, hq⟩ = true ∧ st q ≠ PSt.U then st q else PSt.U := by
  unfold stD; rw [dif_pos hq]

lemma stG_of_mem (z : ℤ × ℤ) (st : ℕ → PSt) (χ : GP P → Bool) {q : ℕ} (hq : q ∈ P.gPrimes) :
    stG P z st χ q = gNew z q (st q) (χ ⟨q, hq⟩) := by
  unfold stG; rw [dif_pos hq]

lemma y_gp (y : P.PT) : y.1.2.1 ∈ P.gPrimes := mem_gPrimes_of_grp P ((mem_partSet P).1 y.2).1

/-- The memory after the ghost choices. -/
lemma ghost_mem {z : ℤ × ℤ} {st : ℕ → PSt} {χ : GP P → Bool}
    (hχ : χ ∈ Fintype.piFinset (gS P z st)) :
    (fun y => encMem P st y - encMem P (stD P st χ) y + encMem P (stB P z st χ) y) =
      encMem P (stG P z st χ) := by
  funext y
  have hy := y_gp P y
  unfold encMem stD stB stG
  rw [dif_pos hy, dif_pos hy, dif_pos hy]
  unfold gNew
  cases hc : χ ⟨y.1.2.1, hy⟩
  · simp
  · have hg := chi_act P hχ hc
    unfold gAct at hg
    simp only at hg
    rcases hg with h | h <;> rw [h] <;> simp [eq_comm]

/-- The born primes after the ghost choices. -/
lemma ghost_born {z : ℤ × ℤ} {st : ℕ → PSt} {χ : GP P → Bool}
    (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) :
    encBorn P st ∪ (P.bornPrimes (encMem P (stB P z st χ))).toFinset =
      encBorn P (stG P z st χ) := by
  ext q
  simp only [mem_union, Multiset.mem_toFinset, mem_bornPrimes, encBorn, mem_filter]
  constructor
  · rintro (⟨hq, hne⟩ | ⟨y, hy, rfl⟩)
    · refine ⟨hq, ?_⟩
      unfold stG gNew; rw [dif_pos hq]
      cases χ ⟨q, hq⟩ <;> simp [hne]
    · have hq := y_gp P y
      refine ⟨hq, ?_⟩
      have hst : stB P z st χ y.1.2.1 = PSt.P y.1.2.2 := by
        unfold encMem at hy; by_contra h; exact hy (if_neg h)
      rw [stB_of_mem P z st χ hq] at hst
      have h1 : χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U := by
        by_contra h; rw [if_neg h] at hst; cases hst
      rw [stG_of_mem P z st χ hq]
      unfold gNew; rw [h1.1]; simp [h1.2]
  · rintro ⟨hq, hne⟩
    by_cases hU : st q = PSt.U
    · right
      unfold stG gNew at hne; rw [dif_pos hq] at hne
      have hc : χ ⟨q, hq⟩ = true := by
        cases hc : χ ⟨q, hq⟩
        · rw [hc] at hne; exact absurd hU (by simpa using hne)
        · rfl
      refine ⟨pt P hdisj ⟨q, hq⟩ (lnF P ⟨q, hq⟩ z), ?_, rfl⟩
      rw [encMem_pt P hdisj, if_pos]
      · simp
      · rw [stB_of_mem P z st χ hq, if_pos ⟨hc, hU⟩]; rfl
    · left; exact ⟨hq, hU⟩

lemma isHit_iff (z : ℤ × ℤ) (y : P.PT) : P.IsHit z y ↔ y.1.2.2 = lineOf y.1.2.1 z := Iff.rfl

/-- The ghost coefficient of the choices `χ` is the product of the local weights. -/
lemma ghost_coeff (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {t : ℕ}
    {z : ℤ × ℤ} {ℓ : P.Lst} {st : ℕ → PSt} {χ : GP P → Bool}
    (hχ : χ ∈ Fintype.piFinset (gS P z st)) :
    P.ghostCoeff t (z, ℓ, encMem P st) (encMem P (stD P st χ), encMem P (stB P z st χ)) =
      ∏ p : GP P, gW P t z (gi P p) p.1 (st p.1) (χ p) := by
  unfold MemParams.ghostCoeff
  rw [if_pos]
  · rw [Complex.ofReal_prod, prod_PT P hdisj]
    refine prod_congr rfl fun p _ => ?_
    rw [prod_eq_single (lnF P p z)]
    · have hhit : P.IsHit z (pt P hdisj p (lnF P p z)) := rfl
      rw [if_pos hhit]
      simp only [encMem_pt P hdisj, lnF, stD_of_mem P st χ p.2, stB_of_mem P z st χ p.2,
        MemParams.lam, pt_val]
      unfold gW
      cases hc : χ p
      · simp only [Bool.false_eq_true, false_and, if_false]
        by_cases hU : st p.1 = PSt.U
        · simp [hU]
        · by_cases hP : st p.1 = PSt.P (lineOf p.1 z)
          · simp [hP]
          · simp [hU, hP]
      · have hg := chi_act P hχ hc
        unfold gAct at hg
        rcases hg with h | h
        · simp [h, MemParams.nu]
          push_cast; ring
        · simp [h]
    · intro L _ hL
      have hh : ¬ P.IsHit z (pt P hdisj p L) := by
        rw [isHit_pt P hdisj]; intro h; exact hL (Fin.ext h)
      simp [hh]
    · simp
  · refine ⟨fun y => ?_, fun y hy => ?_⟩
    · have hq := y_gp P y
      unfold encMem
      dsimp only
      rw [stD_of_mem P st χ hq]
      split_ifs with h1 h2 h3 <;> simp_all
    · have hq := y_gp P y
      rw [isHit_iff] at hy
      unfold encMem
      dsimp only at hy ⊢
      rw [stD_of_mem P st χ hq, stB_of_mem P z st χ hq]
      constructor
      · by_contra hne
        have h2 : (if χ ⟨_, hq⟩ = true ∧ st y.1.2.1 ≠ PSt.U then st y.1.2.1 else PSt.U) =
            PSt.P y.1.2.2 := by
          by_contra h; exact hne (if_neg h)
        by_cases h1 : χ ⟨_, hq⟩ = true ∧ st y.1.2.1 ≠ PSt.U
        · rw [if_pos h1] at h2
          have hg := chi_act P hχ h1.1
          rcases hg with h | h
          · exact h1.2 h
          · rw [h] at h2; exact hy (PSt.P.inj h2).symm
        · rw [if_neg h1] at h2; cases h2
      · by_contra hne
        have h2 : (if χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U then PSt.P (lineOf y.1.2.1 z)
            else PSt.U) = PSt.P y.1.2.2 := by
          by_contra h; exact hne (if_neg h)
        by_cases h1 : χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U
        · rw [if_pos h1] at h2; exact hy (PSt.P.inj h2).symm
        · rw [if_neg h1] at h2; cases h2

lemma recover (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {z : ℤ × ℤ}
    {st : ℕ → PSt} {χ : GP P → Bool} (hχ : χ ∈ Fintype.piFinset (gS P z st)) (p : GP P) :
    (encMem P (stD P st χ) (pt P hdisj p (lnF P p z)) ≠ 0 ∨
      encMem P (stB P z st χ) (pt P hdisj p (lnF P p z)) ≠ 0) ↔ χ p = true := by
  rw [encMem_pt P hdisj, encMem_pt P hdisj, stD_of_mem P st χ p.2, stB_of_mem P z st χ p.2]
  simp only [lnF]
  constructor
  · rintro (h | h)
    · by_contra hc
      rw [if_neg (fun h' => hc h'.1)] at h; simp at h
    · by_contra hc
      rw [if_neg (fun h' => hc h'.1)] at h; simp at h
  · intro hc
    have hg := chi_act P hχ hc
    rcases hg with h | h
    · right; rw [if_pos ⟨hc, h⟩]; simp
    · left; rw [if_pos ⟨hc, by rw [h]; simp⟩, h]; simp

lemma enc_mem_stSet (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hB : P.gPrimes.card ≤ P.B) {z : ℤ × ℤ} (hz : z ∈ P.zSet) {ℓ : P.Lst}
    (hℓ : ∀ i k, ℓ i k ∈ P.grp i) (st : ℕ → PSt) : (z, ℓ, encMem P st) ∈ P.stSet := by
  rw [MemParams.stSet, mem_product, mem_product]
  refine ⟨hz, ?_, encMem_mem P hdisj _ hB⟩
  simp only [listCands, Fintype.mem_piFinset]; exact hℓ

/-- Decoding a ghost choice with nonzero coefficient. -/
lemma ghost_decode (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {t : ℕ}
    {z : ℤ × ℤ} {ℓ : P.Lst} {st : ℕ → PSt} (c : P.Mem × P.Mem)
    (hnd : (P.bornPrimes c.2).Nodup) (hfr : ∀ p ∈ P.bornPrimes c.2, p ∉ encBorn P st)
    (hc : P.ghostCoeff t (z, ℓ, encMem P st) c ≠ 0) :
    ∃ χ ∈ Fintype.piFinset (gS P z st), (encMem P (stD P st χ), encMem P (stB P z st χ)) = c := by
  classical
  have hcond : (∀ y, c.1 y ≤ encMem P st y) ∧ (∀ y, ¬ P.IsHit z y → c.1 y = 0 ∧ c.2 y = 0) := by
    by_contra h
    unfold MemParams.ghostCoeff at hc
    rw [if_neg h] at hc
    exact hc rfl
  have F1 : ∀ y, c.1 y ≠ 0 → st y.1.2.1 = PSt.P y.1.2.2 := by
    intro y hy
    have := hcond.1 y
    unfold encMem at this
    by_contra h; rw [if_neg h] at this; omega
  have F2 : ∀ y, c.2 y ≠ 0 → st y.1.2.1 = PSt.U := by
    intro y hy
    have h1 := hfr y.1.2.1 ((mem_bornPrimes P _ _).2 ⟨y, hy, rfl⟩)
    unfold encBorn at h1
    rw [mem_filter] at h1
    by_contra h; exact h1 ⟨y_gp P y, h⟩
  have F3 : ∀ y, c.2 y ≤ 1 := by
    intro y
    exact (le_count_bornPrimes P c.2 y).trans (Multiset.nodup_iff_count_le_one.1 hnd _)
  have F4 : ∀ y, c.1 y ≤ 1 := fun y => (hcond.1 y).trans (encMem_le_one P st y)
  set χ : GP P → Bool := fun p =>
    decide (c.1 (pt P hdisj p (lnF P p z)) ≠ 0 ∨ c.2 (pt P hdisj p (lnF P p z)) ≠ 0) with hχdef
  have hact : ∀ p, χ p = true → gAct z p.1 (st p.1) := by
    intro p hp
    simp only [hχdef, decide_eq_true_eq] at hp
    rcases hp with h | h
    · right; have := F1 _ h; simpa [pt_val, lnF] using this
    · left; have := F2 _ h; simpa [pt_val] using this
  have hmem : χ ∈ Fintype.piFinset (gS P z st) := by
    rw [Fintype.mem_piFinset]
    intro p
    unfold gS
    split_ifs with hg
    · exact mem_univ _
    · rw [mem_singleton]
      by_contra h
      exact hg (hact p (by simpa using h))
  -- every hit particle is the particle of its prime at the current line
  have hpt : ∀ y : P.PT, P.IsHit z y → y = pt P hdisj ⟨y.1.2.1, y_gp P y⟩ (lnF P ⟨_, y_gp P y⟩ z) := by
    intro y hy
    exact pt_ext P hdisj rfl hy
  refine ⟨χ, hmem, Prod.ext (funext fun y => ?_) (funext fun y => ?_)⟩
  · -- deletions
    have hq := y_gp P y
    show encMem P (stD P st χ) y = c.1 y
    unfold encMem; rw [stD_of_mem P st χ hq]
    by_cases hy : P.IsHit z y
    · have hy' := hpt y hy
      by_cases h1 : c.1 y = 0
      · rw [h1]
        rw [if_neg]
        intro h
        split_ifs at h with h2
        · have h3 : c.2 y ≠ 0 := by
            have := h2.1
            simp only [hχdef, decide_eq_true_eq] at this
            rw [← hy'] at this
            exact this.resolve_left (by simpa using h1)
          exact h2.2 (F2 y h3)
      · have h5 := F4 y
        have hχ1 : χ ⟨_, hq⟩ = true := by
          simp only [hχdef, decide_eq_true_eq]; left; rw [← hy']; exact h1
        have h6 := F1 y h1
        rw [if_pos (show χ ⟨_, hq⟩ = true ∧ st y.1.2.1 ≠ PSt.U from ⟨hχ1, by rw [h6]; simp⟩),
          if_pos h6]
        omega
    · rw [(hcond.2 y hy).1, if_neg]
      intro h
      split_ifs at h with h2
      · have hg := hact _ h2.1
        rcases hg with h3 | h3
        · exact h2.2 h3
        · rw [h3] at h; exact hy (PSt.P.inj h).symm
  · -- births
    have hq := y_gp P y
    show encMem P (stB P z st χ) y = c.2 y
    unfold encMem; rw [stB_of_mem P z st χ hq]
    by_cases hy : P.IsHit z y
    · have hy' := hpt y hy
      by_cases h1 : c.2 y = 0
      · rw [h1, if_neg]
        intro h
        split_ifs at h with h2
        · have h3 : c.1 y ≠ 0 := by
            have := h2.1
            simp only [hχdef, decide_eq_true_eq] at this
            rw [← hy'] at this
            exact this.resolve_right (by simpa using h1)
          have := F1 y h3
          rw [h2.2] at this; cases this
      · have h5 := F3 y
        have hχ1 : χ ⟨_, hq⟩ = true := by
          simp only [hχdef, decide_eq_true_eq]; right; rw [← hy']; exact h1
        rw [if_pos (show χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U from ⟨hχ1, F2 y h1⟩)]
        rw [isHit_iff] at hy
        rw [if_pos (by rw [← hy])]
        omega
    · rw [(hcond.2 y hy).2, if_neg]
      intro h
      split_ifs at h with h2
      · exact hy (PSt.P.inj h).symm

/-- **The ghost operation on an encoded state** is a sum over the local choices. -/
lemma ghost_sum (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hB : P.gPrimes.card ≤ P.B) {t : ℕ} {z : ℤ × ℤ} (hz : z ∈ P.zSet) {ℓ : P.Lst}
    {st : ℕ → PSt} (hv : Valid P ℓ st) (X : P.MState × Finset ℕ → ℂ) :
    P.ghostOpD t X (enc P z ℓ st) = ∑ χ ∈ Fintype.piFinset (gS P z st),
      (∏ p : GP P, gW P t z (gi P p) p.1 (st p.1) (χ p)) * X (enc P z ℓ (stG P z st χ)) := by
  classical
  -- the value of a ghost term at an encoded choice
  have hval : ∀ χ ∈ Fintype.piFinset (gS P z st),
      (if (P.bornPrimes (encMem P (stB P z st χ))).Nodup ∧
          ∀ p ∈ P.bornPrimes (encMem P (stB P z st χ)), p ∉ (enc P z ℓ st).2 then
        P.ghostCoeff t (enc P z ℓ st).1 (encMem P (stD P st χ), encMem P (stB P z st χ)) *
          (if P.ghostOut (enc P z ℓ st).1 (encMem P (stD P st χ), encMem P (stB P z st χ)) ∈
              P.stSet then
            X (P.ghostOut (enc P z ℓ st).1 (encMem P (stD P st χ), encMem P (stB P z st χ)),
              (enc P z ℓ st).2 ∪ (P.bornPrimes (encMem P (stB P z st χ))).toFinset) else 0)
        else 0) =
      (∏ p : GP P, gW P t z (gi P p) p.1 (st p.1) (χ p)) * X (enc P z ℓ (stG P z st χ)) := by
    intro χ hχ
    have hfr : ∀ p ∈ P.bornPrimes (encMem P (stB P z st χ)), p ∉ (enc P z ℓ st).2 := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := (mem_bornPrimes P _ _).1 hp
      have hq := y_gp P y
      have hst : stB P z st χ y.1.2.1 = PSt.P y.1.2.2 := by
        unfold encMem at hy; by_contra h; exact hy (if_neg h)
      rw [stB_of_mem P z st χ hq] at hst
      have h1 : χ ⟨_, hq⟩ = true ∧ st y.1.2.1 = PSt.U := by
        by_contra h; rw [if_neg h] at hst; cases hst
      simp only [enc, encBorn, mem_filter, not_and, not_not]
      exact fun _ => h1.2
    have hout : P.ghostOut (enc P z ℓ st).1 (encMem P (stD P st χ), encMem P (stB P z st χ)) =
        (z, ℓ, encMem P (stG P z st χ)) := by
      unfold MemParams.ghostOut enc
      simp only
      rw [← ghost_mem P hχ]
    have hst : (z, ℓ, encMem P (stG P z st χ)) ∈ P.stSet :=
      enc_mem_stSet P hdisj hB hz hv.lc _
    have hc1 : (P.bornPrimes (encMem P (stB P z st χ))).Nodup ∧
        ∀ p ∈ P.bornPrimes (encMem P (stB P z st χ)), p ∉ (enc P z ℓ st).2 :=
      ⟨nodup_bornPrimes_enc P hdisj _, hfr⟩
    rw [if_pos hc1, hout, if_pos hst]
    simp only [enc]
    rw [ghost_coeff P hdisj hχ, ghost_born P hdisj]
  unfold MemParams.ghostOpD
  symm
  refine sum_bij_ne_zero (fun χ _ _ => (encMem P (stD P st χ), encMem P (stB P z st χ)))
    (fun χ _ _ => ?_) (fun χ₁ h₁ _ χ₂ h₂ _ he => ?_) (fun c hc hne => ?_)
    (fun χ hχ _ => (hval χ hχ).symm)
  · unfold MemParams.ghostChoices
    exact mem_product.2 ⟨encMem_mem P hdisj _ hB, encMem_mem P hdisj _ hB⟩
  · funext p
    have e1 := recover P hdisj h₁ p
    have e2 := recover P hdisj h₂ p
    rw [Prod.mk.injEq] at he
    rw [he.1, he.2] at e1
    rw [e1] at e2
    cases h : χ₁ p <;> cases h' : χ₂ p <;> simp_all
  · have h1 : (P.bornPrimes c.2).Nodup ∧ ∀ p ∈ P.bornPrimes c.2, p ∉ (enc P z ℓ st).2 := by
      by_contra h; exact hne (if_neg h)
    have hgc : P.ghostCoeff t (enc P z ℓ st).1 c ≠ 0 := by
      intro h; apply hne; rw [if_pos h1, h, zero_mul]
    obtain ⟨χ, hχ, rfl⟩ := ghost_decode P hdisj c h1.1 h1.2 hgc
    exact ⟨χ, hχ, by rw [← hval χ hχ]; exact hne, rfl⟩

lemma pfT_eq {t p : ℕ} {z : ℤ × ℤ} {ℓ : P.Lst} {s : PSt} (hact : s = PSt.A ↔ ∃ i k, ℓ i k = p)
    (o : Option ℕ) : ((pfT P t p (z, ℓ) o : ℝ) : ℂ) =
      ((if s = PSt.A then (if o = some (lineOf p z) then 1 else 0)
        else (if o = some (lineOf p z) then P.qv t else 1) : ℝ) : ℂ) := by
  unfold pfT
  by_cases ha : s = PSt.A
  · rw [if_pos (hact.1 ha), if_pos ha]
  · rw [if_neg (fun h => ha (hact.2 h)), if_neg ha]

/-- **The ghost step.** If after the ghost the function is the type expansion with the
coefficients `cg`, then before the ghost it is the type expansion with `cf` times the visit
factor of each type. -/
theorem ghost_step (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hB : P.gPrimes.card ≤ P.B) {t : ℕ} (ht : t ≤ P.N) {z : ℤ × ℤ} (hz : z ∈ P.zSet)
    {ℓ : P.Lst} {st : ℕ → PSt} (hv : Valid P ℓ st) (X : P.MState × Finset ℕ → ℂ)
    (H : (GP P → Option ℕ) → ℂ)
    (hX : ∀ st', Valid P ℓ st' → X (enc P z ℓ st') =
      ∑ τ ∈ Fintype.piFinset (tyS P), (∏ p : GP P, cg P t z p.1 (st' p.1) (τ p)) * H τ) :
    P.ghostOpD t X (enc P z ℓ st) = ∑ τ ∈ Fintype.piFinset (tyS P),
      (∏ p : GP P, cf P t z p.1 (st p.1) (τ p)) *
        ((P.visitFac (dT P τ) t (z, ℓ) : ℝ) : ℂ) * H τ := by
  classical
  rw [ghost_sum P hdisj hB hz hv X]
  rw [sum_congr rfl fun χ hχ => by rw [hX _ (valid_stG P hv hχ), mul_sum]]
  rw [sum_comm]
  refine sum_congr rfl fun τ _ => ?_
  have e1 : ∀ χ : GP P → Bool,
      (∏ p : GP P, gW P t z (gi P p) p.1 (st p.1) (χ p)) *
        ((∏ p : GP P, cg P t z p.1 (stG P z st χ p.1) (τ p)) * H τ) =
      (∏ p : GP P, (gW P t z (gi P p) p.1 (st p.1) (χ p) *
        cg P t z p.1 (gNew z p.1 (st p.1) (χ p)) (τ p))) * H τ := by
    intro χ
    rw [← mul_assoc, ← prod_mul_distrib]
    congr 2
    funext p
    rw [stG_gp]
  simp_rw [e1]
  rw [← sum_mul, ← prod_univ_sum (t := gS P z st) (f := fun p b =>
    gW P t z (gi P p) p.1 (st p.1) b * cg P t z p.1 (gNew z p.1 (st p.1) b) (τ p)),
    visitFac_dT, Complex.ofReal_prod, ← prod_mul_distrib]
  congr 1
  refine prod_congr rfl fun p _ => ?_
  have hloc := ghost_local P t ht z (gi P p) p.1 (hV _) (hb p.1 p.2) (st p.1)
    (st p.1 = PSt.A) Iff.rfl (τ p)
  rw [pfT_eq P (hv.act p.1 p.2), ← hloc]
  unfold gS
  by_cases hg : gAct z p.1 (st p.1)
  · rw [if_pos hg, if_pos hg, Fintype.sum_bool]
  · rw [if_neg hg, if_neg hg, sum_singleton]
    unfold gW gNew
    have h1 : st p.1 ≠ PSt.U := fun h => hg (Or.inl h)
    have h2 : st p.1 ≠ PSt.P (lineOf p.1 z) := fun h => hg (Or.inr h)
    simp [h1, h2]

end Step

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: the edge step of the memory identity

Along an edge `z → z'` with source lists `ℓ` and new last labels `nw`, the memory choices are a
store bit for each source last label and a promotion bit for each new label. On encoded states
the edge coefficient factors over the group primes, and the local sums reproduce the
coefficients `cg` of the source (`edge_local`); the factor `∏ᵢ Vᵢ⁻¹` of the physical edge is
distributed over the new labels. -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

section Lists

variable (P : MemParams)

lemma newList_last (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K) :
    P.newList ℓ nw i (Fin.last P.J) = nw i := by
  simp [MemParams.newList]

lemma newList_castSucc (ℓ : P.Lst) (nw : Fin P.K → ℕ) (i : Fin P.K) (k : Fin P.J) :
    P.newList ℓ nw i k.castSucc = ℓ i k.castSucc := by
  simp [MemParams.newList]

/-- An entry of the source list other than a last label is a pad. -/
lemma pad_of_not_last {k : Fin (P.J + 1)} (hk : k ≠ Fin.last P.J) :
    ∃ j : Fin P.J, k = j.castSucc := by
  induction k using Fin.lastCases with
  | last => exact absurd rfl hk
  | cast j => exact ⟨j, rfl⟩

lemma dvd_padProd (ℓ : P.Lst) (i : Fin P.K) (j : Fin P.J) : ℓ i j.castSucc ∣ padProd ℓ := by
  unfold padProd
  exact (dvd_prod_of_mem (fun j : Fin P.J => ℓ i j.castSucc) (mem_univ j)).trans
    (dvd_prod_of_mem (fun i => ∏ j : Fin P.J, ℓ i j.castSucc) (mem_univ i))

end Lists

section EdgeCtx

variable (P : MemParams)

/-- The prime `q` is the last label of its group in `ℓ`. -/
def isLast (ℓ : P.Lst) (q : GP P) : Prop := ℓ (gi P q) (Fin.last P.J) = q.1

/-- The prime `q` is the new label of its group. -/
def isNew (nw : Fin P.K → ℕ) (q : GP P) : Prop := nw (gi P q) = q.1

noncomputable instance (ℓ : P.Lst) (q : GP P) : Decidable (isLast P ℓ q) :=
  inferInstanceAs (Decidable (_ = _))

noncomputable instance (nw : Fin P.K → ℕ) (q : GP P) : Decidable (isNew P nw q) :=
  inferInstanceAs (Decidable (_ = _))

/-- The status after the edge, given the local bit `b` (store bit for a last label). -/
noncomputable def eNew (z : ℤ × ℤ) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (st : ℕ → PSt) (q : GP P) (b : Bool) :
    PSt :=
  if isLast P ℓ q then (if b then PSt.P (lineOf q.1 z) else PSt.D)
  else if isNew P nw q then PSt.A else st q.1

/-- The statuses after the edge with stored groups `St`. -/
noncomputable def stE (z : ℤ × ℤ) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (st : ℕ → PSt)
    (St : Finset (Fin P.K)) : ℕ → PSt :=
  fun q => if h : q ∈ P.gPrimes then eNew P z ℓ nw st ⟨q, h⟩ (decide (gi P ⟨q, h⟩ ∈ St))
    else st q

/-- The local bits of the memory choices `(St, fl)`. -/
noncomputable def chiE (ℓ : P.Lst) (nw : Fin P.K → ℕ) (St : Finset (Fin P.K))
    (fl : Fin P.K → Bool) (q : GP P) : Bool :=
  if isLast P ℓ q then decide (gi P q ∈ St) else if isNew P nw q then fl (gi P q) else false

/-- Allowed local edge bits. -/
noncomputable def eS (ℓ : P.Lst) (nw : Fin P.K → ℕ) (q : GP P) : Finset Bool :=
  if isLast P ℓ q ∨ isNew P nw q then univ else {false}

/-- The local edge weight (without the type coefficient). -/
noncomputable def wE (z z' : ℤ × ℤ) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (st : ℕ → PSt)
    (q : GP P) (b : Bool) : ℂ :=
  (if st q.1 = PSt.P (lineOf q.1 z) then ((memRho : ℝ) : ℂ) else 1) *
    (if eNew P z ℓ nw st q b = PSt.P (lineOf q.1 z') then ((memRho : ℝ) : ℂ) else 1) *
    (if isLast P ℓ q then 1 else if isNew P nw q then
      (if b then (if st q.1 = PSt.P (lineOf q.1 z') then (((P.Vg (gi P q))⁻¹ : ℝ) : ℂ) else 0)
        else (if st q.1 = PSt.U then ((P.nu (gi P q) q.1 : ℝ) : ℂ) else 0))
      else 1)

/-- The facts of the edge that the identity uses. -/
structure EdgeFacts (z z' : ℤ × ℤ) (ℓ : P.Lst) (nw : Fin P.K → ℕ) (st : ℕ → PSt) : Prop where
  hv : Valid P ℓ st
  hz : Int.gcd z.1 z.2 = 1
  hz' : Int.gcd z'.1 z'.2 = 1
  inj : ∀ i, Function.Injective (ℓ i)
  ban : ∀ i, nw i ∉ Set.range (ℓ i)
  nwg : ∀ i, nw i ∈ P.grp i
  dvd : (padProd ℓ : ℤ) ∣ detZ z z'

variable (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
variable {z z' : ℤ × ℤ} {ℓ : P.Lst} {nw : Fin P.K → ℕ} {st : ℕ → PSt}

/-- The last label of group `i`, as a group prime. -/
def lastG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : GP P :=
  ⟨ℓ i (Fin.last P.J), mem_gPrimes_of_grp P (hE.hv.lc i _)⟩

/-- The new label of group `i`, as a group prime. -/
def newG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : GP P :=
  ⟨nw i, mem_gPrimes_of_grp P (hE.nwg i)⟩

include hdisj

lemma gi_lastG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : gi P (lastG P hE i) = i :=
  gi_eq P hdisj (hE.hv.lc i _)

lemma gi_newG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : gi P (newG P hE i) = i :=
  gi_eq P hdisj (hE.nwg i)

lemma isLast_lastG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) :
    isLast P ℓ (lastG P hE i) := by
  unfold isLast; rw [gi_lastG P hdisj hE]; rfl

lemma isNew_newG (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : isNew P nw (newG P hE i) := by
  unfold isNew; rw [gi_newG P hdisj hE]; rfl

omit hdisj in
lemma not_isLast_of_isNew (hE : EdgeFacts P z z' ℓ nw st) {q : GP P} (h : isNew P nw q) :
    ¬ isLast P ℓ q := by
  unfold isNew at h; unfold isLast
  intro h'
  exact hE.ban (gi P q) ⟨Fin.last P.J, h'.trans h.symm⟩

lemma st_ne_A_of_isNew (hE : EdgeFacts P z z' ℓ nw st) {q : GP P} (h : isNew P nw q) :
    st q.1 ≠ PSt.A := by
  intro hA
  obtain ⟨i, k, hk⟩ := (hE.hv.act q.1 q.2).1 hA
  have hgi : gi P q = i := gi_eq P hdisj (hk ▸ hE.hv.lc i k)
  unfold isNew at h
  rw [hgi] at h
  exact hE.ban i ⟨k, hk.trans h.symm⟩

lemma isLast_iff_lastG (hE : EdgeFacts P z z' ℓ nw st) (q : GP P) :
    isLast P ℓ q ↔ q = lastG P hE (gi P q) := by
  unfold isLast lastG
  constructor
  · intro h; exact Subtype.ext h.symm
  · intro h; exact (congrArg Subtype.val h).symm

lemma isNew_iff_newG (hE : EdgeFacts P z z' ℓ nw st) (q : GP P) :
    isNew P nw q ↔ q = newG P hE (gi P q) := by
  unfold isNew newG
  constructor
  · intro h; exact Subtype.ext h.symm
  · intro h; exact (congrArg Subtype.val h).symm

/-- An active prime that is not a last label is a pad; it keeps its line along the edge. -/
lemma pad_of_active (hE : EdgeFacts P z z' ℓ nw st) {q : GP P} (hA : st q.1 = PSt.A)
    (hL : ¬ isLast P ℓ q) :
    (∃ i, ∃ j : Fin P.J, ℓ i j.castSucc = q.1) ∧ lineOf q.1 z = lineOf q.1 z' := by
  obtain ⟨i, k, hk⟩ := (hE.hv.act q.1 q.2).1 hA
  have hi : gi P q = i := gi_eq P hdisj (hk ▸ hE.hv.lc i k)
  have hk' : k ≠ Fin.last P.J := by
    intro h; apply hL; unfold isLast; rw [hi, ← h, hk]
  obtain ⟨j, rfl⟩ := pad_of_not_last P hk'
  refine ⟨⟨i, j, hk⟩, ?_⟩
  apply lineOf_eq_of_dvd (prime_of_gPrimes P q.2) hE.hz hE.hz'
  have h1 : (q.1 : ℤ) ∣ (padProd ℓ : ℤ) := by
    rw [← hk]; exact_mod_cast dvd_padProd P ℓ i j
  exact h1.trans hE.dvd

omit hdisj in
lemma st_last (hE : EdgeFacts P z z' ℓ nw st) {q : GP P} (h : isLast P ℓ q) : st q.1 = PSt.A :=
  (hE.hv.act q.1 q.2).2 ⟨gi P q, Fin.last P.J, h⟩

/-- **The local edge identity.** -/
lemma edge_local (hE : EdgeFacts P z z' ℓ nw st) (t : ℕ) (q : GP P)
    (hbp : P.bprime q.1 ≠ 0) (hVi : P.Vg (gi P q) ≠ 0) (o : Option ℕ)
    (hH : (∃ i k, P.newList ℓ nw i k = q.1) → o = some (lineOf q.1 z')) :
    ∑ b ∈ eS P ℓ nw q, wE P z z' ℓ nw st q b * cf P (t + 1) z' q.1 (eNew P z ℓ nw st q b) o =
      cg P t z q.1 (st q.1) o *
        (if isNew P nw q then (((P.Vg (gi P q))⁻¹ : ℝ) : ℂ) else 1) := by
  have hρ : ((memRho : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 memRho_ne
  by_cases hL : isLast P ℓ q
  · -- a last label: drop or store
    have hN : ¬ isNew P nw q := fun h => not_isLast_of_isNew P hE h hL
    have hA := st_last P hE hL
    unfold eS wE eNew
    simp only [hL, hN, true_or, if_true, if_false, Fintype.sum_bool, hA, reduceCtorEq, mul_one,
      cf, cg, one_mul, Bool.false_eq_true]
    by_cases he : lineOf q.1 z = lineOf q.1 z'
    · simp only [he, if_true, PSt.P.injEq]
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ memRho_ne]
      simp
    · simp only [PSt.P.injEq, he, if_false, one_mul]
      simp
  · by_cases hN : isNew P nw q
    · -- a new label: fresh or promoted
      have hA := st_ne_A_of_isNew P hdisj hE hN
      have ho : o = some (lineOf q.1 z') := by
        apply hH
        refine ⟨gi P q, Fin.last P.J, ?_⟩
        rw [newList_last]; exact hN
      subst ho
      unfold eS wE eNew
      simp only [hL, hN, or_true, if_true, if_false, Fintype.sum_bool, reduceCtorEq, mul_one,
        cf, one_mul, Bool.false_eq_true]
      rcases hs : st q.1 with _ | _ | L | _
      · simp only [reduceCtorEq, if_false, if_true, cg, cU, zero_add, one_mul, Option.some_ne_none]
        unfold MemParams.nu
        push_cast
        field_simp
      · exact absurd hs hA
      · simp only [PSt.P.injEq, cg, Option.some.injEq, reduceCtorEq, if_false, sub_zero,
          add_zero, mul_one]
        by_cases h1 : L = lineOf q.1 z'
        · subst h1; simp
        · rw [if_neg h1, if_neg (Ne.symm h1)]; simp
      · simp [cg]
    · -- neither: the status is unchanged
      unfold eS wE eNew
      simp only [hL, hN, or_self, if_false, sum_singleton, mul_one]
      rcases hs : st q.1 with _ | _ | L | _
      · simp [cf, cg]
      · obtain ⟨hpad, hline⟩ := pad_of_active P hdisj hE hs hL
        obtain ⟨i, j, hj⟩ := hpad
        have ho : o = some (lineOf q.1 z') := by
          apply hH
          exact ⟨i, j.castSucc, by rw [newList_castSucc]; exact hj⟩
        subst ho
        simp [cf, cg, hline]
      · simp only [PSt.P.injEq, cf, cg]
        by_cases h1 : L = lineOf q.1 z'
        · rw [if_pos h1, if_pos h1, ← mul_assoc, mul_assoc _ ((memRho : ℝ) : ℂ),
            ← Complex.ofReal_mul, mul_inv_cancel₀ memRho_ne]
          simp
        · rw [if_neg h1, if_neg h1]; simp
      · simp [cf, cg]

end EdgeCtx

section EdgeMem

variable (P : MemParams)

lemma promCount_eq (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) (fl : Fin P.K → Bool) (y : P.PT) :
    P.promCount z' (fun i => (nw i, fl i)) y =
      if fl y.1.1 = true ∧ nw y.1.1 = y.1.2.1 ∧ lineOf y.1.2.1 z' = y.1.2.2 then 1 else 0 := by
  classical
  unfold MemParams.promCount MemParams.promPart
  obtain ⟨⟨i, p, L⟩, hy⟩ := y
  simp only
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨i, ?_⟩
    ext i'
    simp only [mem_filter, mem_univ, true_and, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨_, rfl, _, _⟩; rfl
    · rintro rfl; exact ⟨h.1, rfl, h.2.1, h.2.1 ▸ h.2.2⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro i' - ⟨h1, h2⟩
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, h3, h4⟩ := h2
    exact h ⟨h1, h3, h3 ▸ h4⟩

lemma storeCount_eq (z : ℤ × ℤ) (ℓ : P.Lst) (St : Finset (Fin P.K)) (y : P.PT) :
    P.storeCount z ℓ St y =
      if y.1.1 ∈ St ∧ ℓ y.1.1 (Fin.last P.J) = y.1.2.1 ∧ lineOf y.1.2.1 z = y.1.2.2 then 1
      else 0 := by
  classical
  unfold MemParams.storeCount MemParams.storedPart
  obtain ⟨⟨i, p, L⟩, hy⟩ := y
  simp only
  split_ifs with h
  · rw [card_eq_one]
    refine ⟨i, ?_⟩
    ext i'
    simp only [mem_filter, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨_, rfl, _, _⟩; rfl
    · rintro rfl; exact ⟨h.1, rfl, h.2.1, h.2.1 ▸ h.2.2⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro i' hi' h2
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, h3, h4⟩ := h2
    exact h ⟨hi', h3, h3 ▸ h4⟩

variable (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
variable {z z' : ℤ × ℤ} {ℓ : P.Lst} {nw : Fin P.K → ℕ} {st : ℕ → PSt}

/-- The memory choices are admissible: promoted labels are pending at the target line, fresh
labels are unborn. -/
def EOk (z' : ℤ × ℤ) (nw : Fin P.K → ℕ) (st : ℕ → PSt) (fl : Fin P.K → Bool) : Prop :=
  ∀ i, (fl i = true → st (nw i) = PSt.P (lineOf (nw i) z')) ∧ (fl i = false → st (nw i) = PSt.U)

include hdisj

lemma stE_gp (St : Finset (Fin P.K)) (fl : Fin P.K → Bool) (q : GP P) :
    stE P z ℓ nw st St q.1 = eNew P z ℓ nw st q (chiE P ℓ nw St fl q) := by
  unfold stE chiE eNew
  rw [dif_pos q.2]
  by_cases hL : isLast P ℓ q
  · simp [hL]
  · simp [hL]

lemma gi_of_y (y : P.PT) : gi P ⟨y.1.2.1, y_gp P y⟩ = y.1.1 :=
  gi_eq P hdisj ((mem_partSet P).1 y.2).1

/-- The memory after the edge. -/
lemma edgeOutMem_eq (hE : EdgeFacts P z z' ℓ nw st) (St : Finset (Fin P.K))
    (fl : Fin P.K → Bool) (hok : EOk P z' nw st fl) :
    P.edgeOutMem (z, ℓ, encMem P st) (St, z', fun i => (nw i, fl i)) =
      encMem P (stE P z ℓ nw st St) := by
  funext y
  unfold MemParams.edgeOutMem
  simp only
  rw [promCount_eq, storeCount_eq]
  have hq := y_gp P y
  have hgi : gi P ⟨y.1.2.1, hq⟩ = y.1.1 := gi_of_y P hdisj y
  have e := stE_gp P hdisj (z := z) (ℓ := ℓ) (nw := nw) (st := st) St fl ⟨y.1.2.1, hq⟩
  unfold encMem
  rw [e]
  unfold eNew chiE isLast isNew
  simp only [hgi]
  by_cases hL : ℓ y.1.1 (Fin.last P.J) = y.1.2.1
  · have hA : st y.1.2.1 = PSt.A := (hE.hv.act _ hq).2 ⟨_, _, hL⟩
    have hN : nw y.1.1 ≠ y.1.2.1 := fun h => hE.ban y.1.1 ⟨_, hL.trans h.symm⟩
    simp only [hL, if_true, hA, reduceCtorEq, if_false, hN, false_and, and_false,
      Nat.zero_sub, zero_add, true_and]
    by_cases hS : y.1.1 ∈ St
    · simp only [hS, decide_true, if_true, PSt.P.injEq, true_and]
    · simp [hS]
  · simp only [hL, if_false, false_and, and_false, add_zero]
    by_cases hN : nw y.1.1 = y.1.2.1
    · simp only [hN, if_true, true_and, reduceCtorEq]
      have h1 := hok y.1.1
      rw [hN] at h1
      cases hf : fl y.1.1
      · rw [h1.2 hf]; simp
      · rw [h1.1 hf]
        simp only [PSt.P.injEq, if_true, true_and, if_false]
        split_ifs <;> omega
    · simp [hN]

lemma newG_injective (hE : EdgeFacts P z z' ℓ nw st) : Function.Injective (newG P hE) := by
  intro i j h
  have := congrArg Subtype.val h
  simp only [newG] at this
  by_contra hne
  exact disjoint_left.1 (hdisj _ _ hne) (hE.nwg i) (this ▸ hE.nwg j)

lemma nw_injective (hE : EdgeFacts P z z' ℓ nw st) : Function.Injective nw := by
  intro i j h
  by_contra hne
  exact disjoint_left.1 (hdisj _ _ hne) (hE.nwg i) (h ▸ hE.nwg j)

/-- A product over group primes that is trivial off the new labels. -/
lemma prod_over_new (hE : EdgeFacts P z z' ℓ nw st) {M : Type*} [CommMonoid M] (g : GP P → M)
    (hg : ∀ q, ¬ isNew P nw q → g q = 1) : ∏ q, g q = ∏ i, g (newG P hE i) := by
  classical
  rw [← prod_image (fun i _ j _ h => newG_injective P hdisj hE h)]
  refine (prod_subset (subset_univ _) fun q _ hq => hg q fun h => hq ?_).symm
  rw [isNew_iff_newG P hdisj hE] at h
  exact mem_image.2 ⟨gi P q, mem_univ _, h.symm⟩

omit hdisj in
lemma mem_freshPrimes (nw : Fin P.K → ℕ) (fl : Fin P.K → Bool) (p : ℕ) :
    p ∈ P.freshPrimes (fun i => (nw i, fl i)) ↔ ∃ i, fl i = false ∧ nw i = p := by
  unfold MemParams.freshPrimes
  simp

lemma fresh_ok (hE : EdgeFacts P z z' ℓ nw st) (fl : Fin P.K → Bool) (hok : EOk P z' nw st fl) :
    (P.freshPrimes (fun i => (nw i, fl i))).Nodup ∧
      ∀ p ∈ P.freshPrimes (fun i => (nw i, fl i)), p ∉ encBorn P st := by
  refine ⟨?_, fun p hp => ?_⟩
  · unfold MemParams.freshPrimes
    refine List.Nodup.map_on (fun i _ j _ h => nw_injective P hdisj hE h) ?_
    exact (List.nodup_finRange P.K).filter _
  · obtain ⟨i, hi, rfl⟩ := (mem_freshPrimes P nw fl p).1 hp
    simp only [encBorn, mem_filter, not_and, not_not]
    exact fun _ => (hok i).2 hi

lemma born_eq (hE : EdgeFacts P z z' ℓ nw st) (St : Finset (Fin P.K)) (fl : Fin P.K → Bool)
    (hok : EOk P z' nw st fl) :
    encBorn P st ∪ (P.freshPrimes (fun i => (nw i, fl i))).toFinset =
      encBorn P (stE P z ℓ nw st St) := by
  ext q
  simp only [mem_union, List.mem_toFinset, mem_freshPrimes, encBorn, mem_filter]
  by_cases hq : q ∈ P.gPrimes
  · have e := stE_gp P hdisj (z := z) (ℓ := ℓ) (nw := nw) (st := st) St fl ⟨q, hq⟩
    simp only at e
    rw [e]
    unfold eNew
    by_cases hL : isLast P ℓ ⟨q, hq⟩
    · have hA := st_last P hE hL
      simp only [hL, if_true]
      constructor
      · intro _; refine ⟨hq, ?_⟩; split_ifs <;> simp
      · intro _; left; exact ⟨hq, by rw [hA]; simp⟩
    · simp only [hL, if_false]
      by_cases hN : isNew P nw ⟨q, hq⟩
      · simp only [hN, if_true]
        constructor
        · intro _; exact ⟨hq, by simp⟩
        · intro _
          have h1 := hok (gi P ⟨q, hq⟩)
          unfold isNew at hN
          simp only at hN
          rw [hN] at h1
          cases hf : fl (gi P ⟨q, hq⟩)
          · right; exact ⟨_, hf, hN⟩
          · left; exact ⟨hq, by rw [h1.1 hf]; simp⟩
      · simp only [hN, if_false]
        constructor
        · rintro (h | ⟨i, _, rfl⟩)
          · exact h
          · exfalso; apply hN
            unfold isNew; simp only
            rw [gi_eq P hdisj (hE.nwg i)]
        · intro h; left; exact h
  · constructor
    · rintro (h | ⟨i, _, rfl⟩)
      · exact absurd h.1 hq
      · exact absurd (mem_gPrimes_of_grp P (hE.nwg i)) hq
    · intro h; exact absurd h.1 hq

lemma valid_stE (hE : EdgeFacts P z z' ℓ nw st) (St : Finset (Fin P.K)) :
    Valid P (P.newList ℓ nw) (stE P z ℓ nw st St) := by
  refine ⟨fun i k => ?_, fun q hq => ?_, fun q hq L hL => ?_⟩
  · induction k using Fin.lastCases with
    | last => rw [newList_last]; exact hE.nwg i
    | cast j => rw [newList_castSucc]; exact hE.hv.lc i _
  · have e := stE_gp P hdisj (z := z) (ℓ := ℓ) (nw := nw) (st := st) St (fun _ => false) ⟨q, hq⟩
    simp only at e
    rw [e]
    unfold eNew
    have hgq : ∀ i, q ∈ P.grp i → gi P ⟨q, hq⟩ = i := fun i h => gi_eq P hdisj h
    by_cases hL : isLast P ℓ ⟨q, hq⟩
    · simp only [hL, if_true]
      constructor
      · intro h; split_ifs at h
      · rintro ⟨i, k, hk⟩
        exfalso
        unfold isLast at hL; simp only at hL
        induction k using Fin.lastCases with
        | last =>
          rw [newList_last] at hk
          have := hgq i (hk ▸ hE.nwg i)
          rw [this] at hL
          exact hE.ban i ⟨_, hL.trans hk.symm⟩
        | cast j =>
          rw [newList_castSucc] at hk
          have := hgq i (hk ▸ hE.hv.lc i _)
          rw [this] at hL
          exact absurd (hE.inj i (hL.trans hk.symm)) (Fin.castSucc_lt_last j).ne'
    · simp only [hL, if_false]
      by_cases hN : isNew P nw ⟨q, hq⟩
      · simp only [hN, if_true, true_iff]
        exact ⟨gi P ⟨q, hq⟩, Fin.last P.J, by rw [newList_last]; exact hN⟩
      · simp only [hN, if_false]
        rw [hE.hv.act q hq]
        constructor
        · rintro ⟨i, k, hk⟩
          have hi := hgq i (hk ▸ hE.hv.lc i k)
          have hk' : k ≠ Fin.last P.J := by
            intro h; apply hL; unfold isLast; simp only; rw [hi, ← h, hk]
          obtain ⟨j, rfl⟩ := pad_of_not_last P hk'
          exact ⟨i, j.castSucc, by rw [newList_castSucc]; exact hk⟩
        · rintro ⟨i, k, hk⟩
          induction k using Fin.lastCases with
          | last =>
            rw [newList_last] at hk
            exfalso; apply hN; unfold isNew; simp only
            rw [hgq i (hk ▸ hE.nwg i)]; exact hk
          | cast j =>
            rw [newList_castSucc] at hk
            exact ⟨i, _, hk⟩
  · have e := stE_gp P hdisj (z := z) (ℓ := ℓ) (nw := nw) (st := st) St (fun _ => false) ⟨q, hq⟩
    simp only at e
    rw [e] at hL
    unfold eNew at hL
    split_ifs at hL with h1 h2 h3
    · cases hL; exact lineOf_lt (pos_of_gPrimes P hq) z
    · exact hE.hv.pend q hq L hL

lemma rho_pow_hit (z : ℤ × ℤ) (st : ℕ → PSt) :
    ((memRho : ℝ) : ℂ) ^ P.hitCount z (encMem P st) =
      ∏ q : GP P, (if st q.1 = PSt.P (lineOf q.1 z) then ((memRho : ℝ) : ℂ) else 1) := by
  rw [hitCount_enc P hdisj, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun q _ => ?_
  split_ifs <;> simp

lemma memAt_enc (st : ℕ → PSt) {i : Fin P.K} {p : ℕ} (hp : p ∈ P.grp i) (L : ℕ)
    (hL : L < p + 1) :
    P.memAt (encMem P st) (i, p, L) = if st p = PSt.P L then 1 else 0 := by
  have hm : (i, p, L) ∈ P.partSet := (mem_partSet P (y := (i, p, L))).2 ⟨hp, hL⟩
  unfold MemParams.memAt
  rw [dif_pos hm]
  rfl

/-- **The edge coefficient on an encoded state** with admissible memory choices. -/
lemma edgeCoeff_eq (hE : EdgeFacts P z z' ℓ nw st) {ω : ℝ × ℝ × ℝ} {t : ℕ}
    (hEOK : P.EdgeOK ω z z' ℓ nw) (St : Finset (Fin P.K)) (fl : Fin P.K → Bool)
    (hok : EOk P z' nw st fl) :
    P.edgeCoeff ω t (z, ℓ, encMem P st) (St, z', fun i => (nw i, fl i)) =
      (∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q)) *
        P.edgeMult t (detZ z z' / padProd ℓ) (∏ i, nw i) (lastProd ℓ) (padProd ℓ) := by
  have hcond : P.EdgeOK ω z z' ℓ (fun i => (nw i, fl i).1) ∧
      (∀ i, (nw i, fl i).2 = true → P.promPart z' (fun i => (nw i, fl i)) i ∈ P.partSet) ∧
      (∀ i ∈ St, P.storedPart z ℓ i ∈ P.partSet) ∧
      (∀ y, P.promCount z' (fun i => (nw i, fl i)) y ≤ encMem P st y) := by
    refine ⟨hEOK, fun i _ => (mem_partSet P).2 ⟨hE.nwg i, lineOf_lt (prime_of_grp P (hE.nwg i)).pos _⟩,
      fun i _ => (mem_partSet P).2
        ⟨hE.hv.lc i _, lineOf_lt (prime_of_grp P (hE.hv.lc i _)).pos _⟩, fun y => ?_⟩
    rw [promCount_eq]
    split_ifs with h
    · obtain ⟨h1, h2, h3⟩ := h
      have := (hok y.1.1).1 h1
      rw [h2] at this
      unfold encMem; rw [if_pos (by rw [this, h3])]
    · exact Nat.zero_le _
  have hC : ∏ i, ((if fl i = true then
        ((P.memAt (encMem P st) (P.promPart z' (fun i => (nw i, fl i)) i) : ℝ) / P.Vg i)
        else P.nu i (nw i) : ℝ) : ℂ) =
      ∏ q, (if isLast P ℓ q then 1 else if isNew P nw q then
        (if chiE P ℓ nw St fl q then
          (if st q.1 = PSt.P (lineOf q.1 z') then (((P.Vg (gi P q))⁻¹ : ℝ) : ℂ) else 0)
        else (if st q.1 = PSt.U then ((P.nu (gi P q) q.1 : ℝ) : ℂ) else 0)) else 1) := by
    rw [prod_over_new P hdisj hE]
    · refine prod_congr rfl fun i _ => ?_
      have hN := isNew_newG P hdisj hE i
      have hL := not_isLast_of_isNew P hE hN
      have hgi := gi_newG P hdisj hE i
      have hchi : chiE P ℓ nw St fl (newG P hE i) = fl i := by
        unfold chiE; rw [if_neg hL, if_pos hN, hgi]
      rw [if_neg hL, if_pos hN, hchi, hgi]
      have hnv : (newG P hE i).1 = nw i := rfl
      cases hf : fl i
      · simp [hnv, (hok i).2 hf]
      · rw [show P.promPart z' (fun i => (nw i, fl i)) i = (i, nw i, lineOf (nw i) z') from rfl,
          memAt_enc P hdisj st (hE.nwg i) _ (lineOf_lt (prime_of_grp P (hE.nwg i)).pos _)]
        simp [hnv, (hok i).1 hf, div_eq_mul_inv]
    · intro q hq
      rw [if_neg hq]; split_ifs <;> rfl
  have hB : ((memRho : ℝ) : ℂ) ^ P.hitCount z' (encMem P (stE P z ℓ nw st St)) =
      ∏ q, (if eNew P z ℓ nw st q (chiE P ℓ nw St fl q) = PSt.P (lineOf q.1 z') then
        ((memRho : ℝ) : ℂ) else 1) := by
    rw [rho_pow_hit P hdisj]
    refine prod_congr rfl fun q _ => ?_
    rw [stE_gp P hdisj St fl q]
  unfold MemParams.edgeCoeff
  rw [if_pos hcond]
  simp only
  rw [edgeOutMem_eq P hdisj hE St fl hok]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow,
    Complex.ofReal_prod, hC, rho_pow_hit P hdisj, hB]
  simp only [wE, prod_mul_distrib]
  ring

omit hdisj in
lemma newG_val (hE : EdgeFacts P z z' ℓ nw st) (i : Fin P.K) : (newG P hE i).1 = nw i := rfl

omit hdisj in
lemma not_EOk {fl : Fin P.K → Bool} (hok : ¬ EOk P z' nw st fl) :
    ∃ i, (fl i = true ∧ st (nw i) ≠ PSt.P (lineOf (nw i) z')) ∨
      (fl i = false ∧ st (nw i) ≠ PSt.U) := by
  by_contra h
  apply hok
  intro i
  constructor
  · intro hf; by_contra h'; exact h ⟨i, Or.inl ⟨hf, h'⟩⟩
  · intro hf; by_contra h'; exact h ⟨i, Or.inr ⟨hf, h'⟩⟩

/-- Inadmissible memory choices have zero local weight. -/
lemma prod_wE_eq_zero (hE : EdgeFacts P z z' ℓ nw st) (St : Finset (Fin P.K))
    (fl : Fin P.K → Bool) (hok : ¬ EOk P z' nw st fl) :
    ∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q) = 0 := by
  obtain ⟨i, hi⟩ := not_EOk P hok
  refine prod_eq_zero (mem_univ (newG P hE i)) ?_
  have hN := isNew_newG P hdisj hE i
  have hL := not_isLast_of_isNew P hE hN
  have hchi : chiE P ℓ nw St fl (newG P hE i) = fl i := by
    unfold chiE; rw [if_neg hL, if_pos hN, gi_newG P hdisj hE]
  unfold wE
  rw [if_neg hL, if_pos hN, hchi, newG_val]
  rcases hi with ⟨hf, h⟩ | ⟨hf, h⟩
  · simp [hf, h]
  · simp [hf, h]

/-- **One edge memory choice.** -/
lemma edge_term (hE : EdgeFacts P z z' ℓ nw st) {ω : ℝ × ℝ × ℝ} {t : ℕ}
    (hEOK : P.EdgeOK ω z z' ℓ nw) (hz' : z' ∈ P.zSet) (hB : P.gPrimes.card ≤ P.B)
    (G : P.MState × Finset ℕ → ℂ) (St : Finset (Fin P.K)) (fl : Fin P.K → Bool) :
    (if (P.freshPrimes (fun i => (nw i, fl i))).Nodup ∧
        ∀ p ∈ P.freshPrimes (fun i => (nw i, fl i)), p ∉ (enc P z ℓ st).2 then
      P.edgeCoeff ω t (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) *
        (if P.edgeOut (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) ∈ P.stSet then
          G (P.edgeOut (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)),
            (enc P z ℓ st).2 ∪ (P.freshPrimes (fun i => (nw i, fl i))).toFinset) else 0)
      else 0) =
    P.edgeMult t (detZ z z' / padProd ℓ) (∏ i, nw i) (lastProd ℓ) (padProd ℓ) *
      ((∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q)) *
        G (enc P z' (P.newList ℓ nw) (stE P z ℓ nw st St))) := by
  by_cases hok : EOk P z' nw st fl
  · have hout : P.edgeOut (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) =
        (z', P.newList ℓ nw, encMem P (stE P z ℓ nw st St)) := by
      unfold MemParams.edgeOut enc
      simp only
      rw [edgeOutMem_eq P hdisj hE St fl hok]
    have hmem : (z', P.newList ℓ nw, encMem P (stE P z ℓ nw st St)) ∈ P.stSet :=
      enc_mem_stSet P hdisj hB hz' (valid_stE P hdisj hE St).lc _
    have hfr := fresh_ok P hdisj hE fl hok
    rw [if_pos (show _ ∧ ∀ p ∈ _, p ∉ (enc P z ℓ st).2 from hfr), hout, if_pos hmem]
    simp only [enc]
    rw [edgeCoeff_eq P hdisj hE hEOK St fl hok, born_eq P hdisj hE St fl hok]
    ring
  · rw [prod_wE_eq_zero P hdisj hE St fl hok, zero_mul, mul_zero]
    obtain ⟨i, hi⟩ := not_EOk P hok
    rcases hi with ⟨hf, h⟩ | ⟨hf, h⟩
    swap
    · -- a fresh label that is already born
      rw [if_neg]
      rintro ⟨_, h2⟩
      apply h2 (nw i) ((mem_freshPrimes P nw fl _).2 ⟨i, hf, rfl⟩)
      simp only [enc, encBorn, mem_filter]
      exact ⟨mem_gPrimes_of_grp P (hE.nwg i), h⟩
    · -- a promotion of a particle that is not in memory
      have hm : (i, nw i, lineOf (nw i) z') ∈ P.partSet :=
        (mem_partSet P (y := (i, nw i, lineOf (nw i) z'))).2
          ⟨hE.nwg i, lineOf_lt (prime_of_grp P (hE.nwg i)).pos _⟩
      have hce : P.edgeCoeff ω t (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) = 0 := by
        unfold MemParams.edgeCoeff
        rw [if_neg]
        rintro ⟨_, _, _, h4⟩
        have := h4 ⟨_, hm⟩
        rw [promCount_eq] at this
        simp only [hf, true_and, if_true] at this
        unfold enc encMem at this
        simp only [h, if_false] at this
        omega
      rw [hce]
      simp

/-- The memory choices `(St, fl)` are the local bits of the last and new labels. -/
lemma sum_St_fl (hE : EdgeFacts P z z' ℓ nw st) (F : GP P → Bool → ℂ) :
    ∑ St : Finset (Fin P.K), ∑ fl : Fin P.K → Bool, ∏ q, F q (chiE P ℓ nw St fl q) =
      ∏ q, ∑ b ∈ eS P ℓ nw q, F q b := by
  classical
  rw [prod_univ_sum (t := eS P ℓ nw) (f := F), ← sum_product' (univ : Finset (Finset (Fin P.K)))
    (univ : Finset (Fin P.K → Bool)) (fun St fl => ∏ q, F q (chiE P ℓ nw St fl q))]
  refine sum_nbij' (fun x => chiE P ℓ nw x.1 x.2)
    (fun χ => (univ.filter (fun i => χ (lastG P hE i) = true), fun i => χ (newG P hE i)))
    (fun x _ => ?_) (fun χ _ => mem_product.2 ⟨mem_univ _, mem_univ _⟩) (fun x _ => ?_)
    (fun χ hχ => ?_) (fun x _ => rfl)
  · rw [Fintype.mem_piFinset]
    intro q
    unfold eS chiE
    split_ifs with h1 h2 h3 <;>
      first | exact mem_univ _ | exact mem_singleton_self _ | (exfalso; tauto)
  · obtain ⟨St, fl⟩ := x
    simp only [Prod.mk.injEq]
    constructor
    · ext i
      simp only [mem_filter, mem_univ, true_and]
      unfold chiE
      rw [if_pos (isLast_lastG P hdisj hE i), gi_lastG P hdisj hE]
      simp
    · funext i
      have hN := isNew_newG P hdisj hE i
      unfold chiE
      rw [if_neg (not_isLast_of_isNew P hE hN), if_pos hN, gi_newG P hdisj hE]
  · funext q
    have hmem := Fintype.mem_piFinset.1 hχ q
    unfold chiE
    by_cases hL : isLast P ℓ q
    · rw [if_pos hL]
      simp only [mem_filter, mem_univ, true_and, decide_eq_true_eq]
      rw [← (isLast_iff_lastG P hdisj hE q).1 hL]
      cases χ q <;> simp
    · rw [if_neg hL]
      by_cases hN : isNew P nw q
      · rw [if_pos hN]
        show χ (newG P hE (gi P q)) = χ q
        rw [← (isNew_iff_newG P hdisj hE q).1 hN]
      · rw [if_neg hN]
        unfold eS at hmem
        rw [if_neg (by tauto)] at hmem
        exact (mem_singleton.1 hmem).symm

omit hdisj in
lemma sum_piFinset_pair {M : Type*} [AddCommMonoid M] (F : (Fin P.K → ℕ × Bool) → M) :
    ∑ tg ∈ Fintype.piFinset (fun i => P.grp i ×ˢ (univ : Finset Bool)), F tg =
      ∑ nw ∈ Fintype.piFinset P.grp, ∑ fl : Fin P.K → Bool, F (fun i => (nw i, fl i)) := by
  rw [← sum_product' (Fintype.piFinset P.grp) (univ : Finset (Fin P.K → Bool))
    (fun nw fl => F (fun i => (nw i, fl i)))]
  refine (sum_nbij' (fun x : (Fin P.K → ℕ) × (Fin P.K → Bool) =>
      (fun i => (x.1 i, x.2 i) : Fin P.K → ℕ × Bool))
    (fun tg : Fin P.K → ℕ × Bool =>
      ((fun i => (tg i).1, fun i => (tg i).2) : (Fin P.K → ℕ) × (Fin P.K → Bool)))
    (fun x hx => ?_) (fun tg htg => ?_) (fun x _ => rfl) (fun tg _ => rfl) (fun x _ => rfl)).symm
  · rw [mem_product, Fintype.mem_piFinset] at hx
    rw [Fintype.mem_piFinset]
    intro i
    exact mem_product.2 ⟨hx.1 i, mem_univ _⟩
  · rw [Fintype.mem_piFinset] at htg
    rw [mem_product, Fintype.mem_piFinset]
    exact ⟨fun i => (mem_product.1 (htg i)).1, mem_univ _⟩

end EdgeMem

lemma gcd_of_zSet (P : MemParams) {z : ℤ × ℤ} (hz : z ∈ P.zSet) : Int.gcd z.1 z.2 = 1 := by
  simp only [MemParams.zSet, mem_filter] at hz
  exact hz.2

lemma sum3_comm {α β γ M : Type*} [AddCommMonoid M] (s : Finset α) (t : Finset β) (u : Finset γ)
    (f : α → β → γ → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, f a b c := by
  rw [show ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, f a b c from
    sum_congr rfl fun a _ => sum_comm]
  exact sum_comm

section EdgeStep

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
include hdisj

/-- **The ordered edge on an encoded state.** -/
theorem edgeOrd_step (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hB : P.gPrimes.card ≤ P.B) {ω : ℝ × ℝ × ℝ} {t : ℕ} {z : ℤ × ℤ} (hz : z ∈ P.zSet)
    {ℓ : P.Lst} {st : ℕ → PSt} (hv : Valid P ℓ st)
    (Fs : P.MState × Finset ℕ → ℂ) (Ts : (GP P → Option ℕ) → (ℤ × ℤ) × P.Lst → ℂ)
    (hTs : ∀ τ z' ℓ'', (∃ q : GP P, (∃ i k, ℓ'' i k = q.1) ∧ τ q ≠ some (lineOf q.1 z')) →
      Ts τ (z', ℓ'') = 0)
    (hF : ∀ z' ∈ P.zSet, ∀ ℓ'' st'', Valid P ℓ'' st'' → Fs (enc P z' ℓ'' st'') =
      ∑ τ ∈ Fintype.piFinset (tyS P),
        (∏ q : GP P, cf P (t + 1) z' q.1 (st'' q.1) (τ q)) * Ts τ (z', ℓ'')) :
    P.edgeOrdD ω t Fs (enc P z ℓ st) =
      ∑ τ ∈ Fintype.piFinset (tyS P),
        (∏ q : GP P, cg P t z q.1 (st q.1) (τ q)) * P.physEdge ω t (Ts τ) (z, ℓ) := by
  classical
  have hzg : Int.gcd z.1 z.2 = 1 := gcd_of_zSet P hz
  conv_lhs =>
    unfold MemParams.edgeOrdD MemParams.edgeChoices
    rw [sum_product, sum_comm, sum_product]
  conv_rhs =>
    unfold MemParams.physEdge
    simp only [mul_sum]
    rw [sum_comm]
  refine sum_congr rfl fun z' hz' => ?_
  rw [sum_piFinset_pair P]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun nw hnw => ?_
  rw [sum_comm]
  by_cases hOK : P.EdgeOK ω z z' ℓ nw
  · have hzg' : Int.gcd z'.1 z'.2 = 1 := gcd_of_zSet P hz'
    have hE : EdgeFacts P z z' ℓ nw st :=
      ⟨hv, hzg, hzg', hOK.1, hOK.2.1, Fintype.mem_piFinset.1 hnw, hOK.2.2.2.2.1⟩
    simp only [if_pos hOK]
    simp_rw [edge_term P hdisj hE hOK hz' hB Fs, hF z' hz' _ _ (valid_stE P hdisj hE _)]
    -- regroup by types
    have key : ∀ τ ∈ Fintype.piFinset (tyS P),
        ∑ St : Finset (Fin P.K), ∑ fl : Fin P.K → Bool,
          (∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q)) *
            ((∏ q : GP P, cf P (t + 1) z' q.1 (stE P z ℓ nw st St q.1) (τ q)) *
              Ts τ (z', P.newList ℓ nw)) =
        (∏ q : GP P, cg P t z q.1 (st q.1) (τ q)) * (((∏ i, (P.Vg i)⁻¹ : ℝ)) : ℂ) *
          Ts τ (z', P.newList ℓ nw) := by
      intro τ _
      by_cases H : ∀ q : GP P, (∃ i k, P.newList ℓ nw i k = q.1) → τ q = some (lineOf q.1 z')
      · have e1 : ∀ St fl, (∏ q, wE P z z' ℓ nw st q (chiE P ℓ nw St fl q)) *
            ((∏ q : GP P, cf P (t + 1) z' q.1 (stE P z ℓ nw st St q.1) (τ q)) *
              Ts τ (z', P.newList ℓ nw)) =
            (∏ q, (wE P z z' ℓ nw st q (chiE P ℓ nw St fl q) *
              cf P (t + 1) z' q.1 (eNew P z ℓ nw st q (chiE P ℓ nw St fl q)) (τ q))) *
              Ts τ (z', P.newList ℓ nw) := by
          intro St fl
          rw [← mul_assoc, ← prod_mul_distrib]
          congr 1
          refine prod_congr rfl fun q _ => ?_
          rw [stE_gp P hdisj St fl q]
        simp_rw [e1, ← sum_mul]
        congr 1
        rw [sum_St_fl P hdisj hE (fun q b => wE P z z' ℓ nw st q b *
          cf P (t + 1) z' q.1 (eNew P z ℓ nw st q b) (τ q))]
        rw [prod_congr rfl fun q _ => edge_local P hdisj hE t q (hb q.1 q.2) (hV _) (τ q) (H q),
          prod_mul_distrib, Complex.ofReal_prod]
        congr 1
        rw [prod_over_new P hdisj hE]
        · refine prod_congr rfl fun i _ => ?_
          rw [if_pos (isNew_newG P hdisj hE i), gi_newG P hdisj hE]
        · intro q hq; rw [if_neg hq]
      · push_neg at H
        obtain ⟨q, hq1, hq2⟩ := H
        have h0 := hTs τ z' (P.newList ℓ nw) ⟨q, hq1, hq2⟩
        rw [h0]; simp
    simp_rw [mul_sum]
    rw [sum3_comm]
    refine sum_congr rfl fun τ hτ => ?_
    simp_rw [← mul_sum]
    rw [key τ hτ]
    ring
  · simp only [if_neg hOK, mul_zero, sum_const_zero]
    refine sum_eq_zero fun St _ => sum_eq_zero fun fl _ => ?_
    have hce : P.edgeCoeff ω t (enc P z ℓ st).1 (St, z', fun i => (nw i, fl i)) = 0 := by
      unfold MemParams.edgeCoeff
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hOK h1
    simp only [hce, zero_mul, ite_self]

end EdgeStep

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: the tail identity (induction along the path)

For every valid encoded state at visit `N − k`,
`memTailD k b (enc z ℓ st) = ∑_τ ∏_p cf_{N−k}(z, st p, τ p) · physTail ω δ_τ k f (z, ℓ)`.
The ghost step (`ghost_step`) and the edge step (`edgeOrd_step`) are combined with the slot
symmetrizations, which commute with the type expansion. -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

section Tail

variable (P : MemParams)

/-- The final indicator of the physical tail. -/
noncomputable def fOne : (ℤ × ℤ) × P.Lst → ℂ := fun s => if s.1 = (1, 0) then 1 else 0

/-- The list permuted by `pr`. -/
def lperm (ℓ : P.Lst) (pr : Fin P.K → Equiv.Perm (Fin (P.J + 1))) : P.Lst :=
  fun i => ℓ i ∘ pr i

lemma listSym_congr {g₁ g₂ : P.Lst → ℂ} {ℓ : P.Lst}
    (h : ∀ pr, g₁ (lperm P ℓ pr) = g₂ (lperm P ℓ pr)) : P.listSym g₁ ℓ = P.listSym g₂ ℓ := by
  unfold MemParams.listSym
  congr 1
  exact sum_congr rfl fun pr _ => h pr

lemma listSym_sum_mul {ι : Type*} (S : Finset ι) (a : ι → ℂ) (g : ι → P.Lst → ℂ) (ℓ : P.Lst) :
    P.listSym (fun ℓ' => ∑ τ ∈ S, a τ * g τ ℓ') ℓ = ∑ τ ∈ S, a τ * P.listSym (g τ) ℓ := by
  unfold MemParams.listSym
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun pr _ => ?_
  ring

lemma valid_perm {ℓ : P.Lst} {st : ℕ → PSt} (hv : Valid P ℓ st)
    (pr : Fin P.K → Equiv.Perm (Fin (P.J + 1))) : Valid P (lperm P ℓ pr) st := by
  refine ⟨fun i k => hv.lc i _, fun q hq => ?_, hv.pend⟩
  rw [hv.act q hq]
  constructor
  · rintro ⟨i, k, hk⟩; exact ⟨i, (pr i).symm k, by simp [lperm, hk]⟩
  · rintro ⟨i, k, hk⟩; exact ⟨i, pr i k, hk⟩

lemma symMD_enc (G : P.MState × Finset ℕ → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst) (st : ℕ → PSt) :
    P.symMD G (enc P z ℓ st) = P.listSym (fun ℓ' => G (enc P z ℓ' st)) ℓ := rfl

/-- An active prime with the wrong type kills the physical tail. -/
lemma physTail_eq_zero_of (ω : ℝ × ℝ × ℝ) (τ : GP P → Option ℕ) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst)
    (h : ∃ q : GP P, (∃ i k, ℓ i k = q.1) ∧ τ q ≠ some (lineOf q.1 z)) :
    P.physTail ω (dT P τ) k f (z, ℓ) = 0 := by
  obtain ⟨q, hq1, hq2⟩ := h
  have hv : P.visitFac (dT P τ) (P.N - k) (z, ℓ) = 0 := by
    rw [visitFac_dT]
    refine prod_eq_zero (mem_univ q) ?_
    unfold pfT
    rw [if_pos hq1, if_neg hq2]
  cases k with
  | zero => simp only [MemParams.physTail]; rw [show P.N = P.N - 0 by simp, hv]; simp
  | succ k => simp only [MemParams.physTail]; rw [hv]; simp

lemma symP_physTail_eq_zero_of (ω : ℝ × ℝ × ℝ) (τ : GP P → Option ℕ) (k : ℕ)
    (f : (ℤ × ℤ) × P.Lst → ℂ) (z : ℤ × ℤ) (ℓ : P.Lst)
    (h : ∃ q : GP P, (∃ i k, ℓ i k = q.1) ∧ τ q ≠ some (lineOf q.1 z)) :
    P.symP (P.physTail ω (dT P τ) k f) (z, ℓ) = 0 := by
  unfold MemParams.symP MemParams.listSym
  simp only
  rw [sum_eq_zero fun pr _ => ?_, mul_zero]
  obtain ⟨q, ⟨i, k', hk⟩, hq2⟩ := h
  exact physTail_eq_zero_of P ω τ k f z _ ⟨q, ⟨i, (pr i).symm k', by simp [hk]⟩, hq2⟩

/-- Pending status. -/
def pendB : PSt → Bool
  | PSt.P _ => true
  | _ => false

/-- The per-prime sum of the final coefficients: `0` for a pending prime, `1` otherwise. -/
lemma sum_cg_end (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (z : ℤ × ℤ) (q : GP P) (s : PSt)
    (hs : ∀ L, s = PSt.P L → L < q.1 + 1) :
    ∑ o ∈ tyS P q, cg P P.N z q.1 s o = if pendB s then 0 else 1 := by
  have hb' : ((P.bprime q.1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hb q.1 q.2)
  have hp1 : (((q.1 : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    have : ((q.1 : ℝ) + 1 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  unfold tyS
  rw [sum_insertNone]
  rcases s with _ | _ | L | _
  · simp only [cg, cU, if_true, reduceCtorEq, if_false, sum_const, card_range, nsmul_eq_mul,
      pendB, Bool.false_eq_true]
    have hbt : btail P (P.N + 1) q.1 = 1 := by simp [btail]
    rw [hbt]
    push_cast
    field_simp
    ring
  · simp only [cg, reduceCtorEq, if_false, Option.some.injEq, sum_ite_eq', mem_range,
      zero_add, pendB, Bool.false_eq_true]
    rw [if_pos (lineOf_lt (pos_of_gPrimes P q.2) z)]
  · have hL := hs L rfl
    simp only [cg, if_true, reduceCtorEq, if_false, sub_zero, zero_sub, Option.some.injEq,
      pendB]
    rw [← mul_sum, sum_ite_eq']
    simp [mem_range.2 hL]
  · simp [cg, pendB]

lemma encMem_eq_zero_iff (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {ℓ : P.Lst}
    {st : ℕ → PSt} (hv : Valid P ℓ st) :
    encMem P st = 0 ↔ ∀ q : GP P, pendB (st q.1) = false := by
  constructor
  · intro h q
    by_contra hp
    rcases hs : st q.1 with _ | _ | L | _ <;> rw [hs] at hp <;> simp [pendB] at hp
    have hL := hv.pend q.1 q.2 L hs
    have := congrFun h (pt P hdisj q ⟨L, hL⟩)
    rw [encMem_pt P hdisj, if_pos hs] at this
    simp at this
  · intro h
    funext y
    have hq := y_gp P y
    have := h ⟨_, hq⟩
    show (if st y.1.2.1 = PSt.P y.1.2.2 then 1 else 0) = 0
    rw [if_neg]
    intro h'
    rw [h'] at this
    simp [pendB] at this

/-- The final indicator in type-expanded form. -/
lemma bVec_enc (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (z : ℤ × ℤ) {ℓ : P.Lst} {st : ℕ → PSt}
    (hv : Valid P ℓ st) :
    P.bVec (enc P z ℓ st).1 = ∑ τ ∈ Fintype.piFinset (tyS P),
      (∏ q : GP P, cg P P.N z q.1 (st q.1) (τ q)) * fOne P (z, ℓ) := by
  classical
  rw [← sum_mul, ← prod_univ_sum (t := tyS P) (f := fun q o => cg P P.N z q.1 (st q.1) o)]
  rw [prod_congr rfl fun q _ => sum_cg_end P hb z q (st q.1) (hv.pend q.1 q.2)]
  unfold MemParams.bVec fOne enc
  simp only
  have e : (∏ q : GP P, (if pendB (st q.1) then (0 : ℂ) else 1)) =
      if ∀ q : GP P, pendB (st q.1) = false then 1 else 0 := by
    by_cases h : ∀ q : GP P, pendB (st q.1) = false
    · rw [if_pos h]; exact prod_eq_one fun q _ => by simp [h q]
    · rw [if_neg h]
      push_neg at h
      obtain ⟨q, hq⟩ := h
      exact prod_eq_zero (mem_univ q) (by simp at hq; simp [hq])
  rw [e]
  by_cases h2 : ∀ q : GP P, pendB (st q.1) = false
  · have h3 := (encMem_eq_zero_iff P hdisj hv).2 h2
    by_cases h1 : z = (1, 0) <;> simp [h1, h2, h3]
  · have h3 : encMem P st ≠ 0 := fun h => h2 ((encMem_eq_zero_iff P hdisj hv).1 h)
    rw [if_neg h2]
    by_cases h1 : z = (1, 0) <;> simp [h1, h3]

/-- **The tail identity.** -/
theorem tail_identity (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hB : P.gPrimes.card ≤ P.B) (ω : ℝ × ℝ × ℝ) (k : ℕ) (hk : k ≤ P.N) :
    ∀ z ∈ P.zSet, ∀ ℓ st, Valid P ℓ st →
      P.memTailD ω k (fun s => P.bVec s.1) (enc P z ℓ st) =
        ∑ τ ∈ Fintype.piFinset (tyS P), (∏ q : GP P, cf P (P.N - k) z q.1 (st q.1) (τ q)) *
          P.physTail ω (dT P τ) k (fOne P) (z, ℓ) := by
  induction k with
  | zero =>
    intro z hz ℓ st hv
    simp only [MemParams.memTailD, MemParams.physTail, Nat.sub_zero]
    rw [ghost_step P hdisj hb hV hB le_rfl hz hv (fun s => P.bVec s.1)
      (fun _ => fOne P (z, ℓ)) (fun st' hv' => bVec_enc P hdisj hb z hv')]
    exact sum_congr rfl fun τ _ => by ring
  | succ k ih =>
    intro z hz ℓ st hv
    have hk' : k ≤ P.N := by omega
    have ht : P.N - (k + 1) + 1 = P.N - k := by omega
    simp only [MemParams.memTailD, MemParams.physTail]
    set t := P.N - (k + 1) with htdef
    -- the function after the ghost
    have hX : ∀ st', Valid P ℓ st' →
        P.edgeOpD ω t (P.memTailD ω k (fun s => P.bVec s.1)) (enc P z ℓ st') =
          ∑ τ ∈ Fintype.piFinset (tyS P), (∏ q : GP P, cg P t z q.1 (st' q.1) (τ q)) *
            P.symP (P.physEdge ω t (P.symP (P.physTail ω (dT P τ) k (fOne P)))) (z, ℓ) := by
      intro st' hv'
      unfold MemParams.edgeOpD
      rw [symMD_enc]
      have hstep : ∀ pr, P.edgeOrdD ω t (P.symMD (P.memTailD ω k (fun s => P.bVec s.1)))
          (enc P z (lperm P ℓ pr) st') =
          ∑ τ ∈ Fintype.piFinset (tyS P), (∏ q : GP P, cg P t z q.1 (st' q.1) (τ q)) *
            P.physEdge ω t (P.symP (P.physTail ω (dT P τ) k (fOne P))) (z, lperm P ℓ pr) := by
        intro pr
        refine edgeOrd_step P hdisj hb hV hB hz (valid_perm P hv' pr) _ _
          (fun τ z' ℓ'' h => symP_physTail_eq_zero_of P ω τ k _ z' ℓ'' h) ?_
        intro z' hz' ℓ'' st'' hv''
        rw [symMD_enc]
        rw [listSym_congr P (g₂ := fun l3 => ∑ τ ∈ Fintype.piFinset (tyS P),
          (∏ q : GP P, cf P (t + 1) z' q.1 (st'' q.1) (τ q)) *
            P.physTail ω (dT P τ) k (fOne P) (z', l3)) fun pr' => by
              rw [ih hk' z' hz' _ _ (valid_perm P hv'' pr'), ht]]
        rw [listSym_sum_mul]
        rfl
      rw [listSym_congr P (g₂ := fun l2 => ∑ τ ∈ Fintype.piFinset (tyS P),
          (∏ q : GP P, cg P t z q.1 (st' q.1) (τ q)) *
            P.physEdge ω t (P.symP (P.physTail ω (dT P τ) k (fOne P))) (z, l2)) hstep,
        listSym_sum_mul]
      rfl
    rw [ghost_step P hdisj hb hV hB (by omega) hz hv _ _ hX]
    refine sum_congr rfl fun τ _ => ?_
    ring

end Tail

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: D7a, the memory identity ([21] (4.5)–(4.15))

`memory_identity_gen`: for disjoint groups, `b'_p ≠ 0`, `Vᵢ ≠ 0`, a path of length `N ≥ 1` and any
memory bound `B ≥ #(group primes)`, the independent-line moment is the baseline times the memory
moment with global birth distinctness. At `t = 0` the unborn coefficient of the dead type vanishes
(`b'_p[0, N] = b'_p`), so the type expansion of `tail_identity` is exactly the line average of
`rootIL`; the initial list weight `∏ νᵢ` supplies `σ ∏_{p ∈ ℓ₀} ((p+1) b'_p)⁻¹`.

`N ≥ 1` is necessary: for `N = 0` there is no edge, `rootIL` also counts initial lists with
repeated entries, and the identity fails (see `proofs/a102/L102F.md`). -/

namespace ArtinPrimitiveRoots.L102F

open Real Finset

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet

section Lists

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))

lemma mem_allEntries (ℓ : P.Lst) (q : ℕ) : q ∈ P.allEntries ℓ ↔ ∃ i k, ℓ i k = q := by
  unfold MemParams.allEntries
  rw [List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hq⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨i, k, rfl⟩
  · rintro ⟨i, k, rfl⟩
    exact ⟨_, List.mem_ofFn.2 ⟨i, rfl⟩, List.mem_ofFn.2 ⟨k, rfl⟩⟩

include hdisj in
lemma nodup_allEntries_iff {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) :
    (P.allEntries ℓ).Nodup ↔ ∀ i, Function.Injective (ℓ i) := by
  unfold MemParams.allEntries
  rw [List.nodup_flatten]
  constructor
  · rintro ⟨h1, _⟩ i
    exact List.nodup_ofFn.1 (h1 _ (List.mem_ofFn.2 ⟨i, rfl⟩))
  · intro h
    refine ⟨fun l hl => ?_, ?_⟩
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hl
      exact List.nodup_ofFn.2 (h i)
    · rw [List.pairwise_ofFn]
      intro i j hij
      rw [List.disjoint_left]
      intro a ha hb
      obtain ⟨k, rfl⟩ := List.mem_ofFn.1 ha
      obtain ⟨k', hk'⟩ := List.mem_ofFn.1 hb
      exact disjoint_left.1 (hdisj i j hij.ne) (hℓ i k) (hk' ▸ hℓ j k')

/-- The statuses of the initial state: the entries are active, everything else unborn. -/
noncomputable def st0 (ℓ : P.Lst) : ℕ → PSt :=
  fun q => if q ∈ P.allEntries ℓ then PSt.A else PSt.U

lemma valid_st0 {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) : Valid P ℓ (st0 P ℓ) := by
  refine ⟨hℓ, fun q _ => ?_, fun q _ L hL => ?_⟩
  · unfold st0; rw [← mem_allEntries]; split_ifs with h <;> simp [h]
  · unfold st0 at hL; split_ifs at hL

lemma encMem_st0 (ℓ : P.Lst) : encMem P (st0 P ℓ) = 0 := by
  funext y
  unfold encMem st0
  split_ifs with h1 h2 <;> simp_all

lemma encBorn_st0 {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) :
    encBorn P (st0 P ℓ) = (P.allEntries ℓ).toFinset := by
  ext q
  rw [encBorn, mem_filter, List.mem_toFinset]
  unfold st0
  constructor
  · rintro ⟨_, h⟩; by_contra h'; rw [if_neg h'] at h; exact h rfl
  · intro h
    obtain ⟨i, k, hk⟩ := (mem_allEntries P ℓ q).1 h
    exact ⟨hk ▸ mem_gPrimes_of_grp P (hℓ i k), by rw [if_pos h]; simp⟩

/-- A path of length `N ≥ 1` from a list with a repeated entry vanishes (the first edge needs an
injective source list). -/
lemma physTail_eq_zero_of_not_inj (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop)
    (f : (ℤ × ℤ) × P.Lst → ℂ) (hN : 1 ≤ P.N) (z : ℤ × ℤ) (ℓ : P.Lst)
    (h : ¬ ∀ i, Function.Injective (ℓ i)) : P.physTail ω δ P.N f (z, ℓ) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, P.N = k + 1 := ⟨P.N - 1, by omega⟩
  rw [hk]
  simp only [MemParams.physTail]
  have : P.symP (P.physEdge ω (P.N - (k + 1)) (P.symP (P.physTail ω δ k f))) (z, ℓ) = 0 := by
    unfold MemParams.symP MemParams.listSym
    simp only
    rw [sum_eq_zero fun pr _ => ?_, mul_zero]
    unfold MemParams.physEdge
    refine sum_eq_zero fun z' _ => sum_eq_zero fun nw _ => ?_
    rw [if_neg]
    rintro ⟨hinj, _⟩
    apply h
    intro i
    have := hinj i
    simp only at this
    exact (Equiv.injective_comp (pr i) (ℓ i)).1 this
  rw [this, mul_zero]

end Lists

section Start

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))

lemma e1_mem_zSet : ((1, 0) : ℤ × ℤ) ∈ P.zSet := by
  unfold MemParams.zSet
  rw [mem_filter, mem_product, mem_Icc, mem_Icc]
  refine ⟨⟨⟨by omega, by norm_cast; unfold MemParams.zMax; omega⟩,
    ⟨by omega, by positivity⟩⟩, by simp⟩

lemma zero_mem_memSet : (0 : P.Mem) ∈ P.memSet := by
  unfold MemParams.memSet
  rw [mem_filter, Fintype.mem_piFinset]
  exact ⟨fun _ => by simp, by simp [MemParams.memSize]⟩

lemma memWeight_zero : P.memWeight 0 = 1 := by
  unfold MemParams.memWeight; simp

include hdisj in
/-- The memory moment as a sum over initial lists. -/
lemma memMoment_expand (hB : P.gPrimes.card ≤ P.B) (ω : ℝ × ℝ × ℝ) :
    P.memMomentD ω = ∑ ℓ₀ ∈ listCands P.x P.a P.J, if (P.allEntries ℓ₀).Nodup then
      (P.listWeight ℓ₀ : ℂ) * P.memTailD ω P.N (fun s => P.bVec s.1)
        (enc P (1, 0) ℓ₀ (st0 P ℓ₀)) else 0 := by
  unfold MemParams.memMomentD
  rw [MemParams.stSet, sum_product, sum_eq_single_of_mem ((1, 0) : ℤ × ℤ) (e1_mem_zSet P)]
  · rw [sum_product]
    refine sum_congr rfl fun ℓ₀ hℓ₀ => ?_
    have hℓ : ∀ i k, ℓ₀ i k ∈ P.grp i := by
      simp only [listCands, Fintype.mem_piFinset] at hℓ₀; exact hℓ₀
    rw [sum_eq_single_of_mem (0 : P.Mem) (zero_mem_memSet P)]
    · simp only
      split_ifs with h
      · have he : (((1, 0) : ℤ × ℤ), ℓ₀, (0 : P.Mem)) = (enc P (1, 0) ℓ₀ (st0 P ℓ₀)).1 := by
          simp [enc, encMem_st0]
        have hb : (P.allEntries ℓ₀).toFinset = (enc P (1, 0) ℓ₀ (st0 P ℓ₀)).2 := by
          simp [enc, encBorn_st0 P hℓ]
        unfold MemParams.stWeight MemParams.bVec
        simp only [and_self, if_true, memWeight_zero, mul_one]
        rw [he, hb]
      · rfl
    · intro m _ hm
      simp only
      split_ifs <;> simp [MemParams.bVec, hm]
  · intro z _ hz
    refine sum_eq_zero fun y _ => ?_
    split_ifs <;> simp [MemParams.bVec, hz]

end Start

section Final

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))

/-- The initial coefficient of an inactive prime with a line type. -/
noncomputable def gInit (q : GP P) : ℂ := ((1 / (((q.1 : ℝ) + 1) * P.bprime q.1) : ℝ) : ℂ)

lemma btail_zero (q : ℕ) : btail P 0 q = P.bprime q := by
  unfold btail MemParams.bprime; rw [range_eq_Ico]

lemma cf0_none (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (ℓ : P.Lst) (q : GP P) :
    cf P 0 (1, 0) q.1 (st0 P ℓ q.1) none = 0 := by
  unfold st0
  split_ifs
  · simp [cf]
  · simp only [cf, cU, if_true]
    rw [btail_zero, div_self (hb q.1 q.2)]
    simp

include hdisj in
/-- The tail at the initial state, as a line average. -/
lemma memTail_start (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hB : P.gPrimes.card ≤ P.B) (ω : ℝ × ℝ × ℝ) {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) :
    P.memTailD ω P.N (fun s => P.bVec s.1) (enc P (1, 0) ℓ (st0 P ℓ)) =
      (∏ q : GP P, if q.1 ∈ P.allEntries ℓ then 1 else gInit P q) *
        ∑ lam ∈ Fintype.piFinset (fun q : GP P => range (q.1 + 1)),
          P.physTail ω (dT P (fun q => some (lam q))) P.N (fOne P) ((1, 0), ℓ) := by
  classical
  rw [tail_identity P hdisj hb hV hB ω P.N le_rfl (1, 0) (e1_mem_zSet P) ℓ _ (valid_st0 P hℓ),
    Nat.sub_self, mul_sum]
  have hinj : Set.InjOn (fun lam : GP P → ℕ => fun q => some (lam q))
      (Fintype.piFinset (fun q : GP P => range (q.1 + 1)) : Set (GP P → ℕ)) := by
    intro l1 _ l2 _ h
    funext q
    exact Option.some.inj (congrFun h q)
  set S := Fintype.piFinset (fun q : GP P => range (q.1 + 1)) with hS
  set g : (GP P → ℕ) → (GP P → Option ℕ) := fun lam q => some (lam q) with hg
  set F : (GP P → Option ℕ) → ℂ := fun τ => (∏ q : GP P, cf P 0 (1, 0) q.1 (st0 P ℓ q.1) (τ q)) *
    P.physTail ω (dT P τ) P.N (fOne P) ((1, 0), ℓ) with hF
  have hsub : S.image g ⊆ Fintype.piFinset (tyS P) := by
    intro τ hτ
    obtain ⟨lam, hlam, rfl⟩ := mem_image.1 hτ
    rw [Fintype.mem_piFinset] at hlam ⊢
    intro q
    rw [tyS, mem_insertNone]
    intro a ha
    cases ha
    exact hlam q
  have hzero : ∀ τ ∈ Fintype.piFinset (tyS P), τ ∉ S.image g → F τ = 0 := by
    intro τ hτ hτ'
    have : ∃ q, τ q = none := by
      by_contra h
      push_neg at h
      apply hτ'
      refine mem_image.2 ⟨fun q => (τ q).getD 0, ?_, ?_⟩
      · rw [hS, Fintype.mem_piFinset]
        intro q
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (h q)
        have := (Fintype.mem_piFinset.1 hτ) q
        rw [tyS, mem_insertNone] at this
        rw [ha]; exact this a ha
      · funext q
        obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (h q)
        simp [hg, ha]
    obtain ⟨q, hq⟩ := this
    rw [hF]
    dsimp only
    rw [prod_eq_zero (mem_univ q) (by rw [hq]; exact cf0_none P hb ℓ q), zero_mul]
  calc ∑ τ ∈ Fintype.piFinset (tyS P), F τ = ∑ τ ∈ S.image g, F τ :=
        (sum_subset hsub hzero).symm
    _ = ∑ lam ∈ S, F (g lam) := sum_image hinj
    _ = _ := by
      refine sum_congr rfl fun lam _ => ?_
      rw [hF]
      dsimp only
      by_cases hT : P.physTail ω (dT P (g lam)) P.N (fOne P) ((1, 0), ℓ) = 0
      · rw [hT]; simp
      · congr 1
        refine prod_congr rfl fun q _ => ?_
        unfold st0
        split_ifs with h
        · simp only [cf, hg, Option.some.injEq]
          rw [if_pos]
          by_contra hne
          exact hT (physTail_eq_zero_of P ω _ P.N _ _ ℓ
            ⟨q, (mem_allEntries P ℓ q.1).1 h, by simpa [hg] using hne⟩)
        · simp [cf, cU, gInit, hg]

end Final

section Assembly

variable (P : MemParams) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))

/-- `1/((p+1) b'_p)` as a real function. -/
noncomputable def gR (p : ℕ) : ℝ := 1 / (((p : ℝ) + 1) * P.bprime p)

lemma prod_ite_entries {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i) (G : ℕ → ℝ) :
    ∏ q : GP P, (if q.1 ∈ P.allEntries ℓ then G q.1 else 1) =
      ∏ q ∈ (P.allEntries ℓ).toFinset, G q := by
  classical
  rw [show (∏ q : GP P, (if q.1 ∈ P.allEntries ℓ then G q.1 else 1)) =
      ∏ q ∈ P.gPrimes, (if q ∈ P.allEntries ℓ then G q else 1) from
    prod_coe_sort P.gPrimes (fun q => if q ∈ P.allEntries ℓ then G q else 1)]
  rw [← prod_filter]
  congr 1
  ext q
  simp only [mem_filter, List.mem_toFinset]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨i, k, hk⟩ := (mem_allEntries P ℓ q).1 h
    exact ⟨hk ▸ mem_gPrimes_of_grp P (hℓ i k), h⟩

lemma prod_entries {ℓ : P.Lst} (hnd : (P.allEntries ℓ).Nodup) (G : ℕ → ℝ) :
    ∏ q ∈ (P.allEntries ℓ).toFinset, G q = ∏ i, ∏ k, G (ℓ i k) := by
  classical
  rw [List.prod_toFinset _ hnd]
  unfold MemParams.allEntries
  simp [List.map_flatten, List.prod_flatten, List.map_ofFn, List.prod_ofFn, Function.comp_def,
    Fin.prod_univ_succ]

lemma listWeight_eq (hV : ∀ i, P.Vg i ≠ 0) {ℓ : P.Lst} (hℓ : ∀ i k, ℓ i k ∈ P.grp i)
    (hnd : (P.allEntries ℓ).Nodup) :
    P.listWeight ℓ = stateNorm P.x P.a P.J *
      ∏ q : GP P, (if q.1 ∈ P.allEntries ℓ then gR P q.1 else 1) := by
  rw [prod_ite_entries P hℓ, prod_entries P hnd]
  unfold MemParams.listWeight stateNorm gR MemParams.nu
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [show (groupReciprocalSum P.x (P.a i))⁻¹ ^ (P.J + 1) = ∏ _k : Fin (P.J + 1), (P.Vg i)⁻¹ by
    simp [MemParams.Vg], ← prod_mul_distrib]
  refine prod_congr rfl fun k _ => ?_
  have := hV i
  field_simp

/-- The independent-line moment as a sum over lines indexed by the group primes. -/
lemma rootIL_eq (ω : ℝ × ℝ × ℝ) :
    P.rootIL ω = (((∏ p ∈ P.gPrimes, ((p : ℝ) + 1))⁻¹ : ℝ) : ℂ) *
      ∑ lam ∈ Fintype.piFinset (fun q : GP P => range (q.1 + 1)),
        (stateNorm P.x P.a P.J : ℂ) * ∑ ℓ₀ ∈ listCands P.x P.a P.J,
          P.physTail ω (dT P (fun q => some (lam q))) P.N (fOne P) ((1, 0), ℓ₀) := by
  classical
  unfold MemParams.rootIL MemParams.pathPhi
  congr 1
  refine sum_nbij' (fun lam => fun q : GP P => lam q.1 q.2) (fun lam' => fun p h => lam' ⟨p, h⟩)
    (fun lam h => ?_) (fun lam' h => ?_) (fun lam _ => rfl) (fun lam' _ => rfl) (fun lam _ => ?_)
  · rw [Fintype.mem_piFinset]
    intro q
    exact (mem_pi.1 h) q.1 q.2
  · rw [mem_pi]
    intro p hp
    exact (Fintype.mem_piFinset.1 h) ⟨p, hp⟩
  · have hδ : (fun p z => ∃ h : p ∈ P.gPrimes, lineOf p z = lam p h) =
        dT P (fun q => some (lam q.1 q.2)) := by
      funext p z
      apply propext
      unfold dT
      constructor
      · rintro ⟨h, e⟩; exact ⟨h, by rw [e]⟩
      · rintro ⟨h, e⟩; exact ⟨h, (Option.some.inj e).symm⟩
    rw [hδ]
    rfl

include hdisj in
/-- **D7a, the memory identity**, for any memory bound `B ≥ #(group primes)` and `N ≥ 1`. -/
theorem memory_identity_main (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0)
    (hN : 1 ≤ P.N) (hB : P.gPrimes.card ≤ P.B) (ω : ℝ × ℝ × ℝ) :
    P.rootIL ω = (P.baseline : ℂ) * P.memMomentD ω := by
  classical
  rw [memMoment_expand P hdisj hB ω, rootIL_eq P ω, mul_sum, mul_sum]
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro ℓ₀ hℓ₀
  have hℓ : ∀ i k, ℓ₀ i k ∈ P.grp i := by
    simp only [listCands, Fintype.mem_piFinset] at hℓ₀; exact hℓ₀
  by_cases hnd : (P.allEntries ℓ₀).Nodup
  · rw [if_pos hnd, memTail_start P hdisj hb hV hB ω hℓ, listWeight_eq P hV hℓ hnd]
    simp only [mul_sum]
    refine sum_congr rfl fun lam _ => ?_
    -- the constants
    have hbase : (P.baseline : ℂ) * (stateNorm P.x P.a P.J : ℂ) *
        (∏ q : GP P, ((if q.1 ∈ P.allEntries ℓ₀ then gR P q.1 else 1 : ℝ) : ℂ)) *
        (∏ q : GP P, if q.1 ∈ P.allEntries ℓ₀ then 1 else gInit P q) =
        (((∏ p ∈ P.gPrimes, ((p : ℝ) + 1))⁻¹ : ℝ) : ℂ) * (stateNorm P.x P.a P.J : ℂ) := by
      rw [mul_assoc _ (∏ q : GP P, _), ← prod_mul_distrib]
      have e1 : ∀ q : GP P, (((if q.1 ∈ P.allEntries ℓ₀ then gR P q.1 else 1 : ℝ) : ℂ)) *
          (if q.1 ∈ P.allEntries ℓ₀ then 1 else gInit P q) = ((gR P q.1 : ℝ) : ℂ) := by
        intro q
        split_ifs <;> simp [gInit, gR]
      rw [prod_congr rfl fun q _ => e1 q, ← Complex.ofReal_prod]
      unfold MemParams.baseline
      rw [show (∏ q : GP P, gR P q.1) = ∏ p ∈ P.gPrimes, gR P p from
        prod_coe_sort P.gPrimes (gR P)]
      unfold gR
      have hprod : (∏ p ∈ P.gPrimes, P.bprime p) * ∏ p ∈ P.gPrimes, 1 / (((p : ℝ) + 1) * P.bprime p) =
          (∏ p ∈ P.gPrimes, ((p : ℝ) + 1))⁻¹ := by
        rw [← prod_mul_distrib, ← prod_inv_distrib]
        refine prod_congr rfl fun p hp => ?_
        have := hb p hp
        have : ((p : ℝ) + 1) ≠ 0 := by positivity
        field_simp
      rw [← hprod]
      push_cast
      ring
    rw [Complex.ofReal_mul, Complex.ofReal_prod]
    linear_combination (-(P.physTail ω (dT P fun q => some (lam q)) P.N (fOne P) ((1, 0), ℓ₀))) *
      hbase
  · rw [if_neg hnd, mul_zero]
    refine sum_eq_zero fun lam _ => ?_
    rw [physTail_eq_zero_of_not_inj P ω _ _ hN _ ℓ₀
      (fun h => hnd ((nodup_allEntries_iff P hdisj hℓ).2 h)), mul_zero, mul_zero]

end Assembly

end ArtinPrimitiveRoots.L102F
end

section
/-! # L102F: D7a, the memory identity ([21] (4.5)–(4.15))

`MemoryIdentityStmt` (`L102D_MomentCuts`) quantifies over every `P : MemParams`, including
`P.N = 0`; there it is false: with no edge, `rootIL` sums over all initial lists, including those
with a repeated entry, while `memMomentD` keeps only lists with distinct entries. With the extra
hypothesis `1 ≤ P.N` (available in `moment_bound_of_cuts`, where `N = 2R ≥ 2`) it holds:
`memory_identity : MemoryIdentityStmtN`. -/

namespace ArtinPrimitiveRoots.L102F

/-- **D7a as it holds**: `MemoryIdentityStmt` with the additional hypothesis `1 ≤ N`. -/
def MemoryIdentityStmtN : Prop :=
  ∀ (P : MemParams) (ω : ℝ × ℝ × ℝ),
    (∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) →
    (∀ p ∈ P.gPrimes, P.bprime p ≠ 0) → (∀ i, P.Vg i ≠ 0) → 1 ≤ P.N →
    P.rootIL ω = (P.baseline : ℂ) * (P.withB P.gPrimes.card).memMomentD ω

theorem physTail_withB (P : MemParams) (B : ℕ) (ω : ℝ × ℝ × ℝ) (δ : ℕ → ℤ × ℤ → Prop) (k : ℕ)
    (f : (ℤ × ℤ) × (P.withB B).Lst → ℂ) : (P.withB B).physTail ω δ k f = P.physTail ω δ k f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext s
    simp only [MemParams.physTail]
    rw [ih]
    rfl

theorem rootIL_withB (P : MemParams) (B : ℕ) (ω : ℝ × ℝ × ℝ) :
    (P.withB B).rootIL ω = P.rootIL ω := by
  unfold MemParams.rootIL MemParams.pathPhi
  simp only [physTail_withB]
  rfl

/-- The identity for every memory bound `B ≥ #(group primes)` (also used by D7b). -/
theorem memory_identity_withB (P : MemParams) (ω : ℝ × ℝ × ℝ)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0) (hN : 1 ≤ P.N) (B : ℕ)
    (hB : P.gPrimes.card ≤ B) :
    P.rootIL ω = (P.baseline : ℂ) * (P.withB B).memMomentD ω := by
  rw [← rootIL_withB P B ω]
  exact memory_identity_main (P.withB B) hdisj hb hV hN hB ω

/-- **D7a** (with `1 ≤ N`). -/
theorem memory_identity : MemoryIdentityStmtN := fun P ω hdisj hb hV hN =>
  memory_identity_withB P ω hdisj hb hV hN _ le_rfl

end ArtinPrimitiveRoots.L102F

end

section
/-! Check module: `chk_rootIL_eq_baseline_mul_memMomentD`, the published statement `rootIL_eq_baseline_mul_memMomentD` verbatim, proved from the
development. -/

namespace ArtinPrimitiveRoots

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
theorem solution (P : MemParams) (ω : ℝ × ℝ × ℝ)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (hb : ∀ p ∈ P.gPrimes, P.bprime p ≠ 0) (hV : ∀ i, P.Vg i ≠ 0) (hN : 1 ≤ P.N) :
    P.rootIL ω = (P.baseline : ℂ) * (P.withB P.gPrimes.card).memMomentD ω :=
  L102F.memory_identity P ω hdisj hb hV hN
end
