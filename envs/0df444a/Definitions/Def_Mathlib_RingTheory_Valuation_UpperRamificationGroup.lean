-- Prove2me | Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
-- name    : Mathlib_RingTheory_Valuation_UpperRamificationGroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/a050d8ef-d040-57e1-af71-d604331a3c56
-- title:
--   Herbrand functions and upper-numbering ramification groups
-- statement:
--   Throughout, $R$ is a commutative local ring with maximal ideal $\mathfrak m$ and $G$ is a group acting on $R$ by ring automorphisms; the lower-numbering groups $G_i =$ `lowerRamificationGroup R G i` are the inertia groups of $\mathfrak m^{i+1}$, i.e. the $\sigma \in G$ with $\sigma x - x \in \mathfrak m^{i+1}$ for all $x \in R$. The module sets $g_i :=$ `lowerRamificationCard R G i`, the cardinality (via `Nat.card`) of $G_i$, and records that $g_i \ge 1$ when $G$ is finite and $g_i = 1$ when $G$ is trivial. The Herbrand function `herbrandPhi` is defined on $\mathbb Q$ by $\varphi(u) = u$ for $u \le 0$ and, for $u > 0$, by $$\varphi(u) = \Big(\sum_{i=1}^{\lfloor u\rfloor} g_i + (u - \lfloor u\rfloor)\, g_{\lfloor u\rfloor + 1}\Big) \big/ g_0,$$ the floor being the natural-number floor. For finite $G$ it is shown to be strictly monotone, hence injective, positive on positive arguments, to satisfy $\varphi(n) = (\sum_{i=1}^{n} g_i)/g_0$ at natural arguments, and to take arbitrarily large values at natural arguments. The inverse function `herbrandPsi` is defined as `Function.invFun` of $\varphi$, so that it is a genuine left inverse, $\psi(\varphi(u)) = u$, for finite $G$.
--
--   The upper numbering is then given integrally: `upperRamificationIndex R G v` is the least natural number $n$ with $v \le \varphi(n)$, and $G^v :=$ `upperRamificationGroup R G v` is $G_n$ for that $n$ — thus a ceiling variant of the classical $G_{\psi(v)}$, agreeing with the classical definition at the values $v = \varphi(n)$, where $G^{\varphi(n)} = G_n$. Membership unfolds to the congruence condition $\sigma x - x \in \mathfrak m^{n+1}$ for all $x\in R$. Recorded properties: the index vanishes for $v \le 0$ and is monotone; $G^v = G_0$ for $v \le 0$, $G^0$ is the kernel of the action of $G$ on the residue field, $G^v \le G_0$ always, and $v \mapsto G^v$ is antitone for finite $G$. The predicate `UpperRamificationQuotientCompat R G S H` asserts, for a second local ring $S$ with an action of $G/H$ by a normal subgroup $H$, that for every $v \ge 0$ the image of $G^v$ under $G \to G/H$ equals the corresponding upper-numbering group of $S$. Finally, for a valuation subring $A$ of an extension $L/K$, the same $\varphi$, $\psi$ and $G^v$ are defined for the action of the decomposition subgroup on $A$, with $G^0$ identified with the inertia subgroup, $G^v$ contained in it, and antitonicity when the decomposition subgroup is finite.
--
--   **Relation to Mathlib.** Mathlib supplies the underlying ingredients — `Ideal.inertia`, the maximal ideal and residue field of a local ring, and `ValuationSubring.decompositionSubgroup`/`inertiaSubgroup` — but no Herbrand function or upper-numbering ramification filtration; those, together with the lower-numbering groups defined as inertia groups of powers of the maximal ideal, are the project's own.
--
--   **Where it is used.** These definitions form the project's infrastructure for wild ramification of local rings and valuation subrings, used where ramification filtrations in upper numbering are needed in the analysis of local conditions on Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

variable (R G) in

noncomputable def lowerRamificationCard (i : ℕ) : ℕ :=
  Nat.card (lowerRamificationGroup R G i)

theorem lowerRamificationCard_pos [Finite G] (i : ℕ) :
    0 < lowerRamificationCard R G i := by
  haveI : Nonempty (lowerRamificationGroup R G i) := ⟨⟨1, Subgroup.one_mem _⟩⟩
  exact Nat.card_pos

theorem one_le_lowerRamificationCard_cast [Finite G] (i : ℕ) :
    (1 : ℚ) ≤ (lowerRamificationCard R G i : ℚ) :=
  Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr (lowerRamificationCard_pos i).ne')

theorem lowerRamificationCard_of_subsingleton [Subsingleton G] (i : ℕ) :
    lowerRamificationCard R G i = 1 := by
  haveI : Nonempty (lowerRamificationGroup R G i) := ⟨⟨1, Subgroup.one_mem _⟩⟩
  haveI : Subsingleton (lowerRamificationGroup R G i) :=
    ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
  exact Nat.card_unique

variable (R G) in

noncomputable def herbrandPhi (u : ℚ) : ℚ :=
  if u ≤ 0 then u
  else ((∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerRamificationCard R G i : ℚ)) +
      (u - ⌊u⌋₊) * lowerRamificationCard R G (⌊u⌋₊ + 1)) / lowerRamificationCard R G 0

theorem herbrandPhi_of_nonpos {u : ℚ} (h : u ≤ 0) : herbrandPhi R G u = u := if_pos h

@[simp] theorem herbrandPhi_zero : herbrandPhi R G 0 = 0 := herbrandPhi_of_nonpos le_rfl

theorem herbrandPhi_of_pos {u : ℚ} (h : 0 < u) :
    herbrandPhi R G u =
      ((∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerRamificationCard R G i : ℚ)) +
        (u - ⌊u⌋₊) * lowerRamificationCard R G (⌊u⌋₊ + 1)) / lowerRamificationCard R G 0 :=
  if_neg (not_le.mpr h)

theorem herbrandPhi_natCast (n : ℕ) :
    herbrandPhi R G n =
      (∑ i ∈ Finset.Icc 1 n, (lowerRamificationCard R G i : ℚ)) / lowerRamificationCard R G 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, zero_div, Nat.cast_zero, herbrandPhi_zero]
  · have hpos : (0 : ℚ) < n := Nat.cast_pos.mpr hn
    rw [herbrandPhi_of_pos hpos, Nat.floor_natCast, sub_self, zero_mul, add_zero]

theorem herbrandPhi_nonneg {u : ℚ} (h : 0 ≤ u) : 0 ≤ herbrandPhi R G u := by
  rcases eq_or_lt_of_le h with rfl | hu
  · simp
  · rw [herbrandPhi_of_pos hu]
    have h1 : (0 : ℚ) ≤ u - ⌊u⌋₊ := sub_nonneg.mpr (Nat.floor_le hu.le)
    have h2 : (0 : ℚ) ≤ ∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerRamificationCard R G i : ℚ) :=
      Finset.sum_nonneg fun i _ => Nat.cast_nonneg _
    exact div_nonneg (add_nonneg h2 (mul_nonneg h1 (Nat.cast_nonneg _))) (Nat.cast_nonneg _)

theorem herbrandPhi_pos [Finite G] {v : ℚ} (hv : 0 < v) : 0 < herbrandPhi R G v := by
  rw [herbrandPhi_of_pos hv]
  refine div_pos ?_ (Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) 0))
  rcases Nat.eq_zero_or_pos ⌊v⌋₊ with h0 | h0
  · rw [h0, show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, Nat.cast_zero, sub_zero]
    simpa using mul_pos hv
      (Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) 1) : (0 : ℚ) < _)
  · refine add_pos_of_pos_of_nonneg
      (Finset.sum_pos (fun i _ => ?_) ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, h0⟩⟩) ?_
    · exact Nat.cast_pos.mpr (lowerRamificationCard_pos i)
    · exact mul_nonneg (sub_nonneg.mpr (Nat.floor_le hv.le)) (Nat.cast_nonneg _)

set_option maxHeartbeats 1000000 in

theorem herbrandPhi_strictMono [Finite G] : StrictMono (herbrandPhi R G) := by
  intro u v huv
  by_cases hv : v ≤ 0
  · rw [herbrandPhi_of_nonpos (huv.le.trans hv), herbrandPhi_of_nonpos hv]
    exact huv
  rw [not_le] at hv
  by_cases hu : u ≤ 0
  · rw [herbrandPhi_of_nonpos hu]
    exact hu.trans_lt (herbrandPhi_pos hv)
  · rw [not_le] at hu
    rw [herbrandPhi_of_pos hu, herbrandPhi_of_pos hv, div_eq_mul_inv, div_eq_mul_inv]
    have hg0 : (0 : ℚ) < (lowerRamificationCard R G 0 : ℚ) :=
      Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) 0)
    refine mul_lt_mul_of_pos_right ?_ (inv_pos.mpr hg0)
    have hum : ((⌊u⌋₊ : ℚ)) ≤ u := Nat.floor_le hu.le
    have hvM : ((⌊v⌋₊ : ℚ)) ≤ v := Nat.floor_le (hu.trans huv).le
    have hu1 : u < (⌊u⌋₊ : ℚ) + 1 := Nat.lt_floor_add_one u
    have hmM : ⌊u⌋₊ ≤ ⌊v⌋₊ := Nat.floor_mono huv.le
    have hgu : (0 : ℚ) < (lowerRamificationCard R G (⌊u⌋₊ + 1) : ℚ) :=
      Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) (⌊u⌋₊ + 1))
    rcases eq_or_lt_of_le hmM with heq | hlt
    ·
      rw [← heq]
      have hseg : (u - (⌊u⌋₊ : ℚ)) * (lowerRamificationCard R G (⌊u⌋₊ + 1) : ℚ) <
          (v - (⌊u⌋₊ : ℚ)) * (lowerRamificationCard R G (⌊u⌋₊ + 1) : ℚ) :=
        mul_lt_mul_of_pos_right (by linarith) hgu
      linarith
    ·
      have step0 : (u - (⌊u⌋₊ : ℚ)) * (lowerRamificationCard R G (⌊u⌋₊ + 1) : ℚ) <
          1 * (lowerRamificationCard R G (⌊u⌋₊ + 1) : ℚ) :=
        mul_lt_mul_of_pos_right (by linarith) hgu
      rw [one_mul] at step0
      have step1 : (∑ i ∈ Finset.Icc 1 (⌊u⌋₊ + 1), (lowerRamificationCard R G i : ℚ)) =
          (∑ i ∈ Finset.Icc 1 ⌊u⌋₊, (lowerRamificationCard R G i : ℚ)) +
            (lowerRamificationCard R G (⌊u⌋₊ + 1) : ℚ) :=
        Finset.sum_Icc_succ_top (by omega : 1 ≤ ⌊u⌋₊ + 1) _
      have step2 : (∑ i ∈ Finset.Icc 1 (⌊u⌋₊ + 1), (lowerRamificationCard R G i : ℚ)) ≤
          ∑ i ∈ Finset.Icc 1 ⌊v⌋₊, (lowerRamificationCard R G i : ℚ) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Icc_subset_Icc_right (by omega)) (fun i _ _ => Nat.cast_nonneg _)
      have step3 : (0 : ℚ) ≤ (v - ⌊v⌋₊) * lowerRamificationCard R G (⌊v⌋₊ + 1) :=
        mul_nonneg (by linarith) (Nat.cast_nonneg _)
      linarith

theorem herbrandPhi_monotone [Finite G] : Monotone (herbrandPhi R G) :=
  (herbrandPhi_strictMono (R := R) (G := G)).monotone

theorem herbrandPhi_injective [Finite G] : Function.Injective (herbrandPhi R G) :=
  (herbrandPhi_strictMono (R := R) (G := G)).injective

theorem exists_natCast_le_herbrandPhi [Finite G] (v : ℚ) :
    ∃ n : ℕ, v ≤ herbrandPhi R G n := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, v * (lowerRamificationCard R G 0 : ℚ) ≤ n :=
    ⟨⌈v * (lowerRamificationCard R G 0 : ℚ)⌉₊, Nat.le_ceil _⟩
  refine ⟨n, ?_⟩
  have hg0 : (0 : ℚ) < (lowerRamificationCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) 0)
  have h2 : (n : ℚ) ≤ ∑ i ∈ Finset.Icc 1 n, (lowerRamificationCard R G i : ℚ) := by
    have hcard : (Finset.Icc 1 n).card = n := by rw [Nat.card_Icc]; omega
    calc (n : ℚ) = (Finset.Icc 1 n).card • (1 : ℚ) := by rw [hcard, nsmul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ Finset.Icc 1 n, (lowerRamificationCard R G i : ℚ) :=
          Finset.card_nsmul_le_sum _ _ _ (fun i _ => one_le_lowerRamificationCard_cast i)
  have h3 : v * (lowerRamificationCard R G 0 : ℚ) ≤
      ∑ i ∈ Finset.Icc 1 n, (lowerRamificationCard R G i : ℚ) := hn.trans h2
  rw [herbrandPhi_natCast]
  calc v = v * (lowerRamificationCard R G 0 : ℚ) / (lowerRamificationCard R G 0 : ℚ) := by
        rw [mul_div_assoc, div_self hg0.ne', mul_one]
    _ ≤ (∑ i ∈ Finset.Icc 1 n, (lowerRamificationCard R G i : ℚ)) /
          (lowerRamificationCard R G 0 : ℚ) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hg0.le)

variable (R G) in

noncomputable def herbrandPsi : ℚ → ℚ :=
  Function.invFun (herbrandPhi R G)

theorem herbrandPsi_herbrandPhi [Finite G] (u : ℚ) :
    herbrandPsi R G (herbrandPhi R G u) = u :=
  Function.leftInverse_invFun (herbrandPhi_injective (R := R) (G := G)) u

theorem herbrandPsi_zero [Finite G] : herbrandPsi R G 0 = 0 := by
  have h := herbrandPsi_herbrandPhi (R := R) (G := G) 0
  rwa [herbrandPhi_zero] at h

variable (R G) in

noncomputable def upperRamificationIndex (v : ℚ) : ℕ :=
  sInf {n : ℕ | v ≤ herbrandPhi R G n}

variable (R G) in

noncomputable def upperRamificationGroup (v : ℚ) : Subgroup G :=
  lowerRamificationGroup R G (upperRamificationIndex R G v)

theorem upperRamificationIndex_of_nonpos {v : ℚ} (h : v ≤ 0) :
    upperRamificationIndex R G v = 0 :=
  Nat.sInf_eq_zero.mpr (Or.inl (by simpa using h))

@[simp] theorem upperRamificationIndex_zero : upperRamificationIndex R G 0 = 0 :=
  upperRamificationIndex_of_nonpos le_rfl

@[simp] theorem mem_upperRamificationGroup {σ : G} {v : ℚ} :
    σ ∈ upperRamificationGroup R G v ↔
      ∀ x : R, σ • x - x ∈ (maximalIdeal R) ^ (upperRamificationIndex R G v + 1) :=
  Iff.rfl

theorem upperRamificationGroup_of_nonpos {v : ℚ} (h : v ≤ 0) :
    upperRamificationGroup R G v = lowerRamificationGroup R G 0 :=
  congrArg (lowerRamificationGroup R G) (upperRamificationIndex_of_nonpos h)

@[simp] theorem upperRamificationGroup_zero :
    upperRamificationGroup R G 0 = lowerRamificationGroup R G 0 :=
  upperRamificationGroup_of_nonpos le_rfl

theorem upperRamificationGroup_zero_eq_ker :
    upperRamificationGroup R G 0 =
      MonoidHom.ker (MulSemiringAction.toRingAut G (ResidueField R)) :=
  upperRamificationGroup_zero.trans lowerRamificationGroup_zero_eq_ker

theorem upperRamificationGroup_le_zero (v : ℚ) :
    upperRamificationGroup R G v ≤ lowerRamificationGroup R G 0 :=
  lowerRamificationGroup_le_zero _

theorem le_herbrandPhi_upperRamificationIndex [Finite G] (v : ℚ) :
    v ≤ herbrandPhi R G (upperRamificationIndex R G v : ℕ) := by
  have hne : {n : ℕ | v ≤ herbrandPhi R G n}.Nonempty := exists_natCast_le_herbrandPhi v
  have hmem : sInf {n : ℕ | v ≤ herbrandPhi R G n} ∈ {n : ℕ | v ≤ herbrandPhi R G n} :=
    Nat.sInf_mem hne
  exact hmem

theorem upperRamificationIndex_le {v : ℚ} {n : ℕ} (h : v ≤ herbrandPhi R G n) :
    upperRamificationIndex R G v ≤ n := by
  have hmem : n ∈ {m : ℕ | v ≤ herbrandPhi R G m} := h
  exact Nat.sInf_le hmem

theorem upperRamificationIndex_monotone [Finite G] :
    Monotone (upperRamificationIndex R G) := by
  intro v w hvw
  exact upperRamificationIndex_le (hvw.trans (le_herbrandPhi_upperRamificationIndex w))

theorem upperRamificationGroup_antitone [Finite G] :
    Antitone (upperRamificationGroup R G) := by
  intro v w hvw
  exact lowerRamificationGroup_antitone (upperRamificationIndex_monotone (R := R) (G := G) hvw)

theorem upperRamificationIndex_herbrandPhi_natCast [Finite G] (n : ℕ) :
    upperRamificationIndex R G (herbrandPhi R G n) = n := by
  apply le_antisymm
  · exact upperRamificationIndex_le le_rfl
  · have h1 : herbrandPhi R G n ≤
        herbrandPhi R G (upperRamificationIndex R G (herbrandPhi R G n) : ℕ) :=
      le_herbrandPhi_upperRamificationIndex _
    exact Nat.cast_le.mp ((herbrandPhi_strictMono (R := R) (G := G)).le_iff_le.mp h1)

theorem upperRamificationGroup_herbrandPhi_natCast [Finite G] (n : ℕ) :
    upperRamificationGroup R G (herbrandPhi R G n) = lowerRamificationGroup R G n :=
  congrArg (lowerRamificationGroup R G) (upperRamificationIndex_herbrandPhi_natCast n)

variable (R G) in

def UpperRamificationQuotientCompat (S : Type*) [CommRing S] [IsLocalRing S]
    (H : Subgroup G) [H.Normal] [MulSemiringAction (G ⧸ H) S] : Prop :=
  ∀ v : ℚ, 0 ≤ v →
    (upperRamificationGroup R G v).map (QuotientGroup.mk' H) =
      upperRamificationGroup S (G ⧸ H) v

end IsLocalRing

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

noncomputable def herbrandPhi (A : ValuationSubring L) (u : ℚ) : ℚ :=
  IsLocalRing.herbrandPhi A (A.decompositionSubgroup K) u

noncomputable def herbrandPsi (A : ValuationSubring L) (v : ℚ) : ℚ :=
  IsLocalRing.herbrandPsi A (A.decompositionSubgroup K) v

noncomputable def upperRamificationGroup (A : ValuationSubring L) (v : ℚ) :
    Subgroup (A.decompositionSubgroup K) :=
  IsLocalRing.upperRamificationGroup A (A.decompositionSubgroup K) v

variable {K} {A : ValuationSubring L}

@[simp] theorem herbrandPhi_zero : A.herbrandPhi K 0 = 0 :=
  IsLocalRing.herbrandPhi_zero

theorem upperRamificationGroup_zero :
    A.upperRamificationGroup K 0 = A.inertiaSubgroup K := by
  have h1 : A.upperRamificationGroup K 0 = A.lowerRamificationGroup K 0 :=
    IsLocalRing.upperRamificationGroup_zero
  rw [h1, lowerRamificationGroup_zero]

theorem upperRamificationGroup_le_inertiaSubgroup (v : ℚ) :
    A.upperRamificationGroup K v ≤ A.inertiaSubgroup K := by
  have h1 : A.upperRamificationGroup K v ≤ A.lowerRamificationGroup K 0 :=
    IsLocalRing.upperRamificationGroup_le_zero v
  rwa [lowerRamificationGroup_zero] at h1

theorem upperRamificationGroup_antitone [Finite (A.decompositionSubgroup K)] :
    Antitone (A.upperRamificationGroup K) := by
  intro v w hvw
  exact IsLocalRing.upperRamificationGroup_antitone
    (R := A) (G := A.decompositionSubgroup K) hvw

end ValuationSubring

section Gates

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] {u : ℚ} (hu : 0 ≤ u) :
    IsLocalRing.herbrandPhi R G u = u := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · simp
  · rw [IsLocalRing.herbrandPhi_of_pos hu]
    simp only [IsLocalRing.lowerRamificationCard_of_subsingleton, Nat.cast_one, mul_one,
      div_one]
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
    ring

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] (v : ℚ) :
    IsLocalRing.upperRamificationGroup R G v = ⊤ := by
  ext σ
  simp [Subsingleton.elim σ 1]

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Finite G] :
    IsLocalRing.upperRamificationGroup R G 1 ≤ IsLocalRing.upperRamificationGroup R G 0 :=
  IsLocalRing.upperRamificationGroup_antitone (by norm_num)

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R]
    [MulSemiringAction (G ⧸ (⊤ : Subgroup G)) R] :
    IsLocalRing.UpperRamificationQuotientCompat R G R ⊤ := by
  intro v _
  haveI : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  ext x
  obtain rfl : x = 1 := Subsingleton.elim x 1
  exact iff_of_true (Subgroup.one_mem _) (Subgroup.one_mem _)

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] :
    MulSemiringAction (G ⧸ (⊤ : Subgroup G)) R :=
  MulSemiringAction.compHom R (1 : (G ⧸ (⊤ : Subgroup G)) →* RingAut R)

end Gates

/--
info: 'IsLocalRing.herbrandPhi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPhi

/--
info: 'IsLocalRing.herbrandPhi_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPhi_strictMono

/--
info: 'IsLocalRing.herbrandPsi_herbrandPhi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPsi_herbrandPhi

/--
info: 'IsLocalRing.upperRamificationGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup

/--
info: 'IsLocalRing.upperRamificationGroup_zero_eq_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup_zero_eq_ker

/--
info: 'IsLocalRing.upperRamificationGroup_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup_antitone

/--
info: 'IsLocalRing.upperRamificationGroup_herbrandPhi_natCast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup_herbrandPhi_natCast

/--
info: 'IsLocalRing.UpperRamificationQuotientCompat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.UpperRamificationQuotientCompat

/--
info: 'ValuationSubring.upperRamificationGroup_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.upperRamificationGroup_zero


