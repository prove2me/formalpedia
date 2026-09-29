-- Prove2me | Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi
-- name    : Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/a857c076-1195-5be9-9c8e-688446111de8
-- title:
--   Herbrand ψ inverse to φ; upper ramification numbering
-- statement:
--   The setting is a commutative local ring $R$ with a group $G$ acting on it by ring automorphisms. Here $G_i$ denotes `lowerRamificationGroup R G i`, the subgroup of $\sigma \in G$ with $\sigma \cdot x - x \in \mathfrak{m}_R^{i+1}$ for all $x \in R$, $g_i =$ `lowerRamificationCard R G i` its cardinality, and $\varphi =$ `herbrandPhi R G` the piecewise linear function which is the identity on $u \le 0$ and equals $\bigl(\sum_{i=1}^{\lfloor u\rfloor} g_i + (u - \lfloor u\rfloor) g_{\lfloor u\rfloor + 1}\bigr)/g_0$ for $u > 0$; $\psi =$ `herbrandPsi R G` is defined as a one-sided inverse of $\varphi$ via `Function.invFun`.
--
--   The results recorded are: the recursion $\varphi(m+1) = \varphi(m) + g_{m+1}/g_0$ for $m \in \mathbb{N}$; the affine formula $\varphi(u) = \varphi(m) + (u-m)g_{m+1}/g_0$ for $m \le u \le m+1$; and, for finite $G$, an explicit solution of $\varphi(u) = v$ on each segment, whence $\varphi$ is surjective and so bijective. Consequently $\psi$ is a genuine two-sided inverse: $\varphi(\psi(v)) = v$, $\psi$ is strictly monotone, bijective, fixes $v \le 0$, satisfies the Galois-type equivalences $\psi(v) \le u \iff v \le \varphi(u)$ (and the strict and reversed variants), and on $[\varphi(m), \varphi(m+1)]$ is given by $\psi(v) = m + (v - \varphi(m))g_0/g_{m+1}$.
--
--   For the upper numbering, where `upperRamificationIndex R G v` is $\inf\{n : v \le \varphi(n)\}$ and `upperRamificationGroup R G v` is $G$ at that index: the index vanishes exactly when $v \le 0$, equals $m+1$ exactly when $\varphi(m) < v \le \varphi(m+1)$ (with a combined characterisation using truncated subtraction $n-1$), and equals $\lceil \psi(v)\rceil$; hence $G^v = G_{m+1}$ on such a segment and $G^v = G_{\lceil \psi(v)\rceil}$ in general. The same statements are transported to a valuation subring $A$ of an extension $L/K$ of fields, with $G$ the decomposition subgroup $A.\mathrm{decompositionSubgroup}\,K$, under the assumption that this subgroup is finite.
--
--   **Relation to Mathlib.** Mathlib supplies `Ideal.inertia` and `ValuationSubring.inertiaSubgroup`, which give only the index-zero step; the higher ramification groups in lower numbering, the Herbrand functions $\varphi$ and $\psi$, and the upper numbering are the project's own notions built on top of those.
--
--   **Where it is used.** These results convert between the lower and upper numbering of the ramification filtration, the form in which local ramification data is used in computations with the Galois representations occurring in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_Valuation_UpperRamificationGroupPsi.lean

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

theorem herbrandPhi_natCast_succ (m : ℕ) :
    herbrandPhi R G ((m : ℚ) + 1) =
      herbrandPhi R G m +
        (lowerRamificationCard R G (m + 1) : ℚ) / (lowerRamificationCard R G 0 : ℚ) := by
  have hcast : ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ) := by push_cast; ring
  have hsum : (∑ i ∈ Finset.Icc 1 (m + 1), (lowerRamificationCard R G i : ℚ)) =
      (∑ i ∈ Finset.Icc 1 m, (lowerRamificationCard R G i : ℚ)) +
        (lowerRamificationCard R G (m + 1) : ℚ) :=
    Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1) _
  rw [hcast, herbrandPhi_natCast, herbrandPhi_natCast, hsum, add_div]

theorem herbrandPhi_segment (m : ℕ) {u : ℚ} (h1 : (m : ℚ) ≤ u) (h2 : u ≤ (m : ℚ) + 1) :
    herbrandPhi R G u = herbrandPhi R G m +
      (u - m) * (lowerRamificationCard R G (m + 1) : ℚ) / (lowerRamificationCard R G 0 : ℚ) := by
  rcases eq_or_lt_of_le h2 with heq | hlt
  ·
    rw [heq, herbrandPhi_natCast_succ]
    ring
  · rcases le_or_gt u 0 with hu | hu
    ·
      have hm0 : m = 0 := by
        by_contra hm
        have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
        linarith
      subst hm0
      have hu0 : u = 0 := le_antisymm hu (by simpa using h1)
      subst hu0
      simp
    ·
      have hfloor : ⌊u⌋₊ = m := by
        rw [Nat.floor_eq_iff hu.le]
        exact ⟨h1, hlt⟩
      rw [herbrandPhi_of_pos hu, hfloor, herbrandPhi_natCast, add_div]

theorem herbrandPhi_segment_solve [Finite G] (m : ℕ) {v : ℚ}
    (h1 : herbrandPhi R G m ≤ v) (h2 : v ≤ herbrandPhi R G ((m : ℚ) + 1)) :
    herbrandPhi R G ((m : ℚ) + (v - herbrandPhi R G m) *
      (lowerRamificationCard R G 0 : ℚ) / (lowerRamificationCard R G (m + 1) : ℚ)) = v := by
  have hg0 : (0 : ℚ) < (lowerRamificationCard R G 0 : ℚ) :=
    Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) 0)
  have hgm : (0 : ℚ) < (lowerRamificationCard R G (m + 1) : ℚ) :=
    Nat.cast_pos.mpr (lowerRamificationCard_pos (R := R) (G := G) (m + 1))
  have hg0' : (lowerRamificationCard R G 0 : ℚ) ≠ 0 := hg0.ne'
  have hgm' : (lowerRamificationCard R G (m + 1) : ℚ) ≠ 0 := hgm.ne'

  have hrec : herbrandPhi R G ((m : ℚ) + 1) =
      herbrandPhi R G m +
        (lowerRamificationCard R G (m + 1) : ℚ) / (lowerRamificationCard R G 0 : ℚ) :=
    herbrandPhi_natCast_succ m
  have hsub : (v - herbrandPhi R G m) * (lowerRamificationCard R G 0 : ℚ) ≤
      (lowerRamificationCard R G (m + 1) : ℚ) := by
    have h2' : v - herbrandPhi R G m ≤
        (lowerRamificationCard R G (m + 1) : ℚ) / (lowerRamificationCard R G 0 : ℚ) := by
      rw [hrec] at h2
      linarith
    calc (v - herbrandPhi R G m) * (lowerRamificationCard R G 0 : ℚ)
        ≤ ((lowerRamificationCard R G (m + 1) : ℚ) / (lowerRamificationCard R G 0 : ℚ)) *
            (lowerRamificationCard R G 0 : ℚ) := mul_le_mul_of_nonneg_right h2' hg0.le
      _ = (lowerRamificationCard R G (m + 1) : ℚ) := by
          rw [div_mul_eq_mul_div, mul_div_assoc, div_self hg0', mul_one]
  have ht0 : 0 ≤ (v - herbrandPhi R G m) *
      (lowerRamificationCard R G 0 : ℚ) / (lowerRamificationCard R G (m + 1) : ℚ) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr h1) hg0.le) hgm.le
  have ht1 : (v - herbrandPhi R G m) *
      (lowerRamificationCard R G 0 : ℚ) / (lowerRamificationCard R G (m + 1) : ℚ) ≤ 1 := by
    rw [div_le_one hgm]
    exact hsub

  have hA : (m : ℚ) ≤ (m : ℚ) + (v - herbrandPhi R G m) *
      (lowerRamificationCard R G 0 : ℚ) / (lowerRamificationCard R G (m + 1) : ℚ) := by
    linarith
  have hB : (m : ℚ) + (v - herbrandPhi R G m) *
      (lowerRamificationCard R G 0 : ℚ) / (lowerRamificationCard R G (m + 1) : ℚ) ≤
      (m : ℚ) + 1 := by
    linarith
  rw [herbrandPhi_segment m hA hB]
  field_simp
  ring

theorem herbrandPhi_surjective [Finite G] : Function.Surjective (herbrandPhi R G) := by
  intro v
  rcases le_or_gt v 0 with hv | hv
  · exact ⟨v, herbrandPhi_of_nonpos hv⟩
  · have hvn : v ≤ herbrandPhi R G (upperRamificationIndex R G v : ℕ) :=
      le_herbrandPhi_upperRamificationIndex v
    have hn0 : upperRamificationIndex R G v ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, herbrandPhi_zero] at hvn
      exact absurd hvn (not_le.mpr hv)
    obtain ⟨m, hm⟩ : ∃ m, upperRamificationIndex R G v = m + 1 :=
      ⟨upperRamificationIndex R G v - 1, by omega⟩
    have hmlt : herbrandPhi R G m < v := by
      by_contra hle
      rw [not_lt] at hle
      have hcontra := upperRamificationIndex_le hle
      omega
    have hvle : v ≤ herbrandPhi R G ((m : ℚ) + 1) := by
      rw [hm] at hvn
      push_cast at hvn
      exact hvn
    exact ⟨_, herbrandPhi_segment_solve m hmlt.le hvle⟩

theorem herbrandPhi_bijective [Finite G] : Function.Bijective (herbrandPhi R G) :=
  ⟨herbrandPhi_injective, herbrandPhi_surjective⟩

theorem herbrandPhi_herbrandPsi [Finite G] (v : ℚ) :
    herbrandPhi R G (herbrandPsi R G v) = v :=
  Function.rightInverse_invFun (herbrandPhi_surjective (R := R) (G := G)) v

theorem herbrandPsi_rightInverse [Finite G] :
    Function.RightInverse (herbrandPsi R G) (herbrandPhi R G) :=
  herbrandPhi_herbrandPsi (R := R) (G := G)

theorem herbrandPsi_leftInverse [Finite G] :
    Function.LeftInverse (herbrandPsi R G) (herbrandPhi R G) :=
  herbrandPsi_herbrandPhi (R := R) (G := G)

theorem herbrandPsi_strictMono [Finite G] : StrictMono (herbrandPsi R G) := by
  intro v w hvw
  have h1 : herbrandPhi R G (herbrandPsi R G v) < herbrandPhi R G (herbrandPsi R G w) := by
    rwa [herbrandPhi_herbrandPsi, herbrandPhi_herbrandPsi]
  exact (herbrandPhi_strictMono (R := R) (G := G)).lt_iff_lt.mp h1

theorem herbrandPsi_monotone [Finite G] : Monotone (herbrandPsi R G) :=
  (herbrandPsi_strictMono (R := R) (G := G)).monotone

theorem herbrandPsi_injective [Finite G] : Function.Injective (herbrandPsi R G) :=
  (herbrandPsi_strictMono (R := R) (G := G)).injective

theorem herbrandPsi_surjective [Finite G] : Function.Surjective (herbrandPsi R G) :=
  fun u => ⟨herbrandPhi R G u, herbrandPsi_herbrandPhi u⟩

theorem herbrandPsi_bijective [Finite G] : Function.Bijective (herbrandPsi R G) :=
  ⟨herbrandPsi_injective, herbrandPsi_surjective⟩

theorem herbrandPsi_le_iff [Finite G] {v u : ℚ} :
    herbrandPsi R G v ≤ u ↔ v ≤ herbrandPhi R G u := by
  constructor
  · intro h
    have h2 := herbrandPhi_monotone (R := R) (G := G) h
    rwa [herbrandPhi_herbrandPsi] at h2
  · intro h
    have h2 := herbrandPsi_monotone (R := R) (G := G) h
    rwa [herbrandPsi_herbrandPhi] at h2

theorem le_herbrandPsi_iff [Finite G] {v u : ℚ} :
    u ≤ herbrandPsi R G v ↔ herbrandPhi R G u ≤ v := by
  constructor
  · intro h
    have h2 := herbrandPhi_monotone (R := R) (G := G) h
    rwa [herbrandPhi_herbrandPsi] at h2
  · intro h
    have h2 := herbrandPsi_monotone (R := R) (G := G) h
    rwa [herbrandPsi_herbrandPhi] at h2

theorem herbrandPsi_lt_iff [Finite G] {v u : ℚ} :
    herbrandPsi R G v < u ↔ v < herbrandPhi R G u := by
  rw [← not_le, ← not_le, le_herbrandPsi_iff]

theorem lt_herbrandPsi_iff [Finite G] {v u : ℚ} :
    u < herbrandPsi R G v ↔ herbrandPhi R G u < v := by
  rw [← not_le, ← not_le, herbrandPsi_le_iff]

theorem herbrandPsi_of_nonpos [Finite G] {v : ℚ} (h : v ≤ 0) : herbrandPsi R G v = v := by
  have h1 := herbrandPsi_herbrandPhi (R := R) (G := G) v
  rwa [herbrandPhi_of_nonpos h] at h1

theorem herbrandPsi_nonneg [Finite G] {v : ℚ} (h : 0 ≤ v) : 0 ≤ herbrandPsi R G v := by
  have h1 := herbrandPsi_monotone (R := R) (G := G) h
  rwa [herbrandPsi_zero] at h1

theorem herbrandPsi_pos [Finite G] {v : ℚ} (h : 0 < v) : 0 < herbrandPsi R G v := by
  have h1 := herbrandPsi_strictMono (R := R) (G := G) h
  rwa [herbrandPsi_zero] at h1

theorem herbrandPsi_segment [Finite G] (m : ℕ) {v : ℚ}
    (h1 : herbrandPhi R G m ≤ v) (h2 : v ≤ herbrandPhi R G ((m : ℚ) + 1)) :
    herbrandPsi R G v = (m : ℚ) + (v - herbrandPhi R G m) *
      (lowerRamificationCard R G 0 : ℚ) / (lowerRamificationCard R G (m + 1) : ℚ) := by
  have hsolve := herbrandPhi_segment_solve (R := R) (G := G) m h1 h2
  have h3 := herbrandPsi_herbrandPhi (R := R) (G := G) ((m : ℚ) + (v - herbrandPhi R G m) *
      (lowerRamificationCard R G 0 : ℚ) / (lowerRamificationCard R G (m + 1) : ℚ))
  rw [hsolve] at h3
  exact h3

theorem upperRamificationIndex_eq_zero_iff [Finite G] {v : ℚ} :
    upperRamificationIndex R G v = 0 ↔ v ≤ 0 := by
  constructor
  · intro h
    by_contra hv
    rw [not_le] at hv
    have hvn := le_herbrandPhi_upperRamificationIndex (R := R) (G := G) v
    rw [h, Nat.cast_zero, herbrandPhi_zero] at hvn
    exact absurd hvn (not_le.mpr hv)
  · exact upperRamificationIndex_of_nonpos

theorem upperRamificationIndex_eq_succ_iff [Finite G] {v : ℚ} {m : ℕ} :
    upperRamificationIndex R G v = m + 1 ↔
      herbrandPhi R G m < v ∧ v ≤ herbrandPhi R G ((m : ℚ) + 1) := by
  constructor
  · intro h
    constructor
    · by_contra hle
      rw [not_lt] at hle
      have hcontra := upperRamificationIndex_le hle
      omega
    · have hvn := le_herbrandPhi_upperRamificationIndex (R := R) (G := G) v
      rw [h] at hvn
      push_cast at hvn
      exact hvn
  · rintro ⟨h1, h2⟩
    have hub : upperRamificationIndex R G v ≤ m + 1 := by
      apply upperRamificationIndex_le
      push_cast
      exact h2
    have hlb : m < upperRamificationIndex R G v := by
      by_contra hle
      rw [not_lt] at hle
      have h3 : herbrandPhi R G ((upperRamificationIndex R G v : ℕ) : ℚ) ≤
          herbrandPhi R G (m : ℚ) :=
        herbrandPhi_monotone (R := R) (G := G) (by exact_mod_cast hle)
      have h4 := le_herbrandPhi_upperRamificationIndex (R := R) (G := G) v
      linarith
    omega

theorem upperRamificationIndex_eq_iff [Finite G] {v : ℚ} {n : ℕ} :
    upperRamificationIndex R G v = n ↔
      (n = 0 ∧ v ≤ herbrandPhi R G 0) ∨
        (herbrandPhi R G ((n - 1 : ℕ) : ℚ) < v ∧ v ≤ herbrandPhi R G ((n : ℕ) : ℚ)) := by
  rcases n with _ | m
  · rw [upperRamificationIndex_eq_zero_iff]
    constructor
    · intro h
      exact Or.inl ⟨rfl, by simpa using h⟩
    · rintro (⟨_, h⟩ | ⟨h1, h2⟩)
      · simpa using h
      ·
        simp only [Nat.zero_sub, Nat.cast_zero] at h1 h2
        linarith
  · rw [upperRamificationIndex_eq_succ_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine Or.inr ⟨?_, ?_⟩
      · simpa using h1
      · push_cast
        exact h2
    · rintro (⟨h0, _⟩ | ⟨h1, h2⟩)
      · exact absurd h0 (by omega)
      · constructor
        · simpa using h1
        · push_cast at h2
          exact h2

theorem upperRamificationGroup_of_lt_of_le [Finite G] {v : ℚ} {m : ℕ}
    (h1 : herbrandPhi R G m < v) (h2 : v ≤ herbrandPhi R G ((m : ℚ) + 1)) :
    upperRamificationGroup R G v = lowerRamificationGroup R G (m + 1) :=
  congrArg (lowerRamificationGroup R G)
    ((upperRamificationIndex_eq_succ_iff (R := R) (G := G)).mpr ⟨h1, h2⟩)

theorem upperRamificationGroup_eq_of_segment [Finite G] {v w : ℚ} {m : ℕ}
    (hv1 : herbrandPhi R G m < v) (hv2 : v ≤ herbrandPhi R G ((m : ℚ) + 1))
    (hw1 : herbrandPhi R G m < w) (hw2 : w ≤ herbrandPhi R G ((m : ℚ) + 1)) :
    upperRamificationGroup R G v = upperRamificationGroup R G w := by
  rw [upperRamificationGroup_of_lt_of_le hv1 hv2, upperRamificationGroup_of_lt_of_le hw1 hw2]

theorem upperRamificationIndex_eq_ceil_herbrandPsi [Finite G] (v : ℚ) :
    upperRamificationIndex R G v = ⌈herbrandPsi R G v⌉₊ := by
  rcases le_or_gt v 0 with hv | hv
  · rw [upperRamificationIndex_of_nonpos hv, herbrandPsi_of_nonpos hv]
    exact (Nat.ceil_eq_zero.mpr hv).symm
  · obtain ⟨m, hm⟩ : ∃ m, upperRamificationIndex R G v = m + 1 := by
      have h0 : upperRamificationIndex R G v ≠ 0 := by
        rw [Ne, upperRamificationIndex_eq_zero_iff]
        exact not_le.mpr hv
      exact ⟨upperRamificationIndex R G v - 1, by omega⟩
    obtain ⟨h1, h2⟩ := (upperRamificationIndex_eq_succ_iff (R := R) (G := G)).mp hm
    have hpsi1 : (m : ℚ) < herbrandPsi R G v :=
      (lt_herbrandPsi_iff (R := R) (G := G)).mpr h1
    have hpsi2 : herbrandPsi R G v ≤ (m : ℚ) + 1 :=
      (herbrandPsi_le_iff (R := R) (G := G)).mpr h2
    rw [hm]
    refine ((Nat.ceil_eq_iff (by omega : m + 1 ≠ 0)).mpr ?_).symm
    constructor
    · simpa using hpsi1
    · push_cast
      exact hpsi2

theorem upperRamificationGroup_eq_ceil_herbrandPsi [Finite G] (v : ℚ) :
    upperRamificationGroup R G v = lowerRamificationGroup R G ⌈herbrandPsi R G v⌉₊ :=
  congrArg (lowerRamificationGroup R G) (upperRamificationIndex_eq_ceil_herbrandPsi v)

end IsLocalRing

namespace ValuationSubring

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] {A : ValuationSubring L}

theorem herbrandPhi_surjective [Finite (A.decompositionSubgroup K)] :
    Function.Surjective (A.herbrandPhi K) :=
  IsLocalRing.herbrandPhi_surjective (R := A) (G := A.decompositionSubgroup K)

theorem herbrandPhi_herbrandPsi [Finite (A.decompositionSubgroup K)] (v : ℚ) :
    A.herbrandPhi K (A.herbrandPsi K v) = v :=
  IsLocalRing.herbrandPhi_herbrandPsi (R := A) (G := A.decompositionSubgroup K) v

theorem herbrandPsi_strictMono [Finite (A.decompositionSubgroup K)] :
    StrictMono (A.herbrandPsi K) :=
  IsLocalRing.herbrandPsi_strictMono (R := A) (G := A.decompositionSubgroup K)

theorem herbrandPsi_monotone [Finite (A.decompositionSubgroup K)] :
    Monotone (A.herbrandPsi K) :=
  IsLocalRing.herbrandPsi_monotone (R := A) (G := A.decompositionSubgroup K)

theorem upperRamificationGroup_of_lt_of_le [Finite (A.decompositionSubgroup K)] {v : ℚ} {m : ℕ}
    (h1 : A.herbrandPhi K m < v) (h2 : v ≤ A.herbrandPhi K ((m : ℚ) + 1)) :
    A.upperRamificationGroup K v = A.lowerRamificationGroup K (m + 1) :=
  IsLocalRing.upperRamificationGroup_of_lt_of_le
    (R := A) (G := A.decompositionSubgroup K) h1 h2

end ValuationSubring

section Gates

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] :
    IsLocalRing.herbrandPsi R G 1 = 1 := by
  have hphi : IsLocalRing.herbrandPhi R G ((1 : ℕ) : ℚ) = 1 := by
    rw [IsLocalRing.herbrandPhi_natCast, Finset.Icc_self, Finset.sum_singleton,
      IsLocalRing.lowerRamificationCard_of_subsingleton,
      IsLocalRing.lowerRamificationCard_of_subsingleton]
    norm_num
  have h := IsLocalRing.herbrandPsi_herbrandPhi (R := R) (G := G) ((1 : ℕ) : ℚ)
  rw [hphi] at h
  simpa using h

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Finite G] :
    IsLocalRing.herbrandPsi R G 0 < IsLocalRing.herbrandPsi R G 1 :=
  IsLocalRing.herbrandPsi_strictMono (by norm_num)

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Finite G] {v : ℚ}
    (h1 : 0 < v) (h2 : v ≤ IsLocalRing.herbrandPhi R G 1) :
    IsLocalRing.upperRamificationGroup R G v = IsLocalRing.lowerRamificationGroup R G 1 := by
  have h1' : IsLocalRing.herbrandPhi R G ((0 : ℕ) : ℚ) < v := by simpa using h1
  have h2' : v ≤ IsLocalRing.herbrandPhi R G (((0 : ℕ) : ℚ) + 1) := by simpa using h2
  simpa using IsLocalRing.upperRamificationGroup_of_lt_of_le h1' h2'

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Finite G] :
    IsLocalRing.herbrandPhi R G (IsLocalRing.herbrandPsi R G (5 / 2)) = 5 / 2 :=
  IsLocalRing.herbrandPhi_herbrandPsi _

end Gates

/--
info: 'IsLocalRing.herbrandPhi_natCast_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPhi_natCast_succ

/--
info: 'IsLocalRing.herbrandPhi_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPhi_segment

/--
info: 'IsLocalRing.herbrandPhi_segment_solve' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPhi_segment_solve

/--
info: 'IsLocalRing.herbrandPhi_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPhi_surjective

/--
info: 'IsLocalRing.herbrandPhi_herbrandPsi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPhi_herbrandPsi

/--
info: 'IsLocalRing.herbrandPsi_strictMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPsi_strictMono

/--
info: 'IsLocalRing.herbrandPsi_segment' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.herbrandPsi_segment

/--
info: 'IsLocalRing.upperRamificationIndex_eq_succ_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationIndex_eq_succ_iff

/--
info: 'IsLocalRing.upperRamificationGroup_of_lt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup_of_lt_of_le

/--
info: 'IsLocalRing.upperRamificationGroup_eq_ceil_herbrandPsi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.upperRamificationGroup_eq_ceil_herbrandPsi

/--
info: 'ValuationSubring.herbrandPhi_herbrandPsi' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.herbrandPhi_herbrandPsi


