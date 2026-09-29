-- Prove2me | Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
-- name    : Mathlib_RingTheory_Invariant_FixedSubringLocal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/fd2d4154-36bc-536d-88e9-475d8c841842
-- title:
--   Locality of fixed subrings under monoid actions
-- statement:
--   Throughout, $R$ is a ring carrying a `MulSemiringAction` of a monoid $M$ (i.e. $M$ acts on $R$ by ring endomorphisms), and `FixedPoints.subring R M` is Mathlib's subring $R^M$ of elements fixed by every $m \in M$; [`FixedPoints.mem_subring_iff`](../def/Mathlib_RingTheory_Invariant_FixedSubringLocal.html#L9) records that membership is exactly the condition $m \cdot x = x$ for all $m$. The basic observation is [`FixedPoints.smul_eq_self_of_mul_eq_one`](../def/Mathlib_RingTheory_Invariant_FixedSubringLocal.html#L13): if $a$ is fixed and $b$ is a two-sided inverse of $a$ ($ab = 1$ and $ba = 1$), then $b$ is fixed as well, since $a\,(m \cdot b) = 1$ and inverses are unique; hence [`FixedPoints.mem_subring_of_mul_eq_one`](../def/Mathlib_RingTheory_Invariant_FixedSubringLocal.html#L20) places such a $b$ in $R^M$, and [`FixedPoints.isUnit_subring_iff`](../def/Mathlib_RingTheory_Invariant_FixedSubringLocal.html#L24) states that an element $a$ of $R^M$ is a unit of $R^M$ if and only if its image in $R$ is a unit. Two instances follow: the inclusion `(FixedPoints.subring R M).subtype` is a local homomorphism, and if $R$ is a local ring then so is $R^M$, the decomposition $a + b = 1$ in $R^M$ being transported to $R$. [`FixedPoints.isLocalRing_subring_of_finite`](../def/Mathlib_RingTheory_Invariant_FixedSubringLocal.html#L53) is the same conclusion recorded for the action of a finite group $G$ on a commutative local ring.
--
--   For $R$ a commutative local ring, [`FixedPoints.mem_maximalIdeal_subring_iff`](../def/Mathlib_RingTheory_Invariant_FixedSubringLocal.html#L62) identifies the maximal ideal of $R^M$ elementwise with the preimage of $\mathfrak m_R$, [`FixedPoints.maximalIdeal_subring_eq_comap`](../def/Mathlib_RingTheory_Invariant_FixedSubringLocal.html#L69) states this as the ideal equality $\mathfrak m_{R^M} = \mathfrak m_R \cap R^M$ (a `comap` along the inclusion), and [`FixedPoints.isMaximal_comap_maximalIdeal_subring`](../def/Mathlib_RingTheory_Invariant_FixedSubringLocal.html#L76) restates that this contraction is a maximal ideal. Finally, degenerate cases: $R^M = \top$ when every $m$ acts trivially, in particular when $M$ is a subsingleton, in which case [`FixedPoints.subringEquivOfSubsingleton`](../def/Mathlib_RingTheory_Invariant_FixedSubringLocal.html#L96) is the resulting ring isomorphism $R^M \cong R$.
--
--   **Relation to Mathlib.** `FixedPoints.subring` is Mathlib's fixed-point subring for a `MulSemiringAction`; this module adds, in the same namespace, the unit-detection, local-ring and maximal-ideal statements for it.
--
--   **Where it is used.** These lemmas supply the local-ring bookkeeping needed when a local ring is replaced by the fixed subring of a group acting on it, for instance in the valuation- and Herbrand-quotient arguments of the ramification-theoretic layer of the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_Invariant_FixedSubringLocal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace FixedPoints

section Ring

variable {R : Type*} [Ring R] {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem mem_subring_iff {x : R} :
    x ∈ FixedPoints.subring R M ↔ ∀ m : M, m • x = x :=
  Iff.rfl

theorem smul_eq_self_of_mul_eq_one {a b : R} (ha : a ∈ FixedPoints.subring R M)
    (hab : a * b = 1) (hba : b * a = 1) (m : M) : m • b = b := by
  have key : a * (m • b) = 1 := by
    have h : m • (a * b) = m • (1 : R) := congrArg (m • ·) hab
    rwa [smul_mul', mem_subring_iff.mp ha m, smul_one] at h
  exact (left_inv_eq_right_inv hba key).symm

theorem mem_subring_of_mul_eq_one {a b : R} (ha : a ∈ FixedPoints.subring R M)
    (hab : a * b = 1) (hba : b * a = 1) : b ∈ FixedPoints.subring R M :=
  mem_subring_iff.mpr fun m => smul_eq_self_of_mul_eq_one ha hab hba m

theorem isUnit_subring_iff (a : FixedPoints.subring R M) :
    IsUnit a ↔ IsUnit (a : R) := by
  constructor
  · intro h
    simpa using h.map (FixedPoints.subring R M).subtype
  · intro h
    obtain ⟨b, hab, hba⟩ := isUnit_iff_exists.mp h
    refine isUnit_iff_exists.mpr
      ⟨⟨b, mem_subring_of_mul_eq_one a.2 hab hba⟩, Subtype.ext ?_, Subtype.ext ?_⟩
    · simpa using hab
    · simpa using hba

instance isLocalHom_subring_subtype :
    IsLocalHom (FixedPoints.subring R M).subtype :=
  ⟨fun a h => (isUnit_subring_iff a).mpr (by simpa using h)⟩

instance isLocalRing_subring [IsLocalRing R] :
    IsLocalRing (FixedPoints.subring R M) :=
  ⟨fun {a b} hab => by
    have h : (a : R) + (b : R) = 1 := by
      have h1 : ((a + b : FixedPoints.subring R M) : R) = ((1 : FixedPoints.subring R M) : R) :=
        congrArg Subtype.val hab
      simpa using h1
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h' | h'
    · exact Or.inl ((isUnit_subring_iff a).mpr h')
    · exact Or.inr ((isUnit_subring_iff b).mpr h')⟩

end Ring

theorem isLocalRing_subring_of_finite {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] :
    IsLocalRing (FixedPoints.subring R G) :=
  isLocalRing_subring

section MaximalIdeal

variable {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem mem_maximalIdeal_subring_iff {a : FixedPoints.subring R M} :
    a ∈ IsLocalRing.maximalIdeal (FixedPoints.subring R M) ↔
      (a : R) ∈ IsLocalRing.maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff]
  exact not_congr (isUnit_subring_iff a)

theorem maximalIdeal_subring_eq_comap :
    IsLocalRing.maximalIdeal (FixedPoints.subring R M) =
      Ideal.comap (FixedPoints.subring R M).subtype (IsLocalRing.maximalIdeal R) := by
  ext a
  rw [Ideal.mem_comap, Subring.subtype_apply]
  exact mem_maximalIdeal_subring_iff

theorem isMaximal_comap_maximalIdeal_subring :
    (Ideal.comap (FixedPoints.subring R M).subtype (IsLocalRing.maximalIdeal R)).IsMaximal := by
  rw [← maximalIdeal_subring_eq_comap (R := R) (M := M)]
  exact IsLocalRing.maximalIdeal.isMaximal _

end MaximalIdeal

section Degenerate

variable {R : Type*} [Ring R] {M : Type*} [Monoid M] [MulSemiringAction M R]

theorem subring_eq_top_of_forall_smul_eq (h : ∀ (m : M) (x : R), m • x = x) :
    FixedPoints.subring R M = ⊤ :=
  (Subring.eq_top_iff' _).mpr fun x => mem_subring_iff.mpr fun m => h m x

theorem subring_eq_top_of_subsingleton [Subsingleton M] :
    FixedPoints.subring R M = ⊤ :=
  subring_eq_top_of_forall_smul_eq fun m x => by
    rw [Subsingleton.elim m 1, one_smul]

def subringEquivOfSubsingleton [Subsingleton M] :
    FixedPoints.subring R M ≃+* R :=
  (RingEquiv.subringCongr (subring_eq_top_of_subsingleton (R := R) (M := M))).trans
    Subring.topEquiv

end Degenerate

end FixedPoints

section Gates

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    (H : Subgroup G) : IsLocalRing (FixedPoints.subring R H) :=
  inferInstance

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R]
    (H : Subgroup G) [H.Normal] :
    IsLocalRing (FixedPoints.subring R H) ∧
      Nonempty (MulSemiringAction (G ⧸ H) (FixedPoints.subring R H)) :=
  ⟨inferInstance, ⟨inferInstance⟩⟩

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [Finite G]
    [MulSemiringAction G R] :
    IsLocalRing (FixedPoints.subring R G) ∧
      IsLocalRing.maximalIdeal (FixedPoints.subring R G) =
        Ideal.comap (Subring.subtype (FixedPoints.subring R G)) (IsLocalRing.maximalIdeal R) :=
  ⟨FixedPoints.isLocalRing_subring_of_finite, FixedPoints.maximalIdeal_subring_eq_comap⟩

example : IsLocalRing (FixedPoints.subring ℚ (ℚ →+* ℚ)) :=
  inferInstance

example : IsLocalHom (FixedPoints.subring ℚ (ℚ →+* ℚ)).subtype :=
  inferInstance

example {R : Type*} [CommRing R] (M : Type*) [Monoid M] :
    letI : MulSemiringAction M R := MulSemiringAction.compHom R (1 : M →* (R →+* R))
    FixedPoints.subring R M = ⊤ := by
  letI : MulSemiringAction M R := MulSemiringAction.compHom R (1 : M →* (R →+* R))
  exact FixedPoints.subring_eq_top_of_forall_smul_eq fun m x => rfl

example {R : Type*} [CommRing R] [IsLocalRing R] (M : Type*) [Monoid M] [Subsingleton M]
    [MulSemiringAction M R] :
    (FixedPoints.subring R M = ⊤) ∧
      Nonempty ((FixedPoints.subring R M) ≃+* R) ∧
      IsLocalRing (FixedPoints.subring R M) :=
  ⟨FixedPoints.subring_eq_top_of_subsingleton,
    ⟨FixedPoints.subringEquivOfSubsingleton⟩, inferInstance⟩

example {R : Type*} [CommRing R] [IsLocalRing R] {M : Type*} [Monoid M]
    [MulSemiringAction M R] :
    (0 : FixedPoints.subring R M) ∈ IsLocalRing.maximalIdeal (FixedPoints.subring R M) ∧
      (1 : FixedPoints.subring R M) ∉ IsLocalRing.maximalIdeal (FixedPoints.subring R M) :=
  ⟨Ideal.zero_mem _,
    fun h => mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h) isUnit_one⟩

example {R : Type*} [CommRing R] {M : Type*} [Monoid M] [MulSemiringAction M R]
    (a : FixedPoints.subring R M) (h : ¬ IsUnit (a : R)) : ¬ IsUnit a :=
  fun ha => h ((FixedPoints.isUnit_subring_iff a).mp ha)

end Gates

/-- info: 'FixedPoints.mem_subring_iff' depends on axioms: [propext] -/
#guard_msgs in #print axioms FixedPoints.mem_subring_iff

/-- info: 'FixedPoints.smul_eq_self_of_mul_eq_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms FixedPoints.smul_eq_self_of_mul_eq_one

/-- info: 'FixedPoints.mem_subring_of_mul_eq_one' depends on axioms: [propext] -/
#guard_msgs in #print axioms FixedPoints.mem_subring_of_mul_eq_one

/-- info: 'FixedPoints.isUnit_subring_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.isUnit_subring_iff

/-- info: 'FixedPoints.isLocalHom_subring_subtype' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.isLocalHom_subring_subtype

/-- info: 'FixedPoints.isLocalRing_subring' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.isLocalRing_subring

/-- info: 'FixedPoints.isLocalRing_subring_of_finite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.isLocalRing_subring_of_finite

/-- info: 'FixedPoints.mem_maximalIdeal_subring_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.mem_maximalIdeal_subring_iff

/-- info: 'FixedPoints.maximalIdeal_subring_eq_comap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms FixedPoints.maximalIdeal_subring_eq_comap

/--
info: 'FixedPoints.isMaximal_comap_maximalIdeal_subring' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FixedPoints.isMaximal_comap_maximalIdeal_subring

/--
info: 'FixedPoints.subring_eq_top_of_forall_smul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FixedPoints.subring_eq_top_of_forall_smul_eq

/--
info: 'FixedPoints.subring_eq_top_of_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FixedPoints.subring_eq_top_of_subsingleton

/--
info: 'FixedPoints.subringEquivOfSubsingleton' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FixedPoints.subringEquivOfSubsingleton


