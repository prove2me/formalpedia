-- Prove2me | Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup
-- name    : Mathlib_RingTheory_Valuation_LowerRamificationGroup
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/5ca03b91-55b0-5411-8835-4b11cc967afc
-- title:
--   Lower ramification groups for a group acting on a local ring
-- statement:
--   For a commutative local ring $R$ with maximal ideal $\mathfrak m$ and a group $G$ acting on $R$ by ring automorphisms (`MulSemiringAction G R`), [`IsLocalRing.lowerRamificationGroup R G i`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L58) is defined, for $i : \mathbb N$, as the inertia subgroup of the ideal $\mathfrak m^{i+1}$, i.e. the subgroup
--   $$G_i = \{\sigma \in G : \sigma \cdot x - x \in \mathfrak m^{i+1}\ \text{for all}\ x \in R\},$$
--   and membership is recorded in exactly this form. The accompanying results are: $G_i$ is antitone in $i$ (from $\mathfrak m^{j+1} \subseteq \mathfrak m^{i+1}$ for $i \le j$); each $G_i$ is a normal subgroup of $G$; $G_0$ is the inertia subgroup of $\mathfrak m$ itself and also the kernel of the induced homomorphism $G \to \mathrm{Aut}(R/\mathfrak m)$ into the ring automorphisms of the residue field; and, under the separatedness hypothesis $\bigcap_n \mathfrak m^n = 0$, the intersection $\bigcap_i G_i$ lies in the kernel of $G \to \mathrm{Aut}(R)$, hence equals the trivial subgroup when the action is faithful.
--
--   The supporting lemmas of general use are: monotonicity of the inertia subgroup of an additive subgroup, resp. of an ideal, in that subgroup; the inertia subgroup of the unit ideal is all of $G$; the inertia subgroup of an ideal stable under the $G$-action is normal; and the stability of $\mathfrak m$, and of each power $\mathfrak m^n$, under the pointwise action of any $g \in G$ on ideals.
--
--   The construction is then transported to valuation subrings: for a field extension $L/K$ and a valuation subring $A \subseteq L$, [`ValuationSubring.lowerRamificationGroup K A i`](../def/Mathlib_RingTheory_Valuation_LowerRamificationGroup.html#L130) is the above subgroup for the local ring $A$ acted on by the decomposition subgroup $A.\mathrm{decompositionSubgroup}\ K$. It is again antitone and normal, its value at $i = 0$ is the inertia subgroup $A.\mathrm{inertiaSubgroup}\ K$, and every $G_i$ is contained in that inertia subgroup.
--
--   **Relation to Mathlib.** The definitions are built on Mathlib's `Ideal.inertia`, `ValuationSubring.decompositionSubgroup` and `ValuationSubring.inertiaSubgroup`; Mathlib provides the inertia subgroup but not the higher lower-numbering filtration $G_i$, which is this project's own.
--
--   **Where it is used.** The filtration $G_0 \supseteq G_1 \supseteq \cdots$ of a decomposition group is the standard tool for separating the tame and wild parts of local ramification; it is used in the local analysis of Galois representations attached to elliptic curves and in conductor computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

namespace AddSubgroup

variable {M : Type*} [AddGroup M] {G : Type*} [Group G] [MulAction G M]

theorem inertia_mono {I J : AddSubgroup M} (h : I ≤ J) : I.inertia G ≤ J.inertia G :=
  fun _ hσ x => h (hσ x)

end AddSubgroup

namespace Ideal

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem inertia_mono {I J : Ideal R} (h : I ≤ J) :
    I.inertia G ≤ J.inertia G :=
  AddSubgroup.inertia_mono (Submodule.toAddSubgroup_mono h)

@[simp]
theorem inertia_top : (⊤ : Ideal R).inertia G = ⊤ := by
  ext; simp [Ideal.inertia, AddSubgroup.inertia]

theorem inertia_normal_of_forall_smul_eq {I : Ideal R}
    (hI : ∀ g : G, g • I = I) : (I.inertia G).Normal := by
  refine ⟨fun σ hσ τ x => ?_⟩

  have key : τ • (σ • (τ⁻¹ • x) - τ⁻¹ • x) ∈ τ • I :=
    Ideal.smul_mem_pointwise_smul _ _ _ (hσ _)
  simpa [smul_sub, smul_smul, mul_assoc, hI τ] using key

end Ideal

namespace IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {G : Type*} [Group G] [MulSemiringAction G R]

@[simp]
theorem pointwise_smul_maximalIdeal (g : G) :
    g • maximalIdeal R = maximalIdeal R := by
  refine le_antisymm (le_maximalIdeal_of_isPrime _) ?_
  rw [Ideal.subset_pointwise_smul_iff]
  exact le_maximalIdeal_of_isPrime _

@[simp]
theorem pointwise_smul_maximalIdeal_pow (g : G) (n : ℕ) :
    g • (maximalIdeal R) ^ n = (maximalIdeal R) ^ n := by
  rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def,
    pointwise_smul_maximalIdeal]

variable (R G) in

def lowerRamificationGroup (i : ℕ) : Subgroup G :=
  ((maximalIdeal R) ^ (i + 1)).inertia G

variable {i : ℕ}

@[simp]
theorem mem_lowerRamificationGroup {σ : G} :
    σ ∈ lowerRamificationGroup R G i ↔ ∀ x : R, σ • x - x ∈ (maximalIdeal R) ^ (i + 1) :=
  Iff.rfl

theorem lowerRamificationGroup_antitone :
    Antitone (lowerRamificationGroup R G) := fun _ _ hij =>
  Ideal.inertia_mono (Ideal.pow_le_pow_right (by omega))

instance lowerRamificationGroup_normal (i : ℕ) :
    (lowerRamificationGroup R G i).Normal :=
  Ideal.inertia_normal_of_forall_smul_eq fun g => pointwise_smul_maximalIdeal_pow g (i + 1)

theorem lowerRamificationGroup_zero_eq_ker :
    lowerRamificationGroup R G 0 =
      MonoidHom.ker (MulSemiringAction.toRingAut G (ResidueField R)) := by
  ext σ
  simp only [mem_lowerRamificationGroup, zero_add, pow_one, MonoidHom.mem_ker]
  constructor
  · intro hσ
    ext y
    obtain ⟨r, rfl⟩ := residue_surjective y
    have : residue R (σ • r - r) = 0 := (residue_eq_zero_iff _).mpr (hσ r)
    simpa [sub_eq_zero, ResidueField.residue_smul] using this
  · intro hσ r
    rw [← residue_eq_zero_iff, map_sub, ResidueField.residue_smul, sub_eq_zero]
    exact DFunLike.congr_fun hσ (residue R r)

theorem lowerRamificationGroup_zero_eq_inertia :
    lowerRamificationGroup R G 0 = (maximalIdeal R).inertia G := by
  simp only [lowerRamificationGroup, zero_add, pow_one]

theorem lowerRamificationGroup_le_zero (i : ℕ) :
    lowerRamificationGroup R G i ≤ lowerRamificationGroup R G 0 :=
  lowerRamificationGroup_antitone (Nat.zero_le i)

theorem iInf_lowerRamificationGroup_le_ker_toRingAut
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) :
    ⨅ i, lowerRamificationGroup R G i ≤
      MonoidHom.ker (MulSemiringAction.toRingAut G R) := by
  intro σ hσ
  simp only [Subgroup.mem_iInf, mem_lowerRamificationGroup] at hσ
  ext x
  have : σ • x - x ∈ ⨅ n, (maximalIdeal R) ^ n := by
    simp only [Ideal.mem_iInf]
    intro n
    rcases n with _ | n
    · simp
    · exact hσ n x
  rw [hsep] at this
  simpa [sub_eq_zero] using this

theorem iInf_lowerRamificationGroup_eq_bot
    (hsep : ⨅ n, (maximalIdeal R) ^ n = ⊥) [FaithfulSMul G R] :
    ⨅ i, lowerRamificationGroup R G i = (⊥ : Subgroup G) := by
  refine le_bot_iff.mp fun σ hσ => ?_
  have h := iInf_lowerRamificationGroup_le_ker_toRingAut hsep hσ
  rw [MonoidHom.mem_ker] at h
  exact FaithfulSMul.eq_of_smul_eq_smul (α := R) fun x => by
    have := DFunLike.congr_fun h x; simpa using this.trans (one_smul G x).symm

end IsLocalRing

namespace ValuationSubring

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

def lowerRamificationGroup (A : ValuationSubring L) (i : ℕ) :
    Subgroup (A.decompositionSubgroup K) :=
  IsLocalRing.lowerRamificationGroup A (A.decompositionSubgroup K) i

variable {K} {A : ValuationSubring L} {i : ℕ}

@[simp]
theorem mem_lowerRamificationGroup {σ : A.decompositionSubgroup K} :
    σ ∈ A.lowerRamificationGroup K i ↔
      ∀ a : A, σ • a - a ∈ (IsLocalRing.maximalIdeal A) ^ (i + 1) :=
  Iff.rfl

theorem lowerRamificationGroup_antitone :
    Antitone (A.lowerRamificationGroup K) :=
  IsLocalRing.lowerRamificationGroup_antitone

instance lowerRamificationGroup_normal (i : ℕ) :
    (A.lowerRamificationGroup K i).Normal :=
  IsLocalRing.lowerRamificationGroup_normal i

theorem lowerRamificationGroup_zero :
    A.lowerRamificationGroup K 0 = A.inertiaSubgroup K :=
  IsLocalRing.lowerRamificationGroup_zero_eq_ker

theorem lowerRamificationGroup_le_inertiaSubgroup (i : ℕ) :
    A.lowerRamificationGroup K i ≤ A.inertiaSubgroup K :=
  lowerRamificationGroup_zero (K := K) (A := A) ▸ IsLocalRing.lowerRamificationGroup_le_zero i

end ValuationSubring

section Gates

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] [Subsingleton G] (i : ℕ) :
    IsLocalRing.lowerRamificationGroup R G i = ⊤ := by
  ext σ; simp [Subsingleton.elim σ 1]

example {R : Type*} [CommRing R] [IsLocalRing R]
    {G : Type*} [Group G] [MulSemiringAction G R] :
    IsLocalRing.lowerRamificationGroup R G 1 ≤
      IsLocalRing.lowerRamificationGroup R G 0 :=
  IsLocalRing.lowerRamificationGroup_antitone (by omega)

example {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R] :
    (IsLocalRing.lowerRamificationGroup R G 0 : Set G) =
      ((IsLocalRing.maximalIdeal R).inertia G : Set G) := by
  rw [IsLocalRing.lowerRamificationGroup_zero_eq_inertia]

end Gates

/--
info: 'IsLocalRing.lowerRamificationGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup

/--
info: 'IsLocalRing.lowerRamificationGroup_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_antitone

/--
info: 'IsLocalRing.lowerRamificationGroup_normal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_normal

/--
info: 'IsLocalRing.lowerRamificationGroup_zero_eq_ker' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.lowerRamificationGroup_zero_eq_ker

/--
info: 'IsLocalRing.iInf_lowerRamificationGroup_eq_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms IsLocalRing.iInf_lowerRamificationGroup_eq_bot

/--
info: 'ValuationSubring.lowerRamificationGroup_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_zero

/--
info: 'ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms ValuationSubring.lowerRamificationGroup_le_inertiaSubgroup


