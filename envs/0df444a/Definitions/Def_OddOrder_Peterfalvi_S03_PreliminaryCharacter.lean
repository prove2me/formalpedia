-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S03_PreliminaryCharacter
-- name    : OddOrder_Peterfalvi_S03_PreliminaryCharacter
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:38:59.909049+00:00
-- url     : https://prove2.me/theorems/730d0523-c652-4409-be02-dc37494eb7d1
-- title:
--   Peterfalvi §3: preliminary results from character theory
-- statement:
--   The Lean entry point for Peterfalvi, *Character Theory for the Odd Order Theorem*, §3 (pp. 5–9), numbered assertions (1.1)–(1.10). They depend on the character-theory modules for Brauer permutation, Clifford theory, induced characters, second orthogonality and the isometry difference-pair lemma. The file records shared predicates and submodules used by §4–§8.
--
--   Main definitions: `nonidentityElements` ($G^\#$), `ClosedUnderConjugate` (a set of class functions closed under complex conjugation), `HasNoRealCharacters`, `nontrivialIrreducibleClassFunctions` (class functions from nontrivial irreducible characters), `characterDegree` (value at the identity) and `centralizerInSubgroup` ($C_H(g)$ as a subgroup of $G$).
--
--   The bundle also proves 31 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S03_PreliminaryCharacter.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutation
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Clifford
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IsometryDifferencePair
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SecondOrthogonality

namespace OddOrder.Peterfalvi.S03

open OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G]

/-- The nonidentity part `G#`, used throughout Peterfalvi's reduced character
spaces. -/
def nonidentityElements (G : Type*) [One G] : Set G :=
  {g | g ≠ 1}

@[simp] theorem mem_nonidentityElements {g : G} :
    g ∈ nonidentityElements G ↔ g ≠ 1 :=
  Iff.rfl

/-- A set of class functions is closed under complex conjugation. -/
def ClosedUnderConjugate (S : Set (ClassFunction G ℂ)) : Prop :=
  ∀ ⦃χ : ClassFunction G ℂ⦄, χ ∈ S → χ.conj ∈ S

/-- A set of class functions contains no real class functions. -/
def HasNoRealCharacters (S : Set (ClassFunction G ℂ)) : Prop :=
  ∀ ⦃χ : ClassFunction G ℂ⦄, χ ∈ S → ¬ χ.IsReal

theorem ClosedUnderConjugate.conj_mem {S : Set (ClassFunction G ℂ)}
    (hS : ClosedUnderConjugate S) {χ : ClassFunction G ℂ} (hχ : χ ∈ S) :
    χ.conj ∈ S :=
  hS hχ

theorem HasNoRealCharacters.mono {S T : Set (ClassFunction G ℂ)}
    (hS : HasNoRealCharacters S) (hTS : T ⊆ S) :
    HasNoRealCharacters T := by
  intro χ hχ
  exact hS (hTS hχ)

theorem HasNoRealCharacters.not_mem_of_isReal {S : Set (ClassFunction G ℂ)}
    (hS : HasNoRealCharacters S) {χ : ClassFunction G ℂ} (hχ : χ.IsReal) :
    χ ∉ S := by
  intro hmem
  exact hS hmem hχ

/-- The set of class functions arising from the *nontrivial* irreducible complex
characters of `G`.

This is Peterfalvi's `Irr(G) ∖ {1_G}`, viewed inside `CF(G)`.  It is the concrete
source set whose `HasNoRealCharacters` property (under odd order) discharges the
`no_real_characters` field of the §7 coherence hypothesis. -/
def nontrivialIrreducibleClassFunctions (G : Type*) [Group G] :
    Set (ClassFunction G ℂ) :=
  {φ | ∃ χ : IrreducibleCharacter G,
    χ ≠ trivialIrreducibleCharacter G ∧ (χ : ClassFunction G ℂ) = φ}

@[simp] theorem mem_nontrivialIrreducibleClassFunctions {φ : ClassFunction G ℂ} :
    φ ∈ nontrivialIrreducibleClassFunctions G ↔
      ∃ χ : IrreducibleCharacter G,
        χ ≠ trivialIrreducibleCharacter G ∧ (χ : ClassFunction G ℂ) = φ :=
  Iff.rfl

/-- The degree of a complex class function, i.e. its value at the identity.

For genuine characters this is the representation degree.  Naming it here keeps
Peterfalvi's degree hypotheses from unfolding to raw evaluation at `1`. -/
def characterDegree (χ : ClassFunction G ℂ) : ℂ :=
  χ 1

@[simp] theorem characterDegree_def (χ : ClassFunction G ℂ) :
    characterDegree χ = χ 1 :=
  rfl

@[simp] theorem characterDegree_conj (χ : ClassFunction G ℂ) :
    characterDegree χ.conj = star (characterDegree χ) :=
  rfl

@[simp] theorem characterDegree_trivialClassFunction :
    characterDegree (trivialClassFunction G) = 1 :=
  rfl

/-- **The degree of an irreducible character divides the group order**, phrased through Peterfalvi's
`characterDegree` (Isaacs, *Character Theory of Finite Groups*, Thm 3.11; the degree datum behind
Peterfalvi (6.7)).  For an irreducible character `χ` of a finite group `G` there is a positive
natural number `n` with `characterDegree χ = n` and `n ∣ |G|`.

This is the consumer-facing form of the integrality theory: `characterDegree χ` is definitionally
`χ 1` (`characterDegree_def`), and the `IsIrreducibleCharacter`/`ClassFunction` bridge
`exists_natDegree_charValue_one_dvd_card` carries `finrank_dvd_card` (the dimension of any
witnessing representation divides `|G|`) onto that value.  Because `characterDegree` ranges over
`ℂ`, the divisibility is recorded on the natural witness `n`, with `characterDegree χ = (n : ℂ)`
tying the two together. -/
theorem exists_natDegree_characterDegree_dvd_card [Finite G]
    (χ : IrreducibleCharacter G) :
    ∃ n : ℕ, 0 < n ∧ characterDegree (χ : ClassFunction G ℂ) = (n : ℂ) ∧ n ∣ Nat.card G := by
  obtain ⟨n, hpos, hval, hdvd⟩ := χ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  exact ⟨n, hpos, by rw [characterDegree_def]; exact hval, hdvd⟩

/-- **The degree of an irreducible character of a `p`-group is a power of `p`**, phrased through
Peterfalvi's `characterDegree` (Isaacs, *Character Theory of Finite Groups*, Cor. 3.12; the degree
datum behind Peterfalvi (6.6)).  For an irreducible character `χ` of a finite `p`-group `G` there
is a natural number `k` with `characterDegree χ = p ^ k`.

This is the consumer-facing form, through `characterDegree`, of
`IsIrreducibleCharacter.exists_charValue_one_eq_prime_pow_of_isPGroup`: under Hypothesis (6.4) with
`M = 1`, once (6.5.b) gives that `K` is a non-abelian `p`-group, every `θ ∈ Irr K` has `θ(1)` a
power of `p` (Peterfalvi (6.6) proof, mmd L80).  Because `characterDegree χ` is *definitionally*
`χ 1` (`characterDegree_def`), this is exactly that statement recast over the value `χ 1`. -/
theorem exists_characterDegree_eq_prime_pow_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G) (χ : IrreducibleCharacter G) :
    ∃ k : ℕ, characterDegree (χ : ClassFunction G ℂ) = (p ^ k : ℂ) := by
  obtain ⟨k, hk⟩ := χ.isIrreducible.exists_charValue_one_eq_prime_pow_of_isPGroup hp
  exact ⟨k, by rw [characterDegree_def]; exact hk⟩

/-- **Natural degree witness for p-group irreducible characters.**

This packages the p-power degree result in the form consumed by the (6.6) degree-gap assembly:
the same natural witness `d` both evaluates `characterDegree χ = d` and is a prime power `p^k`.
The positivity is included so downstream ratio and divisibility lemmas can avoid reopening the
irreducible-character degree witness. -/
theorem exists_natDegree_characterDegree_eq_prime_pow_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : IsPGroup p G) (χ : IrreducibleCharacter G) :
    ∃ d k : ℕ, 0 < d ∧ characterDegree (χ : ClassFunction G ℂ) = (d : ℂ) ∧ d = p ^ k := by
  obtain ⟨k, hk⟩ := exists_characterDegree_eq_prime_pow_of_isPGroup hp χ
  have hk_nat : characterDegree (χ : ClassFunction G ℂ) = ((p ^ k : ℕ) : ℂ) := by
    simpa [Nat.cast_pow] using hk
  refine ⟨p ^ k, k, ?_, hk_nat, rfl⟩
  exact pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) k

/-- `C_H(g)`, viewed as a subgroup of the ambient group `G`.  This is the
centralizer expression in Peterfalvi (1.2). -/
def centralizerInSubgroup (H : Subgroup G) (g : G) : Subgroup G :=
  H ⊓ Subgroup.centralizer ({g} : Set G)

@[simp] theorem mem_centralizerInSubgroup {H : Subgroup G} {g x : G} :
    x ∈ centralizerInSubgroup H g ↔ x ∈ H ∧ x * g = g * x := by
  simp [centralizerInSubgroup, Subgroup.mem_centralizer_singleton_iff]

/-- The character kernel predicate `g ∈ ker χ`, expressed at the class-function
level by `χ(g) = χ(1)`.  For genuine characters this matches the usual kernel
condition. -/
def characterKernel (χ : ClassFunction G ℂ) : Set G :=
  {g | χ g = characterDegree χ}

@[simp] theorem mem_characterKernel {χ : ClassFunction G ℂ} {g : G} :
    g ∈ characterKernel χ ↔ χ g = characterDegree χ :=
  Iff.rfl

@[simp] theorem one_mem_characterKernel (χ : ClassFunction G ℂ) :
    (1 : G) ∈ characterKernel χ :=
  rfl

@[simp] theorem characterKernel_trivialClassFunction :
    characterKernel (trivialClassFunction G) = Set.univ := by
  ext g
  simp [characterKernel, characterDegree]

@[simp] theorem characterKernel_conj (χ : ClassFunction G ℂ) :
    characterKernel χ.conj = characterKernel χ := by
  ext g
  change star (χ g) = star (χ 1) ↔ χ g = χ 1
  exact star_inj

section CharacterKernelSubgroup

variable {Γ : Type*} [Group Γ] [Finite Γ]

/-- **`ker φ` is closed under multiplication for a genuine character `φ`.**  Writing `φ = χ_ρ`,
`rep_eq_id_of_character_eq_one` turns `x, y ∈ ker φ` into `ρ x = ρ y = id`, so `ρ (xy) = id` and
`φ(xy) = tr(id) = φ(1)`. -/
theorem characterKernel_mul_mem {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ)
    {x y : Γ} (hx : x ∈ characterKernel φ) (hy : y ∈ characterKernel φ) :
    x * y ∈ characterKernel φ := by
  classical
  obtain ⟨V, _, _, _, ρ, hchar⟩ := hφ
  have hval : ∀ g : Γ, φ g = ρ.character g := fun g => congrFun hchar g
  rw [mem_characterKernel, characterDegree_def] at hx hy
  have hidx : ρ x = LinearMap.id :=
    rep_eq_id_of_character_eq_one ρ (by simp only [← hval]; exact hx)
  have hidy : ρ y = LinearMap.id :=
    rep_eq_id_of_character_eq_one ρ (by simp only [← hval]; exact hy)
  have hidxy : ρ (x * y) = LinearMap.id := by
    rw [map_mul, hidx, hidy]; ext v; simp
  rw [mem_characterKernel, characterDegree_def, hval (x * y), hval 1,
    show ρ.character (x * y) = LinearMap.trace ℂ V (ρ (x * y)) from rfl, hidxy,
    Representation.char_one, LinearMap.trace_id]

/-- **`ker φ` is closed under inversion for a genuine character `φ`.**  From `ρ x = id`,
`ρ x⁻¹ = (ρ x)⁻¹ = id` (via `ρ x⁻¹ · ρ x = ρ 1 = 1`). -/
theorem characterKernel_inv_mem {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ)
    {x : Γ} (hx : x ∈ characterKernel φ) : x⁻¹ ∈ characterKernel φ := by
  classical
  obtain ⟨V, _, _, _, ρ, hchar⟩ := hφ
  have hval : ∀ g : Γ, φ g = ρ.character g := fun g => congrFun hchar g
  rw [mem_characterKernel, characterDegree_def] at hx
  have hidx : ρ x = LinearMap.id :=
    rep_eq_id_of_character_eq_one ρ (by simp only [← hval]; exact hx)
  have hidinv : ρ x⁻¹ = LinearMap.id := by
    have h1 : ρ x⁻¹ * ρ x = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    rw [hidx, show (LinearMap.id : V →ₗ[ℂ] V) = 1 from rfl, mul_one] at h1
    rw [h1]; rfl
  rw [mem_characterKernel, characterDegree_def, hval x⁻¹, hval 1,
    show ρ.character x⁻¹ = LinearMap.trace ℂ V (ρ x⁻¹) from rfl, hidinv,
    Representation.char_one, LinearMap.trace_id]

/-- **The character kernel of a genuine character, packaged as a subgroup.** -/
def characterKernelSubgroup {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ) : Subgroup Γ where
  carrier := characterKernel φ
  one_mem' := one_mem_characterKernel φ
  mul_mem' hx hy := characterKernel_mul_mem hφ hx hy
  inv_mem' hx := characterKernel_inv_mem hφ hx

@[simp] theorem mem_characterKernelSubgroup {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ)
    {g : Γ} : g ∈ characterKernelSubgroup hφ ↔ g ∈ characterKernel φ := Iff.rfl

theorem coe_characterKernelSubgroup {φ : ClassFunction Γ ℂ} (hφ : IsCharacter φ) :
    (characterKernelSubgroup hφ : Set Γ) = characterKernel φ := rfl

end CharacterKernelSubgroup

/-- A subset is contained in the character kernel.  This is the set-level shape
used in Peterfalvi (1.6). -/
def SubsetCharacterKernel (A : Set G) (χ : ClassFunction G ℂ) : Prop :=
  A ⊆ characterKernel χ

@[simp] theorem subsetCharacterKernel_conj_iff {A : Set G} {χ : ClassFunction G ℂ} :
    SubsetCharacterKernel A χ.conj ↔ SubsetCharacterKernel A χ := by
  simp [SubsetCharacterKernel]

/-- Pairwise orthogonality for a set of class functions, using the normalized
inner product. -/
def PairwiseOrthogonal (S : Set (ClassFunction G ℂ))
    [Fintype G] [Invertible (Nat.card G : ℂ)] : Prop :=
  ∀ ⦃χ ψ : ClassFunction G ℂ⦄, χ ∈ S → ψ ∈ S → χ ≠ ψ →
    ClassFunction.inner χ ψ = 0

/-- The coefficient of `χ` in the induced-character expansion of a class
function `ψ` on a subgroup `H`.

This names the normalized inner product `(ψ, Res χ)_H` from Peterfalvi (1.3).
The numerical Frobenius-reciprocity theorem proving that these are the actual
induction coefficients remains routed to the `InducedCharacter` proof core. -/
def inductionCoefficient (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)]
    (ψ : ClassFunction H ℂ) (χ : ClassFunction G ℂ) : ℂ :=
  ClassFunction.inner ψ (ClassFunction.restrict H χ)

@[simp] theorem inductionCoefficient_def (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)]
    (ψ : ClassFunction H ℂ) (χ : ClassFunction G ℂ) :
    inductionCoefficient H ψ χ =
      ClassFunction.inner ψ (ClassFunction.restrict H χ) :=
  rfl

@[simp] theorem restrict_trivialClassFunction (H : Subgroup G) :
    ClassFunction.restrict H (trivialClassFunction G) = trivialClassFunction H := by
  ext h
  simp

@[simp] theorem inductionCoefficient_zero_left (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)] (χ : ClassFunction G ℂ) :
    inductionCoefficient H (0 : ClassFunction H ℂ) χ = 0 := by
  simp [inductionCoefficient]

@[simp] theorem inductionCoefficient_zero_right (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)] (ψ : ClassFunction H ℂ) :
    inductionCoefficient H ψ (0 : ClassFunction G ℂ) = 0 := by
  simp [inductionCoefficient]

@[simp] theorem inductionCoefficient_trivial_right (H : Subgroup G) [Fintype H]
    [Invertible (Nat.card H : ℂ)] (ψ : ClassFunction H ℂ) :
    inductionCoefficient H ψ (trivialClassFunction G) =
      ClassFunction.inner ψ (trivialClassFunction H) := by
  simp [inductionCoefficient]

/-- The character difference `χ - χ.conj` that appears in Peterfalvi §7.

This helper exists to keep later statements from accidentally using
`χ - 1`, which is not the expression in §7. -/
def conjugateDifference (χ : ClassFunction G ℂ) : ClassFunction G ℂ :=
  χ - χ.conj

@[simp] theorem conjugateDifference_apply (χ : ClassFunction G ℂ) (g : G) :
    conjugateDifference χ g = χ g - χ.conj g :=
  rfl

@[simp] theorem conjugateDifference_conj (χ : ClassFunction G ℂ) :
    conjugateDifference χ.conj = -conjugateDifference χ := by
  ext g
  simp [conjugateDifference, sub_eq_add_neg, add_comm]

section InducedKernel

variable {A H : Subgroup G} [Fintype G] [Fintype H] [Invertible (Nat.card H : ℂ)]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- For `a ∈ A`, the constant value taken by the induced character `Ind_H^G θ` on a normal
subgroup `A ≤ H` on which `θ` is constant `= θ(1)`.  This is the explicit value formula
`Ind_H^G θ(a) = |G|·θ(1)·|H|⁻¹`, derived from
`ClassFunction.induce_apply_of_mem_normal_of_const` with the kernel hypothesis. -/
theorem induce_apply_eq_of_subgroupOf_subset_characterKernel (hAH : A ≤ H) [A.Normal]
    (θ : ClassFunction ↥H ℂ)
    (hker : (A.subgroupOf H : Set ↥H) ⊆ characterKernel θ) {a : G} (ha : a ∈ A) :
    ClassFunction.induce H θ a =
      ⅟(Nat.card H : ℂ) * ((Nat.card G : ℂ) * characterDegree θ) := by
  refine ClassFunction.induce_apply_of_mem_normal_of_const hAH θ
    (c := characterDegree θ) (fun a' ha' => ?_) ha
  -- `θ` is constant `= characterDegree θ` on `A`, by the kernel hypothesis.
  have hmem : (⟨a', hAH ha'⟩ : ↥H) ∈ A.subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]; exact ha'
  exact hker hmem

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (1.6.a)**, forward direction.  Let `A ⊴ G` with `A ≤ H` and let `θ` be a class
function on `H`.  If `A` is contained in the kernel of `θ` (as a subgroup of `H`), then `A` is
contained in the kernel of the induced character `Ind_H^G θ` (as a subgroup of `G`).

This is the elementary half of (1.6.a): when `θ` is constant on `A`, so is `Ind_H^G θ` (every
term of the induction sum at `a ∈ A` is `θ` evaluated at a conjugate `x⁻¹ a x ∈ A`, hence the
common constant).  The converse is [Is] Lemma 2.21, proved below for irreducible `θ` as
`mem_characterKernel_of_mem_characterKernel_induce`.

The (6.6) use case is the contrapositive: if `Z ⊄ Ker (Ind_H^G θ)` then `Z ⊄ Ker θ`. -/
theorem subsetCharacterKernel_induce_of_subgroupOf (hAH : A ≤ H) [A.Normal]
    (θ : ClassFunction ↥H ℂ)
    (hker : (A.subgroupOf H : Set ↥H) ⊆ characterKernel θ) :
    SubsetCharacterKernel (A : Set G) (ClassFunction.induce H θ) := by
  intro a ha
  rw [mem_characterKernel]
  -- both `Ind θ(a)` and `Ind θ(1) = characterDegree (Ind θ)` equal the common constant.
  have hval : ClassFunction.induce H θ a =
      ⅟(Nat.card H : ℂ) * ((Nat.card G : ℂ) * characterDegree θ) :=
    induce_apply_eq_of_subgroupOf_subset_characterKernel hAH θ hker ha
  have hval1 : characterDegree (ClassFunction.induce H θ) =
      ⅟(Nat.card H : ℂ) * ((Nat.card G : ℂ) * characterDegree θ) := by
    rw [characterDegree_def]
    exact induce_apply_eq_of_subgroupOf_subset_characterKernel hAH θ hker A.one_mem
  rw [hval, hval1]

end InducedKernel

section InducedConstituent

variable {H : Subgroup G} [Fintype G] [Fintype H]
  [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card H : ℂ)]

set_option linter.unusedFintypeInType false in
/-- **Peterfalvi (6.6) `X`-characterization, constituent-existence half** (mmd 04.8 L76).  For
any subgroup `H` of `G` and any irreducible character `χ` of `G`, there is an irreducible
character `θ` of `H` of which `χ` is a constituent of the induced character `Ind_H^G θ`, i.e.
`⟨Ind_H^G θ, χ⟩ ≠ 0`.

This is the "`χ = Ind_K^L θ` constituent" step of (6.6), in its honest unconditional generality:
it requires nothing about a center `Z`, only Frobenius reciprocity.  The proof composes
`IrreducibleCharacter.exists_liesOver` (every `χ` lies over some `θ ∈ Irr H`) with
`IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver` (lying over `θ` ⟺ being a constituent
of `Ind_H^G θ`).

(The `Fintype H` instance feeds the Frobenius-reciprocity bridge in the proof; it does not appear
in the statement.) -/
theorem exists_inner_induce_ne_zero
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G) :
    ∃ θ : OddOrder.RepresentationTheory.IrreducibleCharacter H,
      ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (χ : ClassFunction G ℂ) ≠ 0 := by
  obtain ⟨θ, hθ⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver (G := G) H χ
  exact ⟨θ,
    (OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver
      (G := G) H χ θ).mpr hθ⟩

end InducedConstituent

section ConstituentKernel

variable [Finite G]

/-- **Character-value bound `‖χ(g)‖ ≤ χ(1)`** for an irreducible character, in the
`characterDegree` form ([Isaacs] *Character Theory*, the inequality of (2.27)).  Here `d` is the
natural degree (`(χ : G → ℂ) 1 = d`), and `‖χ(g)‖ ≤ d`.  This is the consumer-facing form, through
`IrreducibleCharacter`, of the keystone bound
`OddOrder.RepresentationTheory.norm_character_le_finrank`. -/
theorem norm_irreducibleCharacter_le_natDegree
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G) {d : ℕ}
    (hd : (χ : ClassFunction G ℂ) 1 = (d : ℂ)) (g : G) :
    ‖(χ : ClassFunction G ℂ) g‖ ≤ (d : ℝ) := by
  obtain ⟨V, _, _, _, ρ, _, hχ⟩ := χ.isIrreducible
  -- `χ g = ρ.character g` and the natural degree `d` is the `finrank`.
  have hcharg : (χ : ClassFunction G ℂ) g = ρ.character g := congrFun hχ g
  have hfin : (Module.finrank ℂ V : ℂ) = (d : ℂ) := by
    rw [← ρ.char_one, ← congrFun hχ 1, hd]
  have hfin' : (Module.finrank ℂ V : ℝ) = (d : ℝ) := by exact_mod_cast hfin
  rw [hcharg, ← hfin']
  exact OddOrder.RepresentationTheory.norm_character_le_finrank ρ g

/-- **Peterfalvi (6.6) G2.2: a constituent inherits a kernel containment** (the equality case of
`‖χ(g)‖ ≤ χ(1)`).  Let `χ : ι → Irr G` be a finite family of irreducible characters with
non-negative integer multiplicities `m : ι → ℕ`.  If the value of `ψ = ∑ mᵢ χᵢ` at `g` equals its
value at `1`, then every constituent `χ i` with `m i ≠ 0` satisfies `χ i (g) = χ i (1)`, i.e.
`g ∈ characterKernel (χ i)`.

This is the keystone-driven closure of the G2.2 residual: it sharpens the central Schur equality
to the general element `g`, using `norm_irreducibleCharacter_le_natDegree` (the bound) and
`RCLike.re_eq_self_of_le` (the unit-circle rigidity) at each summand. -/
theorem irreducibleCharacter_mem_characterKernel_of_natSum_value_eq (g : G)
    {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (χ : ι → OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (d : ι → ℕ) (hd : ∀ i ∈ s, (χ i : ClassFunction G ℂ) 1 = (d i : ℂ))
    (hval : ∑ i ∈ s, (m i : ℂ) * (χ i : ClassFunction G ℂ) g
      = ∑ i ∈ s, (m i : ℂ) * (χ i : ClassFunction G ℂ) 1) :
    ∀ i ∈ s, m i ≠ 0 → g ∈ characterKernel (χ i : ClassFunction G ℂ) := by
  classical
  -- Bound `‖χᵢ(g)‖ ≤ dᵢ`, and `Re χᵢ(g) ≤ ‖χᵢ(g)‖ ≤ dᵢ`, for every `i ∈ s`.
  have hbound : ∀ i ∈ s, ‖(χ i : ClassFunction G ℂ) g‖ ≤ (d i : ℝ) := fun i hi =>
    norm_irreducibleCharacter_le_natDegree (χ i) (hd i hi) g
  have hre_le : ∀ i ∈ s, ((χ i : ClassFunction G ℂ) g).re ≤ (d i : ℝ) := fun i hi =>
    le_trans (by rw [← RCLike.re_eq_complex_re]; exact RCLike.re_le_norm _) (hbound i hi)
  -- Real parts: `∑ mᵢ Re χᵢ(g) = ∑ mᵢ dᵢ` (the RHS is real, `= ∑ mᵢ χᵢ(1)`).
  have hre : ∑ i ∈ s, (m i : ℝ) * ((χ i : ClassFunction G ℂ) g).re
      = ∑ i ∈ s, (m i : ℝ) * (d i : ℝ) := by
    have hcast := congrArg Complex.re hval
    rw [Complex.re_sum, Complex.re_sum] at hcast
    refine Eq.trans ?_ (hcast.trans ?_) <;> refine Finset.sum_congr rfl fun i hi => ?_
    · simp [Complex.mul_re]
    · rw [hd i hi]; simp [Complex.mul_re]
  -- Each summand deficit `mᵢ(dᵢ - Re χᵢ(g)) ≥ 0`, summing to `0`, so each is `0`.
  have hnn : ∀ i ∈ s, (0 : ℝ) ≤ (m i : ℝ) * ((d i : ℝ) - ((χ i : ClassFunction G ℂ) g).re) :=
    fun i hi => mul_nonneg (by positivity) (by linarith [hre_le i hi])
  have hsum0 : ∑ i ∈ s, (m i : ℝ) * ((d i : ℝ) - ((χ i : ClassFunction G ℂ) g).re) = 0 := by
    have hexp : ∀ i ∈ s, (m i : ℝ) * ((d i : ℝ) - ((χ i : ClassFunction G ℂ) g).re)
        = (m i : ℝ) * (d i : ℝ) - (m i : ℝ) * ((χ i : ClassFunction G ℂ) g).re :=
      fun i _ => by ring
    rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← hre, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0
  -- For `mᵢ ≠ 0`: `Re χᵢ(g) = dᵢ`, and with `‖χᵢ(g)‖ ≤ dᵢ` rigidity gives `χᵢ(g) = dᵢ = χᵢ(1)`.
  intro i hi hmi
  have hmi' : (m i : ℝ) ≠ 0 := by exact_mod_cast hmi
  have hre_eq : ((χ i : ClassFunction G ℂ) g).re = (d i : ℝ) := by
    have hterm : (d i : ℝ) - ((χ i : ClassFunction G ℂ) g).re = 0 :=
      (mul_eq_zero.mp (hzero i hi)).resolve_left hmi'
    linarith
  -- `‖χᵢ(g)‖ ≤ dᵢ = Re χᵢ(g)`; unit-circle rigidity gives `χᵢ(g) = (Re χᵢ(g) : ℂ) = dᵢ`.
  have hle : ‖(χ i : ClassFunction G ℂ) g‖ ≤ RCLike.re ((χ i : ClassFunction G ℂ) g) := by
    rw [RCLike.re_eq_complex_re, hre_eq]; exact hbound i hi
  have haeq : (χ i : ClassFunction G ℂ) g = (d i : ℂ) := by
    rw [← RCLike.re_eq_self_of_le (K := ℂ) hle, RCLike.re_eq_complex_re, hre_eq]
    push_cast
    ring
  rw [mem_characterKernel, characterDegree_def, haeq, hd i hi]

end ConstituentKernel

section InducedKernelDescent

/-- **Kernel descent for induced characters**: if `x ∈ H` lies in the kernel of `Ind_H^L θ`
(`θ` irreducible, `H ◁ L`), then `x` lies in the kernel of `θ` itself.
Mackey (`card_smul_restrict_induce_eq_inertia_smul_orbitSum`) writes `|H|·(Ind θ)|_H` as
`|I(θ)|·∑_{orbit} θ^g`; the kernel hypothesis equates the orbit sums at `x` and `1`, and the
triangle-equality keystone (`irreducibleCharacter_mem_characterKernel_of_natSum_value_eq`)
forces every orbit member — in particular `θ` — to have `x` in its kernel.  Contrapositive:
`P ⊄ Ker θ ⟹ P ⊄ Ker (Ind θ)`. -/
theorem mem_characterKernel_of_mem_characterKernel_induce
    {L : Type*} [Group L] [Fintype L] {H : Subgroup L} [H.Normal]
    [Finite ↥H] [Invertible (Nat.card ↥H : ℂ)]
    {θ : ClassFunction ↥H ℂ} (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    {x : L} (hxH : x ∈ H)
    (hker : x ∈ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce H θ)) :
    (⟨x, hxH⟩ : ↥H) ∈ OddOrder.Peterfalvi.S03.characterKernel θ := by
  classical
  have : Fintype ↥H := Fintype.ofFinite ↥H
  -- the Mackey orbit identity, applied at `⟨x,hxH⟩` and at `1`
  have hid :=
    OddOrder.RepresentationTheory.card_smul_restrict_induce_eq_inertia_smul_orbitSum
      (G := L) (H := H) (k := ℂ) θ
  rw [← Nat.cast_smul_eq_nsmul ℂ] at hid
  have happ : ∀ a : ↥H,
      (Nat.card ↥H : ℂ) * ClassFunction.induce H θ (a : L)
        = (Nat.card ↥(ClassFunction.inertia (G := L) (H := H) θ) : ℂ)
          * ∑ ψ ∈ Finset.univ.image (fun g : L => ClassFunction.conjBy g⁻¹ θ), ψ a := by
    intro a
    have h1 := congrArg (fun f : ClassFunction ↥H ℂ => f a) hid
    simpa only [ClassFunction.smul_apply, ClassFunction.restrict_apply, smul_eq_mul,
      OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply] using h1
  -- kernel hypothesis ⟹ the orbit sums at `x` and `1` agree
  have hI0 : (Nat.card ↥(ClassFunction.inertia (G := L) (H := H) θ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hxval : ClassFunction.induce H θ x = ClassFunction.induce H θ (1 : L) := by
    have := (OddOrder.Peterfalvi.S03.mem_characterKernel).mp hker
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using this
  have hsum : ∑ ψ ∈ Finset.univ.image (fun g : L => ClassFunction.conjBy g⁻¹ θ),
        ψ (⟨x, hxH⟩ : ↥H)
      = ∑ ψ ∈ Finset.univ.image (fun g : L => ClassFunction.conjBy g⁻¹ θ), ψ 1 := by
    have h1 := happ ⟨x, hxH⟩
    have h2 := happ 1
    rw [show ((⟨x, hxH⟩ : ↥H) : L) = x from rfl] at h1
    rw [show ((1 : ↥H) : L) = 1 from rfl] at h2
    rw [hxval] at h1
    exact mul_left_cancel₀ hI0 (h1.symm.trans h2)
  -- the orbit members are irreducible of the common degree `θ(1) = n`
  obtain ⟨n, -, hn, -⟩ :=
    OddOrder.Peterfalvi.S03.exists_natDegree_characterDegree_dvd_card (G := ↥H) ⟨θ, hθ⟩
  have hdeg : θ 1 = (n : ℂ) := by
    simpa [OddOrder.Peterfalvi.S03.characterDegree_def] using hn
  set S : Finset (ClassFunction ↥H ℂ) :=
    Finset.univ.image (fun g : L => ClassFunction.conjBy g⁻¹ θ) with hSdef
  have hmemirr : ∀ ψ ∈ S, OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ := by
    intro ψ hψ
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hψ
    exact OddOrder.RepresentationTheory.ClassFunction.IsIrreducibleCharacter.conjBy
      (H := H) hθ g⁻¹
  set fam : ClassFunction ↥H ℂ → OddOrder.RepresentationTheory.IrreducibleCharacter ↥H :=
    fun ψ => if h : OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ
      then ⟨ψ, h⟩ else ⟨θ, hθ⟩ with hfam
  have hfamcoe : ∀ ψ ∈ S, (fam ψ : ClassFunction ↥H ℂ) = ψ := by
    intro ψ hψ
    simp only [hfam]
    rw [dif_pos (hmemirr ψ hψ)]
  have hfamdeg : ∀ ψ ∈ S, (fam ψ : ClassFunction ↥H ℂ) 1 = (n : ℂ) := by
    intro ψ hψ
    rw [hfamcoe ψ hψ]
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hψ
    rw [ClassFunction.conjBy_apply]
    refine (congrArg θ (Subtype.ext ?_)).trans hdeg
    simp
  have hval : ∑ ψ ∈ S, ((1 : ℕ) : ℂ) * (fam ψ : ClassFunction ↥H ℂ) (⟨x, hxH⟩ : ↥H)
      = ∑ ψ ∈ S, ((1 : ℕ) : ℂ) * (fam ψ : ClassFunction ↥H ℂ) 1 := by
    have e1 : ∀ pt : ↥H, ∑ ψ ∈ S, ((1 : ℕ) : ℂ) * (fam ψ : ClassFunction ↥H ℂ) pt
        = ∑ ψ ∈ S, ψ pt := fun pt =>
      Finset.sum_congr rfl (fun ψ hψ => by rw [hfamcoe ψ hψ, Nat.cast_one, one_mul])
    rw [e1, e1]
    exact hsum
  -- keystone: every orbit member has `x` in its kernel; take `ψ = θ` (the `g = 1` member)
  have hθS : θ ∈ S := by
    rw [hSdef]
    exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, by simp⟩
  have hkey := OddOrder.Peterfalvi.S03.irreducibleCharacter_mem_characterKernel_of_natSum_value_eq
    (⟨x, hxH⟩ : ↥H) S (fun _ => 1) fam (fun _ => n) hfamdeg hval θ hθS one_ne_zero
  rwa [hfamcoe θ hθS] at hkey

end InducedKernelDescent

end OddOrder.Peterfalvi.S03


