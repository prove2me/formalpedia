-- Prove2me | Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
-- name    : GroundTheory_LocalFields_MaximalUnramified
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T08:11:56.147554+00:00
-- url     : https://prove2.me/theorems/a7cb78e2-54bf-42e3-ba31-519fd79cdadf
-- title:
--   Maximal Unramified
-- statement:
--   Definitions and structural lemmas for Maximal Unramified, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramified.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_castHom_proj
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_eq_adjoin
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_isGalois
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_ramificationIndex_eq_one
import Theorems.Thm_GroundTheory_LocalField_adjoin_gen_eq_top
import Theorems.Thm_GroundTheory_LocalField_exists_isPrimitiveRoot_card_pow_sub_one
import Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_isNonarchimedeanLocalField
import Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_valuativeExtension
import Theorems.Thm_GroundTheory_LocalField_frobenius_apply_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_isUnramifiedSubextension_adjoin
import Theorems.Thm_GroundTheory_LocalField_natCast_card_pow_sub_one_ne_zero
import Theorems.Thm_GroundTheory_LocalField_orderOf_frobenius
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_zpowers_frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel IntermediateField GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger
section Roots
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem algEquiv_pow_apply_of_apply_eq_pow {L : Type*} [Field L] [Algebra K L] {τ : L ≃ₐ[K] L}
    {x : L} {q : ℕ} (h : τ x = x ^ q) (k : ℕ) : (τ ^ k) x = x ^ q ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, h, ← pow_mul, ← pow_succ']
theorem one_lt_card_residueField_pow {n : ℕ} (hn : n ≠ 0) : 1 < Nat.card 𝓀[K] ^ n :=
  Nat.one_lt_pow hn (one_lt_card_residueField K)
theorem exists_frobenius_adjoin {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) :
    ∃ τ : K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯, τ (AdjoinSimple.gen K ζ) = AdjoinSimple.gen K ζ ^ Nat.card 𝓀[K] ∧
      orderOf τ = n ∧ Subgroup.zpowers τ = ⊤ := by
  obtain ⟨hE, hEn⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  let := (finiteExtensionStructure K K⟮ζ⟯).rel
  let := (finiteExtensionStructure K K⟮ζ⟯).top
  have := finiteExtensionStructure_isNonarchimedeanLocalField K K⟮ζ⟯
  have := finiteExtensionStructure_valuativeExtension K K⟮ζ⟯
  have h := hE.ramificationIndex_eq_one
  have hζ' : IsPrimitiveRoot (AdjoinSimple.gen K ζ) (Nat.card 𝓀[K] ^ n - 1) :=
    hζ.of_map_of_injective (f := K⟮ζ⟯.val) Subtype.val_injective
  refine ⟨frobenius K K⟮ζ⟯ h, frobenius_apply_of_pow_eq_one h
    (natCast_card_pow_sub_one_ne_zero hn) hζ'.pow_eq_one, ?_, zpowers_frobenius K _ h⟩
  rw [orderOf_frobenius, hEn]
theorem exists_apply_eq_pow_pow {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (σ : Ω ≃ₐ[K] Ω) :
    ∃ a : ℕ, σ ζ = ζ ^ Nat.card 𝓀[K] ^ a := by
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  have := hE.isGalois
  obtain ⟨τ, hτ, -, htop⟩ := exists_frobenius_adjoin hn hζ
  have hmem : σ.restrictNormal K⟮ζ⟯ ∈ Subgroup.zpowers τ := htop ▸ Subgroup.mem_top _
  obtain ⟨a, ha⟩ := mem_powers_iff_mem_zpowers.2 hmem
  refine ⟨a, ?_⟩
  have h1 := AlgEquiv.restrictNormal_commutes σ K⟮ζ⟯ (AdjoinSimple.gen K ζ)
  rw [← ha, algEquiv_pow_apply_of_apply_eq_pow hτ] at h1
  simpa using h1.symm
theorem pow_pow_eq_pow_pow_iff {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (a b : ℕ) :
    ζ ^ Nat.card 𝓀[K] ^ a = ζ ^ Nat.card 𝓀[K] ^ b ↔ a ≡ b [MOD n] := by
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin hn hζ
  have := hE.1
  obtain ⟨τ, hτ, hord, -⟩ := exists_frobenius_adjoin hn hζ
  rw [← hord, ← pow_eq_pow_iff_modEq]
  constructor
  · intro h
    have h' : (τ ^ a) (AdjoinSimple.gen K ζ) = (τ ^ b) (AdjoinSimple.gen K ζ) := by
      rw [algEquiv_pow_apply_of_apply_eq_pow hτ, algEquiv_pow_apply_of_apply_eq_pow hτ]
      exact Subtype.ext (by simpa using h)
    have h1 : (τ ^ b)⁻¹ * τ ^ a = 1 := by
      refine algEquiv_eq_one_of_apply_eq (adjoin_gen_eq_top ζ) ?_
      rw [AlgEquiv.mul_apply, h', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    exact (inv_mul_eq_one.mp h1).symm
  · intro h
    have := congrArg (fun ρ : K⟮ζ⟯ ≃ₐ[K] K⟮ζ⟯ ↦ ((ρ (AdjoinSimple.gen K ζ) : K⟮ζ⟯) : Ω)) h
    simpa [algEquiv_pow_apply_of_apply_eq_pow hτ] using this
theorem apply_eq_pow_pow_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) {σ : Ω ≃ₐ[K] Ω} {a : ℕ}
    (ha : σ ζ = ζ ^ Nat.card 𝓀[K] ^ a) {ξ : Ω} (hξ : ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1) :
    σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  have : NeZero (Nat.card 𝓀[K] ^ n - 1) := ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
  rw [map_pow, ha, ← pow_mul, ← pow_mul, mul_comm]
variable (K Ω) in

class HasUnramifiedRoots : Prop where
  exists_isPrimitiveRoot : ∀ n : ℕ, n ≠ 0 → ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)
instance hasUnramifiedRoots_of_isSepClosed [IsSepClosed Ω] : HasUnramifiedRoots K Ω :=
  ⟨fun _ hn ↦ exists_isPrimitiveRoot_card_pow_sub_one (K := K) hn⟩
variable (K Ω) in

def unramifiedRoots : Set Ω :=
  {ξ | ∃ n : ℕ, n ≠ 0 ∧ ξ ^ (Nat.card 𝓀[K] ^ n - 1) = 1}
variable (K) in
open Classical in

def unramifiedCoord (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) : ZMod n :=
  if h : ∃ a : ZMod n, ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 →
      σ ξ = ξ ^ Nat.card 𝓀[K] ^ a.val then h.choose else 0
theorem natCast_eq_unramifiedCoord_iff {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (σ : Ω ≃ₐ[K] Ω) (a : ℕ) :
    (a : ZMod n) = unramifiedCoord K σ n ↔ σ ζ = ζ ^ Nat.card 𝓀[K] ^ a := by
  have hn : (n : ℕ) ≠ 0 := n.ne_zero
  obtain ⟨a₀, ha₀⟩ := exists_apply_eq_pow_pow hn hζ σ
  have hex : ∃ c : ZMod n, ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 →
      σ ξ = ξ ^ Nat.card 𝓀[K] ^ c.val := by
    refine ⟨a₀, fun ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one hn hζ ?_ hξ⟩
    rw [ha₀, pow_pow_eq_pow_pow_iff hn hζ, ZMod.val_natCast]
    exact (Nat.mod_modEq a₀ n).symm
  have hc : unramifiedCoord K σ n = hex.choose := dif_pos hex
  rw [hc, hex.choose_spec ζ hζ.pow_eq_one, pow_pow_eq_pow_pow_iff hn hζ,
    ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact eq_comm
theorem apply_eq_pow_pow_unramifiedCoord {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (σ : Ω ≃ₐ[K] Ω) :
    σ ζ = ζ ^ Nat.card 𝓀[K] ^ (unramifiedCoord K σ n).val :=
  (natCast_eq_unramifiedCoord_iff hζ σ _).1 (ZMod.natCast_zmod_val _)
variable [HasUnramifiedRoots K Ω]
theorem natCast_eq_unramifiedCoord_iff_forall (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) (a : ℕ) :
    (a : ZMod n) = unramifiedCoord K σ n ↔
      ∀ ξ : Ω, ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 → σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  rw [natCast_eq_unramifiedCoord_iff hζ]
  exact ⟨fun h ξ hξ ↦ apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ h hξ, fun h ↦ h ζ hζ.pow_eq_one⟩
theorem unramifiedCoord_one (n : ℕ+) : unramifiedCoord K (1 : Ω ≃ₐ[K] Ω) n = 0 := by
  rw [← (natCast_eq_unramifiedCoord_iff_forall 1 n 0).2 (fun ξ _ ↦ by simp), Nat.cast_zero]
theorem unramifiedCoord_mul (σ τ : Ω ≃ₐ[K] Ω) (n : ℕ+) :
    unramifiedCoord K (σ * τ) n = unramifiedCoord K σ n + unramifiedCoord K τ n := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have h := (natCast_eq_unramifiedCoord_iff hζ (σ * τ)
    ((unramifiedCoord K σ n).val + (unramifiedCoord K τ n).val)).2 (by
      rw [AlgEquiv.mul_apply, apply_eq_pow_pow_unramifiedCoord hζ τ, map_pow,
        apply_eq_pow_pow_unramifiedCoord hζ σ, ← pow_mul, ← pow_add])
  rw [← h, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
theorem castHom_unramifiedCoord (σ : Ω ≃ₐ[K] Ω) {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    ZMod.castHom h (ZMod m) (unramifiedCoord K σ n) = unramifiedCoord K σ m := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  obtain ⟨ξ, hξ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) m m.ne_zero
  have hdvd : Nat.card 𝓀[K] ^ (m : ℕ) - 1 ∣ Nat.card 𝓀[K] ^ (n : ℕ) - 1 := by
    obtain ⟨k, hk⟩ := h
    rw [hk, pow_mul]
    simpa [one_pow] using Nat.sub_dvd_pow_sub_pow (Nat.card 𝓀[K] ^ (m : ℕ)) 1 k
  have hξn : ξ ^ (Nat.card 𝓀[K] ^ (n : ℕ) - 1) = 1 := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul, hξ.pow_eq_one, one_pow]
  have key := apply_eq_pow_pow_of_pow_eq_one n.ne_zero hζ
    (apply_eq_pow_pow_unramifiedCoord hζ σ) hξn
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (natCast_eq_unramifiedCoord_iff hξ σ _).2 key
end Roots
section Degree
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω]
variable (K Ω) in

def unramifiedDegree : (Ω ≃ₐ[K] Ω) →* Multiplicative ℤ̂ where
  toFun σ := Multiplicative.ofAdd ⟨fun n ↦ unramifiedCoord K σ n,
    mem_profiniteIntegers.2 fun _ _ h ↦ castHom_unramifiedCoord σ h⟩
  map_one' := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    ext n
    show unramifiedCoord K 1 n = proj n 0
    rw [map_zero, unramifiedCoord_one]
  map_mul' σ τ := by
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd (_ + _)
    congr 1
    ext n
    show unramifiedCoord K (σ * τ) n = proj n (_ + _)
    rw [map_add, unramifiedCoord_mul]
    rfl
theorem proj_toAdd_unramifiedDegree (σ : Ω ≃ₐ[K] Ω) (n : ℕ+) :
    proj n (Multiplicative.toAdd (unramifiedDegree K Ω σ)) = unramifiedCoord K σ n :=
  rfl
theorem multiplicative_ext {x y : Multiplicative ℤ̂}
    (h : ∀ n, proj n (Multiplicative.toAdd x) = proj n (Multiplicative.toAdd y)) : x = y :=
  Multiplicative.toAdd.injective (ProfiniteInteger.ext h)
theorem unramifiedCoord_mul_of_apply_eq (σ : Ω ≃ₐ[K] Ω) {τ : Ω ≃ₐ[K] Ω} {n : ℕ+} {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ (n : ℕ) - 1)) (hτ : τ ζ = ζ) :
    unramifiedCoord K (σ * τ) n = unramifiedCoord K σ n := by
  have h0 : unramifiedCoord K τ n = 0 := by
    rw [← (natCast_eq_unramifiedCoord_iff hζ τ 0).2 (by simpa using hτ), Nat.cast_zero]
  rw [unramifiedCoord_mul, h0, add_zero]
theorem continuous_unramifiedCoord (n : ℕ+) :
    Continuous fun σ : Ω ≃ₐ[K] Ω ↦ unramifiedCoord K σ n := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have hfin : FiniteDimensional K K⟮ζ⟯ := (isUnramifiedSubextension_adjoin n.ne_zero hζ).1.1
  refine ((IsLocallyConstant.iff_eventually_eq _).2 fun σ ↦ ?_).continuous
  open scoped Pointwise in
  have hU : σ • (K⟮ζ⟯.fixingSubgroup : Set (Ω ≃ₐ[K] Ω)) ∈ nhds σ :=
    (K⟮ζ⟯.fixingSubgroup_isOpen.smul σ).mem_nhds ⟨1, one_mem _, by simp⟩
  filter_upwards [hU] with ρ hρ
  obtain ⟨τ, hτ, rfl⟩ := hρ
  exact unramifiedCoord_mul_of_apply_eq σ hζ
    ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ ζ (mem_adjoin_simple_self K ζ))
theorem continuous_unramifiedDegree : Continuous (unramifiedDegree K Ω) :=
  continuous_ofAdd.comp (Continuous.subtype_mk (continuous_pi fun n ↦ continuous_unramifiedCoord n) _)
theorem exists_unramifiedCoord_eq [Normal K Ω] (n : ℕ+) (c : ZMod n) :
    ∃ σ : Ω ≃ₐ[K] Ω, unramifiedCoord K σ n = c := by
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  obtain ⟨hE, -⟩ := isUnramifiedSubextension_adjoin n.ne_zero hζ
  have := hE.1
  obtain ⟨τ, hτ, -, -⟩ := exists_frobenius_adjoin n.ne_zero hζ
  refine ⟨(τ ^ c.val).liftNormal Ω, ?_⟩
  have h1 := AlgEquiv.liftNormal_commutes (τ ^ c.val) Ω (AdjoinSimple.gen K ζ)
  rw [algEquiv_pow_apply_of_apply_eq_pow hτ] at h1
  have h2 := (natCast_eq_unramifiedCoord_iff hζ ((τ ^ c.val).liftNormal Ω) c.val).2
    (by simpa using h1)
  rw [← h2, ZMod.natCast_zmod_val]
theorem unramifiedDegree_surjective [IsGalois K Ω] : Function.Surjective (unramifiedDegree K Ω) := by
  intro x
  let N : ℕ → ℕ+ := fun k ↦ ⟨(k + 1).factorial, Nat.factorial_pos _⟩
  let S : ℕ → Set (Ω ≃ₐ[K] Ω) := fun k ↦
    {σ | unramifiedCoord K σ (N k) = proj (N k) (Multiplicative.toAdd x)}
  have hS : ∀ k, IsClosed (S k) := fun k ↦
    isClosed_eq (continuous_unramifiedCoord _) continuous_const
  have hdvd : ∀ k, (N k : ℕ) ∣ N (k + 1) := fun k ↦ Nat.factorial_dvd_factorial (by omega)
  have hmono : ∀ k, S (k + 1) ⊆ S k := by
    intro k σ hσ
    simp only [S, Set.mem_ofPred_eq] at hσ ⊢
    rw [← castHom_unramifiedCoord σ (hdvd k), hσ, castHom_proj]
  have hne : ∀ k, (S k).Nonempty := fun k ↦ exists_unramifiedCoord_eq _ _
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hmono hne
    (hS 0).isCompact hS
  rw [Set.mem_iInter] at hσ
  refine ⟨σ, multiplicative_ext fun n ↦ ?_⟩
  have hn : (n : ℕ) ∣ N ((n : ℕ) - 1) := by
    show (n : ℕ) ∣ ((n : ℕ) - 1 + 1).factorial
    rw [Nat.sub_add_cancel n.pos]
    exact Nat.dvd_factorial n.pos le_rfl
  rw [proj_toAdd_unramifiedDegree, ← castHom_unramifiedCoord σ hn, hσ _, castHom_proj]
theorem unramifiedDegree_eq_ofAdd_natCast_iff (σ : Ω ≃ₐ[K] Ω) (a : ℕ) :
    unramifiedDegree K Ω σ = Multiplicative.ofAdd (a : ℤ̂) ↔
      ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ ^ Nat.card 𝓀[K] ^ a := by
  constructor
  · rintro h ξ ⟨n, hn, hξ⟩
    have hc : unramifiedCoord K σ ⟨n, Nat.pos_of_ne_zero hn⟩ = a := by
      have := congrArg (fun y ↦ proj ⟨n, Nat.pos_of_ne_zero hn⟩ (Multiplicative.toAdd y)) h
      refine this.trans ?_
      rw [toAdd_ofAdd, map_natCast]
    exact (natCast_eq_unramifiedCoord_iff_forall σ ⟨n, Nat.pos_of_ne_zero hn⟩ a).1 hc.symm ξ hξ
  · intro h
    refine multiplicative_ext fun n ↦ ?_
    rw [proj_toAdd_unramifiedDegree, toAdd_ofAdd, map_natCast]
    exact ((natCast_eq_unramifiedCoord_iff_forall σ n a).2
      fun ξ hξ ↦ h ξ ⟨n, n.ne_zero, hξ⟩).symm
theorem unramifiedDegree_eq_one_iff (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K Ω σ = 1 ↔ ∀ ξ ∈ unramifiedRoots K Ω, σ ξ = ξ := by
  have := unramifiedDegree_eq_ofAdd_natCast_iff σ 0
  simp only [Nat.cast_zero, ofAdd_zero, pow_zero, pow_one] at this
  exact this
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [HasUnramifiedRoots K Ω] in

theorem mem_fixingSubgroup_adjoin_iff {S : Set Ω} {σ : Ω ≃ₐ[K] Ω} :
    σ ∈ (adjoin K S).fixingSubgroup ↔ ∀ x ∈ S, σ x = x := by
  rw [← Subgroup.zpowers_le, ← le_iff_le, adjoin_le_iff]
  refine ⟨fun h x hx ↦ (mem_fixedField_iff _ _).1 (h hx) σ (Subgroup.mem_zpowers σ), fun h x hx ↦ ?_⟩
  refine (mem_fixedField_iff _ _).2 fun τ hτ ↦ ?_
  have hσ : σ ∈ MulAction.stabilizer (Ω ≃ₐ[K] Ω) x := h x hx
  exact (Subgroup.zpowers_le.2 hσ) hτ
end Degree
section MaximalUnramified
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
variable (K Ω) in

def maximalUnramifiedExtension : IntermediateField K Ω :=
  ⨆ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, E.1
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem IsUnramifiedSubextension.le_maximalUnramifiedExtension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) : E ≤ maximalUnramifiedExtension K Ω :=
  le_iSup (fun E : {E : IntermediateField K Ω // IsUnramifiedSubextension E} ↦ E.1) ⟨E, hE⟩
theorem adjoin_le_maximalUnramifiedExtension {n : ℕ} (hn : n ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) : K⟮ζ⟯ ≤ maximalUnramifiedExtension K Ω :=
  (isUnramifiedSubextension_adjoin hn hζ).1.le_maximalUnramifiedExtension
instance normal_maximalUnramifiedExtension : Normal K (maximalUnramifiedExtension K Ω) := by
  have : ∀ E : {E : IntermediateField K Ω // IsUnramifiedSubextension E}, Normal K E.1 :=
    fun E ↦ E.2.isGalois.to_normal
  unfold maximalUnramifiedExtension
  infer_instance
instance isGalois_maximalUnramifiedExtension [Algebra.IsSeparable K Ω] :
    IsGalois K (maximalUnramifiedExtension K Ω) :=
  have := Algebra.isSeparable_tower_bot_of_isSeparable K (maximalUnramifiedExtension K Ω) Ω
  isGalois_iff.2 ⟨this, inferInstance⟩
variable [HasUnramifiedRoots K Ω]
theorem maximalUnramifiedExtension_eq_adjoin :
    maximalUnramifiedExtension K Ω = adjoin K (unramifiedRoots K Ω) := by
  apply le_antisymm
  · refine iSup_le fun E ↦ ?_
    have := E.2.1
    have hn : Module.finrank K E.1 ≠ 0 := Module.finrank_pos.ne'
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) _ hn
    rw [E.2.eq_adjoin rfl hn hζ, adjoin_simple_le_iff]
    exact subset_adjoin K _ ⟨_, hn, hζ.pow_eq_one⟩
  · rw [adjoin_le_iff]
    rintro ξ ⟨n, hn, hξ⟩
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
    have : NeZero (Nat.card 𝓀[K] ^ n - 1) :=
      ⟨by have := one_lt_card_residueField_pow (K := K) hn; omega⟩
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact adjoin_le_maximalUnramifiedExtension hn hζ (pow_mem (mem_adjoin_simple_self K ζ) i)
theorem unramifiedRoots_subset_maximalUnramifiedExtension :
    unramifiedRoots K Ω ⊆ maximalUnramifiedExtension K Ω := by
  rw [maximalUnramifiedExtension_eq_adjoin]
  exact subset_adjoin K _
instance hasUnramifiedRoots_maximalUnramifiedExtension : HasUnramifiedRoots K (maximalUnramifiedExtension K Ω) :=
  ⟨fun n hn ↦ by
    obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n hn
    exact ⟨⟨ζ, unramifiedRoots_subset_maximalUnramifiedExtension ⟨n, hn, hζ.pow_eq_one⟩⟩,
      hζ.of_map_of_injective (f := (maximalUnramifiedExtension K Ω).val) Subtype.val_injective⟩⟩
theorem ker_unramifiedDegree :
    (unramifiedDegree K Ω).ker = (maximalUnramifiedExtension K Ω).fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_ker, unramifiedDegree_eq_one_iff, maximalUnramifiedExtension_eq_adjoin,
    mem_fixingSubgroup_adjoin_iff]
theorem unramifiedDegree_restrictNormal (σ : Ω ≃ₐ[K] Ω) :
    unramifiedDegree K (maximalUnramifiedExtension K Ω) (σ.restrictNormal (maximalUnramifiedExtension K Ω)) =
      unramifiedDegree K Ω σ := by
  refine multiplicative_ext fun n ↦ ?_
  rw [proj_toAdd_unramifiedDegree, proj_toAdd_unramifiedDegree]
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) n n.ne_zero
  have hζE : ζ ∈ maximalUnramifiedExtension K Ω :=
    unramifiedRoots_subset_maximalUnramifiedExtension ⟨n, n.ne_zero, hζ.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : maximalUnramifiedExtension K Ω) (Nat.card 𝓀[K] ^ (n : ℕ) - 1) :=
    hζ.of_map_of_injective (f := (maximalUnramifiedExtension K Ω).val) Subtype.val_injective
  rw [← (natCast_eq_unramifiedCoord_iff hζ' _ (unramifiedCoord K σ n).val).2 ?_,
    ZMod.natCast_zmod_val]
  apply Subtype.ext
  have h1 := AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedExtension K Ω) ⟨ζ, hζE⟩
  simp only [IntermediateField.algebraMap_apply] at h1
  rw [h1]
  simpa using apply_eq_pow_pow_unramifiedCoord hζ σ
variable [IsGalois K Ω]
theorem unramifiedDegree_maximalUnramifiedExtension_surjective :
    Function.Surjective (unramifiedDegree K (maximalUnramifiedExtension K Ω)) := by
  intro x
  obtain ⟨σ, rfl⟩ := unramifiedDegree_surjective (K := K) (Ω := Ω) x
  exact ⟨_, unramifiedDegree_restrictNormal σ⟩
theorem unramifiedDegree_maximalUnramifiedExtension_injective :
    Function.Injective (unramifiedDegree K (maximalUnramifiedExtension K Ω)) := by
  rw [injective_iff_map_eq_one]
  intro ρ hρ
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
    (K₁ := maximalUnramifiedExtension K Ω) (E := Ω) ρ
  have hσ : σ ∈ (unramifiedDegree K Ω).ker := by
    rw [MonoidHom.mem_ker, ← unramifiedDegree_restrictNormal]
    exact hρ
  rw [ker_unramifiedDegree, ← IntermediateField.restrictNormalHom_ker] at hσ
  exact MonoidHom.mem_ker.1 hσ
variable (K Ω) in

def maximalUnramifiedExtensionGaloisEquiv :
    (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) ≃ₜ* Multiplicative ℤ̂ :=
  let e : (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) ≃* Multiplicative ℤ̂ :=
    MulEquiv.ofBijective (unramifiedDegree K (maximalUnramifiedExtension K Ω))
      ⟨unramifiedDegree_maximalUnramifiedExtension_injective, unramifiedDegree_maximalUnramifiedExtension_surjective⟩
  { e with
    continuous_toFun := continuous_unramifiedDegree
    continuous_invFun :=
      (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) continuous_unramifiedDegree).symm.continuous }
variable (K Ω) in

def maximalUnramifiedExtensionFrobenius : maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω :=
  (maximalUnramifiedExtensionGaloisEquiv K Ω).symm (Multiplicative.ofAdd 1)
end MaximalUnramified
section SeparableClosure
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
instance hasUnramifiedRoots_of_isSepClosure [IsSepClosure K Ω] : HasUnramifiedRoots K Ω :=
  have := IsSepClosure.sep_closed K (K := Ω)
  inferInstance
end SeparableClosure
section Finite
section Card
variable (K M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M] [FiniteDimensional K M]
end Card
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
variable [IsGalois K Ω]
end Finite
end GroundTheory.LocalField


