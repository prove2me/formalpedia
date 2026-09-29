-- Prove2me | Definitions.Def_ValuationSubring_RatPlaceCenterHelpers
-- name    : ValuationSubring_RatPlaceCenterHelpers
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/7ef42ac7-da0a-5748-b30b-2ff784e31b82
-- title:
--   Valuation subrings over a rational prime: nonunits, place centres
-- statement:
--   The module assembles three groups of definitions and helper facts about valuation subrings of a field and their behaviour over a rational prime.
--
--   First, [`IntegralClosure R A`](../def/ValuationSubring_RatPlaceCenterHelpers.html#L22) is a type synonym for Mathlib's subalgebra `integralClosure R A` of elements of $A$ integral over $R$, promoted to a type carrying commutative ring, $R$-algebra and $A$-algebra structures, the scalar tower $R \to \mathrm{IntegralClosure}\,R\,A \to A$, integrality over $R$, and domain and faithful-action instances inherited from $A$. On it are recorded: the semiring action of a monoid $G$ acting on a field $K$ over $R$ (an element is moved by applying $\sigma$ to its underlying element of $K$), the compatibility of this action with the $R$-action, transport of the project's class [`ContinuousSMulDiscrete`](../def/Deformations_ContinuousSMulDiscrete.html#L7) (all sets $\{g : g\cdot x = y\}$ open) from $L$ to the integral closure, transport of `Algebra.IsInvariant` for a valuation subring $R$ of $K$ and a $G$-invariant extension $L/K$, and [`not_isField_integralClosure`](../def/ValuationSubring_RatPlaceCenterHelpers.html#L60): for a valuation subring $R \neq \top$ of $K$ and a field extension $L/K$, the integral closure of $R$ in $L$ is not a field.
--
--   Second, elementary arithmetic of $A.\mathrm{nonunits}$ for a valuation subring $A$ of a field $L$: closure under addition and negation, under multiplication by elements of $A$, the fact that $1$ is not a nonunit, and that a multiset of elements of $A$ with nonunit product has a nonunit member; invariance of $A$ and of $A.\mathrm{nonunits}$ under elements of the decomposition subgroup $\mathrm{Stab}(A) \le L \simeq_{\mathrm{alg}[K]} L$, and the description $x \in (\tau \bullet A).\mathrm{nonunits} \iff \tau^{-1}x \in A.\mathrm{nonunits}$. With $q$ prime and `A.LiesOverPrime q` (that is, $(q : L)$ lies in $A.\mathrm{nonunits}$): integers and naturals prime to $q$ have non-nonunit images; for a $\mathbb{Q}$-algebra $L$, a rational $r$ with $q \nmid \mathrm{den}(r)$ has $\mathrm{algebraMap}\,r \in A$, and additionally lands in $A.\mathrm{nonunits}$ when $q \mid \mathrm{num}(r)$. For a valuation subring $R_0$ of $\mathbb{Q}$ over $q$: membership in $R_0$ forces $q \nmid \mathrm{den}$, membership in $R_0.\mathrm{nonunits}$ forces $q \mid \mathrm{num}$, and both membership and nonunit membership match under $\mathbb{Q} \to L$.
--
--   Third, given $R_0$ a valuation subring of $\mathbb{Q}$ and $A$ one of a $\mathbb{Q}$-algebra field $L$, `algebraMap_integralClosure_mem` shows the integral closure of $R_0$ in $L$ maps into $A$ when both lie over $q$; `placeCenter A hBA` is then the ideal of $\mathrm{IntegralClosure}\,R_0\,L$ of elements whose image in $L$ is a nonunit of $A$, shown to be prime, with contraction to $R_0$ equal to the maximal ideal of $R_0$. Finally, every element of the residue field of $R_0$ is the residue of an integer, and that residue field is finite of cardinality $q$.
--
--   **Relation to Mathlib.** [`IntegralClosure R A`](../def/ValuationSubring_RatPlaceCenterHelpers.html#L22) repackages Mathlib's subalgebra `integralClosure R A` as a type so that ring, algebra, Galois-action and invariance instances can be attached to it; `LiesOverPrime` and [`ContinuousSMulDiscrete`](../def/Deformations_ContinuousSMulDiscrete.html#L7) are the project's own notions, defined in the imported modules. Two of the nonunits lemmas here duplicate, under different names, facts also available in the project's reduction-map module.
--
--   **Where it is used.** These place-arithmetic and place-centre facts underlie the construction of Frobenius elements at places of $\overline{\mathbb{Q}}$ lying over a rational prime $q$, which in turn is what makes the ramification and Frobenius-trace conditions on the mod $p$ representation attached to a Frey curve usable.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (portions (≈18%): `FLT/Deformations/RepresentationTheory/IntegralClosure.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard; `FLT/Deformations/Lemmas.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ValuationSubring_RatPlaceCenterHelpers.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_Deformations_ContinuousSMulDiscrete

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open IsLocalRing
open scoped Pointwise

section

variable {G M : Type*} [TopologicalSpace G] [SMul G M]

end

section

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

def IntegralClosure : Type _ := integralClosure R A

instance : CommRing (IntegralClosure R A) := (integralClosure R A).toCommRing

instance : Algebra R (IntegralClosure R A) := (integralClosure R A).algebra

instance : Algebra (IntegralClosure R A) A := (integralClosure R A).toAlgebra

instance [IsDomain A] : IsDomain (IntegralClosure R A) := by
  delta IntegralClosure; infer_instance

instance : Algebra.IsIntegral R (IntegralClosure R A) := by
  delta IntegralClosure; infer_instance

instance : IsScalarTower R (IntegralClosure R A) A := (integralClosure R A).isScalarTower_mid

instance [FaithfulSMul R A] : FaithfulSMul R (IntegralClosure R A) := by
  refine (faithfulSMul_iff_algebraMap_injective _ _).mpr (.of_comp (f := algebraMap _ A) ?_)
  exact (FaithfulSMul.algebraMap_injective R A)

instance mulSemiringActionIntegralClosure
    {G R K : Type*} [CommRing R] [Field K] [Algebra R K] [Monoid G] [MulSemiringAction G K]
    [SMulCommClass G R K] :
    MulSemiringAction G (IntegralClosure R K) where
  smul σ x := ⟨σ • x.1, x.2.map (MulSemiringAction.toAlgHom R K σ)⟩
  one_smul _ := Subtype.ext (one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (mul_smul _ _ _)
  smul_zero _ := Subtype.ext (smul_zero _)
  smul_add _ _ _ := Subtype.ext (smul_add _ _ _)
  smul_one _ := Subtype.ext (smul_one _)
  smul_mul _ _ _ := Subtype.ext (MulSemiringAction.smul_mul _ _ _)

instance smulCommClass_integralClosure
    {G R K : Type*} [CommRing R] [Field K] [Algebra R K] [Monoid G] [MulSemiringAction G K]
    [SMulCommClass G R K] :
    SMulCommClass G R (IntegralClosure R K) where
  smul_comm _ _ _ := Subtype.ext (smul_comm _ _ _)

lemma not_isField_integralClosure
    {K L : Type*} [Field K] [Field L] [Algebra K L] (R : ValuationSubring K) (hR : R ≠ ⊤) :
    ¬ IsField (IntegralClosure R L) := by
  have : FaithfulSMul K L := inferInstance
  contrapose! hR
  letI := hR.toField
  let F := IsFractionRing.liftAlgHom (K := K) (g := Algebra.ofId R (IntegralClosure R L))
    (FaithfulSMul.algebraMap_injective _ _)
  refine top_le_iff.mp fun x _ ↦ ?_
  have : IsIntegrallyClosed R := GCDMonoid.toIsIntegrallyClosed
  have := (isIntegral_algHom_iff F F.injective).mp (Algebra.IsIntegral.isIntegral (R := R) (F x))
  obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := R)).mp this
  exact x.2

instance isInvariant_integralClosure
    {G K L : Type*} [Field K] [Field L] [Algebra K L] [Group G] [MulSemiringAction G L]
    [SMulCommClass G K L] [Algebra.IsInvariant K L G] (R : ValuationSubring K) :
    Algebra.IsInvariant R (IntegralClosure R L) G where
  isInvariant := by
    rintro ⟨x, hx : IsIntegral _ _⟩ hx'
    obtain ⟨x, rfl⟩ := Algebra.IsInvariant.isInvariant (A := K) x fun g ↦ congr($(hx' g).1)
    rw [isIntegral_algebraMap_iff (algebraMap K L).injective] at hx
    have : IsIntegrallyClosed R := GCDMonoid.toIsIntegrallyClosed
    obtain ⟨x, rfl⟩ := (IsIntegralClosure.isIntegral_iff (A := R)).mp hx
    exact ⟨x, rfl⟩

instance continuousSMulDiscrete_integralClosure
    {G R L : Type*} [CommRing R] [Field L] [Algebra R L] [Group G] [MulSemiringAction G L]
    [SMulCommClass G R L] [TopologicalSpace G] [ContinuousSMulDiscrete G L] :
    ContinuousSMulDiscrete G (IntegralClosure R L) where
  isOpen_smul_eq x y := by
    simp only [IntegralClosure, Subtype.ext_iff]
    exact ContinuousSMulDiscrete.isOpen_smul_eq (G := G) x.1 y.1

instance {R S : Type*} [CommRing R] [CommRing S] {I : Ideal S} [Algebra R S]
    [Nontrivial R] [IsDomain S] [Algebra.IsIntegral R S] [NeZero I] : NeZero (I.under R) :=
  ⟨fun H ↦ NeZero.ne I (Ideal.eq_bot_of_comap_eq_bot H)⟩

end

namespace ValuationSubring

variable {L : Type*} [Field L]

variable (K : Type*) [Field K] [Algebra K L]

end ValuationSubring

namespace ValuationSubring

section Nonunits

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem mul_mem_nonunits_of_mem_of_mem_nonunits {x y : L} (hx : x ∈ A) (hy : y ∈ A.nonunits) :
    x * y ∈ A.nonunits := by
  rw [mem_nonunits_iff] at hy ⊢
  calc A.valuation (x * y) = A.valuation x * A.valuation y := Valuation.map_mul _ _ _
    _ ≤ 1 * A.valuation y := mul_le_mul_left ((valuation_le_one_iff A x).mpr hx) _
    _ = A.valuation y := one_mul _
    _ < 1 := hy

theorem one_notMem_nonunits_alt : (1 : L) ∉ A.nonunits := by
  rw [mem_nonunits_iff, Valuation.map_one]
  exact lt_irrefl 1

theorem neg_mem_nonunits {x : L} (hx : x ∈ A.nonunits) : -x ∈ A.nonunits := by
  rw [mem_nonunits_iff] at hx ⊢
  rwa [Valuation.map_neg]

theorem add_mem_nonunits {x y : L} (hx : x ∈ A.nonunits) (hy : y ∈ A.nonunits) :
    x + y ∈ A.nonunits := by
  rw [mem_nonunits_iff] at hx hy ⊢
  exact (A.valuation.map_add x y).trans_lt (max_lt hx hy)

theorem exists_mem_nonunits_of_multiset_prod_mem
    (s : Multiset L) (hs : ∀ x ∈ s, x ∈ A) (hprod : s.prod ∈ A.nonunits) :
    ∃ x ∈ s, x ∈ A.nonunits := by
  revert hs hprod
  induction s using Multiset.induction_on with
  | empty =>
    intro hs hprod
    rw [Multiset.prod_zero] at hprod
    exact absurd hprod (one_notMem_nonunits_alt A)
  | cons a s ih =>
    intro hs hprod
    rw [Multiset.prod_cons] at hprod
    by_cases ha : a ∈ A.nonunits
    · exact ⟨a, Multiset.mem_cons_self a s, ha⟩
    ·
      have hsA : ∀ x ∈ s, x ∈ A := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
      have hva : (1 : _) ≤ A.valuation a := by
        rw [mem_nonunits_iff, not_lt] at ha
        exact ha
      have hprod' : s.prod ∈ A.nonunits := by
        rw [mem_nonunits_iff] at hprod ⊢
        calc A.valuation s.prod = 1 * A.valuation s.prod := (one_mul _).symm
          _ ≤ A.valuation a * A.valuation s.prod := mul_le_mul_left hva _
          _ = A.valuation (a * s.prod) := (Valuation.map_mul _ _ _).symm
          _ < 1 := hprod
      obtain ⟨x, hxs, hx⟩ := ih hsA hprod'
      exact ⟨x, Multiset.mem_cons_of_mem hxs, hx⟩

end Nonunits

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem smul_mem_iff_of_mem_decompositionSubgroup {A : ValuationSubring L} {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {x : L} : σ x ∈ A ↔ x ∈ A := by
  have hσ' : σ⁻¹ • A = A := MulAction.mem_stabilizer_iff.mp ((A.decompositionSubgroup K).inv_mem hσ)
  calc σ x ∈ A ↔ σ • x ∈ A := Iff.rfl
    _ ↔ x ∈ σ⁻¹ • A := by
        rw [mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
    _ ↔ x ∈ A := by rw [hσ']

theorem smul_mem_nonunits_iff_of_mem_decompositionSubgroup {A : ValuationSubring L}
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K) {x : L} :
    σ x ∈ A.nonunits ↔ x ∈ A.nonunits := by
  have h1 : σ x = 0 ↔ x = 0 := by
    constructor
    · intro h; exact σ.injective (by simpa using h)
    · intro h; simp [h]
  have h2 : σ x⁻¹ ∈ A ↔ x⁻¹ ∈ A := smul_mem_iff_of_mem_decompositionSubgroup hσ
  rw [mem_nonunits_iff_or, mem_nonunits_iff_or, ← map_inv₀, h1, h2]

section SmulNonunits

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mem_smul_nonunits_iff {τ : L ≃ₐ[K] L} {A : ValuationSubring L} {x : L} :
    x ∈ (τ • A).nonunits ↔ τ.symm x ∈ A.nonunits := by
  rw [mem_nonunits_iff_or, mem_nonunits_iff_or]
  constructor
  · rintro (h0 | hinv)
    · left
      rw [h0, map_zero]
    · by_cases hx0 : x = 0
      · left; rw [hx0, map_zero]
      right
      intro hmem
      apply hinv
      have : τ (τ.symm x)⁻¹ ∈ τ • A := by
        rw [mem_pointwise_smul_iff_inv_smul_mem]
        have h1 : (τ⁻¹ : L ≃ₐ[K] L) • τ (τ.symm x)⁻¹ = (τ.symm x)⁻¹ := by
          show τ.symm (τ (τ.symm x)⁻¹) = (τ.symm x)⁻¹
          exact τ.symm_apply_apply _
        rw [h1]
        exact hmem
      rwa [map_inv₀, τ.apply_symm_apply] at this
  · rintro (h0 | hinv)
    · left
      have := congrArg τ h0
      rwa [τ.apply_symm_apply, map_zero] at this
    · right
      intro hmem
      apply hinv
      rw [mem_pointwise_smul_iff_inv_smul_mem] at hmem
      have h1 : (τ⁻¹ : L ≃ₐ[K] L) • x⁻¹ = (τ.symm x)⁻¹ := by
        show τ.symm x⁻¹ = (τ.symm x)⁻¹
        exact map_inv₀ _ _
      rwa [h1] at hmem

end SmulNonunits

end ValuationSubring

namespace ValuationSubring

section RatArithmetic

variable {L : Type*} [Field L]

private lemma intCast_mem'' (A : ValuationSubring L) (n : ℤ) : ((n : ℤ) : L) ∈ A :=
  intCast_mem A.toSubring n

theorem intCast_notMem_nonunits_of_not_dvd {q : ℕ} (hq : q.Prime) {A : ValuationSubring L}
    (hA : A.LiesOverPrime q) {n : ℤ} (hn : ¬ (q : ℤ) ∣ n) : ((n : ℤ) : L) ∉ A.nonunits := by
  intro hmem

  have hqirr : Irreducible ((q : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hq).irreducible
  obtain ⟨u, v, huv⟩ := hqirr.coprime_iff_not_dvd.mpr hn

  have h1 : (u : L) * ((q : ℕ) : L) + (v : L) * ((n : ℤ) : L) = 1 := by
    have h0 : ((u * (q : ℕ) + v * n : ℤ) : L) = ((1 : ℤ) : L) := by rw [huv]
    push_cast at h0
    exact h0

  apply one_notMem_nonunits_alt A
  rw [← h1]
  refine add_mem_nonunits A ?_ ?_
  · exact mul_mem_nonunits_of_mem_of_mem_nonunits A (intCast_mem'' A u) hA
  · exact mul_mem_nonunits_of_mem_of_mem_nonunits A (intCast_mem'' A v) hmem

theorem natCast_notMem_nonunits_of_not_dvd {q : ℕ} (hq : q.Prime) {A : ValuationSubring L}
    (hA : A.LiesOverPrime q) {n : ℕ} (hn : ¬ q ∣ n) : ((n : ℕ) : L) ∉ A.nonunits := by
  have h := intCast_notMem_nonunits_of_not_dvd hq hA (n := (n : ℤ))
    (fun hd => hn (by exact_mod_cast hd))
  rwa [Int.cast_natCast] at h

variable [Algebra ℚ L]

theorem algebraMap_rat_mem_of_not_dvd_den {q : ℕ} (hq : q.Prime) {A : ValuationSubring L}
    (hA : A.LiesOverPrime q) {r : ℚ} (hden : ¬ q ∣ r.den) :
    algebraMap ℚ L r ∈ A := by

  have hd1 : ((r.den : ℕ) : L) ∉ A.nonunits := natCast_notMem_nonunits_of_not_dvd hq hA hden
  have hdinv : (((r.den : ℕ) : L))⁻¹ ∈ A := by
    by_contra hinv
    exact hd1 (A.mem_nonunits_iff_or.mpr (Or.inr hinv))

  have hr : algebraMap ℚ L r = ((r.num : ℤ) : L) * (((r.den : ℕ) : L))⁻¹ := by
    conv_lhs => rw [← Rat.num_div_den r]
    rw [map_div₀, div_eq_mul_inv, map_intCast, map_natCast]
  rw [hr]
  exact MulMemClass.mul_mem (intCast_mem'' A r.num) hdinv

theorem algebraMap_rat_mem_nonunits_of_dvd_num {q : ℕ} (hq : q.Prime) {A : ValuationSubring L}
    (hA : A.LiesOverPrime q) {r : ℚ} (hden : ¬ q ∣ r.den) (hnum : (q : ℤ) ∣ r.num) :
    algebraMap ℚ L r ∈ A.nonunits := by
  obtain ⟨m, hm⟩ := hnum
  have hd1 : ((r.den : ℕ) : L) ∉ A.nonunits := natCast_notMem_nonunits_of_not_dvd hq hA hden
  have hdinv : (((r.den : ℕ) : L))⁻¹ ∈ A := by
    by_contra hinv
    exact hd1 (A.mem_nonunits_iff_or.mpr (Or.inr hinv))

  have hr : algebraMap ℚ L r = (((m : ℤ) : L) * (((r.den : ℕ) : L))⁻¹) * ((q : ℕ) : L) := by
    conv_lhs => rw [← Rat.num_div_den r]
    rw [map_div₀, div_eq_mul_inv, map_intCast, map_natCast, hm]
    push_cast
    ring
  rw [hr]
  exact mul_mem_nonunits_of_mem_of_mem_nonunits A
    (MulMemClass.mul_mem (intCast_mem'' A m) hdinv) hA

end RatArithmetic

section RatPlace

variable {q : ℕ} (hq : q.Prime) {R₀ : ValuationSubring ℚ} (hR₀ : R₀.LiesOverPrime q)

include hq hR₀ in

theorem not_dvd_den_of_mem {r : ℚ} (hr : r ∈ R₀) : ¬ q ∣ r.den := by
  intro hdvd

  have hnum : ¬ (q : ℤ) ∣ r.num := by
    intro hdvd'
    have h1 : q ∣ r.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr hdvd'
      simpa using this
    have h2 := Nat.dvd_gcd h1 hdvd
    have h4 : Nat.gcd r.num.natAbs r.den = 1 := r.reduced
    rw [h4] at h2
    exact hq.one_lt.ne' (Nat.dvd_one.mp h2)

  have hnotmem : ((r.num : ℤ) : ℚ) ∉ R₀.nonunits :=
    intCast_notMem_nonunits_of_not_dvd hq hR₀ hnum

  obtain ⟨c, hc⟩ := hdvd
  have hden0 : ((r.den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  have hrden : ((r.num : ℤ) : ℚ) = (r * (c : ℕ)) * ((q : ℕ) : ℚ) := by
    have h4 : ((r.num : ℤ) : ℚ) = r * ((r.den : ℕ) : ℚ) :=
      (div_eq_iff hden0).mp (Rat.num_div_den r)
    rw [h4, hc]
    push_cast
    ring
  apply hnotmem
  rw [hrden]
  exact mul_mem_nonunits_of_mem_of_mem_nonunits R₀
    (MulMemClass.mul_mem hr (natCast_mem' R₀ c)) hR₀

include hq hR₀ in

theorem dvd_num_of_mem_nonunits {r : ℚ} (hr : r ∈ R₀.nonunits) : (q : ℤ) ∣ r.num := by
  by_contra hnum

  have hnum0 : r.num ≠ 0 := by
    intro h0
    exact hnum (h0 ▸ dvd_zero _)
  have hnotmem : ((r.num : ℤ) : ℚ) ∉ R₀.nonunits :=
    intCast_notMem_nonunits_of_not_dvd hq hR₀ hnum
  have hninv : (((r.num : ℤ) : ℚ))⁻¹ ∈ R₀ := by
    by_contra hinv
    exact hnotmem (R₀.mem_nonunits_iff_or.mpr (Or.inr hinv))

  have hrinv : r⁻¹ = ((r.den : ℕ) : ℚ) * (((r.num : ℤ) : ℚ))⁻¹ := by
    conv_lhs => rw [← Rat.num_div_den r]
    rw [inv_div, div_eq_mul_inv]
  rcases (R₀.mem_nonunits_iff_or).mp hr with h0 | hinv
  · exact hnum0 (Rat.num_eq_zero.mpr h0)
  · exact hinv (hrinv ▸ MulMemClass.mul_mem (natCast_mem' R₀ r.den) hninv)

variable {L : Type*} [Field L] [Algebra ℚ L]
variable {A : ValuationSubring L} (hA : A.LiesOverPrime q)

include hq hR₀ hA in

theorem algebraMap_rat_mem_of_mem {r : ℚ} (hr : r ∈ R₀) : algebraMap ℚ L r ∈ A :=
  algebraMap_rat_mem_of_not_dvd_den hq hA (not_dvd_den_of_mem hq hR₀ hr)

include hq hR₀ hA in

theorem algebraMap_rat_mem_nonunits_of_mem_nonunits {r : ℚ} (hr : r ∈ R₀.nonunits) :
    algebraMap ℚ L r ∈ A.nonunits :=
  algebraMap_rat_mem_nonunits_of_dvd_num hq hA
    (not_dvd_den_of_mem hq hR₀ (R₀.nonunits_subset hr)) (dvd_num_of_mem_nonunits hq hR₀ hr)

include hq hR₀ hA in

theorem mem_nonunits_of_algebraMap_mem_nonunits {r : ℚ}
    (h : algebraMap ℚ L r ∈ A.nonunits) : r ∈ R₀.nonunits := by
  by_contra hnot

  have hr0 : r ≠ 0 := by
    intro h0
    exact hnot (R₀.mem_nonunits_iff_or.mpr (Or.inl h0))
  have hrinv : r⁻¹ ∈ R₀ := by
    by_contra hinv
    exact hnot (R₀.mem_nonunits_iff_or.mpr (Or.inr hinv))
  rcases (A.mem_nonunits_iff_or).mp h with h0 | hinv
  · exact hr0 ((map_eq_zero _).mp h0)
  · exact hinv (by
      rw [← map_inv₀]
      exact algebraMap_rat_mem_of_mem hq hR₀ hA hrinv)

end RatPlace

section IntegralClosureMem

variable {L : Type*} [Field L] [Algebra ℚ L]

set_option maxHeartbeats 400000 in

theorem algebraMap_integralClosure_mem {q : ℕ} (hq : q.Prime)
    {R₀ : ValuationSubring ℚ} (hR₀ : R₀.LiesOverPrime q)
    {A : ValuationSubring L} (hA : A.LiesOverPrime q) (b : IntegralClosure R₀ L) :
    algebraMap (IntegralClosure R₀ L) L b ∈ A := by

  let f : R₀ →+* A :=
    { toFun := fun r => ⟨algebraMap ℚ L (r : ℚ), algebraMap_rat_mem_of_mem hq hR₀ hA r.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by push_cast; simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by push_cast; simp) }
  letI : Algebra R₀ A := f.toAlgebra
  haveI : IsScalarTower R₀ A L := IsScalarTower.of_algebraMap_eq fun r => rfl

  have hint : IsIntegral R₀ (algebraMap (IntegralClosure R₀ L) L b) := by
    have h0 := (Algebra.IsIntegral.isIntegral (R := R₀) b).map
      (IsScalarTower.toAlgHom R₀ (IntegralClosure R₀ L) L)
    rwa [IsScalarTower.toAlgHom_apply] at h0
  have hintA : IsIntegral A (algebraMap (IntegralClosure R₀ L) L b) := hint.tower_top
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintA
  exact ha ▸ a.2

end IntegralClosureMem

section PlaceCenter

variable {L : Type*} [Field L] [Algebra ℚ L] {R₀ : ValuationSubring ℚ}

def placeCenter (A : ValuationSubring L)
    (hBA : ∀ b : IntegralClosure R₀ L, algebraMap (IntegralClosure R₀ L) L b ∈ A) :
    Ideal (IntegralClosure R₀ L) where
  carrier := {b | algebraMap (IntegralClosure R₀ L) L b ∈ A.nonunits}
  add_mem' := fun ha hb => by
    simpa only [Set.mem_setOf_eq, map_add] using add_mem_nonunits A ha hb
  zero_mem' := by
    simpa only [Set.mem_setOf_eq, map_zero] using (A.mem_nonunits_iff_or.mpr (Or.inl rfl))
  smul_mem' := fun c x hx => by
    simpa only [Set.mem_setOf_eq, smul_eq_mul, map_mul] using
      mul_mem_nonunits_of_mem_of_mem_nonunits A (hBA c) hx

theorem mem_placeCenter_iff {A : ValuationSubring L}
    {hBA : ∀ b : IntegralClosure R₀ L, algebraMap (IntegralClosure R₀ L) L b ∈ A}
    {b : IntegralClosure R₀ L} :
    b ∈ placeCenter A hBA ↔ algebraMap (IntegralClosure R₀ L) L b ∈ A.nonunits :=
  Iff.rfl

theorem placeCenter_isPrime (A : ValuationSubring L)
    (hBA : ∀ b : IntegralClosure R₀ L, algebraMap (IntegralClosure R₀ L) L b ∈ A) :
    (placeCenter A hBA).IsPrime := by
  rw [Ideal.isPrime_iff]
  constructor
  · intro htop
    have h1 : (1 : IntegralClosure R₀ L) ∈ placeCenter A hBA := htop ▸ Submodule.mem_top
    rw [mem_placeCenter_iff, map_one] at h1
    exact one_notMem_nonunits_alt A h1
  · intro a b hab
    rw [mem_placeCenter_iff, map_mul] at hab
    rw [mem_placeCenter_iff, mem_placeCenter_iff]
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨ha, hb⟩ := hcon
    have ha0 : algebraMap (IntegralClosure R₀ L) L a ≠ 0 := fun h =>
      ha (A.mem_nonunits_iff_or.mpr (Or.inl h))
    have hb0 : algebraMap (IntegralClosure R₀ L) L b ≠ 0 := fun h =>
      hb (A.mem_nonunits_iff_or.mpr (Or.inl h))
    have hainv : (algebraMap (IntegralClosure R₀ L) L a)⁻¹ ∈ A := by
      by_contra h
      exact ha (A.mem_nonunits_iff_or.mpr (Or.inr h))
    have hbinv : (algebraMap (IntegralClosure R₀ L) L b)⁻¹ ∈ A := by
      by_contra h
      exact hb (A.mem_nonunits_iff_or.mpr (Or.inr h))
    rcases (A.mem_nonunits_iff_or).mp hab with h0 | hinv
    · exact mul_ne_zero ha0 hb0 h0
    · exact hinv (by rw [mul_inv]; exact MulMemClass.mul_mem hainv hbinv)

theorem placeCenter_under {q : ℕ} (hq : q.Prime) (hR₀ : R₀.LiesOverPrime q)
    {A : ValuationSubring L} (hA : A.LiesOverPrime q)
    (hBA : ∀ b : IntegralClosure R₀ L, algebraMap (IntegralClosure R₀ L) L b ∈ A) :
    (placeCenter A hBA).under R₀ = IsLocalRing.maximalIdeal R₀ := by
  ext r
  rw [Ideal.under_def, Ideal.mem_comap, mem_placeCenter_iff]
  have hco : algebraMap (IntegralClosure R₀ L) L (algebraMap R₀ (IntegralClosure R₀ L) r)
      = algebraMap ℚ L (r : ℚ) := by
    rw [← IsScalarTower.algebraMap_apply R₀ (IntegralClosure R₀ L) L]
    rfl
  rw [hco]
  constructor
  · intro h
    exact (R₀.coe_mem_nonunits_iff).mp
      (mem_nonunits_of_algebraMap_mem_nonunits hq hR₀ hA h)
  · intro h
    exact algebraMap_rat_mem_nonunits_of_mem_nonunits hq hR₀ hA
      ((R₀.coe_mem_nonunits_iff).mpr h)

end PlaceCenter

end ValuationSubring

open Polynomial

namespace ValuationSubring

section ResidueFieldRat

variable {q : ℕ} (hq : q.Prime) {R₀ : ValuationSubring ℚ} (hR₀ : R₀.LiesOverPrime q)

include hq hR₀ in

theorem exists_intCast_residue_eq (x : ResidueField R₀) :
    ∃ n : ℤ, residue R₀ (n : R₀) = x := by
  obtain ⟨r, rfl⟩ := residue_surjective x

  have hden : ¬ q ∣ (r : ℚ).den := not_dvd_den_of_mem hq hR₀ r.2

  have hcop : IsCoprime ((r : ℚ).den : ℤ) ((q : ℕ) : ℤ) := by
    refine Nat.Coprime.isCoprime ?_
    exact (Nat.Prime.coprime_iff_not_dvd hq |>.mpr hden).symm
  obtain ⟨c, d, hcd⟩ := hcop
  refine ⟨c * (r : ℚ).num, ?_⟩

  have hmem : r - ((c * (r : ℚ).num : ℤ) : R₀) ∈ IsLocalRing.maximalIdeal R₀ := by
    rw [← coe_mem_nonunits_iff]
    have hden0 : (((r : ℚ).den : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (r : ℚ).den_nz
    have hnum : ((r : ℚ).num : ℚ) = (r : ℚ) * ((r : ℚ).den : ℚ) :=
      (div_eq_iff hden0).mp (Rat.num_div_den (r : ℚ))
    have hkey : ((r : R₀) : ℚ) - ((c * (r : ℚ).num : ℤ) : ℚ)
        = (r : ℚ) * (((d : ℚ)) * ((q : ℕ) : ℚ)) := by
      push_cast
      rw [hnum]
      have : (c : ℚ) * ((r : ℚ).den : ℚ) + (d : ℚ) * ((q : ℕ) : ℚ) = 1 := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hcd
      linear_combination (-((r : R₀) : ℚ)) * this
    have hsub : ((r - ((c * (r : ℚ).num : ℤ) : R₀) : R₀) : ℚ)
        = ((r : R₀) : ℚ) - ((c * (r : ℚ).num : ℤ) : ℚ) := by
      push_cast
      ring
    rw [hsub, hkey]
    refine mul_mem_nonunits_of_mem_of_mem_nonunits R₀ r.2 ?_
    exact mul_mem_nonunits_of_mem_of_mem_nonunits R₀ (intCast_mem R₀.toSubring d) hR₀
  exact (Ideal.Quotient.eq.mpr hmem).symm

include hq hR₀ in

theorem residueField_finite_and_card :
    Finite (ResidueField R₀) ∧ Nat.card (ResidueField R₀) = q := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField R₀) q := charP_residueField_of_liesOverPrime_def hq hR₀

  set f : ZMod q →+* ResidueField R₀ := ZMod.castHom (dvd_refl q) (ResidueField R₀) with hf
  have hinj : Function.Injective f := f.injective
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨n, hn⟩ := exists_intCast_residue_eq hq hR₀ x
    refine ⟨(n : ZMod q), ?_⟩
    rw [map_intCast]
    rw [← hn]
    have : ((n : ℤ) : ResidueField R₀) = residue R₀ ((n : ℤ) : R₀) := by
      simp
    exact this
  have hbij : Function.Bijective f := ⟨hinj, hsurj⟩
  haveI : Finite (ResidueField R₀) := Finite.of_surjective f hsurj
  refine ⟨inferInstance, ?_⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_zmod]

end ResidueFieldRat

end ValuationSubring


