-- Prove2me | solution 1 for ArtinPrimitiveRoots.exists_cutoff_residueSymbol_span_eq_one_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T13:18:35.362996+00:00
-- url     : https://prove2.me/submissions/482a7638-83b4-4381-acce-30cf95afdc4f

import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_Abelian_exists_narrowRayClassChar_conductor_eq_localValue_u0
import Theorems.Thm_ArtinL_Abelian_dvd_conductor_iff_not_isUnramifiedAt
import Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Definitions.Def_ArtinHeckeRowL
import Theorems.Thm_ArtinPrimitiveRoots_heckeLSeries_euler_package_of_le
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_NormPowChar
import Mathlib

universe u

section
section
/-! # L3K_Gamma: the Gamma-factor ratio on the left edge of the convexity strip

* `norm_Gamma_mono`: `σ ↦ ‖Γ(σ + it)‖ / Γ(σ)` is nondecreasing on `σ > 0` (Gauss's product).
* `norm_Gamma_one_add_sq`: `‖Γ(1 + it)‖² = π |t| / |sinh(π t)|`.
* `exists_norm_Gammaℂ_ratio_le`: for `0 < δ < 1`,
  `‖Γ_ℂ(1 + δ − it) / Γ_ℂ(−δ + it)‖ ≤ C (1 + |t|)^3`. -/

open Complex Filter Topology

set_option autoImplicit false

namespace ArtinPrimitiveRoots

namespace L3K

end L3K

end ArtinPrimitiveRoots

end
end

section
section
/-! # T12A_Sum: Dirichlet series over ideals as sums over ideals

For `f : Ideal (𝓞 K) → ℂ` bounded by `1` and `Re s > 1`, the `LSeries` whose `n`-th coefficient is
`∑ᶠ I ∈ {absNorm I = n}, f I` is the (absolutely convergent) sum `∑' I, f I * N(I)^{-s}`. -/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open NumberField Complex Filter Topology Ideal

namespace ArtinPrimitiveRoots.T12A

variable {K : Type*} [Field K] [NumberField K]

instance finite_fiber (n : ℕ) : Finite {I : Ideal (𝓞 K) // absNorm I = n} := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton {I : Ideal (𝓞 K) // absNorm I = 0} :=
      ⟨fun a b => Subtype.ext (by
        rw [Ideal.absNorm_eq_zero_iff.mp a.2, Ideal.absNorm_eq_zero_iff.mp b.2])⟩
    exact Finite.of_subsingleton
  · exact (finite_setOfPred_absNorm_eq n).to_subtype

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # T12A_Ray: a `HeckeChar` as a narrow ray class character

A `HeckeChar K 𝔪` (𝔪 ≠ ⊥) is `I ↦ ψ([I])` on ideals coprime to `𝔪` for a character `ψ` of the narrow
ray class group mod `𝔪` with parity set `∅`, and `χ.LSeries = rayClassLSeries ψ` on `Re s > 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply nonZeroDivisors Complex

namespace ArtinPrimitiveRoots.T12A

section Coprime

variable {F : Type*} [Field F] [NumberField F]

theorem sup_eq_top_iff_forall {I 𝔣 : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    I ⊔ 𝔣 = ⊤ ↔ ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ 𝔣 → ¬ v.asIdeal ∣ I := by
  constructor
  · intro h v hf hI'
    apply v.isPrime.ne_top
    rw [eq_top_iff, ← h]
    exact sup_le (Ideal.le_of_dvd hI') (Ideal.le_of_dvd hf)
  · intro h
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hmb : m ≠ ⊥ := by
      intro hb
      apply hI
      rw [eq_bot_iff, ← hb]
      exact le_trans le_sup_left hle
    let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, hmb⟩
    exact h v (Ideal.dvd_iff_le.mpr (le_trans le_sup_right hle))
      (Ideal.dvd_iff_le.mpr (le_trans le_sup_left hle))

theorem mk0_mem_coprimeToModulus_iff {I 𝔣 : Ideal (𝓞 F)} (hI : I ∈ (Ideal (𝓞 F))⁰) :
    FractionalIdeal.mk0 F ⟨I, hI⟩ ∈ coprimeToModulus F 𝔣 ↔ I ⊔ 𝔣 = ⊤ := by
  have hI0 : I ≠ 0 := nonZeroDivisors.ne_zero hI
  rw [mem_coprimeToModulus_iff, sup_eq_top_iff_forall hI0]
  refine forall_congr' fun v => imp_congr_right fun _ => ?_
  rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coe F v hI0, Nat.cast_eq_zero]
  constructor
  · intro h hd
    exact (Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mpr hd h
  · intro h
    by_contra hc
    exact h ((Associates.count_ne_zero_iff_dvd hI0 v.irreducible).mp hc)

theorem span_ne_bot {α : 𝓞 F} (hα : α ≠ 0) : Ideal.span {α} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact hα

theorem span_sup_eq_top {𝔣 : Ideal (𝓞 F)} {α : 𝓞 F} (h1 : α - 1 ∈ 𝔣) :
    Ideal.span {α} ⊔ 𝔣 = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : (1 : 𝓞 F) = α - (α - 1) := by ring
  rw [h]
  exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self α))
    (Ideal.mem_sup_right h1)

end Coprime

section Factor

variable {F : Type*} [Field F] [NumberField F] {𝔣 : Ideal (𝓞 F)}

end Factor

section Ray

variable {K : Type} [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}

open Classical in
/-- The class of an ideal (`1` when it is zero or not coprime to `𝔪`). -/
noncomputable def cls (𝔪 : Ideal (𝓞 K)) (I : Ideal (𝓞 K)) : NarrowRayClassGroup K 𝔪 :=
  if h : I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ then
    NarrowRayClassGroup.mk K 𝔪 ⟨FractionalIdeal.mk0 K ⟨I, mem_nonZeroDivisors_of_ne_zero h.1⟩,
      (mk0_mem_coprimeToModulus_iff _).2 h.2⟩
  else 1

end Ray

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # C3A_Sieve: Euler products of multiplicative functions of four ideals

A function `f` on 4-tuples of ideals of `𝓞 F`, supported on exterior tuples, with
`f (P^e · y) = A P e · f y` for exterior primes `P` and exterior `y` prime to `P`, and absolutely
summable, has the Euler product `∑' f = ∏'_P ∑'_e A P e` over the exterior primes (`euler4`).
Proof: the finite sieve `∑' f = (∏_{P ∈ T} L_P) · ∑'_{x prime to T} f x` (induction on `T`) and a
tail estimate. Also a bound `‖f‖ ≤ B` for multiplicative majorants (`norm_le_of_mul`). -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

section sieve

variable (𝔪 : Ideal (𝓞 F))

variable {𝔪 f A}

end sieve

end C3A

end ArtinPrimitiveRoots

end
end

section
section
/-!
# T12B: elementary Euler-product glue for `HeckeChar.LSeries`

* `T12B.norm_le_one`: `‖χ I‖ ≤ 1` (values on coprime ideals are roots of unity: class group and
  `(𝓞/𝔪)ˣ` are finite).
* `T12B.lseries_eq_tsum`: `L(s, χ) = ∑'_I χ(I) N(I)^{-s}` for `Re s > 1`.
* `T12B.sieve`: `(∑' g) · ∏_{P ∈ T} (1 − g P) = ∑'_{I coprime to T} g I` for completely
  multiplicative `g` (finite Euler sieve; no infinite product needed).
* `T12B.sieve_bound`: the sieved sum is close to `1` once `T` kills a large finite set.
-/

namespace ArtinPrimitiveRoots

open NumberField Filter Topology
open scoped nonZeroDivisors

namespace T12B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Summability of `∑_I N(I)^{-σ}` -/

instance fiber_finite (n : ℕ) : Finite {I : Ideal (𝓞 F) // Ideal.absNorm I = n} :=
  (Ideal.finite_setOfPred_absNorm_eq n).to_subtype

/-! ### Basic facts on Hecke characters -/

theorem toFun_top {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊤ = 1 := by
  have := χ.map_principal' 1 one_ne_zero (by simp)
  rwa [Ideal.span_singleton_one] at this

theorem toFun_bot {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) : χ.toFun ⊥ = 0 :=
  (χ.eq_zero_iff' ⊥).2 (Or.inl rfl)

/-! ### The Dirichlet series as a sum over ideals -/

/-! ### The finite sieve -/

end T12B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3A_Euler1: Euler products of `L(s, χ)` and `ζ^S(s)` over the exterior primes

From `euler4` (one active coordinate) and T12B's sieve:
* `hasProd_inv_LSeries`: `∏_{P ∉ S} (1 − χ(P) N P^{-s}) = L(s, χ)⁻¹` for `Re s > 1`;
* `hasProd_zetaS`: `∏_{P ∉ S} (1 − N P^{-s})⁻¹ = ∏_{P ⊇ 𝔪} (1 − N P^{-s}) · ζ_F(s)`. -/

open NumberField Filter Topology

namespace ArtinPrimitiveRoots

namespace C3A

variable {F : Type*} [Field F] [NumberField F]

lemma sup_mul_eq_top_iff {𝔪 I J : Ideal (𝓞 F)} :
    I * J ⊔ 𝔪 = ⊤ ↔ I ⊔ 𝔪 = ⊤ ∧ J ⊔ 𝔪 = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_left _
    · rw [eq_top_iff, ← h]; exact sup_le_sup_right Ideal.mul_le_right _
  · rintro ⟨h1, h2⟩
    rw [Ideal.mul_sup_eq_of_coprime_left h1, h2]

/-! ### The one-variable Euler product from `euler4` -/

section one

variable {𝔪 : Ideal (𝓞 F)} (χ : HeckeChar F 𝔪) (s : ℂ)

end one

/-! ### `ζ^S` -/

end C3A

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3K_Hecke: an abelian Artin character as a `HeckeChar` of modulus its conductor

For `K` totally complex, `M/K` Galois and `ψ : Gal(M/K) →* ℂˣ`, library 41aa80ff gives a narrow ray
class character `χ_R` mod `𝔣 = conductor ψ` with `χ_R(v) = localValue ψ v`. Then
`psiH I = χ_R([I])` (on `I` coprime to `𝔣`) is a `HeckeChar K 𝔣` with `psiH = idealValue ψ` on nonzero
ideals, so `ArtinL.Abelian.LSeries ψ = psiH.LSeries`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

/-- The ray class character of 41aa80ff. -/
def chiR : NarrowRayClassGroup K (ArtinL.Abelian.conductor ψ) →* ℂ :=
  (ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0 K M ψ).choose

open scoped Classical in
lemma chiR_spec :
    (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : ¬ v.asIdeal ∣ ArtinL.Abelian.conductor ψ),
        chiR ψ (primeClass K (ArtinL.Abelian.conductor ψ) v hv) = ArtinL.Abelian.localValue ψ v) ∧
      (chiR ψ = 1 ↔ ψ = 1) ∧
      (∀ (α : 𝓞 K) (hα : α ≠ 0)
        (hc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ)),
        α - 1 ∈ ArtinL.Abelian.conductor ψ →
          chiR ψ (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ) ⟨principalUnit K α hα, hc⟩) =
            ∏ w ∈ (Finset.univ.filter fun w : {w : InfinitePlace K // w.IsReal} =>
                ¬ ArtinL.Abelian.IsPlusAt ψ w.1),
              ((SignType.sign (embedding_of_isReal w.2 (α : K)) : ℤ) : ℂ)) := by
  have h := (ArtinL.Abelian.exists_narrowRayClassChar_conductor_eq_localValue_u0 K M ψ).choose_spec
  exact ⟨h.1, h.2.1, h.2.2.1⟩

lemma chiR_ne_zero (C : NarrowRayClassGroup K (ArtinL.Abelian.conductor ψ)) : chiR ψ C ≠ 0 := by
  intro h
  have : chiR ψ C * chiR ψ C⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h, zero_mul] at this; exact zero_ne_one this

lemma sup_eq_top_iff_not_dvd (v : HeightOneSpectrum (𝓞 K)) (𝔣 : Ideal (𝓞 K)) :
    v.asIdeal ⊔ 𝔣 = ⊤ ↔ ¬ v.asIdeal ∣ 𝔣 := by
  rw [Ideal.dvd_iff_le]
  constructor
  · intro h hle
    apply v.isPrime.ne_top; rw [← h]; exact le_antisymm le_sup_left (sup_le le_rfl hle)
  · intro h
    by_contra hne
    have e := v.isMaximal.eq_of_le hne le_sup_left
    exact h (e ▸ le_sup_right)

open Classical in
lemma cls_mul {𝔣 : Ideal (𝓞 K)} {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥ ∧ I ⊔ 𝔣 = ⊤)
    (hJ : J ≠ ⊥ ∧ J ⊔ 𝔣 = ⊤) (hIJ : I * J ≠ ⊥ ∧ I * J ⊔ 𝔣 = ⊤) :
    T12A.cls 𝔣 (I * J) = T12A.cls 𝔣 I * T12A.cls 𝔣 J := by
  rw [T12A.cls, T12A.cls, T12A.cls, dif_pos hI, dif_pos hJ, dif_pos hIJ, ← map_mul]
  congr 1
  apply Subtype.ext
  show FractionalIdeal.mk0 K ⟨I * J, _⟩ = FractionalIdeal.mk0 K ⟨I, _⟩ * FractionalIdeal.mk0 K ⟨J, _⟩
  rw [← map_mul]; rfl

open Classical in
/-- The Hecke character `psiH` of modulus `conductor ψ`. -/
def psiH (hK : ∀ w : InfinitePlace K, w.IsComplex) :
    HeckeChar K (ArtinL.Abelian.conductor ψ) where
  toFun I := if I ≠ ⊥ ∧ I ⊔ ArtinL.Abelian.conductor ψ = ⊤ then
    chiR ψ (T12A.cls (ArtinL.Abelian.conductor ψ) I) else 0
  map_mul' I J := by
    have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
      simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    by_cases hI : I ≠ ⊥ ∧ I ⊔ ArtinL.Abelian.conductor ψ = ⊤ <;>
      by_cases hJ : J ≠ ⊥ ∧ J ⊔ ArtinL.Abelian.conductor ψ = ⊤
    · have hIJ : I * J ≠ ⊥ ∧ I * J ⊔ ArtinL.Abelian.conductor ψ = ⊤ :=
        ⟨hb.2 ⟨hI.1, hJ.1⟩, C3A.sup_mul_eq_top_iff.2 ⟨hI.2, hJ.2⟩⟩
      rw [if_pos hIJ, if_pos hI, if_pos hJ, cls_mul hI hJ hIJ, map_mul]
    · rw [if_neg hJ, mul_zero, if_neg]
      rintro ⟨h1, h2⟩; exact hJ ⟨(hb.1 h1).2, (C3A.sup_mul_eq_top_iff.1 h2).2⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (C3A.sup_mul_eq_top_iff.1 h2).1⟩
    · rw [if_neg hI, zero_mul, if_neg]
      rintro ⟨h1, h2⟩; exact hI ⟨(hb.1 h1).1, (C3A.sup_mul_eq_top_iff.1 h2).1⟩
  eq_zero_iff' I := by
    split_ifs with h
    · simp only [chiR_ne_zero, false_iff, not_or, not_not]; exact h
    · simp only [true_iff]; by_contra h'; push Not at h'; exact h h'
  map_principal' α hα h1 := by
    have hc : Ideal.span {α} ≠ ⊥ ∧ Ideal.span {α} ⊔ ArtinL.Abelian.conductor ψ = ⊤ :=
      ⟨T12A.span_ne_bot hα, T12A.span_sup_eq_top h1⟩
    rw [if_pos hc, T12A.cls, dif_pos hc]
    have hpc : principalUnit K α hα ∈ coprimeToModulus K (ArtinL.Abelian.conductor ψ) :=
      (T12A.mk0_mem_coprimeToModulus_iff _).2 hc.2
    have := (chiR_spec ψ).2.2 α hα hpc h1
    refine (congrArg (chiR ψ) (congrArg (NarrowRayClassGroup.mk K (ArtinL.Abelian.conductor ψ))
      (Subtype.ext rfl))).trans (this.trans ?_)
    apply Finset.prod_eq_one
    intro w _
    exact absurd w.2 (not_isReal_iff_isComplex.2 (hK w.1))

variable (hK : ∀ w : InfinitePlace K, w.IsComplex)

lemma psiH_prime (v : HeightOneSpectrum (𝓞 K)) :
    (psiH ψ hK).toFun v.asIdeal = ArtinL.Abelian.localValue ψ v := by
  classical
  by_cases hv : v.asIdeal ∣ ArtinL.Abelian.conductor ψ
  · have h1 : ¬ (v.asIdeal ≠ ⊥ ∧ v.asIdeal ⊔ ArtinL.Abelian.conductor ψ = ⊤) := fun h =>
      (sup_eq_top_iff_not_dvd v _).1 h.2 hv
    have h2 := (ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt K M ψ v).1 hv
    show (if _ then _ else _) = _
    rw [if_neg h1, ArtinL.Abelian.localValue, if_neg h2]
  · have h1 : v.asIdeal ≠ ⊥ ∧ v.asIdeal ⊔ ArtinL.Abelian.conductor ψ = ⊤ :=
      ⟨v.ne_bot, (sup_eq_top_iff_not_dvd v _).2 hv⟩
    show (if _ then _ else _) = _
    rw [if_pos h1, T12A.cls, dif_pos h1, ← (chiR_spec ψ).1 v hv]
    rfl

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Conv: the convexity bound for an abelian Artin `L`-function with explicit conductor

For `K` totally complex, `ψ ≠ 1`: the entire continuation `L` of `L(s, ψ)` satisfies
`‖L(s)‖ ≤ C (N 𝔣_ψ)^{1/2+δ} (1 + |t|)^{3 r₂}` on `−δ ≤ Re s ≤ 4`, with `C` depending only on `K`
and `δ`, provided `L` has some polynomial growth on the strip (`GrowthHyp`, from L3K_Growth).

Inputs: the FE 3508ac81 (`Λ(1−s) = W Λ'(s)`), `|W| = 1` from `Λ' = conj ∘ Λ ∘ conj`, the Gamma
ratio of L3K_Gamma, and Phragmén–Lindelöf 40726dc6. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Complex

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Growth: the a-priori growth hypothesis for Phragmén–Lindelöf

For `ψ ≠ 1`, the entire continuation of `L(s, ψ)` has polynomial growth on every vertical strip:
library c46e3955 applied to the idelic character `η` of f982cbad attached to `χ_R` (41aa80ff), with
`T` the primes dividing the conductor, and the Euler product of `psiH` (C3A `euler1`).
`η` is nontrivial on the norm-one ideles: otherwise `η = |·|^{it}` (a55d6ac4), finite order forces
`t = 0` (86a18a2c), and then `χ_R = 1` because the prime classes generate the ray class group. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply nonZeroDivisors
  AutomorphicForm NumberField.TateGlobal NumberField.AdelicLevel

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

section Gen

variable {K : Type} [Field K] [NumberField K]

end Gen

section Main

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M] (ψ : (M ≃ₐ[K] M) →* ℂˣ)

end Main

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_KB: the Kummer-field basics of C0Z (C0ZK, C0ZF, parts of C0ZS/ZN/ZU/ZV), copied without
the idelic Artin map, so that the KummerConvexity solution does not pull in the C0-H development. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin Polynomial

noncomputable section

namespace ArtinPrimitiveRoots.L3K.KB

section Kch


variable {F : Type} [Field F] {ℓ : ℕ} [NeZero ℓ]

/-- Every `ℓ`-th root of unity of an `F`-field comes from `F`. -/
theorem exists_of_pow_eq_one {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
    (x : M) (hx : x ^ ℓ = 1) : ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = x := by
  have hζM := hζ.map_of_injective (FaithfulSMul.algebraMap_injective F M)
  obtain ⟨i, -, hi⟩ := hζM.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow], by rw [map_pow, hi]⟩

variable {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ) (M : Type*) [Field M] [Algebra F M]
include hζ

/-- A Kummer generator: a nonzero `β` with `β^ℓ ∈ F`. -/
structure KGen (M : Type*) [Field M] [Algebra F M] (ℓ : ℕ) where
  β : M
  ne_zero : β ≠ 0
  pow_mem : ∃ a : F, β ^ ℓ = algebraMap F M a

variable {M}

theorem ratio_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : (σ g.β / g.β) ^ ℓ = 1 := by
  obtain ⟨a, ha⟩ := g.pow_mem
  rw [div_pow, ← map_pow, ha, AlgEquiv.commutes, ← ha, div_self (pow_ne_zero _ g.ne_zero)]

theorem ratio_mem (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    ∃ y : F, y ^ ℓ = 1 ∧ algebraMap F M y = σ g.β / g.β :=
  exists_of_pow_eq_one hζ M _ (ratio_pow hζ g σ)

/-- The value of the Kummer character in `F`. -/
def kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : F := (ratio_mem hζ g σ).choose

theorem kval_pow (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) : kval hζ g σ ^ ℓ = 1 :=
  (ratio_mem hζ g σ).choose_spec.1

theorem algebraMap_kval (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M (kval hζ g σ) = σ g.β / g.β :=
  (ratio_mem hζ g σ).choose_spec.2

theorem fix_ratio (g : KGen (F := F) M ℓ) (σ τ : M ≃ₐ[F] M) :
    σ (τ g.β / g.β) = τ g.β / g.β := by
  rw [← algebraMap_kval hζ g τ, AlgEquiv.commutes]

/-- The Kummer character `σ ↦ σβ/β`, valued in `μ_ℓ(F)`. -/
def kch (g : KGen (F := F) M ℓ) : (M ≃ₐ[F] M) →* rootsOfUnity ℓ F where
  toFun σ := rootsOfUnity.mkOfPowEq (kval hζ g σ) (kval_pow hζ g σ)
  map_one' := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, OneMemClass.coe_one, Units.val_one]
    apply FaithfulSMul.algebraMap_injective F M
    rw [algebraMap_kval hζ, map_one, AlgEquiv.one_apply, div_self g.ne_zero]
  map_mul' σ τ := by
    apply Subtype.ext; apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq, Subgroup.coe_mul, Units.val_mul]
    apply FaithfulSMul.algebraMap_injective F M
    rw [map_mul, algebraMap_kval hζ, algebraMap_kval hζ, algebraMap_kval hζ, AlgEquiv.mul_apply]
    have h1 : τ g.β = (τ g.β / g.β) * g.β := by field_simp [g.ne_zero]
    conv_lhs => rw [h1, map_mul, fix_ratio hζ g σ τ]
    field_simp [g.ne_zero]

theorem algebraMap_kch (g : KGen (F := F) M ℓ) (σ : M ≃ₐ[F] M) :
    algebraMap F M ((kch hζ g σ : Fˣ) : F) = σ g.β / g.β := by
  simp only [kch, MonoidHom.coe_mk, OneHom.coe_mk, rootsOfUnity.coe_mkOfPowEq]
  exact algebraMap_kval hζ g σ


end Kch

section KFsec


variable (F : Type) [Field F] (ℓ : ℕ)

/-- `F(a^{1/ℓ})`. -/
def KF (a : Fˣ) : Type := (X ^ ℓ - C (a : F)).SplittingField

/-- `F(a^{1/ℓ}, a'^{1/ℓ})`. -/
def KF2 (a a' : Fˣ) : Type := ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))).SplittingField

variable (a a' : Fˣ)

instance : Field (KF F ℓ a) := inferInstanceAs (Field (SplittingField _))
instance : Algebra F (KF F ℓ a) := inferInstanceAs (Algebra F (SplittingField _))
instance : Field (KF2 F ℓ a a') := inferInstanceAs (Field (SplittingField _))
instance : Algebra F (KF2 F ℓ a a') := inferInstanceAs (Algebra F (SplittingField _))
instance : IsSplittingField F (KF F ℓ a) (X ^ ℓ - C (a : F)) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance : IsSplittingField F (KF2 F ℓ a a') ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F))) :=
  inferInstanceAs (IsSplittingField F (SplittingField _) _)
instance : FiniteDimensional F (KF F ℓ a) := IsSplittingField.finiteDimensional _ (X ^ ℓ - C (a : F))
instance : FiniteDimensional F (KF2 F ℓ a a') :=
  IsSplittingField.finiteDimensional _ ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))
instance : Normal F (KF F ℓ a) := Normal.of_isSplittingField (X ^ ℓ - C (a : F))
instance : Normal F (KF2 F ℓ a a') :=
  Normal.of_isSplittingField ((X ^ ℓ - C (a : F)) * (X ^ ℓ - C (a' : F)))

section CharZero

variable [CharZero F]

instance : IsGalois F (KF F ℓ a) := { }
instance : IsGalois F (KF2 F ℓ a a') := { }

end CharZero

instance [NumberField F] : NumberField (KF F ℓ a) := NumberField.of_module_finite F _
instance [NumberField F] : NumberField (KF2 F ℓ a a') := NumberField.of_module_finite F _

variable {F ℓ}

theorem exists_root_of_splits {M : Type*} [Field M] [Algebra F M] (hℓ : ℓ ≠ 0)
    (hs : Splits ((X ^ ℓ - C (a : F)).map (algebraMap F M))) : ∃ β : M, β ^ ℓ = algebraMap F M a := by
  have hdeg : ((X ^ ℓ - C (a : F)).map (algebraMap F M)).degree ≠ 0 := by
    rw [degree_map]
    exact degree_ne_of_natDegree_ne (by rw [natDegree_X_pow_sub_C]; exact hℓ)
  obtain ⟨β, hβ⟩ := hs.exists_eval_eq_zero hdeg
  refine ⟨β, ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
    eval_C] at hβ
  exact sub_eq_zero.mp hβ

/-- A Kummer generator from a root of `X^ℓ - a`. -/
def kgenOf {M : Type*} [Field M] [Algebra F M] {β : M} (hβ : β ^ ℓ = algebraMap F M a)
    (hℓ : ℓ ≠ 0) : KGen (F := F) M ℓ where
  β := β
  ne_zero := by
    rintro rfl
    rw [zero_pow hℓ, eq_comm, map_eq_zero] at hβ
    exact a.ne_zero hβ
  pow_mem := ⟨a, hβ⟩

theorem splits_KF (hℓ : ℓ ≠ 0) :
    Splits ((X ^ ℓ - C (a : F)).map (algebraMap F (KF F ℓ a))) :=
  IsSplittingField.splits (KF F ℓ a) (X ^ ℓ - C (a : F))

theorem root_pow_of_mem_rootSet {M : Type*} [Field M] [Algebra F M] {b : F} {r : M}
    (hr : aeval r (X ^ ℓ - C b) = 0) : r ^ ℓ = algebraMap F M b := by
  simpa [sub_eq_zero] using hr

section Comm

variable [NeZero ℓ] {ζ : F} (hζ : IsPrimitiveRoot ζ ℓ)
include hζ

/-- A root of `X^ℓ - a` is a multiple of a fixed generator by an element of `F`. -/
theorem eq_smul_of_pow_eq {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ) {r : M}
    (hr : r ^ ℓ = g.β ^ ℓ) : ∃ c : F, r = algebraMap F M c * g.β := by
  have h1 : (r / g.β) ^ ℓ = 1 := by rw [div_pow, hr, div_self (pow_ne_zero _ g.ne_zero)]
  obtain ⟨c, -, hc⟩ := exists_of_pow_eq_one hζ M _ h1
  exact ⟨c, by rw [hc]; field_simp [g.ne_zero]⟩

theorem fixes_of_kch_eq_one {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : kch hζ g σ = 1) : σ g.β = g.β := by
  have := algebraMap_kch hζ g σ
  rw [h, OneMemClass.coe_one, Units.val_one, map_one, eq_comm, div_eq_one_iff_eq g.ne_zero] at this
  exact this

theorem fixes_root {M : Type*} [Field M] [Algebra F M] (g : KGen (F := F) M ℓ)
    (σ : M ≃ₐ[F] M) (h : σ g.β = g.β) {r : M} (hr : r ^ ℓ = g.β ^ ℓ) : σ r = r := by
  obtain ⟨c, rfl⟩ := eq_smul_of_pow_eq hζ g hr
  rw [map_mul, AlgEquiv.commutes, h]

theorem eq_one_of_kch_KF (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a)
    (h : kch hζ g σ = 1) : σ = 1 := by
  have f1 := fixes_of_kch_eq_one hζ g σ h
  apply AlgEquiv.coe_toAlgHom_injective
  refine AlgHom.ext_of_adjoin_eq_top
    (IsSplittingField.adjoin_rootSet (KF F ℓ a) (X ^ ℓ - C (a : F))) fun r hr => ?_
  rw [mem_rootSet] at hr
  show σ r = r
  exact fixes_root hζ g σ f1 (by rw [root_pow_of_mem_rootSet hr.2]; exact hg.symm)

theorem kch_KF_injective (g : KGen (F := F) (KF F ℓ a) ℓ)
    (hg : g.β ^ ℓ = algebraMap F (KF F ℓ a) a) : Function.Injective (kch hζ g) :=
  (injective_iff_map_eq_one _).mpr fun σ h => eq_one_of_kch_KF a hζ g hg σ h

end Comm


end KFsec

section RootKF
variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ]

/-- The chosen root of `X^ℓ - a` in `F(a^{1/ℓ})`. -/
def rootKF (a : Fˣ) : KGen (F := F) (KF F ℓ a) ℓ :=
  kgenOf a (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
    (NeZero.ne ℓ)

theorem rootKF_pow (a : Fˣ) : (rootKF F a).β ^ ℓ = algebraMap F (KF F ℓ a) a :=
  (exists_root_of_splits a (NeZero.ne ℓ) (splits_KF a (NeZero.ne ℓ))).choose_spec
end RootKF

section UV
/-- `n`-th roots of unity congruent modulo `Q` with `n ∉ Q` are equal. -/
theorem eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) {n : ℕ}
    (hn : (n : R) ∉ Q) {a b : R} (ha : a ^ n = 1) (hb : b ^ n = 1) (hab : a - b ∈ Q) : a = b := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  set η := b * a ^ (n - 1) with hη
  have han : a ^ (n - 1) * a = 1 := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), ha]
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ (n - 1) * (a - b) := by
      rw [hη, mul_sub, han]; ring
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · calc a = a * 1 := (mul_one a).symm
      _ = a * η := by rw [hη1]
      _ = b * (a ^ (n - 1) * a) := by rw [hη]; ring
      _ = b := by rw [han, mul_one]
  · exfalso
    have hηn : η ^ n = 1 := by
      rw [hη, mul_pow, ← pow_mul, hb, one_mul, mul_comm, pow_mul, ha, one_pow]
    have hsum : ∑ i ∈ Finset.range n, η ^ i = 0 := by
      have h := geom_sum_mul η n
      rw [hηn, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hη1)
    apply hn
    have : (n : R) = ∑ i ∈ Finset.range n, (1 - η ^ i) := by
      rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_one]
    rw [this]
    refine Q.sum_mem fun i _ => ?_
    rw [← geom_sum_mul_neg]
    exact Q.mul_mem_left _ h1

variable (F : Type) [Field F] [NumberField F] {ℓ : ℕ} [NeZero ℓ] {ζ : F}
  (hζ : IsPrimitiveRoot ζ ℓ)

/-- An integral Kummer generator `β = d α` at a place where `a` is a unit. -/
theorem exists_intGen (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) (ha : v.valuation F (a : F) = 1) :
    ∃ (d n : 𝓞 F) (β : 𝓞 (KF F ℓ a)), d ∉ v.asIdeal ∧ n ∉ v.asIdeal ∧
      (a : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n ∧
      (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β ∧
      β ^ ℓ = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (d ^ (ℓ - 1) * n) := by
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (a : F) ha.le
  have hd : (d : 𝓞 F) ∉ v.asIdeal := d.2
  have hn : n ∉ v.asIdeal := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, ha,
      (v.valuation_eq_one_iff_notMem (K := F)).mpr hd, one_mul]
  set K := KF F ℓ a
  set β : K := algebraMap F K (algebraMap (𝓞 F) F d) * (rootKF F a).β
  have hβpow : β ^ ℓ = algebraMap F K (algebraMap (𝓞 F) F ((d : 𝓞 F) ^ (ℓ - 1) * n)) := by
    have hℓ1 : ℓ = (ℓ - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne ℓ))).symm
    rw [mul_pow, rootKF_pow, ← map_pow, ← map_mul]
    congr 1
    rw [map_mul, map_pow, ← hnd]
    conv_lhs => rw [hℓ1, pow_succ]
    ring
  have hint : IsIntegral ℤ β := by
    apply IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow, ← IsScalarTower.algebraMap_apply]
    exact ((((d : 𝓞 F) ^ (ℓ - 1) * n).isIntegral_coe).map (IsScalarTower.toAlgHom ℤ F K))
  refine ⟨d, n, ⟨β, hint⟩, hd, hn, hnd, rfl, ?_⟩
  apply RingOfIntegers.ext
  simp only [map_pow]
  show β ^ ℓ = _
  rw [hβpow, ← IsScalarTower.algebraMap_apply]
  rfl

/-- A root of unity of `F` as an algebraic integer. -/
def rootO (μ : rootsOfUnity ℓ F) : 𝓞 F :=
  ⟨((μ : Fˣ) : F), IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by
    have := μ.2; rw [mem_rootsOfUnity] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]; exact isIntegral_one)⟩

omit [NumberField F] in
theorem rootO_pow (μ : rootsOfUnity ℓ F) : rootO F μ ^ ℓ = 1 := by
  apply RingOfIntegers.ext
  show ((μ : Fˣ) : F) ^ ℓ = 1
  have := μ.2; rw [mem_rootsOfUnity] at this
  rw [← Units.val_pow_eq_pow_val, this, Units.val_one]

include hζ in
/-- `σ β = μ_σ β` in `𝓞 K`. -/
theorem smul_intGen (a : Fˣ) (d : 𝓞 F) (β : 𝓞 (KF F ℓ a))
    (hβ : (β : KF F ℓ a) = algebraMap F (KF F ℓ a) (algebraMap (𝓞 F) F d) * (rootKF F a).β)
    (σ : KF F ℓ a ≃ₐ[F] KF F ℓ a) :
    σ • β = algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ)) * β := by
  apply RingOfIntegers.ext
  have e : ∀ x : 𝓞 F, ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x : 𝓞 (KF F ℓ a)) : KF F ℓ a) =
      algebraMap F (KF F ℓ a) (x : F) := fun x => rfl
  show σ (β : KF F ℓ a) = ((algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) _ : 𝓞 (KF F ℓ a)) : KF F ℓ a) *
    (β : KF F ℓ a)
  rw [e, hβ]
  show σ _ = algebraMap F (KF F ℓ a) ((kch hζ (rootKF F a) σ : Fˣ) : F) * _
  rw [algebraMap_kch, map_mul, AlgEquiv.commutes]
  field_simp [(rootKF (ℓ := ℓ) F a).ne_zero]

include hζ in
/-- **Kummer extensions are unramified** at `v ∤ ℓ` where `a` is a unit. -/
theorem inertia_eq_bot (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) (w : HeightOneSpectrum (𝓞 (KF F ℓ a)))
    (hw : w.under (𝓞 F) = v) :
    w.asIdeal.inertia (KF F ℓ a ≃ₐ[F] KF F ℓ a) = ⊥ := by
  obtain ⟨d, n, β, hd, hn, -, hβ, hβpow⟩ := exists_intGen (ℓ := ℓ) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ ℓ ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ))
    rw [hβpow] at this
    have h2 := hmem _ this
    rcases v.isPrime.mem_or_mem h2 with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have h1 := hσ β
  rw [smul_intGen F hζ a d β hβ σ] at h1
  have h2 : (algebraMap (𝓞 F) (𝓞 (KF F ℓ a)) (rootO F (kch hζ (rootKF F a) σ) - 1)) * β ∈
      w.asIdeal := by rw [map_sub, map_one, sub_mul, one_mul]; exact h1
  rcases w.isPrime.mem_or_mem h2 with h3 | h3
  · have h4 := hmem _ h3
    have h5 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F _) (one_pow ℓ) h4
    apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
    rw [map_one]
    apply Subtype.ext; apply Units.ext
    have := congrArg (fun z : 𝓞 F => (z : F)) h5
    exact this
  · exact absurd h3 hβw

include hζ in

/-- An algebraic integer from an element of `F` that is a root of unity. -/
def toO (x : F) (hx : x ^ ℓ = 1) : 𝓞 F :=
  ⟨x, IsIntegral.of_pow (Nat.pos_of_ne_zero (NeZero.ne ℓ)) (by rw [hx]; exact isIntegral_one)⟩

omit [NumberField F] in
theorem toO_pow (x : F) (hx : x ^ ℓ = 1) : toO F x hx ^ ℓ = 1 := by
  apply RingOfIntegers.ext; show x ^ ℓ = 1; exact hx

include hζ in
/-- `ℓ ∣ N v - 1` when `v ∤ ℓ`. -/
theorem dvd_card_sub_one (v : HeightOneSpectrum (𝓞 F)) (hv : (ℓ : 𝓞 F) ∉ v.asIdeal) :
    ℓ ∣ Nat.card (𝓞 F ⧸ v.asIdeal) - 1 := by
  classical
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  set z := toO F ζ hζ.pow_eq_one
  have hz : z ^ ℓ = 1 := toO_pow F ζ _
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal z) ℓ := by
    refine ⟨by rw [← map_pow, hz, map_one], fun l hl => ?_⟩
    have h1 : z ^ l - 1 ∈ v.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, hl, map_one, sub_self]
    have h2 := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv
      (by rw [← pow_mul, mul_comm, pow_mul, hz, one_pow]) (one_pow ℓ) h1
    apply hζ.dvd_of_pow_eq_one
    have := congrArg (fun x : 𝓞 F => (x : F)) h2
    simpa [z, toO] using this
  have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk v.asIdeal z)
    (hη.ne_zero (NeZero.ne ℓ))
  rw [Fintype.card_eq_nat_card] at this
  exact hη.dvd_of_pow_eq_one _ this


end UV

end ArtinPrimitiveRoots.L3K.KB

end
end
end

section
section
/-! # L3K_Kum: the sextic Kummer character `ψ_a` of `F(a^{1/6})/F`

For `a ∈ Fˣ`, `M = KF F 6 a` and `ψ_a = ι ∘ kch : Gal(M/F) →* ℂˣ` (C0Z):
* `psi_injective`; `psi_ne_one` when `a` is not a sixth power in `F`;
* `isUnramifiedAt_psi`: unramified at `v ∤ 6` with `v(a) = 0` (C0ZU);
* `psi_artinFrob`: there `ψ_a(Frob_v) = ι ω` for the sixth root of unity `ω ≡ a^{(Nv−1)/6}`;
* `not_isUnramifiedAt_psi`: ramified at `v` with `6 ∤ v(a)`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin Polynomial ArtinPrimitiveRoots.L3K.KB

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

/-- The Kummer field `F(a^{1/6})`. -/
abbrev KM := KF F 6 a

/-- `ψ_a(σ) = ι(σβ/β)`. -/
def psi : (KM F a ≃ₐ[F] KM F a) →* ℂˣ :=
  (Units.map ι.toMonoidHom).comp ((rootsOfUnity 6 F).subtype.comp (kch hζ (rootKF (ℓ := 6) F a)))

variable {F}

theorem psi_apply (σ : KM F a ≃ₐ[F] KM F a) :
    ((psi F hζ ι a σ : ℂˣ) : ℂ) = ι ((kch hζ (rootKF (ℓ := 6) F a) σ : Fˣ) : F) := rfl

theorem psi_injective : Function.Injective (psi F hζ ι a) := by
  intro σ τ h
  apply kch_KF_injective a hζ (rootKF F a) (rootKF_pow F a)
  apply Subtype.ext; apply Units.ext
  apply ι.injective
  have := congrArg (fun x : ℂˣ => (x : ℂ)) h
  simpa [psi_apply] using this

theorem psi_eq_one_iff_forall (σ : KM F a ≃ₐ[F] KM F a) : psi F hζ ι a σ = 1 ↔ σ = 1 :=
  ⟨fun h => psi_injective hζ ι a (h.trans (map_one _).symm), fun h => by rw [h, map_one]⟩

/-- The prime of `𝓞 M` over `v`, as a height-one prime. -/
def wAbove (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 (KM F a)) :=
  ⟨primeAbove F (KM F a) v, (primeAbove_isMaximal F (KM F a) v).isPrime,
    primeAbove_ne_bot F (KM F a) v⟩

theorem wAbove_under (v : HeightOneSpectrum (𝓞 F)) : (wAbove a v).under (𝓞 F) = v := by
  ext1; exact under_primeAbove F (KM F a) v

include hζ in
theorem inertiaGroup_eq_bot (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) : ArtinL.Abelian.inertiaGroup F (KM F a) v = ⊥ :=
  inertia_eq_bot F hζ v hv a ha (wAbove a v) (wAbove_under a v)

theorem isUnramifiedAt_psi (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) : ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v := by
  intro σ hσ
  rw [inertiaGroup_eq_bot hζ a v hv ha, Subgroup.mem_bot] at hσ
  rw [hσ, map_one]

include hζ in
/-- **Frobenius.** `kch(Frob_v) = ω` with `ω ≡ a^{(Nv−1)/6} (mod v)` (the argument of C0ZV). -/
theorem kch_artinFrob (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) (ω : F) (hω : ω ^ 6 = 1)
    (hcong : v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - ω) < 1) :
    ((kch hζ (rootKF (ℓ := 6) F a) (artinFrob F (KM F a) v) : Fˣ) : F) = ω := by
  classical
  set K := KM F a
  set Q := primeAbove F K v
  let w : HeightOneSpectrum (𝓞 K) := wAbove a v
  have hw : w.under (𝓞 F) = v := wAbove_under a v
  have hQv : Q.under (𝓞 F) = v.asIdeal := under_primeAbove F K v
  set φ := artinFrob F K v
  have hφ : IsArithFrobAt (𝓞 F) φ w.asIdeal := isArithFrobAt_artinFrob F K v
  have hv' : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal := hv
  -- the Kummer value of the Frobenius
  set μ := kch hζ (rootKF F a) φ
  obtain ⟨d, n, β, hd, hn, hnd, hβ, hβpow⟩ := exists_intGen (ℓ := 6) F v a ha
  have hmem : ∀ x : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) x ∈ w.asIdeal → x ∈ v.asIdeal := by
    intro x hx; rw [← hw]; exact hx
  have hβw : β ∉ w.asIdeal := by
    intro h
    have : β ^ 6 ∈ w.asIdeal := w.asIdeal.pow_mem_of_mem h 6 (Nat.pos_of_ne_zero (NeZero.ne 6))
    rw [hβpow] at this
    rcases v.isPrime.mem_or_mem (hmem _ this) with h3 | h3
    · exact hd (v.isPrime.mem_of_pow_mem _ h3)
    · exact hn h3
  set q := Nat.card (𝓞 F ⧸ v.asIdeal)
  have hq : q = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hFrob : ∀ x : 𝓞 K, φ • x - x ^ q ∈ w.asIdeal := by
    intro x
    have := hφ x
    rw [show w.asIdeal.under (𝓞 F) = v.asIdeal from hQv] at this
    exact this
  -- `6 ∣ q - 1`
  have h6q : 6 ∣ q - 1 := dvd_card_sub_one F hζ v hv
  obtain ⟨K', hK'⟩ := h6q
  have hq1 : q = 6 * K' + 1 := by
    have : 0 < q := by
      rw [hq]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    omega
  have hK'eq : (Ideal.absNorm v.asIdeal - 1) / 6 = K' := by
    rw [← hq, hK', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne 6))]
  rw [hK'eq] at hcong
  set μO := rootO F μ
  have hsm := smul_intGen F hζ a d β hβ φ
  have hfb := hFrob β
  rw [hsm, hq1, pow_succ, pow_mul, hβpow] at hfb
  have hfb' : algebraMap (𝓞 F) (𝓞 K) (μO - ((d ^ (6 - 1) * n) ^ K')) * β ∈ w.asIdeal := by
    rw [map_sub, map_pow, sub_mul]; convert hfb using 1
  have hμA : μO - (d ^ (6 - 1) * n) ^ K' ∈ v.asIdeal := by
    rcases w.isPrime.mem_or_mem hfb' with h | h
    · exact hmem _ h
    · exact absurd h hβw
  -- valuations in `F`
  set D : F := algebraMap (𝓞 F) F d
  set A : F := algebraMap (𝓞 F) F ((d ^ (6 - 1) * n) ^ K')
  have hDv : v.valuation F D = 1 := (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hA : A = D ^ (q - 1) * (a : F) ^ K' := by
    have h61 : 6 = (6 - 1) + 1 := (Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne 6))).symm
    simp only [A, map_pow, map_mul]
    rw [← hnd, hK']
    have e : D ^ (6 - 1) * ((a : F) * D) = (a : F) * D ^ 6 := by
      conv_rhs => rw [h61, pow_succ]
      ring
    rw [e, mul_pow, ← pow_mul, mul_comm]
  -- Fermat: `D^{q-1} ≡ 1`
  have hferm : v.valuation F (D ^ (q - 1) - 1) < 1 := by
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    have hmd : Ideal.Quotient.mk v.asIdeal d ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have := FiniteField.pow_card_sub_one_eq_one _ hmd
    rw [Fintype.card_eq_nat_card, ← map_pow, ← map_one (Ideal.Quotient.mk v.asIdeal),
      Ideal.Quotient.eq] at this
    have e : D ^ (q - 1) - 1 = algebraMap (𝓞 F) F (d ^ (q - 1) - 1) := by
      simp [D]
    rw [e]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr this
  set ωO := toO F ω hω
  have hωF : algebraMap (𝓞 F) F ωO = ω := rfl
  have hωv : v.valuation F ω ≤ 1 := by rw [← hωF]; exact v.valuation_le_one (K := F) ωO
  have hAω : v.valuation F (A - ω) < 1 := by
    rw [hA]
    have e : D ^ (q - 1) * (a : F) ^ K' - ω =
        D ^ (q - 1) * ((a : F) ^ K' - ω) + (D ^ (q - 1) - 1) * ω := by ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_pow, hDv, one_pow, one_mul]; exact hcong
    · rw [map_mul]
      calc _ ≤ v.valuation F (D ^ (q - 1) - 1) * 1 := mul_le_mul_right hωv _
        _ < 1 := by rw [mul_one]; exact hferm
  have hμv : v.valuation F (algebraMap (𝓞 F) F μO - A) < 1 := by
    have := (v.valuation_lt_one_iff_mem (K := F) _).mpr hμA
    change v.valuation F (algebraMap (𝓞 F) F (μO - _)) < 1 at this
    rwa [map_sub] at this
  have hμω : μO - ωO ∈ v.asIdeal := by
    rw [← v.valuation_lt_one_iff_mem (K := F)]
    change v.valuation F (algebraMap (𝓞 F) F (μO - ωO)) < 1
    rw [map_sub, hωF]
    have e : algebraMap (𝓞 F) F μO - ω = (algebraMap (𝓞 F) F μO - A) + (A - ω) := by ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hμv hAω)
  have heq := eq_of_pow_eq_one_of_sub_mem v.asIdeal hv (rootO_pow F μ) (toO_pow F ω hω) hμω
  have := congrArg (fun x : 𝓞 F => (x : F)) heq
  simpa [μO, rootO, ωO, toO] using this

theorem psi_artinFrob (v : HeightOneSpectrum (𝓞 F)) (hv : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (ha : v.valuation F (a : F) = 1) (ω : F) (hω : ω ^ 6 = 1)
    (hcong : v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - ω) < 1) :
    ((psi F hζ ι a (artinFrob F (KM F a) v) : ℂˣ) : ℂ) = ι ω := by
  rw [psi_apply, kch_artinFrob hζ a v hv ha ω hω hcong]

/-- **Ramified** at `v` when `6 ∤ v(a)`. -/
theorem not_isUnramifiedAt_psi (v : HeightOneSpectrum (𝓞 F))
    (ha : ∀ k : ℤ, v.valuation F (a : F) ≠ WithZero.exp (6 * k)) :
    ¬ ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι a) v := by
  intro hun
  set K := KM F a
  have hbot : ArtinL.Abelian.inertiaGroup F K v = ⊥ := by
    rw [eq_bot_iff]; intro σ hσ
    rw [Subgroup.mem_bot]; exact (psi_eq_one_iff_forall hζ ι a σ).1 (hun σ hσ)
  have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[F] K) v.asIdeal
    (primeAbove F K v)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal (primeAbove F K v) (K ≃ₐ[F] K)] at h1
  have hc : Nat.card ((primeAbove F K v).inertia (K ≃ₐ[F] K)) = 1 := by
    have : (primeAbove F K v).inertia (K ≃ₐ[F] K) = ⊥ := hbot
    rw [this]; simp
  rw [hc] at h1
  haveI : (wAbove a v).asIdeal.LiesOver v.asIdeal := primeAbove_liesOver F K v
  have he : v.asIdeal.ramificationIdx' (wAbove a v).asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
    exact h1.symm
  have hval := HeightOneSpectrum.valuation_liesOver K v (wAbove a v) (a : F)
  rw [he, pow_one] at hval
  have hβ : (rootKF (ℓ := 6) F a).β ≠ 0 := (rootKF (ℓ := 6) F a).ne_zero
  have hw0 : (wAbove a v).valuation K (rootKF (ℓ := 6) F a).β ≠ 0 := by
    simpa using hβ
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (wAbove a v).valuation K (rootKF (ℓ := 6) F a).β = WithZero.exp k :=
    ⟨_, (WithZero.exp_log hw0).symm⟩
  apply ha k
  rw [hval, ← rootKF_pow, map_pow, hk, ← WithZero.exp_nsmul]
  congr 1

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Wild: the conductor exponents of `ψ_a`

* `intValuation_smul_sub_le`: for `σ` in the `i`-th ramification group (`i ≥ 1`), i.e.
  `σ x ≡ x (mod 𝔓^{i+1})` for all `x`, one has `w(σx − x) ≤ w(x) e^{−i}` (uniformizer induction).
* `le_of_mem_ramificationGroup`: if moreover `ψ_a σ ≠ 1` then `i ≤ 6 n_v`, where `v(6) = e^{−n_v}`.
* `conductorExponent_psi_le`: `e_v(ψ_a) ≤ 1 + 6 n_v`; it is `0` where `ψ_a` is unramified and `≤ 1`
  at `v ∤ 6`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

section Generic

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {G : Type*} [Group G]
  [MulSemiringAction G R] (w : HeightOneSpectrum R)

end Generic

section Kummer

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

end Kummer

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Cond: `N 𝔣(ψ_a) ≤ N(D₆) · N(𝔟)`

`D₆ = ∏_{v ∣ 6} v^{1 + 6 n_v}` depends on `F` only; `𝔟` is any nonzero ideal contained in every
`v ∤ 6` at which `a` is not a unit. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

section Gen

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

end Gen

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  (a : Fˣ)

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Val: valuations of a generator `u` of `𝔲 R` at exterior primes

For `u ∈ R = SInt 𝔪` with `u R = 𝔲 R` and an exterior prime `v`: `v(u) = e^{−e}` where
`𝔲 ≤ v^e`, `𝔲 ≰ v^{e+1}`. Hence `v(u) = 1` if `v ∤ 𝔲`, and `v(u)` is not an even sixth power of
`e^{±1}` when `v ∣ 𝔲` and `𝔲` is sixth-power-free. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

lemma sInt_val_le_one' (s : SInt 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (s : F) ≤ 1 :=
  s.2 w hw

lemma coe_algebraMap_sInt' (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a := rfl

lemma val_algebraMap_le (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F} {e : ℕ} (hx : x ∈ v.asIdeal ^ e) :
    v.valuation F (algebraMap (𝓞 F) F x) ≤ exp (-(e : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem x e).2 hx

lemma val_le_of_le (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {e : ℕ}
    (he : 𝔲 ≤ v.asIdeal ^ e) : v.valuation F (u : F) ≤ exp (-(e : ℤ)) := by
  have hmem : u ∈ 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hu]; exact Ideal.mem_span_singleton_self u
  clear hu
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [coe_algebraMap_sInt']
    exact val_algebraMap_le v (he hy)
  | zero => simp
  | add x y _ _ hx hy =>
    have : ((x + y : SInt 𝔪) : F) = (x : F) + (y : F) := rfl
    rw [this]; exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul r x _ hx =>
    have : ((r • x : SInt 𝔪) : F) = (r : F) * (x : F) := rfl
    rw [this, map_mul]
    calc v.valuation F (r : F) * v.valuation F (x : F) ≤ 1 * exp (-(e : ℤ)) :=
          mul_le_mul' (sInt_val_le_one' r v hv) hx
      _ = _ := one_mul _

lemma lt_val_of_not_le (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {n : ℕ}
    (hn : ¬ 𝔲 ≤ v.asIdeal ^ n) : exp (-(n : ℤ)) < v.valuation F (u : F) := by
  obtain ⟨x, hx𝔲, hxn⟩ := SetLike.not_le_iff_exists.1 hn
  have hx : algebraMap (𝓞 F) (SInt 𝔪) x ∈ Ideal.span {u} := by
    rw [hu]; exact Ideal.mem_map_of_mem _ hx𝔲
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hx
  have h1 : exp (-(n : ℤ)) < v.valuation F (algebraMap (𝓞 F) F x) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    by_contra h; push Not at h
    exact hxn ((v.intValuation_le_pow_iff_mem x n).1 h)
  have h2 : algebraMap (𝓞 F) F x = (r : F) * (u : F) := by
    rw [← coe_algebraMap_sInt', ← hr]; rfl
  rw [h2, map_mul] at h1
  calc exp (-(n : ℤ)) < v.valuation F (r : F) * v.valuation F (u : F) := h1
    _ ≤ 1 * v.valuation F (u : F) := mul_le_mul' (sInt_val_le_one' r v hv) le_rfl
    _ = _ := one_mul _

/-- `v(u) = e^{−e}` when `𝔲 ≤ v^e` and `𝔲 ≰ v^{e+1}`. -/
lemma val_eq_exp (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) {e : ℕ}
    (he : 𝔲 ≤ v.asIdeal ^ e) (he1 : ¬ 𝔲 ≤ v.asIdeal ^ (e + 1)) :
    v.valuation F (u : F) = exp (-(e : ℤ)) := by
  have hle := val_le_of_le v hv hu he
  have hlt := lt_val_of_not_le v hv hu he1
  have hne : v.valuation F (u : F) ≠ 0 := ne_of_gt ((zero_lt_iff.2 (exp_ne_zero)).trans hlt)
  rw [← exp_log hne] at hle hlt ⊢
  rw [exp_le_exp] at hle
  rw [exp_lt_exp] at hlt
  congr 1
  push_cast at hlt
  omega

lemma val_eq_one (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    {u : SInt 𝔪} (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (h : ¬ 𝔲 ≤ v.asIdeal) : v.valuation F (u : F) = 1 := by
  have := val_eq_exp v hv hu (e := 0) (by simp) (by simpa using h)
  simpa using this

/-- At a prime dividing a sixth-power-free `𝔲`, `v(u)` is not `e^{6k}`. -/
lemma val_ne_exp_six (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) {𝔲 : Ideal (𝓞 F)}
    (h6 : IsSixthPowerFree 𝔲) {u : SInt 𝔪}
    (hu : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))) (h : 𝔲 ≤ v.asIdeal) :
    ∀ k : ℤ, v.valuation F (u : F) ≠ exp (6 * k) := by
  classical
  have hex : ∃ n, ¬ 𝔲 ≤ v.asIdeal ^ n := by
    refine ⟨6, fun hle => ?_⟩
    have := h6 v.asIdeal (Ideal.dvd_iff_le.2 hle)
    exact v.isPrime.ne_top (Ideal.isUnit_iff.1 this)
  set n₀ := Nat.find hex
  have hn₀ : ¬ 𝔲 ≤ v.asIdeal ^ n₀ := Nat.find_spec hex
  have hn₀6 : n₀ ≤ 6 := Nat.find_min' hex (fun hle => by
    have := h6 v.asIdeal (Ideal.dvd_iff_le.2 hle)
    exact v.isPrime.ne_top (Ideal.isUnit_iff.1 this))
  have hn₀2 : 2 ≤ n₀ := by
    by_contra hlt; push Not at hlt
    interval_cases hn : n₀
    · exact hn₀ (by simp)
    · exact hn₀ (by simpa using h)
  have he : 𝔲 ≤ v.asIdeal ^ (n₀ - 1) := by
    by_contra hc
    exact Nat.find_min hex (by omega : n₀ - 1 < n₀) hc
  have hval := val_eq_exp v hv hu he (by rwa [Nat.sub_add_cancel (by omega)])
  intro k hk
  rw [hval, exp_inj] at hk
  omega

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-!
# Transport of `AllowedGen` along a field isomorphism

Used to move from `F : Type u` to the universe-0 copy `CyclotomicField n ℚ`.
-/

namespace ArtinPrimitiveRoots

open NumberField IsDedekindDomain

namespace C0R

/-! ### Generic facts on ideals along a ring equivalence -/

section Ideals

variable {R S : Type*} [CommRing R] [CommRing S]

theorem mem_map_equiv (f : R ≃+* S) (I : Ideal R) (y : S) : y ∈ I.map f ↔ f.symm y ∈ I := by
  rw [Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨x, hx, hxy⟩ => by rw [← hxy, f.symm_apply_apply]; exact hx,
    fun h => ⟨_, h, f.apply_symm_apply y⟩⟩

theorem map_equiv_le_iff (f : R ≃+* S) {I J : Ideal R} : I.map f ≤ J.map f ↔ I ≤ J := by
  constructor
  · intro h x hx
    have : f x ∈ J.map f := h ((mem_map_equiv f I _).2 (by simpa using hx))
    simpa using (mem_map_equiv f J _).1 this
  · intro h y hy
    exact (mem_map_equiv f J y).2 (h ((mem_map_equiv f I y).1 hy))

theorem map_equiv_symm_map (f : R ≃+* S) (I : Ideal R) : (I.map f).map f.symm = I := by
  ext x
  rw [mem_map_equiv, RingEquiv.symm_symm, mem_map_equiv, RingEquiv.symm_apply_apply]

theorem map_equiv_coe (f : R ≃+* S) (I : Ideal R) : I.map (f : R →+* S) = I.map f := rfl

end Ideals

/-! ### The equivalences -/

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

omit [NumberField F] [NumberField F'] in
theorem mapRingEquiv_symm (e : F ≃+* F') :
    RingOfIntegers.mapRingEquiv e.symm = (RingOfIntegers.mapRingEquiv e).symm := by
  ext x; rfl

/-- `S`-integrality transports along `e`. -/
theorem mem_integer_map (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : F)
    (hx : x ∈ (placesOf 𝔪).integer F) :
    e x ∈ (placesOf (𝔪.map (RingOfIntegers.mapRingEquiv e))).integer F' := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro v' hv'
  let v : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := v'.asIdeal.comap (eO : 𝓞 F →+* 𝓞 F')
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := by
        intro h
        apply v'.ne_bot
        rw [← Ideal.map_comap_of_surjective (eO : 𝓞 F →+* 𝓞 F') eO.surjective v'.asIdeal, h,
          Ideal.map_bot] }
  have hv : v ∉ placesOf 𝔪 := by
    intro h
    apply hv'
    change 𝔪.map eO ≤ v'.asIdeal
    rw [← map_equiv_coe]
    exact Ideal.map_le_iff_le_comap.2 h
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v x (hx v hv)
  have hd : eO d ∉ v'.asIdeal := d.2
  have hnd' : e x * algebraMap (𝓞 F') F' (eO d) = algebraMap (𝓞 F') F' (eO n) := by
    have := congrArg e hnd
    rw [map_mul] at this
    exact this
  have h1 : v'.valuation F' (algebraMap (𝓞 F') F' (eO d)) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
    exact hd
  have h2 : v'.valuation F' (algebraMap (𝓞 F') F' (eO n)) ≤ 1 := v'.valuation_le_one _
  rw [← hnd', map_mul, h1, mul_one] at h2
  exact h2

/-- The ring `R = 𝓞_S` transports along `e`. -/
def sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) :
    SInt 𝔪 ≃+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)) where
  toFun x := ⟨e x, mem_integer_map e 𝔪 x x.2⟩
  invFun y := ⟨e.symm y, by
    have := mem_integer_map e.symm (𝔪.map (RingOfIntegers.mapRingEquiv e)) y y.2
    rwa [mapRingEquiv_symm, map_equiv_symm_map] at this⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  map_mul' x y := Subtype.ext (map_mul e _ _)
  map_add' x y := Subtype.ext (map_add e _ _)

@[simp] theorem sIntEquiv_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (x : SInt 𝔪) :
    ((sIntEquiv e 𝔪 x : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) : F') = e x := rfl

@[simp] theorem sIntEquiv_symm_coe (e : F ≃+* F') (𝔪 : Ideal (𝓞 F))
    (y : SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))) :
    (((sIntEquiv e 𝔪).symm y : SInt 𝔪) : F) = e.symm y := rfl

theorem map_map_sIntEquiv (e : F ≃+* F') (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    (I.map (algebraMap (𝓞 F) (SInt 𝔪))).map (sIntEquiv e 𝔪) =
      (I.map (RingOfIntegers.mapRingEquiv e)).map
        (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e)))) := by
  show Ideal.map ((sIntEquiv e 𝔪 : SInt 𝔪 →+* SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map (algebraMap (𝓞 F) (SInt 𝔪))) =
    Ideal.map (algebraMap (𝓞 F') (SInt (𝔪.map (RingOfIntegers.mapRingEquiv e))))
      (I.map ((RingOfIntegers.mapRingEquiv e : 𝓞 F →+* 𝓞 F')))
  rw [Ideal.map_map, Ideal.map_map]
  congr 1

theorem absNorm_map_equiv (e : F ≃+* F') (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (RingOfIntegers.mapRingEquiv e)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I _ (RingOfIntegers.mapRingEquiv e) rfl).toEquiv).symm

theorem isExterior_map (e : F ≃+* F') {𝔪 I : Ideal (𝓞 F)} (h : IsExterior 𝔪 I) :
    IsExterior (𝔪.map (RingOfIntegers.mapRingEquiv e)) (I.map (RingOfIntegers.mapRingEquiv e)) := by
  refine ⟨fun h0 => h.1 ?_, ?_⟩
  · exact (Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.mapRingEquiv e).injective).1 h0
  · rw [← Ideal.map_sup, h.2, Ideal.map_top]

/-! ### Uniqueness of the sixth root of unity modulo `P` -/

theorem eq_of_pow_six {R : Type*} [CommRing R] [IsDomain R] (Q : Ideal R) (h6 : (6 : R) ∉ Q)
    {a b : R} (ha : a ^ 6 = 1) (hb : b ^ 6 = 1) (hab : a - b ∈ Q) : a = b := by
  set η := b * a ^ 5 with hη
  have h1 : 1 - η ∈ Q := by
    have : 1 - η = a ^ 5 * (a - b) := by rw [hη]; linear_combination (-1 : R) * ha
    rw [this]; exact Q.mul_mem_left _ hab
  by_cases hη1 : η = 1
  · have : b = a := calc
        b = b * a ^ 6 := by rw [ha, mul_one]
        _ = (b * a ^ 5) * a := by ring
        _ = a := by rw [← hη, hη1, one_mul]
    exact this.symm
  · exfalso
    have hη6 : η ^ 6 = 1 := by
      rw [hη]
      calc (b * a ^ 5) ^ 6 = b ^ 6 * (a ^ 6) ^ 5 := by ring
        _ = 1 := by rw [ha, hb]; ring
    have hsum : 1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5 = 0 := by
      have : (η - 1) * (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) = 0 := by
        linear_combination hη6
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hη1
      · exact h
    apply h6
    have : (6 : R) = (1 - η) * (5 + 4 * η + 3 * η ^ 2 + 2 * η ^ 3 + η ^ 4) +
        (1 + η + η ^ 2 + η ^ 3 + η ^ 4 + η ^ 5) := by ring
    rw [this, hsum, add_zero]
    exact Q.mul_mem_right _ h1

/-! ### The residue symbol transports -/

theorem sexticResidueSymbol_transport (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 P : Ideal (𝓞 F))
    (h6 : P ⊔ Ideal.span {6} = ⊤) (x : SInt 𝔪) :
    sexticResidueSymbol (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))
        (P.map (RingOfIntegers.mapRingEquiv e)) (sIntEquiv e 𝔪 x) =
      sexticResidueSymbol ι 𝔪 P x := by
  classical
  set eO := RingOfIntegers.mapRingEquiv e
  set eS := sIntEquiv e 𝔪
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set f' := algebraMap (𝓞 F') (SInt (𝔪.map eO))
  set Q := P.map f
  have hQ' : (P.map eO).map f' = Q.map eS := (map_map_sIntEquiv e 𝔪 P).symm
  have hmem : ∀ y : SInt 𝔪, eS y ∈ (P.map eO).map f' ↔ y ∈ Q := fun y => by
    rw [hQ', mem_map_equiv, RingEquiv.symm_apply_apply]
  have hN : Ideal.absNorm (P.map eO) = Ideal.absNorm P := absNorm_map_equiv e P
  unfold sexticResidueSymbol
  simp only [Ideal.Quotient.eq_zero_iff_mem]
  by_cases hx : x ∈ Q
  · rw [if_pos hx, if_pos ((hmem x).2 hx)]
  rw [if_neg hx, if_neg (fun h => hx ((hmem x).1 h)), hN]
  set k := (Ideal.absNorm P - 1) / 6
  -- `6 ∉ Q`
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h6m
    apply hx
    have : Q = ⊤ := by
      rw [eq_top_iff, ← Ideal.map_top f, ← h6, Ideal.map_sup]
      refine sup_le le_rfl ?_
      rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.span_le,
        Set.singleton_subset_iff]
      exact h6m
    rw [this]; trivial
  have hC : ∀ ζ : 𝓞 F, (ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k) ↔
      ((eO ζ) ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' (eO ζ)) =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k) := by
    intro ζ
    apply and_congr
    · rw [← map_pow, ← map_one eO]
      exact eO.injective.eq_iff.symm
    · rw [← map_pow, ← map_pow, Ideal.Quotient.eq, Ideal.Quotient.eq, ← map_pow eS,
        show f' (eO ζ) = eS (f ζ) from rfl, ← map_sub, hmem]
  have huniq : ∀ ζ₁ ζ₂ : 𝓞 F, (ζ₁ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₁) = Ideal.Quotient.mk Q x ^ k) →
      (ζ₂ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ₂) = Ideal.Quotient.mk Q x ^ k) → ζ₁ = ζ₂ := by
    intro ζ₁ ζ₂ h1 h2
    have hsub : f ζ₁ - f ζ₂ ∈ Q := by
      rw [← Ideal.Quotient.eq, h1.2, h2.2]
    have := eq_of_pow_six Q h6Q (by rw [← map_pow, h1.1, map_one])
      (by rw [← map_pow, h2.1, map_one]) hsub
    have h' : ((f ζ₁ : SInt 𝔪) : F) = ((f ζ₂ : SInt 𝔪) : F) := by rw [this]
    exact RingOfIntegers.ext h'
  by_cases h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q x ^ k
  · have h' : ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k :=
      ⟨eO h.choose, (hC _).1 h.choose_spec⟩
    rw [dif_pos h, dif_pos h']
    have hspec : eO (eO.symm h'.choose) = h'.choose := eO.apply_symm_apply _
    have hC' := (hC (eO.symm h'.choose)).2 (by rw [hspec]; exact h'.choose_spec)
    have := huniq _ _ hC' h.choose_spec
    rw [← this]
    simp [eO]
  · have h' : ¬ ∃ ζ' : 𝓞 F', ζ' ^ 6 = 1 ∧ Ideal.Quotient.mk ((P.map eO).map f') (f' ζ') =
        Ideal.Quotient.mk ((P.map eO).map f') (eS x) ^ k := by
      rintro ⟨ζ', hζ'⟩
      apply h
      refine ⟨eO.symm ζ', (hC _).2 ?_⟩
      rw [eO.apply_symm_apply]; exact hζ'
    rw [dif_neg h, dif_neg h']

/-! ### `AllowedGen` transports -/

/-- `SmallPrimesDvd` transports. -/
theorem smallPrimesDvd_map (e : F ≃+* F') {N₀ : ℕ} {𝔪 : Ideal (𝓞 F)} (h : SmallPrimesDvd N₀ 𝔪) :
    SmallPrimesDvd N₀ (𝔪.map (RingOfIntegers.mapRingEquiv e)) := by
  set eO := RingOfIntegers.mapRingEquiv e
  intro P' hP' hP'0 hN
  set P := P'.map eO.symm
  have hPP : P.map eO = P' := by
    have := map_equiv_symm_map eO.symm P'
    rwa [RingEquiv.symm_symm] at this
  have hP : P.IsPrime := Ideal.map_isPrime_of_equiv eO.symm
  have hP0 : P ≠ ⊥ := fun h0 => hP'0 (by rw [← hPP, h0, Ideal.map_bot])
  have hNP : Ideal.absNorm P ≤ N₀ := by rw [← absNorm_map_equiv e P, hPP]; exact hN
  rw [← hPP]
  exact (map_equiv_le_iff eO).2 (h P hP hP0 hNP)

end C0R

end ArtinPrimitiveRoots

end
end

section
section
/-! C0Y: valuations of prime generators in `SInt 𝔪` and the sextic residue symbol. -/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace C0Y

variable {F : Type} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem sInt_val_le_one (s : SInt 𝔪) (w : HeightOneSpectrum (𝓞 F)) (hw : ¬ 𝔪 ≤ w.asIdeal) :
    w.valuation F (s : F) ≤ 1 :=
  s.2 w hw

theorem coe_algebraMap_sInt (a : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a := rfl

/-- Elements of `P · SInt` have `v_P < 1`. -/
theorem val_lt_one_of_mem_map (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    {z : SInt 𝔪} (hz : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (z : F) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_algebraMap_sInt]
    exact (v.valuation_lt_one_iff_mem (K := F) a).mpr ha
  | zero => simp
  | add x y _ _ hx hy =>
    simp only [Subalgebra.coe_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul a x _ hx =>
    simp only [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * v.valuation F (x : F) :=
          mul_le_mul_left (sInt_val_le_one a v hv) _
      _ < 1 := by rw [one_mul]; exact hx

/-- Valuations of a generator of `P · SInt`. -/
theorem val_generator (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (p : F) = WithZero.exp (-1 : ℤ) ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ w.asIdeal → w ≠ v → w.valuation F (p : F) = 1 := by
  have hpmem : p ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    rw [← hp]; exact Ideal.subset_span rfl
  have hlt := val_lt_one_of_mem_map v hv hpmem
  -- every `a ∈ P` is a multiple of `p` in `SInt`
  have hdiv : ∀ a ∈ v.asIdeal, ∃ s : SInt 𝔪, algebraMap (𝓞 F) F a = (p : F) * (s : F) := by
    intro a ha
    have : algebraMap (𝓞 F) (SInt 𝔪) a ∈ Ideal.span {p} := by
      rw [hp]; exact Ideal.mem_map_of_mem _ ha
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp this
    refine ⟨s, ?_⟩
    rw [← coe_algebraMap_sInt (𝔪 := 𝔪), ← hs, Subalgebra.coe_mul, mul_comm]
  refine ⟨?_, fun w hw hwv => ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer' F
    have hπmem : π ∈ v.asIdeal := by
      rw [← v.valuation_lt_one_iff_mem (K := F), hπ]; exact by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    obtain ⟨s, hs⟩ := hdiv π hπmem
    have h1 : v.valuation F (p : F) * v.valuation F (s : F) = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← hs, hπ]
    have hs1 := sInt_val_le_one s v hv
    have hp0 : v.valuation F (p : F) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h1; exact WithZero.exp_ne_zero h1.symm
    have hge : WithZero.exp (-1 : ℤ) ≤ v.valuation F (p : F) := by
      rw [← h1]; exact mul_le_of_le_one_right' hs1
    have hle : v.valuation F (p : F) ≤ WithZero.exp (-1 : ℤ) := by
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hp0
      rw [← hk] at hlt ⊢
      rw [show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp 0 from rfl] at hlt
      have : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [this, WithZero.exp_lt_exp] at hlt
      rw [this, WithZero.exp_le_exp]
      omega
    exact le_antisymm hle hge
  · -- `P ⊄ w`
    have hnle : ¬ v.asIdeal ≤ w.asIdeal := by
      intro hle
      have := v.isMaximal.eq_of_le w.isPrime.ne_top hle
      exact hwv (HeightOneSpectrum.ext this.symm)
    obtain ⟨a, ha, haw⟩ := Set.not_subset.mp hnle
    obtain ⟨s, hs⟩ := hdiv a ha
    have h1 : w.valuation F (p : F) * w.valuation F (s : F) = 1 := by
      rw [← map_mul, ← hs]; exact (w.valuation_eq_one_iff_notMem (K := F)).mpr haw
    have hp1 := sInt_val_le_one p w hw
    have hs1 := sInt_val_le_one s w hw
    by_contra hne
    have hlt : w.valuation F (p : F) < 1 := lt_of_le_of_ne hp1 hne
    have : w.valuation F (p : F) * w.valuation F (s : F) < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt hs1) le_rfl
    rw [h1] at this
    exact lt_irrefl _ this

/-- Elements of `SInt` with `v_P < 1` lie in `P · SInt` (given a generator). -/
theorem mem_map_of_val_lt_one (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal) (p : SInt 𝔪)
    (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) (z : SInt 𝔪)
    (hz : v.valuation F (z : F) < 1) : z ∈ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨hpv, hpw⟩ := val_generator v hv p hp
  have hp0 : (p : F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hpv; exact WithZero.exp_ne_zero hpv.symm
  have hq : (z : F) / (p : F) ∈ (placesOf 𝔪).integer F := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv
      rw [map_div₀, hpv]
      by_cases hz0 : w.valuation F (z : F) = 0
      · rw [hz0, zero_div]; exact zero_le
      obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp hz0
      rw [← hk] at hz ⊢
      have e : (k : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd k) := rfl
      rw [e, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hz
      rw [e, ← WithZero.exp_sub, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [map_div₀, hpw w hw hwv, div_one]
      exact sInt_val_le_one z w hw
  have : z = p * ⟨(z : F) / (p : F), hq⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]
    field_simp
  rw [← hp, this]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- The sextic residue symbol at an exterior prime with generator: `6 ∣ N P − 1`, and
`χ_P(y) = ι ξ` for the sixth root of unity `ξ ≡ y^{(N P − 1)/6} (mod P)`. -/
theorem sextic_spec (ι : F →+* ℂ) (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ 𝔪 ≤ v.asIdeal)
    (p : SInt 𝔪) (hp : Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (h6 : (6 : 𝓞 F) ∉ v.asIdeal) (y : SInt 𝔪)
    (hy : v.valuation F (y : F) = 1) :
    6 ∣ Ideal.absNorm v.asIdeal - 1 ∧ ∃ ξ : 𝓞 F, ξ ^ 6 = 1 ∧
      v.valuation F ((y : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - algebraMap (𝓞 F) F ξ) < 1 ∧
      sexticResidueSymbol ι 𝔪 v.asIdeal y = ι (algebraMap (𝓞 F) F ξ) := by
  classical
  set P := v.asIdeal with hPdef
  letI : Field (𝓞 F ⧸ P) := Ideal.Quotient.field P
  haveI : Finite (𝓞 F ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P v.ne_bot
  letI : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hinj : ∀ a b : 𝓞 F, a ^ 6 = 1 → b ^ 6 = 1 →
      Ideal.Quotient.mk P a = Ideal.Quotient.mk P b → a = b := fun a b ha hb h =>
    C0R.eq_of_pow_six P h6 ha hb (Ideal.Quotient.eq.mp h)
  have hη : IsPrimitiveRoot (Ideal.Quotient.mk P z6) 6 := by
    refine ⟨by rw [← map_pow, hz6.pow_eq_one, map_one], fun l hl => ?_⟩
    have : z6 ^ l = 1 := hinj _ _ (by rw [← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow])
      (one_pow 6) (by rw [map_pow, hl, map_one])
    exact hz6.dvd_of_pow_eq_one l this
  have h6N : 6 ∣ Ideal.absNorm P - 1 := by
    have := FiniteField.pow_card_sub_one_eq_one (Ideal.Quotient.mk P z6) (hη.ne_zero (by norm_num))
    rw [hcard] at this
    exact hη.dvd_of_pow_eq_one _ this
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v (y : F) hy.le
  have hd : (d : 𝓞 F) ∉ P := d.2
  have hdv : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F)).mpr hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    intro h0; rw [h0, map_zero] at hdv; exact zero_ne_one hdv
  have hn : (n : 𝓞 F) ∉ P := by
    rw [← v.valuation_eq_one_iff_notMem (K := F), ← hnd, map_mul, hy, hdv, one_mul]
  set k := (Ideal.absNorm P - 1) / 6 with hk
  set u : 𝓞 F ⧸ P := Ideal.Quotient.mk P n * (Ideal.Quotient.mk P d)⁻¹ with hu
  have hmd : Ideal.Quotient.mk P (d : 𝓞 F) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hmn : Ideal.Quotient.mk P n ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hu0 : u ≠ 0 := mul_ne_zero hmn (inv_ne_zero hmd)
  have hu6 : (u ^ k) ^ 6 = 1 := by
    rw [← pow_mul, hk, Nat.div_mul_cancel h6N, ← hcard]
    exact FiniteField.pow_card_sub_one_eq_one u hu0
  obtain ⟨i, -, hi⟩ := hη.eq_pow_of_pow_eq_one hu6
  set ξ := z6 ^ i with hξ
  have hξ6 : ξ ^ 6 = 1 := by rw [hξ, ← pow_mul, mul_comm, pow_mul, hz6.pow_eq_one, one_pow]
  have hcong : n ^ k - ξ * (d : 𝓞 F) ^ k ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, map_pow, map_pow, hi,
      hu, mul_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hmd), mul_one, sub_self]
  have hval : v.valuation F ((y : F) ^ k - algebraMap (𝓞 F) F ξ) < 1 := by
    have hyd : (y : F) = algebraMap (𝓞 F) F n / algebraMap (𝓞 F) F d := by
      rw [← hnd, mul_div_cancel_right₀ _ hdF]
    have : (y : F) ^ k - algebraMap (𝓞 F) F ξ =
        algebraMap (𝓞 F) F (n ^ k - ξ * (d : 𝓞 F) ^ k) / (algebraMap (𝓞 F) F d) ^ k := by
      rw [hyd, eq_div_iff (pow_ne_zero _ hdF)]
      simp only [map_sub, map_mul, map_pow]
      rw [sub_mul, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hdF)]
    rw [this, map_div₀, map_pow, hdv, one_pow, div_one]
    exact (v.valuation_lt_one_iff_mem (K := F) _).mpr hcong
  refine ⟨h6N, ξ, hξ6, hval, ?_⟩
  set f := algebraMap (𝓞 F) (SInt 𝔪)
  set Q := P.map f
  have hyQ : y ∉ Q := fun h => by
    have := val_lt_one_of_mem_map v hv h; rw [hy] at this; exact lt_irrefl _ this
  have h6Q : (6 : SInt 𝔪) ∉ Q := by
    intro h
    have := val_lt_one_of_mem_map v hv h
    have e : ((6 : SInt 𝔪) : F) = algebraMap (𝓞 F) F 6 := by rw [map_ofNat]; rfl
    rw [e, (v.valuation_eq_one_iff_notMem (K := F)).mpr h6] at this
    exact lt_irrefl _ this
  have hex : f ξ - y ^ k ∈ Q := by
    apply mem_map_of_val_lt_one v hv p hp
    have e : ((f ξ - y ^ k : SInt 𝔪) : F) = -((y : F) ^ k - algebraMap (𝓞 F) F ξ) := by
      simp [f, coe_algebraMap_sInt]
    rw [e, Valuation.map_neg]; exact hval
  unfold sexticResidueSymbol
  rw [if_neg (by rwa [Ideal.Quotient.eq_zero_iff_mem])]
  have hE : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧ Ideal.Quotient.mk Q (f ζ) = Ideal.Quotient.mk Q y ^ k :=
    ⟨ξ, hξ6, by rw [← map_pow, Ideal.Quotient.eq]; exact hex⟩
  rw [dif_pos hE]
  have hch := hE.choose_spec
  have hsub : f hE.choose - f ξ ∈ Q := by
    rw [← Ideal.Quotient.eq, hch.2, ← map_pow, Ideal.Quotient.eq]
    have : y ^ k - f ξ = -(f ξ - y ^ k) := by ring
    rw [this]; exact Q.neg_mem hex
  have heq := C0R.eq_of_pow_six Q h6Q (by rw [← map_pow, hch.1, map_one])
    (by rw [← map_pow, hξ6, map_one]) hsub
  have : hE.choose = ξ := by
    have h' := congrArg (fun z : SInt 𝔪 => (z : F)) heq
    simp only [f, coe_algebraMap_sInt] at h'
    exact FaithfulSMul.algebraMap_injective (𝓞 F) F h'
  rw [this]

end C0Y

end
end
end

section
section
/-! # L3K_Bridge: `kummerL` is `L(s, ψ_u)` up to finitely many Euler factors at `S`

Setting (universe 0): `ζ` a primitive sixth root of unity in `F`, every prime containing `6`
contains `𝔪`, every exterior prime is principal in `R`, `u R = 𝔲 R` with `𝔲` exterior and
sixth-power-free, `u` not a sixth power. With `ψ = ψ_u`:
* exterior `v`: `localValue ψ v = χ_v(u)` (`v ∤ 𝔲`, unramified) and `ψ` is ramified at `v ∣ 𝔲`;
* `kummerL u = L(ψ) · ∏_{P ⊇ 𝔣𝔪, P + 𝔣 = 1} (1 − ψ(P) N P^{-s})` on `Re s > 1`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinPrimitiveRoots.L3K.KB UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type} [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6) (ι : F →+* ℂ)
  {𝔪 : Ideal (𝓞 F)}

/-- The data of the bridge. -/
structure BridgeHyp (𝔪 : Ideal (𝓞 F)) (u : SInt 𝔪) (𝔲 : Ideal (𝓞 F)) : Prop where
  ne_bot : 𝔪 ≠ ⊥
  six : ∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal
  prin : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal →
    ∃ p : SInt 𝔪, Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))
  gen : Ideal.span {u} = 𝔲.map (algebraMap (𝓞 F) (SInt 𝔪))
  sfree : IsSixthPowerFree 𝔲
  nonsix : ∀ b : F, b ^ 6 ≠ (u : F)

variable {u : SInt 𝔪} {𝔲 : Ideal (𝓞 F)}

lemma BridgeHyp.ne_zero (h : BridgeHyp 𝔪 u 𝔲) : (u : F) ≠ 0 := fun h0 =>
  h.nonsix 0 (by rw [h0]; ring)

/-- `u` as a unit of `F`. -/
def uUnit (h : BridgeHyp 𝔪 u 𝔲) : Fˣ := Units.mk0 (u : F) h.ne_zero

/-- `ζ` as an algebraic integer. -/
def z6 : 𝓞 F := ⟨ζ, IsIntegral.of_pow (by norm_num : 0 < 6) (by rw [hζ.pow_eq_one]; exact isIntegral_one)⟩

lemma z6_prim : IsPrimitiveRoot (z6 hζ) 6 :=
  (IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) (by
    show IsPrimitiveRoot ζ 6; exact hζ) (FaithfulSMul.algebraMap_injective _ _))

lemma six_not_mem (h : BridgeHyp 𝔪 u 𝔲) {v : HeightOneSpectrum (𝓞 F)} (hv : ¬ 𝔪 ≤ v.asIdeal) :
    (6 : 𝓞 F) ∉ v.asIdeal := fun h6 => hv (h.six v h6)

/-- **Exterior primes away from `𝔲`.** -/
theorem localValue_eq_sextic (h : BridgeHyp 𝔪 u 𝔲) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ 𝔪 ≤ v.asIdeal) (hv𝔲 : ¬ 𝔲 ≤ v.asIdeal) :
    ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι (uUnit h)) v ∧
      ArtinL.Abelian.localValue (psi F hζ ι (uUnit h)) v = sexticResidueSymbol ι 𝔪 v.asIdeal u := by
  have hval : v.valuation F ((uUnit h : Fˣ) : F) = 1 := val_eq_one v hv h.gen hv𝔲
  have h6 := six_not_mem h hv
  have h6' : ((6 : ℕ) : 𝓞 F) ∉ v.asIdeal := by exact_mod_cast h6
  have hun := isUnramifiedAt_psi hζ ι (uUnit h) v h6' hval
  obtain ⟨p, hp⟩ := h.prin v hv
  obtain ⟨-, ξ, hξ6, hcong, hsx⟩ := C0Y.sextic_spec ι v hv p hp (z6_prim hζ) h6 u hval
  refine ⟨hun, ?_⟩
  rw [ArtinL.Abelian.localValue, if_pos hun, hsx,
    psi_artinFrob hζ ι (uUnit h) v h6' hval (algebraMap (𝓞 F) F ξ) (by rw [← map_pow, hξ6, map_one])
      hcong]

/-- **Primes dividing `𝔲` are ramified**, and there `χ_v(u) = 0`. -/
theorem ramified_of_le (h : BridgeHyp 𝔪 u 𝔲) {v : HeightOneSpectrum (𝓞 F)}
    (hv : ¬ 𝔪 ≤ v.asIdeal) (hv𝔲 : 𝔲 ≤ v.asIdeal) :
    ¬ ArtinL.Abelian.IsUnramifiedAt (psi F hζ ι (uUnit h)) v ∧
      sexticResidueSymbol ι 𝔪 v.asIdeal u = 0 := by
  refine ⟨not_isUnramifiedAt_psi hζ ι (uUnit h) v (val_ne_exp_six v hv h.sfree h.gen hv𝔲), ?_⟩
  obtain ⟨p, hp⟩ := h.prin v hv
  have hlt : v.valuation F (u : F) < 1 := by
    have := val_le_of_le v hv h.gen (e := 1) (by simpa using hv𝔲)
    refine this.trans_lt ?_
    rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)
  have hmem := C0Y.mem_map_of_val_lt_one v hv p hp u hlt
  unfold sexticResidueSymbol
  rw [if_pos (Ideal.Quotient.eq_zero_iff_mem.2 hmem)]

lemma residueSymbol_mul' (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma residueSymbol_prime' {P : Ideal (𝓞 F)} (hP : Irreducible P) (x : SInt 𝔪) :
    residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  unfold residueSymbol
  rw [normalizedFactors_irreducible hP, normalize_eq]; simp

lemma residueSymbol_top' (x : SInt 𝔪) : residueSymbol ι 𝔪 ⊤ x = 1 := by
  unfold residueSymbol
  rw [← Ideal.one_eq_top, normalizedFactors_one]; simp

open Classical in
/-- `g(I) = χ_I(u)` on exterior `I`, `0` elsewhere. -/
def gK (𝔪 : Ideal (𝓞 F)) (u : SInt 𝔪) (I : Ideal (𝓞 F)) : ℂ :=
  if IsExterior 𝔪 I then residueSymbol ι 𝔪 I u else 0

lemma isExterior_mul_iff {I J : Ideal (𝓞 F)} :
    IsExterior 𝔪 (I * J) ↔ IsExterior 𝔪 I ∧ IsExterior 𝔪 J := by
  unfold IsExterior
  have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
    simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
  rw [hb, C3A.sup_mul_eq_top_iff]; tauto

lemma gK_mul (I J : Ideal (𝓞 F)) : gK ι 𝔪 u (I * J) = gK ι 𝔪 u I * gK ι 𝔪 u J := by
  classical
  unfold gK
  by_cases hI : IsExterior 𝔪 I <;> by_cases hJ : IsExterior 𝔪 J
  · rw [if_pos (isExterior_mul_iff.2 ⟨hI, hJ⟩), if_pos hI, if_pos hJ,
      residueSymbol_mul' ι I J hI.1 hJ.1]
  · rw [if_neg (fun h => hJ (isExterior_mul_iff.1 h).2), if_neg hJ, mul_zero]
  · rw [if_neg (fun h => hI (isExterior_mul_iff.1 h).1), if_neg hI, zero_mul]
  · rw [if_neg (fun h => hI (isExterior_mul_iff.1 h).1), if_neg hI, zero_mul]

lemma sup_mul_top {P I J : Ideal (𝓞 F)} : P ⊔ I * J = ⊤ ↔ P ⊔ I = ⊤ ∧ P ⊔ J = ⊤ := by
  rw [sup_comm, C3A.sup_mul_eq_top_iff, sup_comm I, sup_comm J]

variable (hK : ∀ w : InfinitePlace F, w.IsComplex)

/-- The Hecke character `χ'` of modulus `𝔣 𝔪` given by 019ae22c from `psiH`. -/
lemma exists_chi' (h : BridgeHyp 𝔪 u 𝔲) :
    ∃ χ' : HeckeChar F (ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) * 𝔪),
      (∀ I, χ'.toFun I = gK ι 𝔪 u I) ∧
      ∀ s : ℂ, 1 < s.re → (psiH (psi F hζ ι (uUnit h)) hK).LSeries s = χ'.LSeries s *
        ∏ᶠ (P : Ideal (𝓞 F)) (_ : P.IsPrime ∧ P ≠ ⊥ ∧
            ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) * 𝔪 ≤ P ∧
            P ⊔ ArtinL.Abelian.conductor (psi F hζ ι (uUnit h)) = ⊤),
          (1 - (psiH (psi F hζ ι (uUnit h)) hK).toFun P * (Ideal.absNorm P : ℂ) ^ (-s))⁻¹ := by
  classical
  set ψ := psi F hζ ι (uUnit h)
  set 𝔣 := ArtinL.Abelian.conductor ψ
  obtain ⟨-, -, -, χ', hagree, hL⟩ := heckeLSeries_euler_package_of_le F 𝔣 (𝔣 * 𝔪)
    (mul_ne_zero (ArtinL.Abelian.conductor_ne_bot ψ) h.ne_bot) Ideal.mul_le_left (psiH ψ hK)
  refine ⟨χ', ?_, hL⟩
  have hext : ∀ v : HeightOneSpectrum (𝓞 F), IsExterior 𝔪 v.asIdeal ↔ ¬ 𝔪 ≤ v.asIdeal := by
    intro v
    rw [IsExterior, sup_eq_top_iff_not_dvd, Ideal.dvd_iff_le]
    exact ⟨fun h => h.2, fun h => ⟨v.ne_bot, h⟩⟩
  have hprime : ∀ v : HeightOneSpectrum (𝓞 F), χ'.toFun v.asIdeal = gK ι 𝔪 u v.asIdeal := by
    intro v
    have hirr : Irreducible v.asIdeal := v.irreducible
    by_cases hA : v.asIdeal ⊔ 𝔣 * 𝔪 = ⊤
    · rw [hagree _ hA, psiH_prime]
      obtain ⟨h𝔣, hm⟩ := sup_mul_top.1 hA
      have hvm : ¬ 𝔪 ≤ v.asIdeal := (hext v).1 ⟨v.ne_bot, hm⟩
      have hun : ArtinL.Abelian.IsUnramifiedAt ψ v := by
        by_contra hc
        exact (sup_eq_top_iff_not_dvd v 𝔣).1 h𝔣
          ((ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt F _ ψ v).2 hc)
      have hv𝔲 : ¬ 𝔲 ≤ v.asIdeal := fun hle => (ramified_of_le hζ ι h hvm hle).1 hun
      rw [(localValue_eq_sextic hζ ι h hvm hv𝔲).2, gK, if_pos ((hext v).2 hvm),
        residueSymbol_prime' ι hirr]
    · rw [(χ'.eq_zero_iff' _).2 (Or.inr hA), gK]
      split_ifs with he
      · have hvm : ¬ 𝔪 ≤ v.asIdeal := (hext v).1 he
        have h𝔣 : ¬ v.asIdeal ⊔ 𝔣 = ⊤ := fun h𝔣 => hA (sup_mul_top.2 ⟨h𝔣, he.2⟩)
        have hram : ¬ ArtinL.Abelian.IsUnramifiedAt ψ v :=
          (ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt F _ ψ v).1
            (by by_contra hc; exact h𝔣 ((sup_eq_top_iff_not_dvd v 𝔣).2 hc))
        have hv𝔲 : 𝔲 ≤ v.asIdeal := by
          by_contra hc; exact hram (localValue_eq_sextic hζ ι h hvm hc).1
        rw [residueSymbol_prime' ι hirr, (ramified_of_le hζ ι h hvm hv𝔲).2]
      · rfl
  intro I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Ideal.zero_eq_bot, T12B.toFun_bot, gK, if_neg (fun h => h.1 rfl)]
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.1 hx, T12B.toFun_top, gK, if_pos ⟨top_ne_bot, top_sup_eq _⟩,
      residueSymbol_top']
  | h₃ a p ha hp ih =>
    rw [χ'.map_mul', gK_mul, ih]
    congr 1
    exact hprime (HeightOneSpectrum.ofPrime hp)

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Core: (8.14) for a number field in `Type`

For `F : Type` totally complex with a primitive sixth root of unity: for every `u ∈ R` with
`u R = 𝔲 R`, `𝔲` sixth-power-free and `u ∉ F^{×6}`, `kummerL u` continues to an entire `Λ` with
`‖Λ(w)‖ ≤ C (N𝔲)^{1/2+ε} (2 + |Im w|)^{3 r₂}` on `.003 ≤ Re w ≤ 4`. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain ArtinPrimitiveRoots.L3K.KB

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3K_Freq: a nonprincipal frequency element is not a sixth power

* `span_freqElt`: `u R = 𝔲 R` for `u = freqElt g r`, `𝔲 = r.1.1`;
* `freqElt_ne_pow_six`: for `r ≠ principalFreq`, `u ∉ F^{×6}` (`𝔲 ≠ ⊤`: an exterior valuation of `u`
  lies in `1..5`; `𝔲 = ⊤`: `u = rep(ε) gen ⊤` with `gen ⊤ ∈ U_S^6` and `ε ≠ 1`). -/

set_option autoImplicit false

open NumberField IsDedekindDomain WithZero

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # T12A_Prin: removing Euler factors from `ζ_K`

For a finite set `T` of primes and `Re s > 1`,
`∑_{I coprime to T} N(I)^{-s} = ∏_{v ∈ T} (1 - N(v)^{-s}) · ζ_K(s)`. -/

set_option maxHeartbeats 4000000
set_option autoImplicit false

open NumberField Complex Ideal IsDedekindDomain

namespace ArtinPrimitiveRoots.T12A

variable {K : Type*} [Field K] [NumberField K]

end ArtinPrimitiveRoots.T12A

end
end

section
section
/-! # T12A_Main: continuation of `HeckeChar.LSeries` (cut T1)

* nontrivial ray class character: entire, by 17728196 (`IsParity` with `S = ∅`);
* trivial: `L(s, χ) = ∏_{v ∣ 𝔪} (1 - N v^{-s}) · ζ_K(s)`, continued by 8087d96f;
* a field in an arbitrary universe is moved to `Type` along a ring isomorphism. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply Complex

namespace ArtinPrimitiveRoots

namespace T12A

section Principal

variable {K : Type} [Field K] [NumberField K] {𝔪 : Ideal (𝓞 K)}

end Principal

section Transport


theorem exists_small_model (F : Type u) [Field F] [NumberField F] :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : NumberField F₀), Nonempty (F₀ ≃+* F) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ F
  have hint : IsIntegral ℚ α := Algebra.IsIntegral.isIntegral α
  haveI : Fact (Irreducible (minpoly ℚ α)) := ⟨minpoly.irreducible hint⟩
  let e : AdjoinRoot (minpoly ℚ α) ≃ₐ[ℚ] F :=
    (IntermediateField.adjoinRootEquivAdjoin ℚ hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  haveI : FiniteDimensional ℚ (AdjoinRoot (minpoly ℚ α)) :=
    LinearEquiv.finiteDimensional e.toLinearEquiv.symm
  haveI : NumberField (AdjoinRoot (minpoly ℚ α)) := { }
  exact ⟨_, inferInstance, inferInstance, ⟨e.toRingEquiv⟩⟩

end Transport

end T12A

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3K_Main: KummerConvexity (8.14), statement verbatim, for `F : Type*`

Transport of `L3K.core` from a universe-0 model `F₀ ≃+* F` (T12A `exists_small_model`, C0R
transport lemmas). This module does not import the target's stub. -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3K

/-- A number field with a primitive sixth root of unity is totally complex. -/
lemma isComplex_of_prim6 (K : Type*) [Field K] [NumberField K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ 6) (w : InfinitePlace K) : w.IsComplex := by
  rw [← not_isReal_iff_isComplex]
  intro hw
  have h := hζ.map_of_injective (embedding_of_isReal hw).injective
  have h6 : ((embedding_of_isReal hw) ζ) ^ 6 = 1 := h.pow_eq_one
  have h2 : ((embedding_of_isReal hw) ζ) ^ 2 = 1 := by
    have : (((embedding_of_isReal hw) ζ) ^ 2) ^ 3 = 1 := by rw [← pow_mul]; exact h6
    exact (pow_eq_one_iff_of_nonneg (sq_nonneg _) (by norm_num)).1 this
  have := h.dvd_of_pow_eq_one 2 h2
  omega

variable {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']

lemma rsMul (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (I J : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (x : SInt 𝔪) :
    residueSymbol ι 𝔪 (I * J) x = residueSymbol ι 𝔪 I x * residueSymbol ι 𝔪 J x := by
  unfold residueSymbol
  rw [normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

lemma rsPrime (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} {P : Ideal (𝓞 F)} (hP : Irreducible P)
    (x : SInt 𝔪) : residueSymbol ι 𝔪 P x = sexticResidueSymbol ι 𝔪 P x := by
  unfold residueSymbol
  rw [normalizedFactors_irreducible hP, normalize_eq]; simp

lemma rsTop (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (x : SInt 𝔪) : residueSymbol ι 𝔪 ⊤ x = 1 := by
  unfold residueSymbol
  rw [← Ideal.one_eq_top, normalizedFactors_one]; simp

lemma extMul {𝔪 I J : Ideal (𝓞 F)} :
    IsExterior 𝔪 (I * J) ↔ IsExterior 𝔪 I ∧ IsExterior 𝔪 J := by
  unfold IsExterior
  have hb : I * J ≠ ⊥ ↔ I ≠ ⊥ ∧ J ≠ ⊥ := by
    simp only [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
  rw [hb, C3A.sup_mul_eq_top_iff]; tauto

/-- Residue symbols of exterior ideals transport. -/
lemma residueSymbol_transport (e : F ≃+* F') (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤)
    (x : SInt 𝔪) (I : Ideal (𝓞 F)) (hI : IsExterior 𝔪 I) :
    residueSymbol (ι.comp (e.symm : F' →+* F)) (𝔪.map (RingOfIntegers.mapRingEquiv e))
        (I.map (RingOfIntegers.mapRingEquiv e)) (C0R.sIntEquiv e 𝔪 x) =
      residueSymbol ι 𝔪 I x := by
  set eO := RingOfIntegers.mapRingEquiv e
  revert hI
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro hI; exact absurd rfl hI.1
  | h₂ y hy =>
    intro _
    rw [Ideal.isUnit_iff.1 hy, Ideal.map_top, rsTop, rsTop]
  | h₃ a p ha hp ih =>
    intro hI
    obtain ⟨hpE, haE⟩ := extMul.1 hI
    have hpm : (p.map eO) ≠ ⊥ := fun h0 =>
      hpE.1 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
    have ham : (a.map eO) ≠ ⊥ := fun h0 =>
      haE.1 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
    have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hpE.1).1 hp
    have hpmP : (p.map eO).IsPrime := Ideal.map_isPrime_of_equiv eO
    rw [Ideal.map_mul, rsMul _ _ _ hpm ham, rsMul _ _ _ hpE.1 haE.1,
      ih haE, rsPrime _ ((Ideal.prime_iff_isPrime hpm).2 hpmP).irreducible,
      rsPrime _ hp.irreducible,
      C0R.sexticResidueSymbol_transport e ι 𝔪 p (h6 p hpP hpE)]

end L3K

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # C3B_Norm: the additive character on `R`, the unit ideal, and `a(1,1,1,1) = 1` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Unit: `U_S⁶`-invariance of `poissonFactor`, and `u = 1` for the principal class

* `exists_sub_mem_map`: `𝓞/P → R/PR` is onto for `P ∉ S`; hence Fermat in `R/PR`.
* `sexticResidueSymbol_unit_pow_six`: `χ_P(μ⁶ x) = χ_P(x)` when `6 ∣ N P − 1`.
* `poissonFactor_unit_pow_six`: `F(𝔰, 𝔄, μ⁶ h) = F(𝔰, 𝔄, h)` for exterior `𝔰, 𝔄` whose prime
  factors all have `6 ∣ N P − 1`.
* `freqElt_principalFreq`: the principal frequency element is `μ⁶` for an `S`-unit `μ`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

section residue

variable {𝔪 : Ideal (𝓞 F)}

lemma coe_algebraMap_SInt (x : 𝓞 F) :
    ((algebraMap (𝓞 F) (SInt 𝔪) x : SInt 𝔪) : F) = (x : F) := rfl

lemma card_quot (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥) [Fintype (𝓞 F ⧸ P)] :
    Fintype.card (𝓞 F ⧸ P) = Ideal.absNorm P := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end residue

section gen

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end gen

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Good: exterior primes satisfy `6 ∣ N P − 1` once `S` contains the primes above `2, 3` -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-- A prime of norm divisible by the rational prime `p` has norm at most `p^[F:ℚ]`. -/
theorem absNorm_le_of_prime_dvd (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 F)) (hP0 : P ≠ ⊥)
    [P.IsMaximal] (hpd : p ∣ Ideal.absNorm P) :
    Ideal.absNorm P ≤ p ^ Module.finrank ℤ (𝓞 F) := by
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  have hcard := card_quot P hP0
  obtain ⟨f, hq, hpf⟩ := FiniteField.card (𝓞 F ⧸ P) (ringChar (𝓞 F ⧸ P))
  rw [hcard] at hpf
  rw [hpf] at hpd
  have hpq : p = ringChar (𝓞 F ⧸ P) :=
    (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpd)
  have hp0 : ((p : ℕ) : 𝓞 F ⧸ P) = 0 := by rw [hpq]; exact ringChar.Nat.cast_ringChar
  have hmem : (p : 𝓞 F) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  have hle : Ideal.span {(p : 𝓞 F)} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hmem
  have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_singleton] at hdvd
  have hn : Algebra.norm ℤ (p : 𝓞 F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 F) := by
    rw [show (p : 𝓞 F) = algebraMap ℤ (𝓞 F) p by simp, Algebra.norm_algebraMap]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  exact Nat.le_of_dvd (pow_pos hp.pos _) hdvd

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3B_Main: (7.16)–(7.17) at `u = 1` from four arithmetic cuts

With `b(𝔠, 𝔫, 𝔰, 𝔯) = γ₂(𝔠) ϑ(𝔠𝔫³) F(𝔰, 𝔠𝔫³, gen(𝔯)⁶)` (the coefficient at `u = 1`, without the
`S`-unit `u`), the target `exists_cutoff_freqCoeff_principalFreq_eq_one_and_eq_mul` follows from

* `CutMul`: cross-prime multiplicativity `b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀},P^l,P^k,P^m) b(𝔠,𝔫,𝔰,𝔯)`
  ((7.14), (7.16): Chinese remainders + reciprocity (3.3));
* `CutF`: the local Poisson factor `F(P^k, P^{e₀}(P^l)³, gen(P^m)⁶)` ((7.15), (7.17));
* `CutHD`: `γ₁(P) γ₂(P) Λ̄(P) Ḡ(P) = −1` (Davenport–Hasse, (3.9)–(3.11));
* `CutG6`: `Ḡ(P)⁶ = 1`.

Proved here: `a(1,1,1,1) = 1` (`C3B_Norm`), the `U_S⁶`-invariance replacing `u` by `1`
(`C3B_Unit`, `C3B_Good`), `ϑ` on prime powers, `Λ⁶ = jacobiPhaseSix`, and the table algebra. -/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3B

variable {F : Type*} [Field F] [NumberField F]

/-! ### Elementary lemmas -/

end C3B

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Res: the residue rings `R / P^j R` at a prime `P ∉ S`

For a height-one prime `v` of `𝓞 F` outside `S = placesOf 𝔪`:
* `mem_map_pow_iff`: `r ∈ v^j R ↔ v(r) ≤ exp(-j)` for `r ∈ R`;
* `quotEquiv`: `𝓞/v^j ≃+* R/v^j R`; `natCard_quot`: `#(R/v^j R) = N(v)^j`;
* `isMaximal_map`: `v R` is maximal;
* `finsum_quot_fibre`: summing a function that only depends on the class mod `v^i R`
  over `R/v^j R` (`i ≤ j`) gives `N(v)^(j-i)` times the sum over `R/v^i R`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

section val

variable {v : HeightOneSpectrum (𝓞 F)}

lemma coe_alg (a : 𝓞 F) : ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) = algebraMap (𝓞 F) F a :=
  rfl

lemma val_le_one (hv : v ∉ placesOf 𝔪) (r : SInt 𝔪) : v.valuation F (r : F) ≤ 1 := r.2 v hv

lemma val_alg (a : 𝓞 F) : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a :=
  v.valuation_of_algebraMap a

/-- Elements of `v^j R` have valuation at most `exp(-j)`. -/
lemma val_le_of_mem (hv : v ∉ placesOf 𝔪) (j : ℕ) {r : SInt 𝔪}
    (hr : r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) :
    v.valuation F (r : F) ≤ exp (-(j : ℤ)) := by
  rw [Ideal.map] at hr
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [coe_alg, val_alg]
    exact (v.intValuation_le_pow_iff_mem a j).2 ha
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subalgebra.coe_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, Subalgebra.coe_mul, map_mul]
    calc v.valuation F (a : F) * v.valuation F (x : F) ≤ 1 * exp (-(j : ℤ)) :=
          mul_le_mul' (val_le_one hv a) hx
      _ = _ := one_mul _

/-- An element of `𝓞` not in `v` has an inverse modulo `v^j`. -/
lemma exists_mul_sub_one_mem (j : ℕ) {d : 𝓞 F} (hd : d ∉ v.asIdeal) :
    ∃ c : 𝓞 F, c * d - 1 ∈ v.asIdeal ^ j := by
  have h1 : IsCoprime v.asIdeal (Ideal.span {d}) := by
    obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv hd
    exact Ideal.isCoprime_iff_exists.mpr ⟨i, hi, y * d, Ideal.mul_mem_left _ _
      (Ideal.mem_span_singleton_self d), by rw [add_comm]; exact hyi⟩
  obtain ⟨i, hi, x, hx, hix⟩ := (h1.pow_left (m := j)).exists
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  refine ⟨c, ?_⟩
  have : c * d - 1 = -i := by linear_combination hix
  rw [this]
  exact neg_mem hi

/-- Every `x ∈ F` with `v(x) ≤ 1` is congruent modulo `v^j` (in valuation) to an element of `𝓞`. -/
lemma exists_val_sub_le (j : ℕ) (x : F) (hx : v.valuation F x ≤ 1) :
    ∃ a : 𝓞 F, v.valuation F (x - algebraMap (𝓞 F) F a) ≤ exp (-(j : ℤ)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) x hx
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  refine ⟨c * n, ?_⟩
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have heq : x - algebraMap (𝓞 F) F (c * n) =
      -(x * algebraMap (𝓞 F) F (c * d - 1)) := by
    have hnd' : x * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
    rw [map_mul, ← hnd', map_sub, map_mul, map_one]; ring
  rw [heq, Valuation.map_neg, map_mul, val_alg]
  calc v.valuation F x * v.intValuation (c * d - 1) ≤ 1 * exp (-(j : ℤ)) :=
        mul_le_mul' hx ((v.intValuation_le_pow_iff_mem _ j).2 hc)
    _ = _ := one_mul _

/-- Elements of `R` of valuation at most `exp(-j)` lie in `v^j R`. -/
lemma mem_of_val_le (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪)
    (h : v.valuation F (r : F) ≤ exp (-(j : ℤ))) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨n, ⟨d, hd⟩, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := F) (r : F) (r.2 v hv)
  have hnd' : (r : F) * algebraMap (𝓞 F) F d = algebraMap (𝓞 F) F n := hnd
  have hvd : v.valuation F (algebraMap (𝓞 F) F d) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hd
  have hn : n ∈ v.asIdeal ^ j := by
    rw [← v.intValuation_le_pow_iff_mem, ← val_alg (v := v), ← hnd', map_mul, hvd, mul_one]
    exact h
  obtain ⟨c, hc⟩ := exists_mul_sub_one_mem (v := v) j hd
  have heq : r = algebraMap (𝓞 F) (SInt 𝔪) (c * n) -
      r * algebraMap (𝓞 F) (SInt 𝔪) (c * d - 1) := by
    apply Subtype.ext
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul, coe_alg, coe_alg, map_mul, map_sub, map_mul,
      map_one, ← hnd']
    ring
  rw [heq]
  exact sub_mem (Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ _ hn))
    (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hc))

lemma mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    r ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      v.valuation F (r : F) ≤ exp (-(j : ℤ)) :=
  ⟨val_le_of_mem hv j, mem_of_val_le hv j r⟩

lemma alg_mem_map_pow_iff (hv : v ∉ placesOf 𝔪) (j : ℕ) (a : 𝓞 F) :
    algebraMap (𝓞 F) (SInt 𝔪) a ∈ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) ↔
      a ∈ v.asIdeal ^ j := by
  rw [mem_map_pow_iff hv, coe_alg, val_alg, v.intValuation_le_pow_iff_mem]

lemma exists_sub_mem_map_pow (hv : v ∉ placesOf 𝔪) (j : ℕ) (r : SInt 𝔪) :
    ∃ a : 𝓞 F, r - algebraMap (𝓞 F) (SInt 𝔪) a ∈
      (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  obtain ⟨a, ha⟩ := exists_val_sub_le (v := v) j (r : F) (r.2 v hv)
  exact ⟨a, mem_of_val_le hv j _ (by rw [Subalgebra.coe_sub, coe_alg]; exact ha)⟩

end val

section quot

variable {v : HeightOneSpectrum (𝓞 F)}

/-- `𝓞/v^j → R/v^j R`. -/
noncomputable def quotHom (𝔪 : Ideal (𝓞 F)) (I : Ideal (𝓞 F)) :
    𝓞 F ⧸ I →+* SInt 𝔪 ⧸ I.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.quotientMap _ (algebraMap (𝓞 F) (SInt 𝔪)) Ideal.le_comap_map

lemma quotHom_mk (I : Ideal (𝓞 F)) (a : 𝓞 F) :
    quotHom 𝔪 I (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map (algebraMap (𝓞 F) (SInt 𝔪))) (algebraMap (𝓞 F) (SInt 𝔪) a) :=
  rfl

lemma quotHom_bijective (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Function.Bijective (quotHom 𝔪 (v.asIdeal ^ j)) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [quotHom_mk, Ideal.Quotient.eq_zero_iff_mem, alg_mem_map_pow_iff hv] at hx
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
  · intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_sub_mem_map_pow hv j r
    exact ⟨Ideal.Quotient.mk _ a, by rw [quotHom_mk]; exact (Ideal.Quotient.eq.mpr ha).symm⟩

/-- `𝓞/v^j ≃+* R/v^j R`. -/
noncomputable def quotEquiv (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    𝓞 F ⧸ v.asIdeal ^ j ≃+* SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  RingEquiv.ofBijective _ (quotHom_bijective hv j)

lemma finite_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Finite (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have : Finite (𝓞 F ⧸ v.asIdeal ^ j) :=
    Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero _ v.ne_bot)
  exact Finite.of_equiv _ (quotEquiv hv j).toEquiv

lemma natCard_quot (hv : v ∉ placesOf 𝔪) (j : ℕ) :
    Nat.card (SInt 𝔪 ⧸ (v.asIdeal ^ j).map (algebraMap (𝓞 F) (SInt 𝔪))) =
      Ideal.absNorm v.asIdeal ^ j := by
  rw [← Nat.card_congr (quotEquiv hv j).toEquiv, ← map_pow, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]

/-- `v R` is a maximal ideal of `R`. -/
lemma isMaximal_map (hv : v ∉ placesOf 𝔪) :
    (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal := by
  have e := quotEquiv (𝔪 := 𝔪) hv 1
  rw [pow_one] at e
  apply Ideal.Quotient.maximal_of_isField
  have : (v.asIdeal).IsMaximal := v.isMaximal
  have hf : IsField (𝓞 F ⧸ v.asIdeal) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp this
  exact MulEquiv.isField hf e.symm.toMulEquiv

end quot

section fibre

variable {v : HeightOneSpectrum (𝓞 F)}

end fibre

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Add: the additive character `e`

* `HasWit 𝔪 x`: `x` has a witness `y` in the definition of `sAddChar` (`x - y ∈ R`, `y` integral
  at `S`). `hasWit_of_mul_mem`: true when `x I ⊆ R` for an ideal `I` coprime to `𝔪`; in particular
  `hasWit_div_gen`: `a / gen 𝔞` for `a ∈ R`, `𝔞` exterior.
* `sAddChar_eq_of_wit`: `e(x) = exp(-2πi Tr y)` for every witness; `sAddChar_add`: `e` is additive
  on elements with witnesses.
* `exists_trace_not_int`: for `P ∤ 𝔇`, some `z ∈ P⁻¹` has `Tr z ∉ ℤ`; `sAddChar_ne_one_of_dual`.
* `exists_sAddChar_ne_one`: primitivity at every level: for `x ∈ R ∖ P^j R` some `r ∈ R` has
  `e(x r / gen(P^j)) ≠ 1`.
-/

set_option linter.style.haveILetI false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ}

/-! ### The inverse different -/

/-! ### Primitivity at every level -/

section prim

variable {v : HeightOneSpectrum (𝓞 F)}

end prim

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Base: hypotheses from section A, finite quotients `R/𝔞R`, residue-symbol algebra

* `HypAdd 𝔪`: `e` is additive on `F` (needs the existence of `sAddChar` witnesses).
* `HypChi ι 𝔪`: at every exterior prime `P`, `χ_P` is multiplicative on `R` and `χ_P(x)⁶ = 1`
  for `x ∉ PR`.
-/

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- Hypothesis (section A): at an exterior prime, the sextic symbol is multiplicative on `R`, with
sixth power `1` off `PR`. -/
def HypChi (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) : Prop :=
  ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P →
    (∀ x y : SInt 𝔪, sexticResidueSymbol ι 𝔪 P (x * y) =
      sexticResidueSymbol ι 𝔪 P x * sexticResidueSymbol ι 𝔪 P y) ∧
    (∀ x : SInt 𝔪, x ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) → sexticResidueSymbol ι 𝔪 P x ^ 6 = 1)

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Ideals -/

/-- An exterior prime does not become the unit ideal in `R`. -/
lemma map_ne_top {Q : Ideal (𝓞 F)} (hQ : Q.IsPrime) (hQe : IsExterior 𝔪 Q) :
    Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≠ ⊤ := by
  intro htop
  let v : HeightOneSpectrum (𝓞 F) := ⟨Q, hQ, hQe.1⟩
  have hvS : v ∉ placesOf 𝔪 := by
    intro hv
    have : (⊤ : Ideal (𝓞 F)) ≤ Q := hQe.2 ▸ sup_le le_rfl hv
    exact hQ.ne_top (eq_top_iff.mpr this)
  let J : Ideal (SInt 𝔪) :=
    { carrier := {x | v.valuation F (x : F) < 1}
      add_mem' := fun {a b} ha hb => by
        show v.valuation F ((a + b : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_add]
        exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
      zero_mem' := by
        show v.valuation F ((0 : SInt 𝔪) : F) < 1
        simp
      smul_mem' := fun c x hx => by
        show v.valuation F ((c * x : SInt 𝔪) : F) < 1
        rw [Subalgebra.coe_mul, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (c.2 v hvS)) hx }
  have hle : Q.map (algebraMap (𝓞 F) (SInt 𝔪)) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show v.valuation F ((algebraMap (𝓞 F) (SInt 𝔪) a : SInt 𝔪) : F) < 1
    rw [C3B.coe_algebraMap_SInt]
    exact (v.valuation_lt_one_iff_mem a).mpr ha
  have h1 : (1 : SInt 𝔪) ∈ J := hle (htop ▸ Submodule.mem_top)
  have : v.valuation F ((1 : SInt 𝔪) : F) < 1 := h1
  simp at this

/-! ### Residue symbols -/

variable {ι : F →+* ℂ}

/-! ### Generators -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Sum: the Poisson sum and the Gauss sum with free generators; CRT and twists

* `PS 𝔰 𝔄 s A Af c h = ∑_{d mod 𝔰} ∑_{v mod 𝔄} [h ≡ Af d (𝔰)] χ_𝔰(d) χ_𝔄(v) e((h − Af d) v c/(sA))`;
  `poissonFactor g 𝔰 𝔄 h = PS 𝔰 𝔄 (gen 𝔰) (gen 𝔄) (gen 𝔄) 1 h`.
* `GS 𝔠 c c' j = ∑_{x mod 𝔠} χ_𝔠(x)^j e(x c'/c)`; `gaussPhase g j 𝔠 = q^{-1/2} GS 𝔠 (gen 𝔠) 1 j`.
* `PS_crt`, `GS_crt`: Chinese remainders with idempotents `β s₂A₂`, `α s₁A₁`.
* `PS_twist`, `GS_twist`: unit substitutions.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

section defs

variable (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))

end defs

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Generic lemmas -/

/-! ### Coercions -/

/-! ### The Poisson summand -/

section U

variable {𝔰 𝔄 : Ideal (𝓞 F)} {s A Af c h : SInt 𝔪}

end U

/-! ### Field identities -/

/-! ### CRT and twists for `PS` -/

section crt

variable {𝔰₁ 𝔰₂ 𝔄₁ 𝔄₂ : Ideal (𝓞 F)} {s₁ s₂ A₁ A₂ Af c h α β : SInt 𝔪}

end crt

/-! ### Gauss sums -/

section gs

variable {𝔠 : Ideal (𝓞 F)} {c c' : SInt 𝔪} {j : ℕ}

end gs

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Mul: twisted multiplicativity of `γ_j`, of `F(𝔰, 𝔄, gen(𝔯)⁶)`, of `ϑ`, and reciprocity

* `gaussPhase_mul` (3.10): `γ_j(𝔠₁𝔠₂) = χ_{𝔠₁}(c₂)^j χ_{𝔠₂}(c₁)^j γ_j(𝔠₁) γ_j(𝔠₂)`.
* `poissonFactor_mul`: for `𝔰₁𝔄₁` coprime to `𝔰₂𝔄₂`, `𝔯ᵢ` coprime to the other side,
  `χ_{𝔰₁}(A₂) χ_{𝔰₂}(A₁) F(𝔰₁𝔰₂, 𝔄₁𝔄₂, gen(𝔯₁𝔯₂)⁶)
     = χ_{𝔄₁}(s₂A₂) χ_{𝔄₂}(s₁A₁) F(𝔰₁, 𝔄₁, gen(𝔯₁)⁶) F(𝔰₂, 𝔄₂, gen(𝔯₂)⁶)`.
* `residueSymbol_gen_prime`: `χ_𝔟(gen P) = χ_P(gen 𝔟)` (from (3.3)).
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

/-! ### Coprimality in `R` -/

/-! ### Change of generators -/

/-! ### Generators and residue symbols -/

/-! ### `ϑ` and norms -/

/-! ### (3.10) -/

/-! ### Cross-prime multiplicativity of the Poisson factor -/

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Main: CutMul from `HypAdd` and `HypChi`

`b(P^{e₀}𝔠, P^l𝔫, P^k𝔰, P^m𝔯) = b(P^{e₀}, P^l, P^k, P^m) b(𝔠, 𝔫, 𝔰, 𝔯)`: `ϑ` is completely
multiplicative; `γ₂` and `F` split by (3.10) and `poissonFactor_mul`; with `a = χ_P(gen 𝔠)`,
`w = χ_P(gen 𝔠𝔫³) = a b³`, `σ = χ_P(gen 𝔰)`, `t = e₀ + 3l` the cross factors are
`a^{4e₀}` and `w^{2t}`, whose product is `1`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- `HypChi` for all moduli divisible by the small primes. -/
def HypChiAll (F : Type*) [Field F] [NumberField F] (ι : F →+* ℂ) : Prop :=
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → HypChi ι 𝔪

variable {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3I_Char: `χ_P` as a multiplicative character and `x ↦ e(x/π)` as a primitive additive
character of the residue field `L = R / P R`

Standing hypotheses `Good 𝔪 v`: `v` coprime to `𝔪`, `12 ∣ N v − 1`, `v ∤ 𝔇`; and a primitive
sixth root of unity `ω ∈ 𝓞`.

* `chi`: `MulChar L ℂ` with `chi (mk x) = sexticResidueSymbol ι 𝔪 v x`; `chi_neg_one`,
  `chi_pow_six`, `chi_pow_ne_one` (`6 ∤ j`), `chi_cube_eq` (`χ³` is the quadratic character).
* `psi`: `AddChar L ℂ` with `psi (mk x) = e(x / gen P)`; `psi_isPrimitive`.
* `cubicResidueChar_eq`: `ρ_P(x) = χ(x)²` through `𝓞/P ≃ L`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid WithZero

namespace ArtinPrimitiveRoots

namespace C3I

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The standing hypotheses at the prime `v`. -/
structure Good (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) : Prop where
  cop : v.asIdeal ⊔ 𝔪 = ⊤
  twelve : 12 ∣ Ideal.absNorm v.asIdeal - 1
  diff : ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal

variable {v : HeightOneSpectrum (𝓞 F)}

lemma Good.notS (h : Good 𝔪 v) : v ∉ placesOf 𝔪 := fun hv =>
  v.isPrime.ne_top (eq_top_iff.2 (h.cop ▸ sup_le le_rfl hv))

lemma absNorm_ne_one (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm v.asIdeal ≠ 1 := by
  rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top

lemma absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm v.asIdeal := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot

lemma Good.coprime_six (h : Good 𝔪 v) : (Ideal.absNorm v.asIdeal).Coprime 6 := by
  have h1 := absNorm_pos v
  obtain ⟨k, hk⟩ := h.twelve
  have : Ideal.absNorm v.asIdeal = 12 * k + 1 := by omega
  rw [this, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, show (12 * k + 1) % 6 = 1 by omega,
    Nat.gcd_one_left]

lemma isMaximal_v (h : Good 𝔪 v) : (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))).IsMaximal :=
  isMaximal_map h.notS

lemma finite_L (h : Good 𝔪 v) : Finite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) := by
  have := finite_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one] at this

lemma natCard_L (h : Good 𝔪 v) :
    Nat.card (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = Ideal.absNorm v.asIdeal := by
  have := natCard_quot (𝔪 := 𝔪) h.notS 1
  rwa [pow_one, pow_one] at this

lemma quotHom_bijective_one (h : v ∉ placesOf 𝔪) :
    Function.Bijective (quotHom 𝔪 v.asIdeal) := by
  have := quotHom_bijective (𝔪 := 𝔪) h 1
  rwa [pow_one] at this

/-! ### The sixth roots of unity -/

section roots

variable (ι : F →+* ℂ)

/-- Choice-free value of a root of unity: if `f ζ = f ω ^ i` then `ι ζ = ι ω ^ i`. -/
lemma iota_eq_pow_of_map {K : Type*} [CommRing K] [IsDomain K] (f : 𝓞 F →+* K) {m : ℕ}
    (hm : 0 < m) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω m) (hωf : IsPrimitiveRoot (f ω) m)
    {ζ : 𝓞 F} (hζ : ζ ^ m = 1) {i : ℕ} (h : f ζ = f ω ^ i) : ι (ζ : F) = ι (ω : F) ^ i := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨j, hj, rfl⟩ := hω.eq_pow_of_pow_eq_one hζ
  have hpow : ∀ (z : K) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have hpowC : ∀ (z : ℂ) (hz : z ^ m = 1) (n : ℕ), z ^ n = z ^ (n % m) := by
    intro z hz n
    conv_lhs => rw [← Nat.div_add_mod n m, pow_add, pow_mul, hz, one_pow, one_mul]
  have h1 : f ω ^ j = f ω ^ (i % m) := by
    rw [← map_pow, h, hpow _ hωf.pow_eq_one]
  have hji : j = i % m := hωf.pow_inj hj (Nat.mod_lt _ hm) h1
  have hιω : ι (ω : F) ^ m = 1 := by
    rw [← map_pow, ← map_pow (algebraMap (𝓞 F) F), hω.pow_eq_one, map_one, map_one]
  rw [show ((ω ^ j : 𝓞 F) : F) = (ω : F) ^ j from map_pow (algebraMap (𝓞 F) F) ω j, map_pow, hji,
    ← hpowC _ hιω]

end roots

section chi

/-- The function underlying `sexticResidueSymbol` on `L = R / P R`. -/
noncomputable def sexFun (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F)) (y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) : ℂ := by
  classical
  exact if y = 0 then 0 else
    if h : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
        Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
          (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)
    then ι (h.choose : F) else 0

lemma sexticResidueSymbol_eq (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F)) (v : HeightOneSpectrum (𝓞 F))
    (x : SInt 𝔪) :
    sexticResidueSymbol ι 𝔪 v.asIdeal x =
      sexFun ι 𝔪 v (Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) x) := by
  unfold sexticResidueSymbol sexFun
  congr 1

variable {ι : F →+* ℂ}

/-- The image of `ω` in `L`. -/
noncomputable abbrev omegaL (ω : 𝓞 F) : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
  Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) ω)

lemma omegaL_prim (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    IsPrimitiveRoot (omegaL (𝔪 := 𝔪) (v := v) ω) 6 := by
  have h1 : IsPrimitiveRoot (Ideal.Quotient.mk v.asIdeal ω) 6 :=
    hω.idealQuotient_mk (absNorm_ne_one v) h.coprime_six
  have h2 := h1.map_of_injective (quotHom_bijective_one (𝔪 := 𝔪) h.notS).1
  exact h2

lemma pow_card_sub_one_L (h : Good 𝔪 v)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    y ^ (Ideal.absNorm v.asIdeal - 1) = 1 := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  haveI := finite_L h
  letI := Fintype.ofFinite (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  rw [← natCard_L h, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card_sub_one_eq_one y hy

lemma six_mul_e (h : Good 𝔪 v) :
    6 * ((Ideal.absNorm v.asIdeal - 1) / 6) = Ideal.absNorm v.asIdeal - 1 :=
  Nat.mul_div_cancel' ((Nat.dvd_trans (by norm_num) h.twelve))

/-- Every nonzero `y ∈ L` has `y^e` a power of `ω`. -/
lemma exists_pow_e (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    ∃ i : ℕ, i < 6 ∧ y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have h6 : (y ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) ^ 6 = 1 := by
    rw [← pow_mul, mul_comm, six_mul_e h, pow_card_sub_one_L h hy]
  obtain ⟨i, hi, hi'⟩ := (omegaL_prim h hω).eq_pow_of_pow_eq_one h6
  exact ⟨i, hi, hi'.symm⟩

lemma sexFun_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    sexFun ι 𝔪 v y = ι (ω : F) ^ i := by
  haveI := isMaximal_v h
  letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
  have hex : ∃ ζ : 𝓞 F, ζ ^ 6 = 1 ∧
      Ideal.Quotient.mk (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
        (algebraMap (𝓞 F) (SInt 𝔪) ζ) = y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) :=
    ⟨ω ^ i, by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], by
      rw [map_pow, map_pow, hi]⟩
  classical
  unfold sexFun
  rw [if_neg hy, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set f : 𝓞 F →+* SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)) :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 F) (SInt 𝔪))
  exact iota_eq_pow_of_map ι f (by norm_num) hω (omegaL_prim h hω) h1 (by
    change Ideal.Quotient.mk _ (algebraMap (𝓞 F) (SInt 𝔪) hex.choose) = omegaL ω ^ i
    rw [h2, hi])

lemma sexFun_zero : sexFun ι 𝔪 v (0 : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) = 0 := by
  classical
  unfold sexFun; rw [if_pos rfl]

lemma iota_omega_prim {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) : IsPrimitiveRoot (ι (ω : F)) 6 :=
  (hω.map_of_injective RingOfIntegers.coe_injective).map_of_injective ι.injective

/-- `χ_P` as a multiplicative character of `L`. -/
noncomputable def chi (ι : F →+* ℂ) (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) :
    MulChar (SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))) ℂ where
  toFun := sexFun ι 𝔪 v
  map_one' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    rw [sexFun_eq_pow h hω one_ne_zero (i := 0) (by rw [one_pow, pow_zero])]
    simp
  map_mul' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro x y
    by_cases hx : x = 0
    · simp [hx, sexFun_zero]
    by_cases hy : y = 0
    · simp [hy, sexFun_zero]
    obtain ⟨i, -, hi⟩ := exists_pow_e h hω hx
    obtain ⟨j, -, hj⟩ := exists_pow_e h hω hy
    rw [sexFun_eq_pow h hω hx hi, sexFun_eq_pow h hω hy hj,
      sexFun_eq_pow h hω (mul_ne_zero hx hy) (i := i + j) (by rw [mul_pow, hi, hj, pow_add]),
      pow_add]
  map_nonunit' := by
    haveI := isMaximal_v h
    letI := Ideal.Quotient.field (v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    intro a ha
    have : a = 0 := by
      by_contra h'
      exact ha (Ne.isUnit h')
    rw [this]; exact sexFun_zero

lemma chi_mk (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6) (x : SInt 𝔪) :
    chi ι h hω (Ideal.Quotient.mk _ x) = sexticResidueSymbol ι 𝔪 v.asIdeal x :=
  (sexticResidueSymbol_eq ι 𝔪 v x).symm

lemma chi_eq_pow (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) {i : ℕ}
    (hi : y ^ ((Ideal.absNorm v.asIdeal - 1) / 6) = omegaL ω ^ i) :
    chi ι h hω y = ι (ω : F) ^ i :=
  sexFun_eq_pow h hω hy hi

lemma chi_pow_six_apply (h : Good 𝔪 v) {ω : 𝓞 F} (hω : IsPrimitiveRoot ω 6)
    {y : SInt 𝔪 ⧸ v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪))} (hy : y ≠ 0) :
    chi ι h hω y ^ 6 = 1 := by
  obtain ⟨i, -, hi⟩ := exists_pow_e h hω hy
  rw [chi_eq_pow h hω hy hi, ← pow_mul, mul_comm, pow_mul, (iota_omega_prim hω).pow_eq_one,
    one_pow]

end chi

end C3I

end ArtinPrimitiveRoots

end
end

section
section
/-! # C3M_Chk: `HypChi` from section A's `χ_P` (`C3I_Char`), and CutMul

Exterior primes are `C3I.Good` once `N₀ ≥ max(3^[F:ℚ], N 𝔇)`: `12 ∣ N P − 1` because `μ₁₂ ⊂ F`
and `P ∤ 6`, and `P ∤ 𝔇` because `N P > N 𝔇`.
-/

set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace ArtinPrimitiveRoots

namespace C3M

variable {F : Type*} [Field F] [NumberField F]

/-- In `ℚ(μ_n)` with `12 ∣ n`, a prime of norm `> 3^[F:ℚ]` has `12 ∣ N P − 1`. -/
theorem twelve_dvd_absNorm_sub_one (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    [IsCyclotomicExtension {n} ℚ F]
    (P : Ideal (𝓞 F)) (hP : P.IsPrime) (hP0 : P ≠ ⊥)
    (hQ : 3 ^ Module.finrank ℤ (𝓞 F) < Ideal.absNorm P) : 12 ∣ Ideal.absNorm P - 1 := by
  have : P.IsMaximal := hP.isMaximal hP0
  let _ := Ideal.Quotient.field P
  have : Finite (𝓞 F ⧸ P) := Ring.HasFiniteQuotients.finiteQuotient hP0
  let _ : Fintype (𝓞 F ⧸ P) := Fintype.ofFinite _
  set Q := Ideal.absNorm P
  have hd : 0 < Module.finrank ℤ (𝓞 F) := Module.finrank_pos
  have h23 : 2 ^ Module.finrank ℤ (𝓞 F) ≤ 3 ^ Module.finrank ℤ (𝓞 F) :=
    Nat.pow_le_pow_left (by norm_num) _
  have h3le : 3 ≤ 3 ^ Module.finrank ℤ (𝓞 F) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hd
  have h2 : ¬ 2 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 2 Nat.prime_two P hP0 h; omega
  have h3 : ¬ 3 ∣ Q := fun h => by
    have := C3B.absNorm_le_of_prime_dvd 3 Nat.prime_three P hP0 h; omega
  have hcop : Q.Coprime 12 := by
    have c2 : Q.Coprime 2 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2))
    have c3 : Q.Coprime 3 :=
      (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
    have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
    rw [this]; exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 c2) c3
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ12 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 12)) 12 :=
    hζ.pow hn0 (Nat.div_mul_cancel hn).symm
  have hω : IsPrimitiveRoot hζ12.toInteger 12 := hζ12.toInteger_isPrimitiveRoot
  have hωb : IsPrimitiveRoot (Ideal.Quotient.mk P hζ12.toInteger) 12 :=
    hω.idealQuotient_mk (by omega) hcop
  have h1 : Ideal.Quotient.mk P hζ12.toInteger ^ (Q - 1) = 1 := by
    rw [show Q = Fintype.card (𝓞 F ⧸ P) from (C3B.card_quot P hP0).symm]
    exact FiniteField.pow_card_sub_one_eq_one _ (hωb.ne_zero (by norm_num))
  exact (hωb.pow_eq_one_iff_dvd _).mp h1

/-- `HypChi` holds for every modulus divisible by the primes of norm `≤ max(3^[F:ℚ], N 𝔇)`. -/
theorem hypChiAll (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) [IsCyclotomicExtension {n} ℚ F]
    (ι : F →+* ℂ) : HypChiAll F ι := by
  refine ⟨max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))),
    fun 𝔪 _ hS P hP hPe => ?_⟩
  have h𝔪 : ¬ 𝔪 ≤ P := by
    intro h
    apply hP.ne_top
    rw [eq_top_iff, ← hPe.2]
    exact sup_le le_rfl h
  have hgt : max (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F))) <
      Ideal.absNorm P := by
    by_contra hc
    exact h𝔪 (hS P hP hPe.1 (not_lt.mp hc))
  let v : HeightOneSpectrum (𝓞 F) := ⟨P, hP, hPe.1⟩
  have hdiff : ¬ differentIdeal ℤ (𝓞 F) ≤ P := by
    intro hle
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    have hD0 : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hdvd
    have := le_max_right (3 ^ Module.finrank ℤ (𝓞 F)) (Ideal.absNorm (differentIdeal ℤ (𝓞 F)))
    omega
  have hgood : C3I.Good 𝔪 v :=
    ⟨hPe.2, twelve_dvd_absNorm_sub_one n hn0 hn P hP hPe.1 (lt_of_le_of_lt (le_max_left _ _) hgt),
      hdiff⟩
  have : NeZero n := ⟨hn0.ne'⟩
  have hζ := IsCyclotomicExtension.zeta_spec n ℚ F
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ (n / 6)) 6 :=
    hζ.pow hn0 (Nat.div_mul_cancel (Nat.dvd_trans (by norm_num) hn)).symm
  have hω : IsPrimitiveRoot hζ6.toInteger 6 := hζ6.toInteger_isPrimitiveRoot
  have e : ∀ z : SInt 𝔪, C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) z) =
      sexticResidueSymbol ι 𝔪 P z := fun z => C3I.chi_mk hgood hω z
  refine ⟨fun x y => ?_, fun x hx => ?_⟩
  · have h : C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x *
        Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) =
        C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x) *
          C3I.chi ι hgood hω (Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) y) :=
      map_mul _ _ _
    rw [← map_mul, e, e, e] at h
    exact h
  · have hne : Ideal.Quotient.mk (P.map (algebraMap (𝓞 F) (SInt 𝔪))) x ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h := C3I.chi_pow_six_apply (ι := ι) hgood hω hne
    rwa [e] at h

end C3M

end ArtinPrimitiveRoots

end
end

section
section
/-! # L3X_Meas: sheet measures on the model `SModel 𝔪 k` of `F_S^× / U`

* `lnorm y = Σ_w log|y_w|_w + log |y_f|_{S_f}` (the log of the `S`-norm).
* For a place `w₀`, the base space `SFin × (ℝ^{W∖w₀} × (ℝ/2πℤ)^W)` carries counting ⊗ Lebesgue ⊗
  Haar, and `slice w₀ a` sends it onto the sheet `{lnorm = a}`, solving for the `w₀` log-coordinate.
* `shMeasure w₀ a` is the push-forward: the sheet measure on `X_{e^a}`.
* Translation by `d` maps `shMeasure a` to `shMeasure (a + lnorm d)`; negation maps `shMeasure a` to
  `shMeasure (-a)`; moving the `w₀` coordinate by `t` moves the slice from `a` to `a + t`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

instance instDiscrSFin : DiscreteMeasurableSpace (SFin 𝔪 k) := ⟨fun _ => trivial⟩

theorem countable_field (F : Type*) [Field F] [NumberField F] : Countable F := by
  have b := Module.finBasis ℚ F
  exact b.equivFun.injective.countable

instance instCountableSFin : Countable (SFin 𝔪 k) := by
  have := countable_field F
  have : Countable Fˣ := Function.Injective.countable (f := fun u : Fˣ => (u : F))
    Units.val_injective
  have : Countable (Fˣ ⧸ SLevel 𝔪 k) := (QuotientGroup.mk_surjective).countable
  exact Countable.of_equiv (Fˣ ⧸ SLevel 𝔪 k) Additive.ofMul

/-! ### The finite norm -/

/-! ### `lnorm` -/

/-! ### Slices -/

variable (w₀ : InfinitePlace F)


/-! ### Measure preservation -/

instance : MeasurableAdd (SFin 𝔪 k) :=
  ⟨fun _ => measurable_of_countable _, fun _ => measurable_of_countable _⟩

instance : MeasurableNeg (SFin 𝔪 k) := ⟨measurable_of_countable _⟩

instance : MeasurableAdd₂ (SFin 𝔪 k) := ⟨measurable_of_countable _⟩

instance instMeasurableAddSModel : MeasurableAdd (SModel 𝔪 k) := by
  constructor
  · intro c
    exact (measurable_fst.const_add c.1).prodMk
      (((measurable_fst.comp measurable_snd).const_add c.2.1).prodMk
        ((measurable_snd.comp measurable_snd).const_add c.2.2))
  · intro c
    exact (measurable_fst.add_const c.1).prodMk
      (((measurable_fst.comp measurable_snd).add_const c.2.1).prodMk
        ((measurable_snd.comp measurable_snd).add_const c.2.2))

instance instMeasurableNegSModel : MeasurableNeg (SModel 𝔪 k) := by
  constructor
  exact measurable_fst.neg.prodMk ((measurable_fst.comp measurable_snd).neg.prodMk
    (measurable_snd.comp measurable_snd).neg)

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-!
# L3P_Sfin: the finite places of `S`, combinatorially

`S` a finite type with `q v > 1`. For `j : S → ℤ`, `NN j = ∏ q_v^{j_v}`. The weight
`Om j = Σ_{e ⊆ S} (−1)^{|e|} 1[j + 1_e ≥ 0] / NN (j + 1_e)` is the profile of the Fourier transform
of `∏_v 1_{𝒪_v^×}` (self-dual normalisation), and
`Σ_j Om j · NN j^{1−z} = ∏_v (1 − q_v^{z−1}) / (1 − q_v^{−z})` for `Re z > 0`.
-/

namespace ArtinPrimitiveRoots.L3P

open scoped BigOperators Classical

set_option linter.unusedSectionVars false

/-! ### Products of geometric series over `S → ℕ` -/

/-! ### The weight `Om` -/

section Om

variable {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ)

variable (hq : ∀ v, 1 < q v)
include hq

end Om

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-!
# L3P_Val: valuations as counts of principal fractional ideals

For `x ≠ 0` in a number field, `v.valuation x = exp (−count_v (x))`, where
`count_v (x) = FractionalIdeal.count F v (spanSingleton x)`. Membership in a nonzero fractional
ideal is a comparison of counts.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F]

/-! ### The places of `S` -/

variable {𝔪 : Ideal (𝓞 F)}

/-! ### Units, the different, and the trace dual -/

end ArtinPrimitiveRoots.L3P

end
end

section
section
/-! # L3X_Emb: the embedding `F^× → SModel 𝔪 k`

* `sEmb` is a homomorphism on `F^×`.
* The `v`-adic absolute value is `q_v^{-ord_v}`; the finite norm of `[x]` is `∏_{v∈S_f} q_v^{-ord_v x}`.
* The product formula: `lnorm (sEmb m) = log N 𝔟` for an `S`-integer `m` generating the exterior
  ideal `𝔟 R`; in particular `lnorm (sEmb ε) = 0` for `S`-units.
* Valuations at `S_f` descend to `SFin`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Absolute values and valuations -/

end

end ArtinPrimitiveRoots.L3X

end
end

section
section
/-! # L3L_Phi: the character `Φ(x) = ∏_{v ∉ S} ψ(P_v)^{ord_v x}` of `F^×`

* `Phi 𝔪 ψ` is multiplicative on `F^×` (given `ψ ≠ 0` at exterior primes), trivial on `S`-units, and
  equals `∏_{P ∈ nf 𝔄} ψ P` on any `x` with `ord_v x = v_P(𝔄)` outside `S` (e.g. generators of `𝔄 R`,
  or elements of `𝓞` generating the exterior ideal `𝔄`).
* `ang m x = ∏_w (w x / |w x|)^{m_w}` (in the angle coordinate of `sEmb`), multiplicative.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots.L3L

open NumberField IsDedekindDomain UniqueFactorizationMonoid FractionalIdeal
open scoped nonZeroDivisors Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The angular character -/

end

end ArtinPrimitiveRoots.L3L

end
end

section
section
/-! # L3L_Approx: elements of `SLevel 𝔪 k` are quotients `α/β` with `α ≡ β ≡ 1 (mod 𝔪^j)`

For `k` large (depending on `j`), every `x ∈ SLevel 𝔪 k` is `α/β` with `α, β ∈ 𝓞` and
`α − 1, β − 1 ∈ 𝔪^j`. The denominator `β` is taken in the exterior part `D` of a denominator of `x`
and `≡ 1 (mod 𝔪^j)` (CRT); then `α = xβ` is integral, and `α − 1 = x(β − 1) + (x − 1)` is deep at `S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots.L3L

open NumberField IsDedekindDomain UniqueFactorizationMonoid FractionalIdeal
open scoped nonZeroDivisors Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

end

end ArtinPrimitiveRoots.L3L

end
end

section
section
/-! # L3L_Desc: a Hecke-type `ψ` gives a unitary character `Lf` of `SFin 𝔪 k`

Hypothesis `HeckeHyp 𝔪 ψ j m`: for `α ∈ 𝓞`, `α ≡ 1 (mod 𝔪^j)`, `∏_{P ∈ nf (α)} ψ P = ang m α`.
Then (`j ≥ 1`):
* `‖ψ P‖ = 1` at exterior primes (a power of `P` is `(β)` with `β ≡ 1 mod 𝔪^j`);
* `Θ(x) = Φ(x) · ang(−m)(x)` is a character of `F^×`, trivial on `SLevel 𝔪 k` for `k ≥ k₀`
  (`L3L_Approx`); `Lf` is its descent, and `Lf [x] · ang m x = Φ x`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinPrimitiveRoots.L3L

open NumberField IsDedekindDomain UniqueFactorizationMonoid FractionalIdeal
open scoped nonZeroDivisors Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem isExterior_of_sub_one_mem {j : ℕ} (hj : 1 ≤ j) {α : 𝓞 F} (hα : α ≠ 0)
    (h : α - 1 ∈ 𝔪 ^ j) : IsExterior 𝔪 (Ideal.span {α}) := by
  refine ⟨by rwa [ne_eq, Ideal.span_singleton_eq_bot], ?_⟩
  rw [eq_top_iff]
  have h1 : α - 1 ∈ 𝔪 := Ideal.pow_le_self (by omega) h
  have : (1 : 𝓞 F) = α - (α - 1) := by ring
  intro z _
  rw [← mul_one z, this]
  exact Ideal.mul_mem_left _ z (Submodule.sub_mem _ (Ideal.mem_sup_left
    (Ideal.mem_span_singleton_self α)) (Ideal.mem_sup_right h1))

end

end ArtinPrimitiveRoots.L3L

end
end

section
section
/-! # L3L_Kum: `χ_•(u)` is trivial on `(α)`, `α ≡ 1 (mod 𝔪^j)`, for an `S`-unit `u` (Lemma 3.3)

* Not a sixth power: L3K's Hecke character `χ'` of modulus `𝔣 𝔪` (`L3K.exists_chi'`, universe 0) agrees
  with `χ_•(u)` on exterior ideals; the conductor `𝔣` is supported on `S`, so `𝔪^j ≤ 𝔣 𝔪`. Transported to
  `F : Type*` along a universe-0 model (C0R / L3K transport lemmas).
* A sixth power `u = b⁶`: `b ∈ R` and `χ_P(u) = χ_P(b)⁶ = 1`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField NumberField.InfinitePlace IsDedekindDomain UniqueFactorizationMonoid

noncomputable section

namespace ArtinPrimitiveRoots

namespace L3L

theorem exists_pow_le_of_primes {R : Type*} [CommRing R] [IsDedekindDomain R] {𝔪 I : Ideal R}
    (hI : I ≠ ⊥) (h : ∀ v : HeightOneSpectrum R, I ≤ v.asIdeal → 𝔪 ≤ v.asIdeal) :
    ∃ j : ℕ, 𝔪 ^ j ≤ I := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg_radical ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun J ⟨hIJ, hJ⟩ => ?_
  have hJ0 : J ≠ ⊥ := fun h0 => hI (le_bot_iff.1 (h0 ▸ hIJ))
  exact h ⟨J, hJ, hJ0⟩ hIJ

theorem residueSymbol_bot {F : Type*} [Field F] [NumberField F] (ι : F →+* ℂ) (𝔪 : Ideal (𝓞 F))
    (x : SInt 𝔪) : residueSymbol ι 𝔪 ⊥ x = 1 := by
  unfold residueSymbol
  rw [← Ideal.zero_eq_bot, normalizedFactors_zero]; simp

theorem isSixthPowerFree_top {F : Type*} [Field F] [NumberField F] :
    IsSixthPowerFree (⊤ : Ideal (𝓞 F)) := by
  intro J hJ
  rw [← Ideal.one_eq_top] at hJ
  exact isUnit_of_dvd_one (dvd_trans (dvd_pow_self J (by norm_num)) hJ)

/-- Universe-0 core (not a sixth power). -/
theorem kummer_core (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 6)
    (hK : ∀ w : InfinitePlace F, w.IsComplex) (ι : F →+* ℂ) {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥)
    (six : ∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → 𝔪 ≤ v.asIdeal)
    (prin : ∀ v : HeightOneSpectrum (𝓞 F), ¬ 𝔪 ≤ v.asIdeal →
      ∃ p : SInt 𝔪, Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F) (SInt 𝔪)))
    (u : SInt 𝔪) (hu : IsUnit u) (nonsix : ∀ b : F, b ^ 6 ≠ (u : F)) :
    ∃ j : ℕ, ∀ α : 𝓞 F, α - 1 ∈ 𝔪 ^ j → residueSymbol ι 𝔪 (Ideal.span {α}) u = 1 := by
  classical
  have h : L3K.BridgeHyp 𝔪 u ⊤ := ⟨h𝔪, six, prin,
    by rw [Ideal.map_top, Ideal.span_singleton_eq_top]; exact hu, isSixthPowerFree_top, nonsix⟩
  set 𝔣 := ArtinL.Abelian.conductor (L3K.psi F hζ ι (L3K.uUnit h))
  obtain ⟨χ', hχ', -⟩ := L3K.exists_chi' hζ ι hK h
  have hf : ∀ v : HeightOneSpectrum (𝓞 F), 𝔣 ≤ v.asIdeal → 𝔪 ≤ v.asIdeal := by
    intro v hle
    by_contra hvm
    have hun := (L3K.localValue_eq_sextic hζ ι h hvm
      (fun hle' => v.isPrime.ne_top (top_le_iff.1 hle'))).1
    exact ((ArtinL.Abelian.dvd_conductor_iff_not_isUnramifiedAt F _ _ v).1
      (Ideal.dvd_iff_le.2 hle)) hun
  obtain ⟨j, hj⟩ := exists_pow_le_of_primes (ArtinL.Abelian.conductor_ne_bot _) hf
  refine ⟨j + 1, fun α hα => ?_⟩
  have hmem : α - 1 ∈ 𝔣 * 𝔪 := by
    rw [pow_succ] at hα; exact Ideal.mul_mono_left hj hα
  by_cases hα0 : α = 0
  · rw [hα0, Ideal.span_singleton_eq_bot.2 rfl, residueSymbol_bot]
  have h1 := χ'.map_principal' α hα0 hmem
  rw [hχ', L3K.gK] at h1
  have hext : IsExterior 𝔪 (Ideal.span {α}) := by
    refine ⟨by rwa [ne_eq, Ideal.span_singleton_eq_bot], ?_⟩
    have hm : α - 1 ∈ 𝔪 := Ideal.mul_le_right hmem
    rw [eq_top_iff]
    intro z _
    have : (1 : 𝓞 F) = α - (α - 1) := by ring
    rw [← mul_one z, this]
    exact Ideal.mul_mem_left _ z (Submodule.sub_mem _ (Ideal.mem_sup_left
      (Ideal.mem_span_singleton_self α)) (Ideal.mem_sup_right hm))
  rwa [if_pos hext] at h1

/-- The sixth-power case, for any universe. -/
theorem kummer_six {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)}
    (hχ : C3M.HypChi ι 𝔪) (u : SInt 𝔪) (hu : IsUnit u) {b : F} (hb : b ^ 6 = (u : F))
    {𝔞 : Ideal (𝓞 F)} (h𝔞 : IsExterior 𝔪 𝔞) : residueSymbol ι 𝔪 𝔞 u = 1 := by
  have hbR : b ∈ (placesOf 𝔪).integer F := by
    intro v hv
    have hu1 : v.valuation F (u : F) ≤ 1 := u.2 v hv
    rw [← hb, map_pow] at hu1
    exact (pow_le_one_iff (by norm_num)).1 hu1
  set b' : SInt 𝔪 := ⟨b, hbR⟩
  have hb' : b' ^ 6 = u := Subtype.ext (by simp [b', hb])
  unfold residueSymbol
  refine Multiset.prod_eq_one fun z hz => ?_
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hz
  have hPp : P.IsPrime := (Ideal.isPrime_of_prime (prime_of_normalized_factor P hP))
  have hP0 : P ≠ ⊥ := (prime_of_normalized_factor P hP).ne_zero
  have hPe : IsExterior 𝔪 P := by
    refine ⟨hP0, ?_⟩
    rw [eq_top_iff, ← h𝔞.2]
    exact sup_le_sup_right (Ideal.le_of_dvd (dvd_of_mem_normalizedFactors hP)) _
  obtain ⟨hmul, hsix⟩ := hχ P hPp hPe
  have hbP : b' ∉ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
    intro hmem
    have : u ∈ P.map (algebraMap (𝓞 F) (SInt 𝔪)) := hb' ▸ Ideal.pow_mem_of_mem _ hmem 6 (by norm_num)
    exact C3M.map_ne_top hPp hPe (Ideal.eq_top_of_isUnit_mem _ this hu)
  have hpow : ∀ k : ℕ, sexticResidueSymbol ι 𝔪 P (b' ^ (k + 1)) =
      sexticResidueSymbol ι 𝔪 P b' ^ (k + 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, hmul, ih, ← pow_succ]
  rw [← hb', hpow 5, hsix b' hbP]


/-- **Kummer**, for `F : Type*`. -/
theorem kummer (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n) (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
    ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
      ∀ u : SInt 𝔪, IsUnit u → ∃ j : ℕ, ∀ α : 𝓞 F, α - 1 ∈ 𝔪 ^ j →
        residueSymbol ι 𝔪 (Ideal.span {α}) u = 1 := by
  classical
  haveI : NeZero n := ⟨hn0.ne'⟩
  have hζn := IsCyclotomicExtension.zeta_spec n ℚ F
  obtain ⟨k, hk⟩ := (show 6 ∣ n from dvd_trans (by norm_num) hn)
  have hζ6 : IsPrimitiveRoot (IsCyclotomicExtension.zeta n ℚ F ^ k) 6 :=
    hζn.pow hn0 (by rw [hk]; ring)
  obtain ⟨F₀, _, _, ⟨e₀⟩⟩ := T12A.exists_small_model F
  set e : F ≃+* F₀ := e₀.symm
  set eO := RingOfIntegers.mapRingEquiv e
  have hζ' := hζ6.map_of_injective e.injective
  have hK' := L3K.isComplex_of_prim6 F₀ hζ'
  obtain ⟨N₁, hN₁⟩ := C3M.hypChiAll n hn0 hn ι
  refine ⟨max (Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)})) N₁, fun 𝔪 h𝔪 hsmallM g u hu => ?_⟩
  have hsmall : SmallPrimesDvd (Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)})) 𝔪 :=
    fun P hP hP0 hN => hsmallM P hP hP0 (hN.trans (le_max_left _ _))
  have hχ : C3M.HypChi ι 𝔪 :=
    hN₁ 𝔪 h𝔪 (fun P hP hP0 hN => hsmallM P hP hP0 (hN.trans (le_max_right _ _)))
  suffices H : ∃ j : ℕ, ∀ α : 𝓞 F, α ≠ 0 → α - 1 ∈ 𝔪 ^ j → IsExterior 𝔪 (Ideal.span {α}) →
      residueSymbol ι 𝔪 (Ideal.span {α}) u = 1 by
    obtain ⟨j, hj⟩ := H
    refine ⟨j + 1, fun α hα => ?_⟩
    by_cases hα0 : α = 0
    · rw [hα0, Ideal.span_singleton_eq_bot.2 rfl, residueSymbol_bot]
    exact hj α hα0 (Ideal.pow_le_pow_right (by omega) hα)
      (isExterior_of_sub_one_mem (by omega) hα0 hα)
  by_cases hsix : ∃ b : F, b ^ 6 = (u : F)
  · obtain ⟨b, hb⟩ := hsix
    exact ⟨1, fun α _ _ hext => kummer_six hχ u hu hb hext⟩
  push Not at hsix
  set 𝔪' := 𝔪.map eO
  have h𝔪' : 𝔪' ≠ ⊥ := fun h0 => h𝔪 ((Ideal.map_eq_bot_iff_of_injective eO.injective).1 h0)
  have hsmall' : SmallPrimesDvd (Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)})) 𝔪' :=
    C0R.smallPrimesDvd_map e hsmall
  have six' : ∀ v : HeightOneSpectrum (𝓞 F₀), (6 : 𝓞 F₀) ∈ v.asIdeal → 𝔪' ≤ v.asIdeal := by
    intro v h6
    have hle : Ideal.span {(6 : 𝓞 F₀)} ≤ v.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 h6
    have hN : Ideal.absNorm v.asIdeal ≤ Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)}) := by
      refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (Ideal.absNorm_dvd_absNorm_of_le hle)
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      intro h; have := congrArg (fun x : 𝓞 F₀ => (x : F₀)) h; simp at this
    exact hsmall' _ v.isPrime v.ne_bot hN
  -- exterior primes of `F` avoid `6`
  have h6 : ∀ P : Ideal (𝓞 F), P.IsPrime → IsExterior 𝔪 P → P ⊔ Ideal.span {6} = ⊤ := by
    intro P hP hE
    have hPm : (P.map eO).IsPrime := Ideal.map_isPrime_of_equiv eO
    have hEm := C0R.isExterior_map e hE
    have hmax : (P.map eO).IsMaximal := hPm.isMaximal hEm.1
    have h1 : P.map eO ⊔ Ideal.span {(6 : 𝓞 F₀)} = ⊤ := by
      by_contra hne
      have hle : Ideal.span {(6 : 𝓞 F₀)} ≤ P.map eO :=
        le_of_eq (hmax.eq_of_le hne le_sup_left).symm |>.trans' le_sup_right
      have hN : Ideal.absNorm (P.map eO) ≤ Ideal.absNorm (Ideal.span {(6 : 𝓞 F₀)}) := by
        refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (Ideal.absNorm_dvd_absNorm_of_le hle)
        rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
        intro h; have := congrArg (fun x : 𝓞 F₀ => (x : F₀)) h; simp at this
      have := hsmall' _ hPm hEm.1 hN
      apply hPm.ne_top
      rw [eq_top_iff, ← hEm.2]; exact sup_le le_rfl this
    have h2 : (P ⊔ Ideal.span {6}).map eO = ⊤ := by
      rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_ofNat]; exact h1
    rw [← C0R.map_equiv_symm_map eO (P ⊔ Ideal.span {6}), h2, Ideal.map_top]
  -- exterior primes of `F₀` are principal in `R₀`
  have hprin' : ∀ v : HeightOneSpectrum (𝓞 F₀), ¬ 𝔪' ≤ v.asIdeal →
      ∃ p : SInt 𝔪', Ideal.span {p} = v.asIdeal.map (algebraMap (𝓞 F₀) (SInt 𝔪')) := by
    intro v hv
    set P := v.asIdeal.map eO.symm
    have hPP : P.map eO = v.asIdeal := by
      have := C0R.map_equiv_symm_map eO.symm v.asIdeal
      rwa [RingEquiv.symm_symm] at this
    have hP : P.IsPrime := Ideal.map_isPrime_of_equiv eO.symm
    have hP0 : P ≠ ⊥ := fun h0 => v.ne_bot (by rw [← hPP, h0, Ideal.map_bot])
    have hPm : ¬ 𝔪 ≤ P := fun hle => hv (by rw [← hPP]; exact (C0R.map_equiv_le_iff eO).2 hle)
    have hE : IsExterior 𝔪 P := ⟨hP0, by
      by_contra hne
      exact hPm (le_trans le_sup_right (le_of_eq ((hP.isMaximal hP0).eq_of_le hne le_sup_left).symm))⟩
    refine ⟨C0R.sIntEquiv e 𝔪 (g.gen P), ?_⟩
    have := congrArg (Ideal.map (C0R.sIntEquiv e 𝔪)) (g.span_gen P hE)
    rw [Ideal.map_span, Set.image_singleton, C0R.map_map_sIntEquiv, hPP] at this
    exact this
  set u' := C0R.sIntEquiv e 𝔪 u
  have hu' : IsUnit u' := hu.map _
  have nonsix' : ∀ b : F₀, b ^ 6 ≠ (u' : F₀) := by
    intro b hb
    apply hsix (e.symm b)
    rw [← map_pow, hb, C0R.sIntEquiv_coe, RingEquiv.symm_apply_apply]
  obtain ⟨j, hj⟩ := kummer_core F₀ hζ' hK' (ι.comp (e.symm : F₀ →+* F)) h𝔪' six' hprin' u' hu'
    nonsix'
  refine ⟨j, fun α hα0 hα hext => ?_⟩
  have hα' : eO α - 1 ∈ 𝔪' ^ j := by
    rw [← Ideal.map_pow]
    have := Ideal.mem_map_of_mem eO hα
    rwa [map_sub, map_one] at this
  have := hj (eO α) hα'
  rw [← L3K.residueSymbol_transport e ι 𝔪 h6 u _ hext, Ideal.map_span, Set.image_singleton]
  exact this

end L3L

end ArtinPrimitiveRoots

end
end
end

section
section
/-! # L3M_DevK: Lemma 3.3 for S-units, `exists_cutoff_residueSymbol_span_eq_one_of_isUnit` (L3L's `kummer`) -/

namespace ArtinPrimitiveRoots

open NumberField

theorem exists_cutoff_residueSymbol_span_eq_one_of_isUnit (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∀ u : SInt 𝔪, IsUnit u → ∃ j : ℕ, ∀ α : 𝓞 F, α - 1 ∈ 𝔪 ^ j →
      residueSymbol ι 𝔪 (Ideal.span {α}) u = 1
  := L3L.kummer n hn0 hn F ι

end ArtinPrimitiveRoots

end
end

section
open ArtinPrimitiveRoots

open NumberField

theorem solution (n : ℕ) (hn0 : 0 < n) (hn : 12 ∣ n)
    (F : Type*) [Field F] [NumberField F] [IsCyclotomicExtension {n} ℚ F] (ι : F →+* ℂ) :
  ∃ N₀ : ℕ, ∀ 𝔪 : Ideal (𝓞 F), 𝔪 ≠ ⊥ → SmallPrimesDvd N₀ 𝔪 → ∀ g : AllowedGen ι 𝔪,
    ∀ u : SInt 𝔪, IsUnit u → ∃ j : ℕ, ∀ α : 𝓞 F, α - 1 ∈ 𝔪 ^ j →
      residueSymbol ι 𝔪 (Ideal.span {α}) u = 1
  := by
  exact ArtinPrimitiveRoots.exists_cutoff_residueSymbol_span_eq_one_of_isUnit n hn0 hn F ι

end
