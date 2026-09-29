-- Prove2me | Definitions.Def_NumberField_NormResidueCharacter
-- name    : NumberField_NormResidueCharacter
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/3fe7b251-eb45-5c83-ba75-98a16821e889
-- title:
--   Norm-residue characters on narrow ray class groups
-- statement:
--   Throughout, $K$ is a number field and $m$ a nonzero natural number. The modulus used here is `fm K m`, the ideal $m\mathcal{O}_K =$ `Ideal.span {(m : 𝓞 K)}`, which is shown to be nonzero; the narrow ray class group of $K$ of modulus $m\mathcal{O}_K$ is thereby finite and is equipped with a `Fintype`. The homomorphism `nu` is the project's norm class character `normClassChar K m` taken at the modulus $m\mathcal{O}_K$ itself (via `dvd_refl`): it is the descent to the narrow ray class group of the multiplicative ray symbol built from `normClass K m`, which sends a height-one prime $v$ to the unit class of $N v =$ `Ideal.absNorm v.asIdeal` in $(\mathbb{Z}/m)^\times$ when $N v$ is coprime to $m$, and to $1$ otherwise. For a Dirichlet character $\psi$ modulo $m$ with values in $\mathbb{C}$, `chi K m ψ` is the composite $\psi \circ \nu$, a monoid homomorphism from the narrow ray class group to $\mathbb{C}$; it is multiplicative in $\psi$ and sends the trivial character to $1$. The accompanying computations identify the associated ideal function [`M4aP2.chiIdeal`](../def/NumberField_RayCharacterData.html#L20) of `chi K m ψ`: on a prime $v$ it is $0$ when $v \mid m\mathcal{O}_K$ and $\psi(N v \bmod m)$ otherwise (uniformly, $\psi(N v)$, since $\psi$ kills nonunits), and on a principal ideal $(\alpha)$ with $\alpha \neq 0$ and $\alpha - 1 \in m\mathcal{O}_K$ it is $\psi$ of the sign of $\mathrm{N}_{K/\mathbb{Q}}(\alpha)$. Correspondingly `paritySet ψ` is the empty set of real infinite places if $\psi(-1) = 1$ and the set of all of them otherwise; $\psi(-1)$ is shown to be $\pm 1$.
--
--   A second group of declarations works over a field $L$ that is an $m$-th cyclotomic extension of $K$, with $\zeta \in L$ a primitive $m$-th root of unity. Here `U0 K m hζ` is the image in $(\mathbb{Z}/m)^\times$ of the cyclotomic character `hζ.autToPow K` of $\mathrm{Gal}(L/K)$, a subgroup of cardinality $[L:K]$. It is proved that $N\mathfrak{P} \equiv 1 \pmod m$ for every prime $\mathfrak{P}$ of $L$ with $m \notin \mathfrak{P}$, that the fibre of primes of $L$ above a prime of $K$ is finite with at most $[L:K]$ elements (its cardinality being that of the set of primes over the corresponding ideal), that a prime of $L$ whose absolute norm is a rational prime has the same absolute norm as the prime of $K$ below it, and that `normClass K m v` lies in `U0` for every height-one prime $v$ of $K$ — via the cyclotomic index of an arithmetic Frobenius at a prime above $v$ — whence `nu` takes values in `U0` and its range is contained in `U0`.
--
--   **Relation to Mathlib.** Mathlib supplies `DirichletCharacter`, `Ideal.absNorm`, `IsPrimitiveRoot.autToPow` and the theory of primes over a prime in a Dedekind extension; the narrow ray class group, the ray symbol and the ideal-valued extension [`M4aP2.chiIdeal`](../def/NumberField_RayCharacterData.html#L20) used here are the project's own notions, and `U0` is simply the image of Mathlib's `IsPrimitiveRoot.autToPow`.
--
--   **Where it is used.** These characters supply the Hecke-character vocabulary used in the Artin/Langlands–Tunnell part of the argument, where Dirichlet characters modulo $m$ are pulled back to narrow ray class characters of a number field and compared with cyclotomic data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_NormResidueCharacter.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_NormClass
import Definitions.Def_NumberField_RayCharacterData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace NumberField.NormResidueChar

open NumberField NumberField.InfinitePlace IsDedekindDomain Deep.NTSupply
open LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K] (m : ℕ) [NeZero m]

abbrev fm : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)}

theorem fm_ne_bot : fm K m ≠ ⊥ := by
  rw [fm, Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast NeZero.ne m

instance finite_G : Finite (NarrowRayClassGroup K (fm K m)) := Deep.NTSupply.finite K (fm_ne_bot K m)

noncomputable instance fintype_G : Fintype (NarrowRayClassGroup K (fm K m)) := Fintype.ofFinite _

def nu : NarrowRayClassGroup K (fm K m) →* (ZMod m)ˣ := normClassChar K m (dvd_refl _)

def chi (ψ : DirichletCharacter ℂ m) : NarrowRayClassGroup K (fm K m) →* ℂ :=
  (Units.coeHom ℂ).comp ((MulChar.toUnitHom ψ).comp (nu K m))

theorem chi_apply (ψ : DirichletCharacter ℂ m) (g : NarrowRayClassGroup K (fm K m)) :
    chi K m ψ g = ψ ((nu K m g : (ZMod m)ˣ) : ZMod m) := by
  simp [chi]

theorem chi_mul (ψ θ : DirichletCharacter ℂ m) : chi K m (ψ * θ) = chi K m ψ * chi K m θ := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.mul_apply, chi_apply, chi_apply, chi_apply, MulChar.mul_apply]

theorem chi_one : chi K m 1 = 1 := by
  refine MonoidHom.ext fun g => ?_
  rw [chi_apply, MonoidHom.one_apply, MulChar.one_apply_coe]

variable {K m}

theorem dvd_fm_iff (v : HeightOneSpectrum (𝓞 K)) : v.asIdeal ∣ fm K m ↔ (m : 𝓞 K) ∈ v.asIdeal := by
  rw [fm, Ideal.dvd_span_singleton]

theorem absNorm_mem (v : HeightOneSpectrum (𝓞 K)) : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ∈ v.asIdeal :=
  Ideal.absNorm_mem v.asIdeal

theorem not_coprime_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : (m : 𝓞 K) ∈ v.asIdeal) :
    ¬ (Ideal.absNorm v.asIdeal).Coprime m := by
  intro hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have hg := Nat.gcd_eq_gcd_ab (Ideal.absNorm v.asIdeal) m
  rw [Nat.Coprime.gcd_eq_one hcop] at hg
  have h1' : (1 : 𝓞 K) = (Ideal.absNorm v.asIdeal : 𝓞 K) * (Nat.gcdA (Ideal.absNorm v.asIdeal) m : 𝓞 K) +
      (m : 𝓞 K) * (Nat.gcdB (Ideal.absNorm v.asIdeal) m : 𝓞 K) := by
    have := congrArg (fun z : ℤ => (z : 𝓞 K)) hg
    push_cast at this
    exact this
  rw [h1']
  exact v.asIdeal.add_mem (v.asIdeal.mul_mem_right _ (absNorm_mem v)) (v.asIdeal.mul_mem_right _ hv)

theorem coprime_of_not_mem {v : HeightOneSpectrum (𝓞 K)} (hv : (m : 𝓞 K) ∉ v.asIdeal) :
    (Ideal.absNorm v.asIdeal).Coprime m :=
  absNorm_coprime_of_not_dvd K m v (by rwa [dvd_fm_iff] at *)

theorem mk0_prime_mem_iff {𝔣 : Ideal (𝓞 K)} (v : HeightOneSpectrum (𝓞 K))
    (h : (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0) :
    Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) h ∈ coprimeToModulus K 𝔣 ↔ ¬ v.asIdeal ∣ 𝔣 := by
  rw [mem_coprimeToModulus_iff]
  constructor
  · intro hc hv
    have := hc v hv
    rw [Units.val_mk0, FractionalIdeal.count_self] at this
    exact one_ne_zero this
  · intro hv w hw
    rw [Units.val_mk0]
    exact FractionalIdeal.count_maximal_coprime K w (fun h => hv (h ▸ hw))

theorem chiIdeal_prime {𝔣 : Ideal (𝓞 K)} (χ : NarrowRayClassGroup K 𝔣 →* ℂ)
    (v : HeightOneSpectrum (𝓞 K)) :
    M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) =
      if hv : v.asIdeal ∣ 𝔣 then 0 else χ (primeClass K 𝔣 v hv) := by
  have h0 : (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact v.ne_bot
  rw [M4aP2.chiIdeal, dif_pos h0]
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [dif_pos hv, dif_neg (by rw [mk0_prime_mem_iff]; exact not_not.mpr hv)]
  · have hc : Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) h0 ∈ coprimeToModulus K 𝔣 := by
      rwa [mk0_prime_mem_iff]
    rw [dif_neg hv, dif_pos hc, primeClass]
    have heq : (⟨Units.mk0 _ h0, hc⟩ : ↥(coprimeToModulus K 𝔣)) =
        ⟨primeUnit K v, primeUnit_mem_coprimeToModulus K hv⟩ :=
      Subtype.ext (Units.ext (by rw [Units.val_mk0, primeUnit_val]))
    rw [heq]

theorem chi_primeClass (ψ : DirichletCharacter ℂ m) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ v.asIdeal ∣ fm K m) :
    chi K m ψ (primeClass K (fm K m) v hv) = ψ (Ideal.absNorm v.asIdeal : ZMod m) := by
  rw [chi_apply, nu, normClassChar_primeClass, normClass_coe]
  exact coprime_of_not_mem (by rwa [dvd_fm_iff] at hv)

theorem chiIdeal_chi (ψ : DirichletCharacter ℂ m) (v : HeightOneSpectrum (𝓞 K)) :
    M4aP2.chiIdeal K (fm K m) (chi K m ψ) (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) =
      ψ (Ideal.absNorm v.asIdeal : ZMod m) := by
  rw [chiIdeal_prime]
  by_cases hv : v.asIdeal ∣ fm K m
  · rw [dif_pos hv, eq_comm]
    apply MulChar.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    exact not_coprime_of_mem ((dvd_fm_iff v).mp hv)
  · rw [dif_neg hv, chi_primeClass]

def paritySet (ψ : DirichletCharacter ℂ m) : Finset {w : InfinitePlace K // w.IsReal} :=
  if ψ (-1) = 1 then ∅ else Finset.univ

theorem psi_neg_one_sq (ψ : DirichletCharacter ℂ m) : ψ (-1) * ψ (-1) = 1 := by
  rw [← map_mul, neg_mul_neg, one_mul, map_one]

theorem psi_neg_one_eq (ψ : DirichletCharacter ℂ m) : ψ (-1) = 1 ∨ ψ (-1) = -1 := by
  have h := psi_neg_one_sq ψ
  have : (ψ (-1) - 1) * (ψ (-1) + 1) = 0 := by ring_nf; rw [sq, h]; ring
  rcases mul_eq_zero.mp this with h1 | h1
  · left; exact sub_eq_zero.mp h1
  · right; exact eq_neg_of_add_eq_zero_left h1

theorem chiIdeal_chi_span (ψ : DirichletCharacter ℂ m) {α : 𝓞 K} (hα : α ≠ 0)
    (h1 : α - 1 ∈ fm K m) :
    M4aP2.chiIdeal K (fm K m) (chi K m ψ) ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ψ ((SignType.sign (Algebra.norm ℤ α) : ℤ) : ZMod m) := by
  have hspan : (Ideal.span {α} : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hα
  have h0 : ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hspan
  have hcmem : Units.mk0 _ h0 ∈ coprimeToModulus K (fm K m) := by
    have h := principalUnit_mem_coprimeToModulus K hα h1
    rw [mem_coprimeToModulus_iff] at h ⊢
    intro v hv
    have := h v hv
    rwa [principalUnit_val] at this
  rw [M4aP2.chiIdeal, dif_pos h0, dif_pos hcmem, chi_apply, nu, normClassChar, raySymbolDescend_mk,
    raySymbolHom_apply]
  have hcop : (Ideal.span {α} : Ideal (𝓞 K)) ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1' : α - (α - 1) = 1 := by ring
    exact h1' ▸ Submodule.sub_mem _
      (Ideal.mem_sup_left (Ideal.subset_span rfl))
      (Ideal.mem_sup_right h1)
  have hval : ((⟨Units.mk0 _ h0, hcmem⟩ : ↥(coprimeToModulus K (fm K m))) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) =
      Units.mk0 _ h0 := rfl
  rw [hval, Units.val_mk0, raySymbol_normClass_coe K m hspan hcop, Ideal.absNorm_span_singleton]
  congr 1

  have hN1 : ((Algebra.norm ℤ α : ℤ) : ZMod m) = 1 := norm_int_cast_eq_one_of_sub_one_mem K m h1
  have habs : ((Algebra.norm ℤ α).natAbs : ℤ) = (SignType.sign (Algebra.norm ℤ α) : ℤ) * Algebra.norm ℤ α := by
    rw [← Int.sign_eq_sign, Int.sign_mul_self_eq_natAbs]
  rw [← Int.cast_natCast (R := ZMod m) (Algebra.norm ℤ α).natAbs, habs, Int.cast_mul, hN1, mul_one]

section Cyclo

variable {L : Type} [Field L] [NumberField L] [Algebra K L] [IsCyclotomicExtension {m} K L]

theorem absNorm_cast_eq_one {ζ : L} (hζ : IsPrimitiveRoot ζ m) (w : HeightOneSpectrum (𝓞 L))
    (hw : (m : 𝓞 L) ∉ w.asIdeal) : (Ideal.absNorm w.asIdeal : ZMod m) = 1 := by
  have hζ' : IsPrimitiveRoot hζ.toInteger m := hζ.toInteger_isPrimitiveRoot
  have hcop : (Ideal.absNorm w.asIdeal).Coprime m := coprime_of_not_mem hw
  have hN1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
  haveI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  have hinj := Ideal.rootsOfUnityMapQuot_injective (I := w.asIdeal) m hN1 hcop
  have hdvd := Subgroup.card_dvd_of_injective _ hinj
  rw [hζ'.card_rootsOfUnity, Nat.card_units, ← Submodule.cardQuot_apply,
    ← Ideal.absNorm_apply] at hdvd
  have hpos : 1 ≤ Ideal.absNorm w.asIdeal := Nat.one_le_iff_ne_zero.mpr (by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot)
  have : ((Ideal.absNorm w.asIdeal : ℕ) : ZMod m) = ((Ideal.absNorm w.asIdeal - 1 + 1 : ℕ) : ZMod m) := by
    rw [Nat.sub_add_cancel hpos]
  rw [this, Nat.cast_add, Nat.cast_one, (ZMod.natCast_eq_zero_iff _ _).mpr hdvd, zero_add]

theorem mem_primesOver_of_under_eq {w : HeightOneSpectrum (𝓞 L)} {v : HeightOneSpectrum (𝓞 K)}
    (h : w.under (𝓞 K) = v) : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) := by
  refine ⟨w.isPrime, ⟨?_⟩⟩
  rw [← h]
  rfl

include m in

theorem ncard_primesOver_le (v : HeightOneSpectrum (𝓞 K)) :
    (v.asIdeal.primesOver (𝓞 L)).ncard ≤ Module.finrank K L := by
  haveI : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  haveI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 L) (L ≃ₐ[K] L)
  rw [IsGalois.card_aut_eq_finrank] at h
  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have hne : v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    omega
  calc (v.asIdeal.primesOver (𝓞 L)).ncard
      ≤ (v.asIdeal.primesOver (𝓞 L)).ncard * (v.asIdeal.ramificationIdxIn (𝓞 L) * v.asIdeal.inertiaDegIn (𝓞 L)) :=
        Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
    _ = Module.finrank K L := h

theorem ncard_fibre_eq (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.ncard = (v.asIdeal.primesOver (𝓞 L)).ncard := by
  have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal) {w | w.under (𝓞 K) = v} :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  rw [← hinj.ncard_image]
  congr 1
  ext I
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mem_primesOver_of_under_eq hw
  · rintro ⟨hI, hIo⟩
    have hIbot : I ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot I
    refine ⟨⟨I, hI, hIbot⟩, ?_, rfl⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal]
    exact hIo.over.symm

theorem finite_fibre (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.Finite := by
  have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 L) => w.asIdeal) {w | w.under (𝓞 K) = v} :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  refine Set.Finite.of_finite_image ?_ hinj
  refine (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact mem_primesOver_of_under_eq hw

include m in
theorem ncard_fibre_le (v : HeightOneSpectrum (𝓞 K)) :
    {w : HeightOneSpectrum (𝓞 L) | w.under (𝓞 K) = v}.ncard ≤ Module.finrank K L := by
  rw [ncard_fibre_eq]
  exact ncard_primesOver_le (m := m) v

theorem absNorm_under_eq_of_prime (w : HeightOneSpectrum (𝓞 L)) (hp : (Ideal.absNorm w.asIdeal).Prime) :
    Ideal.absNorm (w.under (𝓞 K)).asIdeal = Ideal.absNorm w.asIdeal := by
  haveI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
  set v := w.under (𝓞 K)
  haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 L ⧸ w.asIdeal) := Ideal.Quotient.field _
  have hpow : Nat.card (𝓞 L ⧸ w.asIdeal) =
      Nat.card (𝓞 K ⧸ v.asIdeal) ^ Module.finrank (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ w.asIdeal) :=
    Module.natCard_eq_pow_finrank
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← Submodule.cardQuot_apply,
    ← Ideal.absNorm_apply] at hpow
  rw [hpow] at hp
  have hf := Nat.Prime.eq_one_of_pow hp
  rw [hpow, hf, pow_one]

variable (K m)

def U0 {ζ : L} (hζ : IsPrimitiveRoot ζ m) : Subgroup (ZMod m)ˣ := (hζ.autToPow K).range

theorem card_U0 {ζ : L} (hζ : IsPrimitiveRoot ζ m) : Nat.card (U0 K m hζ) = Module.finrank K L := by
  haveI : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  rw [U0, ← IsGalois.card_aut_eq_finrank K L, ← Nat.card_range_of_injective (hζ.autToPow_injective K)]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => MonoidHom.mem_range))

theorem normClass_mem_U0 {ζ : L} (hζ : IsPrimitiveRoot ζ m) (v : HeightOneSpectrum (𝓞 K)) :
    normClass K m v ∈ U0 K m hζ := by
  by_cases hv : (Ideal.absNorm v.asIdeal).Coprime m
  · haveI : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
    haveI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
      IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
    haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot

    have hker : RingHom.ker (algebraMap (𝓞 K) (𝓞 L)) ≤ v.asIdeal := by
      have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 L)) := by
        intro x y hxy
        have h' : algebraMap (𝓞 K) L x = algebraMap (𝓞 K) L y := by
          rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L,
            IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L) L, hxy]
        rw [IsScalarTower.algebraMap_apply (𝓞 K) K L, IsScalarTower.algebraMap_apply (𝓞 K) K L] at h'
        exact RingOfIntegers.coe_injective ((algebraMap K L).injective h')
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    obtain ⟨Q, hQmax, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
    haveI : Q.IsMaximal := hQmax
    have hunder : Q.under (𝓞 K) = v.asIdeal := hQv
    have hmQ : (m : 𝓞 L) ∉ Q := by
      intro hmem
      apply not_coprime_of_mem (K := K) (m := m) (v := v) _ hv
      have : algebraMap (𝓞 K) (𝓞 L) (m : 𝓞 K) ∈ Q := by rwa [map_natCast]
      rw [← Ideal.mem_comap] at this
      rw [← hunder]
      exact this
    haveI : Q.LiesOver v.asIdeal := ⟨hunder.symm⟩
    haveI : Finite (𝓞 L ⧸ Q) := Q.finiteQuotientOfFreeOfNeBot
      (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q)
    set φ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q with hφdef
    have hφ : IsArithFrobAt (𝓞 K) φ Q := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q
    have hζ' : IsPrimitiveRoot hζ.toInteger m := hζ.toInteger_isPrimitiveRoot
    have hcardK : Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) = Ideal.absNorm v.asIdeal := by
      rw [hunder, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hφζ' : φ • hζ.toInteger = hζ.toInteger ^ Ideal.absNorm v.asIdeal := by
      have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hφ hζ'.pow_eq_one hmQ
      rw [hcardK] at h
      exact h
    have hφζ : φ ζ = ζ ^ Ideal.absNorm v.asIdeal := by
      have h := congrArg (fun x : 𝓞 L => (x : L)) hφζ'
      have h2 : ((φ • hζ.toInteger : 𝓞 L) : L) = φ ζ := rfl
      simpa [h2, hζ.coe_toInteger] using h
    have hspec := hζ.autToPow_spec K φ
    rw [hφζ] at hspec
    have hmod : ((hζ.autToPow K φ : ZMod m)).val ≡ Ideal.absNorm v.asIdeal [MOD m] := by
      have hm : 0 < m := NeZero.pos m
      rw [← pow_mod_orderOf ζ ((hζ.autToPow K φ : ZMod m)).val, ← pow_mod_orderOf ζ (Ideal.absNorm v.asIdeal),
        ← hζ.eq_orderOf] at hspec
      exact hζ.pow_inj (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) hspec
    have heq : hζ.autToPow K φ = normClass K m v := by
      apply Units.ext
      rw [normClass_coe K m v hv, ← ZMod.natCast_zmod_val ((hζ.autToPow K φ : ZMod m)),
        ZMod.natCast_eq_natCast_iff]
      exact hmod
    rw [← heq]
    exact ⟨φ, rfl⟩
  · rw [normClass, dif_neg hv]
    exact one_mem _

theorem nu_mem_U0 {ζ : L} (hζ : IsPrimitiveRoot ζ m) (g : NarrowRayClassGroup K (fm K m)) :
    nu K m g ∈ U0 K m hζ := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
  have hmk : (QuotientGroup.mk y : NarrowRayClassGroup K (fm K m)) = NarrowRayClassGroup.mk K (fm K m) y := rfl
  rw [hmk, nu, normClassChar, raySymbolDescend_mk, raySymbolHom_apply, raySymbol]
  refine finprod_induction (· ∈ U0 K m hζ) (one_mem _) (fun x y hx hy => mul_mem hx hy) ?_
  intro v
  exact zpow_mem (normClass_mem_U0 K m hζ v) _

theorem range_nu_le_U0 {ζ : L} (hζ : IsPrimitiveRoot ζ m) : (nu K m).range ≤ U0 K m hζ := by
  rintro _ ⟨g, rfl⟩
  exact nu_mem_U0 K m hζ g

end Cyclo

end NumberField.NormResidueChar

end


