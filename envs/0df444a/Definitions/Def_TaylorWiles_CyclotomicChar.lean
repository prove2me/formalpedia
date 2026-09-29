-- Prove2me | Definitions.Def_TaylorWiles_CyclotomicChar
-- name    : TaylorWiles_CyclotomicChar
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/6a3873e5-7c97-54c8-87d9-a96a84cd4d30
-- title:
--   Mod-m cyclotomic character and cyclotomic level structures
-- statement:
--   Throughout, $L$ is a Galois number field over $\mathbb{Q}$. Given $m$ with $m \neq 0$ and $\zeta \in \mathcal{O}_L$ with `IsPrimitiveRoot ζ m`, [`TaylorWiles.cycloChar`](../def/TaylorWiles_CyclotomicChar.html#L21) is the monoid homomorphism $(L \simeq_{\mathbb{Q}} L) \to (\mathbb{Z}/m)^\times$ obtained by letting $\mathrm{Gal}(L/\mathbb{Q})$ act on $\mathcal{O}_L$ by $\mathbb{Z}$-algebra automorphisms and composing with Mathlib's `IsPrimitiveRoot.autToPow`; `cycloChar_spec` records the defining property $\zeta^{(\chi(\sigma)).\mathrm{val}} = \sigma \bullet \zeta$. Two immediate consequences are isolated: for $m \neq 1$, every $\sigma$ in the kernel fixes $\zeta$, and every commutator $⁅g,h⁆$ lies in the kernel, the target being abelian. Helper lemmas compute $\#(\mathbb{Z}/(Q \cap \mathbb{Z})) = \ell$ for a prime $Q$ of $\mathcal{O}_L$ lying over $(\ell)$, and show $m \notin Q$ when $\ell \nmid m$.
--
--   `modEq_one_of_realizesCyclicAt` is the resulting congruence: if $\zeta$ is a primitive $m$-th root of unity with $m \neq 1$, $\sigma$ lies in $\ker(\chi)$, $\ell \nmid m$, and `RealizesCyclicAt L σ ℓ` holds — that is, $\ell$ is prime and for every prime $Q$ of $\mathcal{O}_L$ over $(\ell)$ with finite residue field some power $\sigma^k$, with $k$ coprime to $\mathrm{ord}(\sigma)$, is conjugate to the arithmetic Frobenius at $Q$ — then $\ell \equiv 1 \pmod m$. The argument compares $\mathrm{Frob}_Q \bullet \zeta = \zeta^\ell$ with the fact that $\mathrm{Frob}_Q$, being conjugate to an element of the normal subgroup $\ker(\chi)$, fixes $\zeta$.
--
--   The structure `CyclotomicLevelStructure L p n S` packages a subgroup $N \le \mathrm{Gal}(L/\mathbb{Q})$ together with two theorems as fields: $N$ contains all commutators, and every $\sigma \in N$ and prime $\ell \notin S$ realized cyclically by $\sigma$ satisfies $\ell \equiv 1 \pmod{p^n}$. For $p$ prime with $p \in S$ and $\zeta$ a primitive $p^n$-th root of unity in $\mathcal{O}_L$, `cyclotomicLevelStructureOfIsPrimitiveRoot` produces such a structure with $N = \ker(\chi_{p^n})$, the case $n = 0$ being trivial.
--
--   **Relation to Mathlib.** The character is built from Mathlib's `IsPrimitiveRoot.autToPow` together with the Galois action on the ring of integers; `CyclotomicLevelStructure` and the predicate `RealizesCyclicAt` it refers to are the project's own notions.
--
--   **Where it is used.** These definitions supply the arithmetic half of the construction of Taylor–Wiles primes: a subgroup containing the commutator subgroup inside which every cyclically realized prime is $\equiv 1 \pmod{p^n}$, so that the existence of a Taylor–Wiles seed for a residual representation is reduced to a condition on the image of that representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TaylorWiles_CyclotomicChar.lean

import Definitions.Def_TaylorWiles_Primes
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise
open scoped commutatorElement

open Matrix MatrixGroups

namespace TaylorWiles

open NumberField FrobeniusDensity Ideal

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

section CycloChar

variable {m : ℕ} [NeZero m] {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ m)

noncomputable def cycloChar : (L ≃ₐ[ℚ] L) →* (ZMod m)ˣ :=
  (hζ.autToPow ℤ).comp (MulSemiringAction.toAlgAut (L ≃ₐ[ℚ] L) ℤ (𝓞 L))

omit [IsGalois ℚ L] in

lemma cycloChar_spec (σ : L ≃ₐ[ℚ] L) :
    ζ ^ ((cycloChar hζ σ : ZMod m)).val = σ • ζ := by
  simp [cycloChar]

omit [IsGalois ℚ L] in

lemma smul_eq_self_of_mem_ker_cycloChar (hm : m ≠ 1) {σ : L ≃ₐ[ℚ] L}
    (hσ : σ ∈ (cycloChar hζ).ker) : σ • ζ = ζ := by
  have h1 : cycloChar hζ σ = 1 := MonoidHom.mem_ker.mp hσ
  have h2 := cycloChar_spec hζ σ
  rw [h1, Units.val_one, ZMod.val_one'' hm, pow_one] at h2
  exact h2.symm

omit [IsGalois ℚ L] in

lemma commutatorElement_mem_ker_cycloChar (g h : L ≃ₐ[ℚ] L) :
    ⁅g, h⁆ ∈ (cycloChar hζ).ker := by
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)

end CycloChar

section Frobenius

variable {m : ℕ} [NeZero m]

omit [NumberField L] [IsGalois ℚ L] in

lemma natCard_quotient_under_eq {ℓ : ℕ} (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] : Nat.card (ℤ ⧸ Q.under ℤ) = ℓ := by
  rw [← Q.over_def (ratPrimeIdeal ℓ)]
  exact (Nat.card_congr (Int.quotientSpanNatEquivZMod ℓ).toEquiv).trans (Nat.card_zmod ℓ)

omit [NumberField L] [IsGalois ℚ L] [NeZero m] in

lemma natCast_notMem_of_not_dvd {ℓ : ℕ} (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver (ratPrimeIdeal ℓ)] (h : ¬ ℓ ∣ m) : ((m : ℕ) : 𝓞 L) ∉ Q := by
  intro hmem
  apply h
  have h1 : ((m : ℤ)) ∈ Q.under ℤ := Ideal.mem_comap.mpr (by rwa [map_natCast])
  rw [← Q.over_def (ratPrimeIdeal ℓ), Ideal.mem_span_singleton] at h1
  exact_mod_cast h1

theorem modEq_one_of_realizesCyclicAt {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ m) (hm : m ≠ 1)
    {σ : L ≃ₐ[ℚ] L} (hσ : σ ∈ (cycloChar hζ).ker) {ℓ : ℕ} (hℓm : ¬ ℓ ∣ m)
    (hreal : RealizesCyclicAt L σ ℓ) : ℓ ≡ 1 [MOD m] := by
  obtain ⟨hℓp, hQ⟩ := hreal
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  obtain ⟨⟨Q, hQp, hQl⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 L) (ratPrimeIdeal ℓ)
  haveI := hQp
  haveI := hQl
  haveI : Finite ((𝓞 L) ⧸ Q) := finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓp)
  obtain ⟨k, -, hconj⟩ := hQ Q hQp hQl ‹_›
  have hker : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q ∈ (cycloChar hζ).ker := by
    obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
    rw [← hτ]
    exact (MonoidHom.normal_ker _).conj_mem _ (pow_mem hσ k) τ
  have hfix : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q • ζ = ζ :=
    smul_eq_self_of_mem_ker_cycloChar hζ hm hker
  have hpow : arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q • ζ = ζ ^ ℓ := by
    have h1 := (IsArithFrobAt.arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q).apply_of_pow_eq_one
      hζ.pow_eq_one (natCast_notMem_of_not_dvd (ℓ := ℓ) Q hℓm)
    rwa [MulSemiringAction.toAlgHom_apply, natCard_quotient_under_eq (ℓ := ℓ) Q] at h1
  have hord : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨m, Nat.pos_of_ne_zero (NeZero.ne m), hζ.pow_eq_one⟩
  have heq : ζ ^ ℓ = ζ ^ 1 := by rw [pow_one, ← hpow, hfix]
  rw [hζ.eq_orderOf]
  exact hord.pow_eq_pow_iff_modEq.mp heq

end Frobenius

variable (L) in

structure CyclotomicLevelStructure (p n : ℕ) (S : Finset ℕ) where
  N : Subgroup (L ≃ₐ[ℚ] L)
  commutator_mem : ∀ g h : L ≃ₐ[ℚ] L, ⁅g, h⁆ ∈ N
  congruent : ∀ σ ∈ N, ∀ ℓ : ℕ, ℓ ∉ S → RealizesCyclicAt L σ ℓ → ℓ ≡ 1 [MOD p ^ n]

variable (L) in

noncomputable def cyclotomicLevelStructureOfIsPrimitiveRoot (p n : ℕ) [hp : Fact p.Prime]
    {S : Finset ℕ} (hpS : p ∈ S) {ζ : 𝓞 L} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    CyclotomicLevelStructure L p n S :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  { N := (cycloChar hζ).ker
    commutator_mem := commutatorElement_mem_ker_cycloChar hζ
    congruent := by
      intro σ hσ ℓ hℓS hreal
      rcases Nat.eq_zero_or_pos n with hn | hn
      · rw [hn, pow_zero]
        exact Nat.modEq_one
      refine modEq_one_of_realizesCyclicAt hζ (Nat.one_lt_pow hn.ne' hp.out.one_lt).ne' hσ
        (fun hdvd => ?_) hreal
      obtain ⟨hℓp, -⟩ := hreal
      exact hℓS (((Nat.prime_dvd_prime_iff_eq hℓp hp.out).mp
        (hℓp.dvd_of_dvd_pow hdvd)) ▸ hpS) }

end TaylorWiles


