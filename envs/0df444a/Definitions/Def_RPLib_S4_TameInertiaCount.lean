-- Prove2me | Definitions.Def_RPLib_S4_TameInertiaCount
-- name    : RPLib_S4_TameInertiaCount
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:49:17.990078+00:00
-- url     : https://prove2.me/theorems/41a82eac-9f6b-487f-9063-362b3e953e9f
-- title:
--   The inertia orbit of an $N$-th root of the small root is full
-- statement:
--   Let $S/R$ be a finite Galois extension of Dedekind domains with group $G$, $P$ a prime of $S$ with finite residue field, $F \in K$ with a pole of order $c$ at $P \cap R$ and $\gcd(c, N) = 1$, $w$ the unique root of $X^{p+1} - F X + 1$ with $v_P(w) < 1$, and $z^N = w$. The file proves $v_P(w) = |I|\,c$, while $v_P(z)$ is divisible by the order of the stabiliser of $z$ in $I = I(P)$, hence $N$ divides the size of the $I$-orbit of $z$; as the orbit lies among the $N$-th roots of $w$, $$\forall \zeta,\ \zeta^N = 1 \implies \exists \tau \in I,\ \tau z = \zeta z.$$
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J.-P. Serre, Local Fields, GTM 67, Springer (1979), Chapter I, Sections 4 and 7, and Chapter IV, Section 2

import Mathlib
import Definitions.Def_RPLib_S4_TameInertiaFix
import Definitions.Def_RPLib_S4_SwanGlobVal

/-!
# Tame inertia, part Count: the inertia orbit of an `N`-th root of the small root is full (S4-PD item (2), T8 count)

Let `S / R` be a finite Galois extension of Dedekind domains with group `G`, `P` a prime of `S` with finite residue
field, `F = a ∈ K = Frac R` a pole of order `c` at `P ∩ R` with `gcd(c, N) = 1`, `w` the unique root of
`X^(p+1) - F X + 1` with `v_P(w) < 1`, and `z^N = w`. Then `v_P(w) = |I| c` (`adicAdd_small_root`), while `v_P(z)`
is divisible by the order of the stabilizer `H` of `z` in `I = I(P)` (Swan `exists_adicAdd_fixed_eq`), so
`N |H| k = |I| c = |I : H| |H| c`, hence `N ∣ |I z|`; the orbit lies in the `N`-th roots of `w`, so it is all of them:
`∃ τ ∈ I, τ z = ζ z` for every `ζ` with `ζ^N = 1` (`exists_inertia_smul_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial IsDedekindDomain WithZero

namespace RamanujanPetersson
namespace TameInertia

open Swan

noncomputable section

section Small

variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L] [IsFractionRing S L]

/-- The small root of the trinomial has `v_P(w) = -v_P(F)` (additive valuations). -/
theorem adicAdd_small_root (P : HeightOneSpectrum S) {p : ℕ} (hp : 0 < p) {F w : L}
    (hF : 1 < P.valuation L F) (hw : (trin p F).IsRoot w) (hwv : P.valuation L w < 1) (t : ℤ)
    (ht : adicAdd P F = ((-t : ℤ) : WithTop ℤ)) : adicAdd P w = (t : WithTop ℤ) := by
  have hw' := (trin_isRoot_iff p F w).1 hw
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw'
  have hF0 : F ≠ 0 := by
    rintro rfl
    rw [map_zero] at hF
    exact not_lt_of_ge zero_le hF
  have hwv0 : P.valuation L w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
  have hFv0 : P.valuation L F ≠ 0 := (Valuation.ne_zero_iff _).2 hF0
  have hc0 : 0 < log (P.valuation L F) := by
    rw [← exp_log hFv0, ← exp_zero, exp_lt_exp] at hF
    exact hF
  have ha0 : log (P.valuation L w) < 0 := by
    rw [← exp_log hwv0, ← exp_zero, exp_lt_exp] at hwv
    exact hwv
  rcases trin_val_cases (P.valuation L) hw' (exp_log hwv0).symm (exp_log hFv0).symm hc0 with h | h
  · rw [adicAdd_apply, negLogV_of_ne P hF0] at ht
    have ht' := WithTop.coe_inj.1 ht
    rw [adicAdd_apply, negLogV_of_ne P hw0, h, WithTop.coe_inj]
    linarith
  · exfalso
    have hp' : (0 : ℤ) < p := by exact_mod_cast hp
    have := mul_neg_of_pos_of_neg hp' ha0
    linarith

end Small

section Count

variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
  {K L : Type*} [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [MulSemiringAction G L]
  (hc : ∀ (σ : G) (s : S), σ • algebraMap S L s = algebraMap S L (σ • s))
  (P : HeightOneSpectrum S) [Finite (S ⧸ P.asIdeal)]

include R hc in
/-- **T8 count.** The inertia orbit of an `N`-th root `z` of the small root `w` contains `ζ z` for every
`N`-th root of unity `ζ`, when the pole order `c` of `a` at `P ∩ R` is prime to `N`. -/
theorem exists_inertia_smul_eq {p : ℕ} (hp : 0 < p) {N : ℕ} (hN : 0 < N) {a : K} {c : ℕ}
    (hcN : Nat.Coprime c N) (ha : adicAdd (P.under R) a = ((-(c : ℤ) : ℤ) : WithTop ℤ))
    (hF : 1 < P.valuation L (algebraMap K L a)) (hs : (trin p (algebraMap K L a)).Splits)
    (hfix : ∀ σ : G, σ • algebraMap K L a = algebraMap K L a)
    {w z ζ : L} (hw : (trin p (algebraMap K L a)).IsRoot w) (hwv : P.valuation L w < 1)
    (hz : z ^ N = w) (hζ : ζ ^ N = 1) :
    ∃ τ ∈ P.asIdeal.inertia G, τ • z = ζ * z := by
  classical
  have hw0 : w ≠ 0 := by
    rintro rfl
    have hw' := (trin_isRoot_iff p _ _).1 hw
    simp at hw'
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hz
    exact hw0 hz.symm
  -- the stabilizer of `z` in the inertia group
  set I := P.asIdeal.inertia G with hIdef
  let St : Subgroup I := MulAction.stabilizer I z
  let H : Subgroup G := St.map I.subtype
  have hH : H ≤ I := Subgroup.map_subtype_le _
  have hzH : ∀ h ∈ H, h • z = z := by
    rintro _ ⟨h, hh, rfl⟩
    exact hh
  have hHSt : Nat.card H = Nat.card St := Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hcard : Nat.card St * (MulAction.orbit I z).ncard = Nat.card I := by
    rw [← MulAction.index_stabilizer]
    exact Subgroup.card_mul_index St
  -- valuations
  obtain ⟨k, hk⟩ := exists_adicAdd_fixed_eq (R := R) hc P H hH z hzH hz0
  have hFv := adicAdd_algebraMap_eq (A := R) (L := L) G P a (-(c : ℤ)) ha
  have h1 : adicAdd P w = (((N : ℤ) * ((Nat.card H : ℤ) * k) : ℤ) : WithTop ℤ) := by
    rw [← hz, AddValuation.map_pow, hk, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have h2 : adicAdd P w = (((Nat.card I : ℤ) * c : ℤ) : WithTop ℤ) :=
    adicAdd_small_root P hp hF hw hwv _ (by rw [hFv]; congr 1; ring)
  have h3 : (N : ℤ) * ((Nat.card H : ℤ) * k) = (Nat.card I : ℤ) * c := WithTop.coe_inj.1 (h1.symm.trans h2)
  set O := (MulAction.orbit I z).ncard with hOdef
  have hH0 : (Nat.card H : ℤ) ≠ 0 := by
    have : 0 < Nat.card H := Nat.card_pos
    exact_mod_cast this.ne'
  have h4 : (Nat.card H : ℤ) * ((N : ℤ) * k) = (Nat.card H : ℤ) * ((O : ℤ) * c) := by
    rw [← hcard, ← hHSt] at h3
    push_cast at h3
    linear_combination h3
  have h5 := mul_left_cancel₀ hH0 h4
  have h6 : (N : ℤ) ∣ ((O * c : ℕ) : ℤ) := ⟨k, by push_cast; linarith⟩
  have h7 : N ∣ O := Nat.Coprime.dvd_of_dvd_mul_right hcN.symm (Int.natCast_dvd_natCast.1 h6)
  have hOfin : (MulAction.orbit I z).Finite := Set.finite_range _
  have hOpos : 0 < O := (Set.ncard_pos hOfin).2 ⟨z, MulAction.mem_orbit_self z⟩
  have hNO : N ≤ O := Nat.le_of_dvd hOpos h7
  -- the orbit lies in the `N`-th roots of `w`
  by_contra hne
  have hmem : ζ * z ∈ (nthRoots N w).toFinset := by
    rw [Multiset.mem_toFinset, mem_nthRoots hN, mul_pow, hζ, one_mul, hz]
  have hsub : MulAction.orbit I z ⊆ (((nthRoots N w).toFinset.erase (ζ * z) : Finset L) : Set L) := by
    rintro y ⟨τ, rfl⟩
    rw [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe, Multiset.mem_toFinset,
      mem_nthRoots hN]
    refine ⟨?_, fun h => hne ⟨τ, τ.2, h⟩⟩
    have hτw : (τ : G) • w = w := fix_small_root hc P hp hF hs τ.2 (hfix τ) hw hwv
    show ((τ : G) • z) ^ N = w
    rw [← smul_pow', hz, hτw]
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, Finset.card_erase_of_mem hmem] at hle
  have hcardN : (nthRoots N w).toFinset.card ≤ N := (Multiset.toFinset_card_le _).trans (card_nthRoots N w)
  omega

end Count

end

end TameInertia
end RamanujanPetersson


