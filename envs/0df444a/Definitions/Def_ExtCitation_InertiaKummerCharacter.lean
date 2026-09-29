-- Prove2me | Definitions.Def_ExtCitation_InertiaKummerCharacter
-- name    : ExtCitation_InertiaKummerCharacter
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/fef99313-1bd1-566e-ab53-16f1b1e49200
-- title:
--   Kummer character on pulled-back inertia at a prime q
-- statement:
--   Fix a prime $q$, write $G_q$ for the local Galois group $\mathrm{Gal}(\overline{\mathbb{Q}_q}/\mathbb{Q}_q)$ of the project (`primeLocalGaloisGroup`), $r$ for the homomorphism `primeLocalToGlobal` into $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by restricting a local automorphism along a fixed embedding $\overline{\mathbb{Q}} \hookrightarrow \overline{\mathbb{Q}_q}$, and $A_q$ for the valuation subring `primeLocalPlace q` of $\overline{\mathbb{Q}}$ pulled back from the valuation ring of $\overline{\mathbb{Q}_q}$ along that embedding. The first part of the module records the arithmetic of $A_q$: $q$ lies in its non-units, so its residue field has characteristic $q$; `toDecomp` is $r$ with codomain restricted to the decomposition subgroup of $A_q$ over $\mathbb{Q}$; a unit of $A_q$ killed by an exponent $m$ with $q \nmid m$ and reducing to $1$ equals $1$; consequently every $\sigma$ in the pullback $I' = r^{-1}(\,$`inertiaSubgroupIn`$\,)$ fixes each $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^m = 1$, $q \nmid m$, while any $\varphi$ with `IsFrobeniusAt` $\,r(\varphi)$, $q$ (that is, acting on the residue field by $x \mapsto x^q$) sends such $\zeta$ to $\zeta^q$.
--
--   The second part fixes, for a prime $p$, a $p$-th root $\alpha$ of $q$ in $\overline{\mathbb{Q}}$ (`kummerRoot`) and a primitive $p$-th root of unity $\zeta_p$ (`primRoot`), and defines the Kummer exponent `kummerExp` $p\,q\,g \in \mathbb{Z}/p$ of an automorphism $g$ of $\overline{\mathbb{Q}}$ by $g(\alpha) = \zeta_p^{a(g)}\alpha$ with $0 \le a(g) < p$, together with the characterising lemma that $g(\alpha) = \zeta_p^{n}\alpha$ forces `kummerExp` $= n$. Assuming $q \neq p$, `kummerCharacter` is the resulting homomorphism $I' \to \mathrm{Multiplicative}(\mathbb{Z}/p)$, $\sigma \mapsto a(r(\sigma))$; additivity rests on $I'$ fixing $\zeta_p$. Finally `kummerCharacter_conj` states that for $\varphi$ a Frobenius at $A_q$ and $\sigma \in I'$ with $\varphi\sigma\varphi^{-1} \in I'$ one has $\chi(\varphi\sigma\varphi^{-1}) = \chi(\sigma)^q$.
--
--   **Relation to Mathlib.** Mathlib supplies the decomposition and inertia subgroups of a valuation subring and the modular cyclotomic character; [`ValuationSubring.inertiaSubgroupIn`](../def/FLTPrelim_Ramification.html#L21) (the image of the inertia subgroup inside the full automorphism group) and [`ValuationSubring.IsFrobeniusAt`](../def/EllipticCurve_FrobeniusTrace.html#L51) are the project's own definitions, and the Kummer character of $q^{1/p}$ constructed here has no Mathlib counterpart.
--
--   **Where it is used.** These objects provide the mod-$p$ tame vocabulary at an auxiliary prime $q \neq p$: a distinguished homomorphism $I' \to \mathbb{Z}/p$ and its behaviour under Frobenius conjugation, used in the local computations at such primes that enter the Taylor–Wiles local conditions and the bounding of the relevant first cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ExtCitation_InertiaKummerCharacter.lean

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ExtCitation

section RootsOfUnity

variable (q : Nat.Primes)

theorem mem_nonunits_comap_iff {K L : Type*} [Field K] [Field L] {B : ValuationSubring L} {f : K →+* L} {x : K} :
    x ∈ (B.comap f).nonunits ↔ f x ∈ B.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀]
  constructor
  · rintro (rfl | h)
    · exact Or.inl (map_zero f)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ((map_eq_zero f).mp h)
    · exact Or.inr h

open scoped NNReal in

theorem natCast_mem_nonunits_primeLocalPlace : ((q : ℕ) : AlgebraicClosure ℚ) ∈ (primeLocalPlace q).nonunits := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hq : Valued.v ((q : ℕ) : PadicAlgCl q) = 1 / ((q : ℕ) : ℝ≥0) := PadicAlgCl.valuation_p q
  have hq2 : (2 : ℕ) ≤ (q : ℕ) := (Fact.out : (q : ℕ).Prime).two_le
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ (padicPlace (q : ℕ)).nonunits
  rw [padicPlace, mem_nonunits_comap_iff, ValuationSubring.mem_nonunits_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring _).lt_one_iff_lt_one]
  change Valued.v ((padicEmbedding q) ((q : ℕ) : AlgebraicClosure ℚ)) < 1
  rw [map_natCast, hq, div_lt_one (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq2)]
  exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two hq2

theorem charP_residueField_primeLocalPlace : CharP (IsLocalRing.ResidueField ↥(primeLocalPlace q)) q := by
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  have hq0 : ((q : ℕ) : IsLocalRing.ResidueField ↥(primeLocalPlace q)) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥(primeLocalPlace q)), IsLocalRing.residue_eq_zero_iff,
      ← ValuationSubring.coe_mem_nonunits_iff]
    have : ((((q : ℕ) : ↥(primeLocalPlace q)) : AlgebraicClosure ℚ)) = ((q : ℕ) : AlgebraicClosure ℚ) := by simp
    rw [this]
    exact natCast_mem_nonunits_primeLocalPlace q
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : (q : ℕ).Prime)).mpr hq0

theorem primeLocalPlace_eq_one_of_residue_eq_one {u : ↥(primeLocalPlace q)} {m : ℕ} (hum : u ^ m = 1)
    (hm : ¬ (q : ℕ) ∣ m) (hres : IsLocalRing.residue _ u = 1) : u = 1 := by
  haveI := charP_residueField_primeLocalPlace q
  have hmκ : (m : IsLocalRing.ResidueField ↥(primeLocalPlace q)) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff _ (q : ℕ)]
  by_contra hu
  have h1 : (∑ i ∈ Finset.range m, u ^ i) * (u - 1) = 0 := by rw [geom_sum_mul, hum, sub_self]
  have h2 : ∑ i ∈ Finset.range m, u ^ i = 0 := (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr hu)
  apply hmκ
  have := congrArg (IsLocalRing.residue ↥(primeLocalPlace q)) h2
  rw [map_sum, map_zero] at this
  simpa [map_pow, hres] using this

noncomputable abbrev toDecomp : primeLocalGaloisGroup q →* ↥((primeLocalPlace q).decompositionSubgroup ℚ) :=
  haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
  (primeLocalToGlobal q).codRestrict _ (fun g => localGaloisToGlobal_mem_decompositionSubgroup (q : ℕ) g)

theorem coe_toDecomp_smul (g : primeLocalGaloisGroup q) (a : ↥(primeLocalPlace q)) :
    ((toDecomp q g • a : ↥(primeLocalPlace q)) : AlgebraicClosure ℚ) = primeLocalToGlobal q g a := rfl

theorem mem_primeLocalPlace_of_pow_eq_one {ζ : AlgebraicClosure ℚ} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) :
    ζ ∈ primeLocalPlace q := by
  rw [← ValuationSubring.valuation_le_one_iff]
  have : ((primeLocalPlace q).valuation ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  exact ((pow_eq_one_iff_of_nonneg zero_le' hm).mp this).le

theorem inertiaPullback_smul_eq_of_pow_eq_one {σ : primeLocalGaloisGroup q}
    (hσ : σ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))
    {ζ : AlgebraicClosure ℚ} {m : ℕ} (hm : ¬ (q : ℕ) ∣ m) (hζ : ζ ^ m = 1) :
    primeLocalToGlobal q σ ζ = ζ := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hζA : ζ ∈ primeLocalPlace q := mem_primeLocalPlace_of_pow_eq_one q hm0 hζ
  set z : ↥(primeLocalPlace q) := ⟨ζ, hζA⟩
  have hzm : z ^ m = 1 := Subtype.ext (by simp [z, hζ])

  have hres : IsLocalRing.residue _ (toDecomp q σ • z) = IsLocalRing.residue _ z := by
    rw [IsLocalRing.ResidueField.residue_smul]
    rw [Subgroup.mem_comap, ValuationSubring.inertiaSubgroupIn, Subgroup.mem_map] at hσ
    obtain ⟨τ, hτ, hτσ⟩ := hσ
    have : toDecomp q σ = τ := Subtype.ext hτσ.symm
    rw [this]
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hτ
    have := congrArg (fun e => (e : IsLocalRing.ResidueField ↥(primeLocalPlace q) ≃+* _) (IsLocalRing.residue _ z)) hτ
    simpa using this

  have hw : (toDecomp q σ • z) * z ^ (m - 1) = 1 := by
    apply primeLocalPlace_eq_one_of_residue_eq_one q (m := m) _ hm
    · rw [map_mul, hres, ← map_mul, ← pow_succ', Nat.sub_add_cancel hm1, hzm, map_one]
    · rw [mul_pow, ← smul_pow', hzm, smul_one, one_mul, ← pow_mul, mul_comm, pow_mul, hzm, one_pow]
  have key : toDecomp q σ • z = z := by
    calc toDecomp q σ • z = (toDecomp q σ • z) * z ^ (m - 1) * z := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hm1, hzm, mul_one]
      _ = z := by rw [hw, one_mul]
  have := congrArg Subtype.val key
  rwa [coe_toDecomp_smul] at this

theorem frobenius_smul_eq_pow_of_pow_eq_one {φ : primeLocalGaloisGroup q}
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    {ζ : AlgebraicClosure ℚ} {m : ℕ} (hm : ¬ (q : ℕ) ∣ m) (hζ : ζ ^ m = 1) :
    primeLocalToGlobal q φ ζ = ζ ^ (q : ℕ) := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero _)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hζA : ζ ∈ primeLocalPlace q := mem_primeLocalPlace_of_pow_eq_one q hm0 hζ
  set z : ↥(primeLocalPlace q) := ⟨ζ, hζA⟩
  have hzm : z ^ m = 1 := Subtype.ext (by simp [z, hζ])
  have hres : IsLocalRing.residue _ (toDecomp q φ • z) = IsLocalRing.residue _ (z ^ (q : ℕ)) := by
    rw [IsLocalRing.ResidueField.residue_smul, map_pow]
    exact hφ.smul_residue_eq _
  have hw : (toDecomp q φ • z) * (z ^ (m - 1)) ^ (q : ℕ) = 1 := by
    apply primeLocalPlace_eq_one_of_residue_eq_one q (m := m) _ hm
    · rw [map_mul, hres, ← map_mul, ← mul_pow, ← pow_succ', Nat.sub_add_cancel hm1, hzm, one_pow, map_one]
    · rw [mul_pow, ← smul_pow', hzm, smul_one, one_mul, ← pow_mul, ← pow_mul,
        show (m - 1) * ((q : ℕ) * m) = m * ((m - 1) * (q : ℕ)) by ring, pow_mul, hzm, one_pow]
  have key : toDecomp q φ • z = z ^ (q : ℕ) := by
    calc toDecomp q φ • z = (toDecomp q φ • z) * (z ^ (m - 1)) ^ (q : ℕ) * z ^ (q : ℕ) := by
          rw [mul_assoc, ← mul_pow, ← pow_succ, Nat.sub_add_cancel hm1, hzm, one_pow, mul_one]
      _ = z ^ (q : ℕ) := by rw [hw, one_mul]
  have := congrArg Subtype.val key
  rwa [coe_toDecomp_smul, SubmonoidClass.coe_pow] at this

end RootsOfUnity

section Kummer

variable (p : ℕ) [Fact p.Prime] (q : Nat.Primes)

noncomputable def kummerRoot : AlgebraicClosure ℚ :=
  (IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos).choose

theorem kummerRoot_pow : kummerRoot p q ^ p = ((q : ℕ) : AlgebraicClosure ℚ) :=
  (IsAlgClosed.exists_pow_nat_eq ((q : ℕ) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos).choose_spec

theorem kummerRoot_ne_zero : kummerRoot p q ≠ 0 := by
  intro h
  have := kummerRoot_pow p q
  rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at this
  exact (Nat.cast_ne_zero.mpr q.2.ne_zero) this.symm

noncomputable def primRoot : AlgebraicClosure ℚ :=
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p).choose

theorem isPrimitiveRoot_primRoot : IsPrimitiveRoot (primRoot p) p := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  exact (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p).choose_spec

theorem exists_apply_kummerRoot_eq (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ i : ℕ, i < p ∧ g (kummerRoot p q) = primRoot p ^ i * kummerRoot p q := by
  have h1 : (g (kummerRoot p q) * (kummerRoot p q)⁻¹) ^ p = 1 := by
    rw [mul_pow, ← map_pow, kummerRoot_pow, map_natCast, inv_pow, kummerRoot_pow,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr q.2.ne_zero)]
  obtain ⟨i, hi, hζ⟩ := (isPrimitiveRoot_primRoot p).eq_pow_of_pow_eq_one h1
  exact ⟨i, hi, by rw [hζ, inv_mul_cancel_right₀ (kummerRoot_ne_zero p q)]⟩

noncomputable def kummerExp (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ZMod p :=
  ((exists_apply_kummerRoot_eq p q g).choose : ℕ)

theorem apply_kummerRoot (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    g (kummerRoot p q) = primRoot p ^ (kummerExp p q g).val * kummerRoot p q := by
  have h := (exists_apply_kummerRoot_eq p q g).choose_spec
  rw [kummerExp, ZMod.val_natCast_of_lt h.1]
  exact h.2

theorem kummerExp_eq_of_apply_eq (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {n : ℕ}
    (h : g (kummerRoot p q) = primRoot p ^ n * kummerRoot p q) : kummerExp p q g = n := by
  have h2 := apply_kummerRoot p q g
  rw [h] at h2
  have h3 : primRoot p ^ n = primRoot p ^ (kummerExp p q g).val := mul_right_cancel₀ (kummerRoot_ne_zero p q) h2
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hord : orderOf (primRoot p) = p := (isPrimitiveRoot_primRoot p).eq_orderOf.symm
  rw [← pow_mod_orderOf, hord] at h3
  have hlt : (kummerExp p q g).val < p := ZMod.val_lt _
  rw [← pow_mod_orderOf (primRoot p) (kummerExp p q g).val, hord, Nat.mod_eq_of_lt hlt] at h3
  have h4 : n % p = (kummerExp p q g).val := (isPrimitiveRoot_primRoot p).pow_inj (Nat.mod_lt _ hp) hlt h3
  rw [← ZMod.natCast_mod n p, h4, ZMod.natCast_zmod_val]

theorem not_dvd_of_ne (hqp : (q : ℕ) ≠ p) : ¬ (q : ℕ) ∣ p := fun h =>
  hqp (((Nat.prime_dvd_prime_iff_eq q.2 (Fact.out : p.Prime)).mp h))

noncomputable def kummerCharacter (hqp : (q : ℕ) ≠ p) :
    ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) →* Multiplicative (ZMod p) :=
  MonoidHom.mk' (fun σ => Multiplicative.ofAdd (kummerExp p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q))))
    (by
      intro σ τ
      rw [← ofAdd_add]
      congr 1
      have hζ : primeLocalToGlobal q (σ : primeLocalGaloisGroup q) (primRoot p) = primRoot p :=
        inertiaPullback_smul_eq_of_pow_eq_one q σ.2 (not_dvd_of_ne p q hqp) (isPrimitiveRoot_primRoot p).pow_eq_one
      have hrep : primeLocalToGlobal q ((σ * τ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))) :
            primeLocalGaloisGroup q) (kummerRoot p q)
          = primRoot p ^ ((kummerExp p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q))).val
              + (kummerExp p q (primeLocalToGlobal q (τ : primeLocalGaloisGroup q))).val) * kummerRoot p q := by
        rw [Subgroup.coe_mul, map_mul, AlgEquiv.mul_apply,
          apply_kummerRoot p q (primeLocalToGlobal q (τ : primeLocalGaloisGroup q)), map_mul, map_pow, hζ,
          apply_kummerRoot p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q)), ← mul_assoc, ← pow_add, add_comm]
      rw [kummerExp_eq_of_apply_eq p q _ hrep, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])

theorem kummerCharacter_apply (hqp : (q : ℕ) ≠ p)
    (σ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q))) :
    kummerCharacter p q hqp σ = Multiplicative.ofAdd (kummerExp p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q))) :=
  rfl

theorem kummerCharacter_conj (hqp : (q : ℕ) ≠ p) {φ : primeLocalGaloisGroup q}
    (hφ : (primeLocalPlace q).IsFrobeniusAt (primeLocalToGlobal q φ) q)
    (σ : ↥(((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)))
    (h : φ * σ * φ⁻¹ ∈ ((primeLocalPlace q).inertiaSubgroupIn ℚ).comap (primeLocalToGlobal q)) :
    kummerCharacter p q hqp ⟨φ * σ * φ⁻¹, h⟩ = kummerCharacter p q hqp σ ^ (q : ℕ) := by
  rw [kummerCharacter_apply, kummerCharacter_apply, ← ofAdd_nsmul, nsmul_eq_mul]
  congr 1

  set a := kummerExp p q (primeLocalToGlobal q (σ : primeLocalGaloisGroup q)) with ha
  obtain ⟨c, hc, hcφ⟩ := exists_apply_kummerRoot_eq p q (primeLocalToGlobal q φ⁻¹)
  have hζσ : primeLocalToGlobal q (σ : primeLocalGaloisGroup q) (primRoot p) = primRoot p :=
    inertiaPullback_smul_eq_of_pow_eq_one q σ.2 (not_dvd_of_ne p q hqp) (isPrimitiveRoot_primRoot p).pow_eq_one
  have hζφ : primeLocalToGlobal q φ (primRoot p) = primRoot p ^ (q : ℕ) :=
    frobenius_smul_eq_pow_of_pow_eq_one q hφ (not_dvd_of_ne p q hqp) (isPrimitiveRoot_primRoot p).pow_eq_one

  have hφα : primeLocalToGlobal q φ (kummerRoot p q) * primRoot p ^ ((q : ℕ) * c) = kummerRoot p q := by
    have : primeLocalToGlobal q φ (primeLocalToGlobal q φ⁻¹ (kummerRoot p q)) = kummerRoot p q := by
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    rw [hcφ, map_mul, map_pow, hζφ, ← pow_mul] at this
    rwa [mul_comm] at this

  have hcalc : primeLocalToGlobal q (φ * σ * φ⁻¹) (kummerRoot p q) = primRoot p ^ ((q : ℕ) * a.val) * kummerRoot p q := by
    rw [map_mul, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hcφ, map_mul, map_pow, hζσ, apply_kummerRoot p q,
      ← ha, map_mul, map_mul, map_pow, map_pow, hζφ, ← pow_mul, ← pow_mul]

    calc primRoot p ^ ((q : ℕ) * c) * (primRoot p ^ ((q : ℕ) * a.val) * primeLocalToGlobal q φ (kummerRoot p q))
        = primRoot p ^ ((q : ℕ) * a.val) * (primeLocalToGlobal q φ (kummerRoot p q) * primRoot p ^ ((q : ℕ) * c)) := by ring
      _ = primRoot p ^ ((q : ℕ) * a.val) * kummerRoot p q := by rw [hφα]
  have := kummerExp_eq_of_apply_eq p q _ hcalc
  rw [this, Nat.cast_mul, ZMod.natCast_zmod_val]

end Kummer

end ExtCitation


