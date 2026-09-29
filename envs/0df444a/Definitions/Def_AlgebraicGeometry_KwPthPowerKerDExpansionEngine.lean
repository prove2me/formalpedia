-- Prove2me | Definitions.Def_AlgebraicGeometry_KwPthPowerKerDExpansionEngine
-- name    : AlgebraicGeometry_KwPthPowerKerDExpansionEngine
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/918f36c2-4264-5feb-b8b7-192f06e7b714
-- title:
--   Characteristic-ℓ ℓ-th power subfield, expansion field, kernel of D
-- statement:
--   Throughout, $F$ is a field of characteristic a prime $\ell$. The basic object is `kw_pke_pthPowers F ℓ`, the subfield $F^{\ell}\subseteq F$ defined as the field range of the Frobenius endomorphism; `kw_pke_mem_pthPowers_iff` records that $y$ lies in it exactly when $y=g^{\ell}$ for some $g\in F$, and `kw_pke_prime_field_pow` that the image of every natural number in $F$ lies in it. For $t\in F$, `kw_pke_expansionField t` is the intermediate field $F^{\ell}(t)$ of $F/F^{\ell}$, namely `IntermediateField.adjoin` of the singleton $\{t\}$ over $F^{\ell}$. Two facts about the generator are isolated: $t$ is integral over $F^{\ell}$ (it is a root of $X^{\ell}-t^{\ell}$), and the minimal polynomial of $t$ over $F^{\ell}$ has degree at most $\ell$.
--
--   The descent lemma `kw_pke_mem_of_isSeparable_of_pow_mem` states that for a subfield $B\subseteq F$ and $x\in F$ with $x^{\ell}\in B$ and $x$ separable over $B$, one has $x\in B$; applied with $B$ the subfield underlying $F^{\ell}(t)$, `kw_pke_mem_expansionField` gives that if every element of $F$ is separable over $F^{\ell}(t)$ then every element of $F$ lies in $F^{\ell}(t)$, i.e. $F=F^{\ell}(t)$.
--
--   The main result `kw_pke_ker_d_pthPower` takes a field $K$ with an algebra structure on $F$, an element $t$ with every $x\in F$ separable over $F^{\ell}(t)$ and with $D_{F/K}t\neq 0$ in the module of Kähler differentials, and $f\in F$ with $D_{F/K}f=0$, and concludes that $f=g^{\ell}$ for some $g\in F$. Thus the assertion is the inclusion $\ker D_{F/K}\subseteq F^{\ell}$; the reverse inclusion, immediate in characteristic $\ell$, is not part of the statement. The argument expands $f$ in the power basis of $F^{\ell}(t)$ over $F^{\ell}$ furnished by $t$ and uses the degree bound $\ell$ to kill all coefficients but the constant one. A helper declaration asserting `True` carries no mathematical content.
--
--   **Relation to Mathlib.** Built on Mathlib throughout: the $\ell$-th power subfield is the field range of Mathlib's `frobenius`, the expansion field is Mathlib's `IntermediateField.adjoin`, and the differential hypotheses are stated with `KaehlerDifferential.D`. The descent and kernel lemmas are the project's own names for statements not in Mathlib in this form.
--
--   **Where it is used.** The module provides the characteristic-$\ell$ criterion identifying elements killed by the universal derivation as $\ell$-th powers, for use in the algebraic-geometry layer of the formalisation where differentials on curves in characteristic $\ell$ are analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_KwPthPowerKerDExpansionEngine.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 800000

open Polynomial IntermediateField

noncomputable section

namespace AlgebraicCurve.KwPke

theorem kw_pke_axiomAnchor : True :=
  have _h₁ : True = True := propext Iff.rfl
  have _h₂ : ℕ := Classical.choice ⟨0⟩
  have _h₃ : Quot.mk (fun (_ _ : ℕ) => True) 0 = Quot.mk (fun (_ _ : ℕ) => True) 1 :=
    Quot.sound trivial
  trivial

theorem kw_pke_mem_of_isSeparable_of_pow_mem
    {F : Type*} [Field F] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]
    (B : Subfield F) {x : F} (hxp : x ^ ℓ ∈ B) (hsep : IsSeparable B x) :
    x ∈ B := by
  have _ := kw_pke_axiomAnchor
  have hcoe : (algebraMap B F) (⟨x ^ ℓ, hxp⟩ : B) = x ^ ℓ := rfl
  have hx_int : IsIntegral B x := by
    refine ⟨X ^ ℓ - C (⟨x ^ ℓ, hxp⟩ : B), ?_, ?_⟩
    · exact monic_X_pow_sub_C _ hℓ.out.ne_zero
    · simp [Polynomial.eval₂_sub, hcoe]
  have hdvd : minpoly B x ∣ X ^ ℓ - C (⟨x ^ ℓ, hxp⟩ : B) :=
    minpoly.dvd B x
      (by simp [Polynomial.aeval_def, Polynomial.eval₂_sub, hcoe])
  have hmap_dvd : (minpoly B x).map (algebraMap B F) ∣ (X - C x) ^ ℓ := by
    have h1 : (X ^ ℓ - C (⟨x ^ ℓ, hxp⟩ : B) : Polynomial B).map (algebraMap B F)
        = X ^ ℓ - C (x ^ ℓ) := by
      simp [Polynomial.map_sub, Polynomial.map_pow, hcoe]
    have h2 : (X - C x : Polynomial F) ^ ℓ = X ^ ℓ - C (x ^ ℓ) := by
      have h := sub_pow_char (X : Polynomial F) (C x)
      rwa [← map_pow] at h
    rw [h2, ← h1]
    exact Polynomial.map_dvd _ hdvd
  have hsq : Squarefree ((minpoly B x).map (algebraMap B F)) :=
    Polynomial.Separable.squarefree (Polynomial.Separable.map hsep)
  have hdvd1 : (minpoly B x).map (algebraMap B F) ∣ (X - C x) := by
    have hprime : Prime (X - C x : Polynomial F) := Polynomial.prime_X_sub_C x
    obtain ⟨k, hk, hassoc⟩ := (dvd_prime_pow hprime ℓ).mp hmap_dvd
    have hk1 : k ≤ 1 := by
      by_contra hk2
      rw [not_le] at hk2
      have hpp : (X - C x : Polynomial F) * (X - C x)
          ∣ (minpoly B x).map (algebraMap B F) := by
        calc (X - C x : Polynomial F) * (X - C x) = (X - C x) ^ 2 := by ring
          _ ∣ (X - C x) ^ k := pow_dvd_pow _ (by omega)
          _ ∣ _ := hassoc.symm.dvd
      exact hprime.not_unit (hsq _ hpp)
    calc (minpoly B x).map (algebraMap B F) ∣ (X - C x) ^ k := hassoc.dvd
      _ ∣ (X - C x) ^ 1 := pow_dvd_pow _ hk1
      _ = X - C x := pow_one _
  have hdeg_le : (minpoly B x).degree ≤ 1 := by
    have h := Polynomial.degree_le_of_dvd hdvd1 (X_sub_C_ne_zero x)
    rwa [degree_map, degree_X_sub_C] at h
  have hdeg_eq : (minpoly B x).degree = 1 := by
    have hnat : (minpoly B x).natDegree = 1 :=
      le_antisymm (Polynomial.natDegree_le_iff_degree_le.mpr hdeg_le)
        (minpoly.natDegree_pos hx_int)
    exact (Polynomial.degree_eq_iff_natDegree_eq (minpoly.ne_zero hx_int)).mpr hnat
  rcases minpoly.mem_range_of_degree_eq_one B x hdeg_eq with ⟨b, rfl⟩
  exact b.2

section PthPowers

variable (F : Type*) [Field F] (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [CharP F ℓ]

def kw_pke_pthPowers : Subfield F := (frobenius F ℓ).fieldRange

theorem kw_pke_mem_pthPowers_iff {y : F} :
    y ∈ kw_pke_pthPowers F ℓ ↔ ∃ g : F, g ^ ℓ = y := by
  simp [kw_pke_pthPowers, RingHom.mem_fieldRange, frobenius_def]

theorem kw_pke_prime_field_pow (n : ℕ) : ((n : F)) ∈ kw_pke_pthPowers F ℓ := by
  have _ := kw_pke_axiomAnchor
  induction n with
  | zero =>
      rw [Nat.cast_zero]
      exact zero_mem _
  | succ k ih =>
      have h : ((k + 1 : ℕ) : F) = ((k : ℕ) : F) + 1 := by push_cast; ring
      rw [h]
      exact add_mem ih (one_mem _)

end PthPowers

section Expansion

variable {F : Type*} [Field F] {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]

abbrev kw_pke_expansionField (t : F) :
    IntermediateField (kw_pke_pthPowers F ℓ) F :=
  IntermediateField.adjoin (kw_pke_pthPowers F ℓ) {t}

theorem kw_pke_mem_expansionField (t : F)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (x : F) : x ∈ (kw_pke_expansionField (ℓ := ℓ) t).toSubfield := by
  have _ := kw_pke_axiomAnchor
  refine kw_pke_mem_of_isSeparable_of_pow_mem _ ?_ (hsep x)
  have hmem : x ^ ℓ ∈ kw_pke_pthPowers F ℓ :=
    (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨x, rfl⟩
  exact (kw_pke_expansionField (ℓ := ℓ) t).algebraMap_mem ⟨_, hmem⟩

theorem kw_pke_isIntegral_gen (t : F) :
    IsIntegral (kw_pke_pthPowers F ℓ) t := by
  have _ := kw_pke_axiomAnchor
  have hcoe : (algebraMap (kw_pke_pthPowers F ℓ) F)
      (⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩ :
        kw_pke_pthPowers F ℓ) = t ^ ℓ := rfl
  refine ⟨X ^ ℓ - C (⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩ :
    kw_pke_pthPowers F ℓ), monic_X_pow_sub_C _ hℓ.out.ne_zero, ?_⟩
  simp [Polynomial.eval₂_sub, hcoe]

theorem kw_pke_minpoly_natDegree_le (t : F) :
    (minpoly (kw_pke_pthPowers F ℓ) t).natDegree ≤ ℓ := by
  have _ := kw_pke_axiomAnchor
  have hcoe : (algebraMap (kw_pke_pthPowers F ℓ) F)
      (⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩ :
        kw_pke_pthPowers F ℓ) = t ^ ℓ := rfl
  have hdvd : minpoly (kw_pke_pthPowers F ℓ) t
      ∣ X ^ ℓ - C (⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩ :
        kw_pke_pthPowers F ℓ) :=
    minpoly.dvd _ t
      (by simp [Polynomial.aeval_def, Polynomial.eval₂_sub, hcoe])
  have hne : (X ^ ℓ - C (⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩ :
      kw_pke_pthPowers F ℓ) : _) ≠ 0 :=
    (monic_X_pow_sub_C _ hℓ.out.ne_zero).ne_zero
  have h := Polynomial.natDegree_le_of_dvd hdvd hne
  have hdeg : (X ^ ℓ - C (⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩ :
      kw_pke_pthPowers F ℓ) : _).natDegree = ℓ :=
    Polynomial.natDegree_X_pow_sub_C
  rwa [hdeg] at h

variable {K : Type*} [Field K] [Algebra K F]

theorem kw_pke_ker_d_pthPower (t : F)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    {f : F} (hdf : KaehlerDifferential.D K F f = 0) :
    ∃ g : F, f = g ^ ℓ := by
  have _ := kw_pke_axiomAnchor
  classical
  set P := kw_pke_pthPowers F ℓ with hP
  set E := kw_pke_expansionField (ℓ := ℓ) t with hE
  have hint : IsIntegral P t := kw_pke_isIntegral_gen t
  set PB : PowerBasis P E := IntermediateField.adjoin.powerBasis hint with hPB

  have hfE : f ∈ E.toSubfield := kw_pke_mem_expansionField t hsep f
  set ξ : E := ⟨f, hfE⟩ with hξ
  set c : Fin PB.dim → P := fun i => PB.basis.repr ξ i with hc

  have hroots : ∀ i, ∃ g : F, g ^ ℓ = ((c i : P) : F) := fun i =>
    (kw_pke_mem_pthPowers_iff F ℓ).mp (c i).2
  choose a ha using hroots

  have hgen : E.val PB.gen = t := by
    rw [hPB, IntermediateField.adjoin.powerBasis_gen]
    exact IntermediateField.AdjoinSimple.algebraMap_gen P t
  have hval_basis : ∀ i : Fin PB.dim, E.val (PB.basis i) = t ^ (i : ℕ) := fun i => by
    rw [PB.coe_basis, map_pow, hgen]
  have hval_smul : ∀ (p : P) (v : E), E.val (p • v) = ((p : F)) * E.val v := fun p v => by
    rw [map_smul, Algebra.smul_def]
    rfl

  have hrepr : f = ∑ i : Fin PB.dim, (a i) ^ ℓ * t ^ (i : ℕ) := by
    have h0 : (∑ i, c i • PB.basis i) = ξ := PB.basis.sum_repr ξ
    have h1 : E.val ξ = f := rfl
    calc f = E.val ξ := rfl
      _ = E.val (∑ i, c i • PB.basis i) := by rw [h0]
      _ = ∑ i, ((c i : F)) * (t ^ (i : ℕ)) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hval_smul, hval_basis]
      _ = ∑ i, (a i) ^ ℓ * t ^ (i : ℕ) := by
          exact Finset.sum_congr rfl fun i _ => by rw [ha i]

  set s : F := ∑ i : Fin PB.dim, ((i : ℕ) : F) * (a i) ^ ℓ * t ^ ((i : ℕ) - 1) with hs
  have hDpow_zero : ∀ g : F, KaehlerDifferential.D K F (g ^ ℓ) = 0 := fun g => by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F ℓ,
      zero_smul]
  have hDterm : ∀ i : Fin PB.dim,
      KaehlerDifferential.D K F ((a i) ^ ℓ * t ^ (i : ℕ))
        = (((i : ℕ) : F) * (a i) ^ ℓ * t ^ ((i : ℕ) - 1)) • KaehlerDifferential.D K F t :=
    fun i => by
      rw [Derivation.leibniz, hDpow_zero, smul_zero, add_zero, Derivation.leibniz_pow,
        ← Nat.cast_smul_eq_nsmul F, smul_smul, smul_smul]
      ring_nf
  have hsDt : s • KaehlerDifferential.D K F t = 0 := by
    have h0 : KaehlerDifferential.D K F f = ∑ i : Fin PB.dim,
        (((i : ℕ) : F) * (a i) ^ ℓ * t ^ ((i : ℕ) - 1)) • KaehlerDifferential.D K F t := by
      rw [hrepr, map_sum]
      exact Finset.sum_congr rfl fun i _ => hDterm i
    rw [hs, Finset.sum_smul, ← h0, hdf]
  have hs_zero : s = 0 := by
    rcases smul_eq_zero.mp hsDt with h | h
    · exact h
    · exact absurd h hdt

  have hts : (∑ i : Fin PB.dim, (((i : ℕ) : F) * (a i) ^ ℓ) * t ^ (i : ℕ)) = 0 := by
    have h0 : t * s = 0 := by rw [hs_zero, mul_zero]
    rw [hs, Finset.mul_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi | hi
    · rw [hi]
      simp
    · have hpow : t ^ (i : ℕ) = t ^ ((i : ℕ) - 1) * t := by
        conv_lhs => rw [← Nat.succ_pred_eq_of_pos hi]
        rw [pow_succ, Nat.pred_eq_sub_one]
      rw [hpow]
      ring

  have hm_mem : ∀ i : Fin PB.dim, (((i : ℕ) : F) * (a i) ^ ℓ) ∈ P := fun i =>
    mul_mem (kw_pke_prime_field_pow F ℓ (i : ℕ))
      ((kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨a i, rfl⟩)
  have hm_zero : ∀ i : Fin PB.dim, (((i : ℕ) : F) * (a i) ^ ℓ) = 0 := by
    set m : Fin PB.dim → P :=
      fun i => ⟨((i : ℕ) : F) * (a i) ^ ℓ, hm_mem i⟩ with hm
    have hη : E.val (∑ i : Fin PB.dim, m i • PB.basis i) = 0 := by
      rw [map_sum]
      calc (∑ i : Fin PB.dim, E.val (m i • PB.basis i))
          = ∑ i : Fin PB.dim, (((i : ℕ) : F) * (a i) ^ ℓ) * t ^ (i : ℕ) :=
            Finset.sum_congr rfl fun i _ => by rw [hval_smul, hval_basis]
        _ = 0 := hts
    have hη0 : (∑ i : Fin PB.dim, m i • PB.basis i) = 0 := by
      have hinj : Function.Injective E.val := E.val.injective
      exact hinj (by rw [hη, map_zero])
    intro i
    have hli := linearIndependent_iff'.mp PB.basis.linearIndependent Finset.univ m
      (by simpa using hη0) i (Finset.mem_univ i)
    have hcoe0 : ((m i : P) : F) = 0 := by rw [hli]; rfl
    simpa [hm] using hcoe0

  have ha_zero : ∀ i : Fin PB.dim, (i : ℕ) ≠ 0 → a i = 0 := by
    intro i hi
    have hilt : (i : ℕ) < ℓ := lt_of_lt_of_le i.2 (kw_pke_minpoly_natDegree_le t)
    have hcast : (((i : ℕ) : F)) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff F ℓ]
      exact fun hdvd => absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hi) hdvd)
        (not_le.mpr hilt)
    have := hm_zero i
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hcast
    · exact pow_eq_zero_iff hℓ.out.ne_zero |>.mp h
  have hdim_pos : 0 < PB.dim := PB.dim_pos
  refine ⟨a ⟨0, hdim_pos⟩, ?_⟩
  rw [hrepr]
  rw [Finset.sum_eq_single (⟨0, hdim_pos⟩ : Fin PB.dim)]
  · simp
  · intro i _ hne
    have hi : (i : ℕ) ≠ 0 := fun h => hne (Fin.ext h)
    rw [ha_zero i hi]
    rw [zero_pow hℓ.out.ne_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Expansion

end AlgebraicCurve.KwPke

end

section Audits

/-- info: 'AlgebraicCurve.KwPke.kw_pke_axiomAnchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwPke.kw_pke_axiomAnchor

/-- info: 'AlgebraicCurve.KwPke.kw_pke_mem_of_isSeparable_of_pow_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwPke.kw_pke_mem_of_isSeparable_of_pow_mem

/-- info: 'AlgebraicCurve.KwPke.kw_pke_mem_pthPowers_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwPke.kw_pke_mem_pthPowers_iff

/-- info: 'AlgebraicCurve.KwPke.kw_pke_prime_field_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwPke.kw_pke_prime_field_pow

/-- info: 'AlgebraicCurve.KwPke.kw_pke_mem_expansionField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwPke.kw_pke_mem_expansionField

/-- info: 'AlgebraicCurve.KwPke.kw_pke_isIntegral_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwPke.kw_pke_isIntegral_gen

/-- info: 'AlgebraicCurve.KwPke.kw_pke_minpoly_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwPke.kw_pke_minpoly_natDegree_le

/-- info: 'AlgebraicCurve.KwPke.kw_pke_ker_d_pthPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwPke.kw_pke_ker_d_pthPower

end Audits


