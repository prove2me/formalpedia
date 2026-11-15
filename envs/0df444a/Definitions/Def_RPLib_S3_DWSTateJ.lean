-- Prove2me | Definitions.Def_RPLib_S3_DWSTateJ
-- name    : RPLib_S3_DWSTateJ
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T17:38:29.128197+00:00
-- url     : https://prove2.me/theorems/c2f530ef-4e9b-4827-8d77-2036163410c7
-- title:
--   Weight-two Ramanujan-Petersson library: `E[m]` is a cyclic `R`-module (b7c, step J)
-- statement:
--   `E[m]` is a cyclic `R`-module (b7c, step J).
--
--   `R = QuadraticAlgebra ℤ a b` acting on `E` by an `R`-structure `s : OAct R W L`, `p ∤ m`.
--   * `intCast_dvd_iff_QA`, `natCast_dvd_iff_QA`: `(m : R) ∣ r ↔ m ∣ re r ∧ m ∣ im r`.
--   * `OAct.natCast_dvd_of_kills` (FAITH): if `ι r` kills `E[m]` then `(m : R) ∣ r`.
--   * `IsGen s m P`: `m P = 0` and `Ann(P) ⊆ mR`.
--   * `exists_isGen_prime` (prime `ℓ`), `isGen_of_nsmul_eq` (prime powers), `isGen_add` (coprime gluing),
--     **`exists_isGen`**: every `E[m]` (`p ∤ m`) has a free generator;
--     **`IsGen.exists_eq`**: a free generator generates `E[m]` (`E[m] = R P₀`); `IsGen.nsmul_self`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateI

/-!
# S3-DWS-Tate, part J: `E[m]` is a cyclic `R`-module (b7c, step J)

`R = QuadraticAlgebra ℤ a b` acting on `E` by an `R`-structure `s : OAct R W L`, `p ∤ m`.
* `intCast_dvd_iff_QA`, `natCast_dvd_iff_QA`: `(m : R) ∣ r ↔ m ∣ re r ∧ m ∣ im r`.
* `OAct.natCast_dvd_of_kills` (FAITH): if `ι r` kills `E[m]` then `(m : R) ∣ r`.
* `IsGen s m P`: `m P = 0` and `Ann(P) ⊆ mR`.
* `exists_isGen_prime` (prime `ℓ`), `isGen_of_nsmul_eq` (prime powers), `isGen_add` (coprime gluing),
  **`exists_isGen`**: every `E[m]` (`p ∤ m`) has a free generator;
  **`IsGen.exists_eq`**: a free generator generates `E[m]` (`E[m] = R P₀`); `IsGen.nsmul_self`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section QAdvd

variable {a b : ℤ}

theorem QA_decomp (r : QuadraticAlgebra ℤ a b) :
    r = ((r.re : ℤ) : QuadraticAlgebra ℤ a b) + ((r.im : ℤ) : QuadraticAlgebra ℤ a b) * ⟨0, 1⟩ := by
  ext <;> simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, QuadraticAlgebra.re_mul,
    QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, Int.cast_id] <;> ring

theorem intCast_dvd_iff_QA {m : ℤ} {r : QuadraticAlgebra ℤ a b} :
    (m : QuadraticAlgebra ℤ a b) ∣ r ↔ m ∣ r.re ∧ m ∣ r.im := by
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.re, ?_⟩, ⟨x.im, ?_⟩⟩ <;>
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
        QuadraticAlgebra.im_intCast, Int.cast_id] <;> ring
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    refine ⟨⟨u, v⟩, ?_⟩
    ext <;> simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
        QuadraticAlgebra.im_intCast, Int.cast_id, hu, hv] <;> ring

theorem natCast_dvd_iff_QA {m : ℕ} {r : QuadraticAlgebra ℤ a b} :
    (m : QuadraticAlgebra ℤ a b) ∣ r ↔ (m : ℤ) ∣ r.re ∧ (m : ℤ) ∣ r.im := by
  rw [← intCast_dvd_iff_QA, Int.cast_natCast]

lemma zmod_eq_of_dvd {m : ℕ} [NeZero m] {c c' : ZMod m} (h : (m : ℤ) ∣ (c.val : ℤ) - (c'.val : ℤ)) :
    c = c' := by
  have h1 : (((c.val : ℤ) - (c'.val : ℤ) : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr h
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
    sub_eq_zero] at h1
  exact h1

end QAdvd

section Cyc

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W : WeierstrassCurve F} [W.IsElliptic] {R : Type*} [CommRing R]

lemma OAct.ι_sub_apply (s : OAct R W L) (x y : R) (P : Pt W L) : s.ι (x - y) P = s.ι x P - s.ι y P := by
  rw [map_sub]; rfl

lemma OAct.intCast_apply (s : OAct R W L) (z : ℤ) (P : Pt W L) : s.ι (z : R) P = z • P := by
  rw [map_intCast, AddMonoid.End.intCast_apply]

/-- **(FAITH)** If `ι r` kills `E[m]` (`p ∤ m`) then `(m : R) ∣ r`. -/
theorem OAct.natCast_dvd_of_kills (s : OAct R W L) {m : ℕ} (hm : (m : F) ≠ 0) {r : R}
    (h : ∀ P : Pt W L, m • P = 0 → s.ι r P = 0) : (m : R) ∣ r := by
  obtain ⟨χ, hχ, he⟩ := endFq_div hm (s.mem r) h
  obtain ⟨z, rfl⟩ := s.surj _ hχ
  exact ⟨z, s.inj (by rw [he, map_mul, map_natCast])⟩

lemma card_torsN {m : ℕ} (hm : (m : F) ≠ 0) : Nat.card (torsN W L m) = m ^ 2 := by
  have h : torsN W L m = RPLib.Torsion.tors (W.baseChange L) m :=
    AddSubgroup.ext fun P => by rw [mem_torsN]; exact Iff.rfl
  rw [h]
  exact RPLib.Torsion.card_tors_baseChange (W := W) L m hm

variable (s : OAct R W L)

/-- `P` is a free generator of `E[m]`: `m P = 0` and `Ann(P) ⊆ mR`. -/
def IsGen (m : ℕ) (P : Pt W L) : Prop :=
  m • P = 0 ∧ ∀ r : R, s.ι r P = 0 → (m : R) ∣ r

variable {s}

/-- Prime powers: a lift `Q` of a free generator of `E[ℓ]` along `[ℓ^i]` is a free generator of `E[ℓ^(i+1)]`. -/
theorem isGen_of_nsmul_eq {ℓ : ℕ} {v : Pt W L} (hv : IsGen s ℓ v) :
    ∀ i : ℕ, ∀ Q : Pt W L, ℓ ^ i • Q = v → IsGen s (ℓ ^ (i + 1)) Q := by
  intro i
  induction i with
  | zero =>
    intro Q hQ
    rw [pow_zero, one_nsmul] at hQ
    subst hQ
    rw [zero_add, pow_one]
    exact hv
  | succ i ih =>
    intro Q hQ
    refine ⟨?_, fun r hr => ?_⟩
    · rw [pow_succ', mul_nsmul', hQ]
      exact hv.1
    · have hrv : s.ι r v = 0 := by rw [← hQ, map_nsmul, hr, nsmul_zero]
      obtain ⟨r', rfl⟩ := hv.2 r hrv
      have hQ' : ℓ ^ i • (ℓ • Q) = v := by rw [← mul_nsmul', ← pow_succ]; exact hQ
      have hr' : s.ι r' (ℓ • Q) = 0 := by
        rw [map_nsmul, ← s.natCast_apply, ← s.ι_mul_apply]; exact hr
      obtain ⟨z, hz⟩ := (ih (ℓ • Q) hQ').2 r' hr'
      refine ⟨z, ?_⟩
      rw [hz, ← mul_assoc, ← Nat.cast_mul, ← pow_succ']

/-- Coprime gluing of free generators. -/
theorem isGen_add {m₁ m₂ : ℕ} (hcop : Nat.Coprime m₁ m₂) {P₁ P₂ : Pt W L}
    (h₁ : IsGen s m₁ P₁) (h₂ : IsGen s m₂ P₂) : IsGen s (m₁ * m₂) (P₁ + P₂) := by
  have hc : IsCoprime (m₁ : R) (m₂ : R) := by
    have := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom R)
    simpa using this
  refine ⟨?_, fun r hr => ?_⟩
  · rw [smul_add, mul_nsmul P₁ m₁ m₂, mul_nsmul' P₂ m₁ m₂, h₁.1, h₂.1, nsmul_zero, nsmul_zero, add_zero]
  · have e₁ : s.ι r (m₂ • P₁) = 0 := by
      calc s.ι r (m₂ • P₁) = s.ι r (m₂ • (P₁ + P₂)) := by rw [smul_add, h₂.1, add_zero]
        _ = m₂ • s.ι r (P₁ + P₂) := map_nsmul _ _ _
        _ = 0 := by rw [hr, nsmul_zero]
    have e₂ : s.ι r (m₁ • P₂) = 0 := by
      calc s.ι r (m₁ • P₂) = s.ι r (m₁ • (P₁ + P₂)) := by rw [smul_add, h₁.1, zero_add]
        _ = m₁ • s.ι r (P₁ + P₂) := map_nsmul _ _ _
        _ = 0 := by rw [hr, nsmul_zero]
    have d₁ : (m₁ : R) ∣ (m₂ : R) * r :=
      h₁.2 _ (by rw [s.ι_mul_apply, s.natCast_apply, ← map_nsmul]; exact e₁)
    have d₂ : (m₂ : R) ∣ (m₁ : R) * r :=
      h₂.2 _ (by rw [s.ι_mul_apply, s.natCast_apply, ← map_nsmul]; exact e₂)
    rw [Nat.cast_mul]
    exact hc.mul_dvd (hc.dvd_of_dvd_mul_left d₁) (hc.symm.dvd_of_dvd_mul_left d₂)

/-- From a free generator of `E[n²]` to one of `E[n]`. -/
theorem IsGen.nsmul_self [IsDomain R] {n : ℕ} (hn : (n : R) ≠ 0) {P : Pt W L}
    (h : IsGen s (n * n) P) : IsGen s n (n • P) := by
  refine ⟨by rw [← mul_nsmul']; exact h.1, fun r hr => ?_⟩
  have h1 : s.ι ((n : R) * r) P = 0 := by rw [s.ι_mul_apply, s.natCast_apply, ← map_nsmul]; exact hr
  obtain ⟨z, hz⟩ := h.2 _ h1
  refine ⟨z, mul_left_cancel₀ hn ?_⟩
  rw [hz, Nat.cast_mul, mul_assoc]

end Cyc

section CycQA

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {W : WeierstrassCurve F} [W.IsElliptic] {a b : ℤ}

lemma OAct.ι_apply_eq (s : OAct (QuadraticAlgebra ℤ a b) W L) (r : QuadraticAlgebra ℤ a b) (P : Pt W L) :
    s.ι r P = r.re • P + r.im • s.ι ⟨0, 1⟩ P := by
  conv_lhs => rw [QA_decomp r]
  rw [s.ι_add_apply, s.ι_mul_apply, s.intCast_apply, s.intCast_apply]

/-- **(J1)** `E[ℓ]` has a free generator (`ℓ` prime, `ℓ ≠ p`): otherwise `ω` would act on `E[ℓ]` as a scalar. -/
theorem exists_isGen_prime (s : OAct (QuadraticAlgebra ℤ a b) W L) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓF : (ℓ : F) ≠ 0) : ∃ v : Pt W L, IsGen s ℓ v := by
  obtain ⟨k, hk⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, (Nat.sub_add_cancel hℓ.one_lt.le).symm⟩
  subst hk
  have hfact : Fact (k + 1).Prime := ⟨hℓ⟩
  letI : Module (ZMod (k + 1)) (torsN W L (k + 1)) := AddCommGroup.zmodModule (fun x => Subtype.ext (by
    simp only [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero]; exact mem_torsN.mp x.2))
  have hω : ∀ P : Pt W L, (k + 1) • P = 0 → (k + 1) • s.ι ⟨0, 1⟩ P = 0 := fun P hP => by
    rw [← map_nsmul, hP, map_zero]
  let f : torsN W L (k + 1) →+ torsN W L (k + 1) :=
    { toFun := fun x => ⟨s.ι ⟨0, 1⟩ x.1, mem_torsN.mpr (hω x.1 (mem_torsN.mp x.2))⟩
      map_zero' := Subtype.ext (map_zero (s.ι ⟨0, 1⟩))
      map_add' := fun x y => Subtype.ext (map_add (s.ι ⟨0, 1⟩) x.1 y.1) }
  let fL : torsN W L (k + 1) →ₗ[ZMod (k + 1)] torsN W L (k + 1) := f.toZModLinearMap (k + 1)
  have hfL : ∀ x, (fL x).1 = s.ι ⟨0, 1⟩ x.1 := fun x => rfl
  by_contra hne
  have hdep : ∀ v : torsN W L (k + 1), ¬ LinearIndependent (ZMod (k + 1)) ![v, fL v] := by
    intro v hv
    apply hne ⟨v.1, ?_⟩
    refine ⟨mem_torsN.mp v.2, fun r hr => ?_⟩
    rw [LinearIndependent.pair_iff] at hv
    have key : ((r.re : ZMod (k + 1))) • v + ((r.im : ZMod (k + 1))) • fL v = 0 := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      apply Subtype.ext
      rw [AddSubgroup.coe_add, AddSubgroup.coe_zsmul, AddSubgroup.coe_zsmul, hfL, AddSubgroup.coe_zero,
        ← s.ι_apply_eq]
      exact hr
    obtain ⟨h1, h2⟩ := hv _ _ key
    exact natCast_dvd_iff_QA.mpr ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ (k + 1)).mp h1,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ (k + 1)).mp h2⟩
  obtain ⟨c, hc⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent hdep
  have hc' : ∀ x : torsN W L (k + 1), fL x = c • x := fun x => by
    rw [hc, LinearMap.smul_apply, Module.End.one_apply]
  have hsc : ∀ P : Pt W L, (k + 1) • P = 0 → s.ι ⟨0, 1⟩ P = c.val • P := by
    intro P hP
    have h1 := congrArg Subtype.val (hc' ⟨P, mem_torsN.mpr hP⟩)
    rw [hfL, ← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, AddSubgroup.coe_nsmul] at h1
    exact h1
  have hd := s.natCast_dvd_of_kills hℓF (r := ⟨0, 1⟩ - (((c.val : ℤ)) : QuadraticAlgebra ℤ a b))
    (fun P hP => by rw [s.ι_sub_apply, hsc P hP, s.intCast_apply, natCast_zsmul, sub_self])
  have him := (natCast_dvd_iff_QA.mp hd).2
  simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_intCast, sub_zero] at him
  have h1 : ((k + 1 : ℕ) : ℤ) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg _) him
  exact hℓ.one_lt.ne' (by exact_mod_cast h1)

/-- **(J)** Every `E[m]` with `p ∤ m` has a free generator. -/
theorem exists_isGen (s : OAct (QuadraticAlgebra ℤ a b) W L) :
    ∀ m : ℕ, (m : F) ≠ 0 → ∃ P : Pt W L, IsGen s m P := by
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow ℓ k hℓ hk =>
    intro hm
    have hℓF : (ℓ : F) ≠ 0 := fun h0 => hm (by rw [Nat.cast_pow, h0, zero_pow hk.ne'])
    obtain ⟨v, hv⟩ := exists_isGen_prime s hℓ hℓF
    have hk1 : ((ℓ ^ (k - 1) : ℕ) : F) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓF
    obtain ⟨Q, hQ⟩ := nsmul_surjective (W := W) (L := L) (natCast_ne_zero_L' hk1) v
    have hQ' : ℓ ^ (k - 1) • Q = v := hQ
    have h := isGen_of_nsmul_eq hv (k - 1) Q hQ'
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk.ne')] at h
    exact ⟨Q, h⟩
  | zero => intro hm; exact (hm Nat.cast_zero).elim
  | one => intro _; exact ⟨0, smul_zero _, fun r _ => by rw [Nat.cast_one]; exact one_dvd r⟩
  | coprime m₁ m₂ _ _ hcop ih₁ ih₂ =>
    intro hm
    rw [Nat.cast_mul] at hm
    obtain ⟨P₁, h₁⟩ := ih₁ (left_ne_zero_of_mul hm)
    obtain ⟨P₂, h₂⟩ := ih₂ (right_ne_zero_of_mul hm)
    exact ⟨P₁ + P₂, isGen_add hcop h₁ h₂⟩

/-- **(J) cyclicity**: a free generator `P₀` of `E[m]` generates it: every `P ∈ E[m]` is `ι r P₀`. -/
theorem IsGen.exists_eq {s : OAct (QuadraticAlgebra ℤ a b) W L} {m : ℕ} (hm : (m : F) ≠ 0) {P₀ : Pt W L}
    (h : IsGen s m P₀) {P : Pt W L} (hP : m • P = 0) : ∃ r, s.ι r P₀ = P := by
  have : NeZero m := ⟨fun h0 => hm (by rw [h0, Nat.cast_zero])⟩
  have := finite_torsN (W := W) (L := L) hm
  have hmem : ∀ r, s.ι r P₀ ∈ torsN W L m := fun r =>
    mem_torsN.mpr (by rw [← map_nsmul, h.1, map_zero])
  let g : ZMod m × ZMod m → torsN W L m := fun cd =>
    ⟨s.ι ⟨(cd.1.val : ℤ), (cd.2.val : ℤ)⟩ P₀, hmem _⟩
  have hinj : Function.Injective g := by
    rintro ⟨c, d⟩ ⟨c', d'⟩ hcd
    have h1 : s.ι ((⟨(c.val : ℤ), (d.val : ℤ)⟩ : QuadraticAlgebra ℤ a b) - ⟨(c'.val : ℤ), (d'.val : ℤ)⟩) P₀
        = 0 := by
      rw [s.ι_sub_apply, sub_eq_zero]; exact congrArg Subtype.val hcd
    obtain ⟨h2, h3⟩ := natCast_dvd_iff_QA.mp (h.2 _ h1)
    simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.im_sub] at h2 h3
    exact Prod.ext (zmod_eq_of_dvd h2) (zmod_eq_of_dvd h3)
  have hbij := hinj.bijective_of_nat_card_le
    (le_of_eq (by rw [card_torsN hm, Nat.card_prod, Nat.card_zmod, sq]))
  obtain ⟨⟨c, d⟩, hcd⟩ := hbij.2 ⟨P, mem_torsN.mpr hP⟩
  exact ⟨_, congrArg Subtype.val hcd⟩

end CycQA

end RPLib.DWS


