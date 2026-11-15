-- Prove2me | Definitions.Def_RPLib_S3_SBGalA
-- name    : RPLib_S3_SBGalA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:31:11.825224+00:00
-- url     : https://prove2.me/theorems/f609329f-cea3-448a-b601-16bbc188fdea
-- title:
--   Weight-two Ramanujan-Petersson library: S3-ZetaSB, E2b: the Galois action on `Rfin` and the twisted point bound
-- statement:
--   S3-ZetaSB, E2b: the Galois action on `Rfin` and the twisted point bound.
--
--   For a function field `E` over `Fq` that is Galois over `K = RatFunc Fq` with group `G`:
--   * `G` acts on `Rfin Fq E` (`galActRfin`), invariantly over `Fq[X]` (`isInvariant_poly`);
--   * an `L`-valued point `y` with `y ∘ g = Frob^m ∘ y` has a kernel `P` on which `g f ≡ f ^ (q ^ m)`
--     (`valuation_twist_lt`), so twisted Stepanov bounds the number of such points
--     (`card_twisted_le`): `N(g) ≤ ℓ0 (q ^ m + (2 g_E + 1) q ^ (m/2))`;
--   * if `ℓ0 ∣ m`, `N(g) = 0` unless `g` fixes the constant field (`fix_const_of_twist`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_SBCount
import Definitions.Def_RPLib_S3_SBTransport

/-!
# S3-ZetaSB, E2b: the Galois action on `Rfin` and the twisted point bound

For a function field `E` over `Fq` that is Galois over `K = RatFunc Fq` with group `G`:
* `G` acts on `Rfin Fq E` (`galActRfin`), invariantly over `Fq[X]` (`isInvariant_poly`);
* an `L`-valued point `y` with `y ∘ g = Frob^m ∘ y` has a kernel `P` on which `g f ≡ f ^ (q ^ m)`
  (`valuation_twist_lt`), so twisted Stepanov bounds the number of such points
  (`card_twisted_le`): `N(g) ≤ ℓ0 (q ^ m + (2 g_E + 1) q ^ (m/2))`;
* if `ℓ0 ∣ m`, `N(g) = 0` unless `g` fixes the constant field (`fix_const_of_twist`).
-/

set_option autoImplicit false

open WithZero IsDedekindDomain Polynomial

namespace RamanujanPetersson.ZetaSB

open RR

section FF

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {E : Type*} [Field E] [Algebra Fq E] [Algebra Fq[X] E] [Algebra (RatFunc Fq) E]
  [IsScalarTower Fq[X] (RatFunc Fq) E] [IsScalarTower Fq Fq[X] E] [FunctionField Fq E]
  [Algebra.IsSeparable (RatFunc Fq) E]

instance smulCommClass_gal_poly : SMulCommClass (E ≃ₐ[RatFunc Fq] E) Fq[X] E where
  smul_comm g a x := by
    change g (a • x) = a • g x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) E,
      AlgEquiv.commutes]

noncomputable instance galActRfin : MulSemiringAction (E ≃ₐ[RatFunc Fq] E) (Places.Rfin Fq E) :=
  inferInstanceAs (MulSemiringAction (E ≃ₐ[RatFunc Fq] E) (integralClosure Fq[X] E))

instance smulCommClass_gal_poly_Rfin : SMulCommClass (E ≃ₐ[RatFunc Fq] E) Fq[X] (Places.Rfin Fq E) :=
  inferInstanceAs (SMulCommClass (E ≃ₐ[RatFunc Fq] E) Fq[X] (integralClosure Fq[X] E))

theorem coe_gal_smul (g : E ≃ₐ[RatFunc Fq] E) (b : Places.Rfin Fq E) :
    ((g • b : Places.Rfin Fq E) : E) = g (b : E) := rfl

theorem gal_algebraMap_Fq (g : E ≃ₐ[RatFunc Fq] E) (c : Fq) : g (algebraMap Fq E c) = algebraMap Fq E c := by
  rw [IsScalarTower.algebraMap_apply Fq (RatFunc Fq) E, AlgEquiv.commutes]

instance smulCommClass_gal_Fq_Rfin : SMulCommClass (E ≃ₐ[RatFunc Fq] E) Fq (Places.Rfin Fq E) where
  smul_comm g c b := by
    apply Subtype.ext
    change g ((c • b : Places.Rfin Fq E) : E) = ((c • (g • b) : Places.Rfin Fq E) : E)
    rw [Subalgebra.coe_smul, Subalgebra.coe_smul, coe_gal_smul, Algebra.smul_def, Algebra.smul_def, map_mul,
      gal_algebraMap_Fq]

/-- Fixed points of the full Galois group in `Rfin` are polynomials. -/
theorem isInvariant_poly [IsGalois (RatFunc Fq) E] :
    Algebra.IsInvariant Fq[X] (Places.Rfin Fq E) (E ≃ₐ[RatFunc Fq] E) := by
  refine ⟨fun b hb => ?_⟩
  have hfix : ∀ g : E ≃ₐ[RatFunc Fq] E, g (b : E) = b := fun g => congrArg Subtype.val (hb g)
  have hmem : (b : E) ∈ (⊥ : IntermediateField (RatFunc Fq) E) := by
    rw [← IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField (RatFunc Fq) E)]
    exact fun g => hfix g
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  have hint : IsIntegral Fq[X] c := by
    have h2 : IsIntegral Fq[X] (b : E) := b.2
    rw [← hc] at h2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom Fq[X] (RatFunc Fq) E)
      (algebraMap (RatFunc Fq) E).injective).mp h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, Subtype.ext ?_⟩
  rw [← hc, ← ha, ← IsScalarTower.algebraMap_apply Fq[X] (RatFunc Fq) E]
  rfl

/-- If `g • b ≡ b ^ Q` modulo `P` for every integral `b` (with `Q` a power of the characteristic),
then `g f ≡ f ^ Q` at `P` for every `P`-integral `f`. -/
theorem valuation_twist_lt (g : E ≃ₐ[RatFunc Fq] E) (P : HeightOneSpectrum (Places.Rfin Fq E))
    (p k : ℕ) [hp : Fact p.Prime] [CharP E p]
    (h : ∀ b : Places.Rfin Fq E, g • b - b ^ (p ^ k) ∈ P.asIdeal) (f : E) (hf : P.valuation E f ≤ 1) :
    P.valuation E (g f - f ^ (p ^ k)) < 1 := by
  have hpk : 0 < p ^ k := pow_pos hp.out.pos k
  have hfixP : HeightOneSpectrum.equivOfRingEquiv (finEquiv g) P = P := by
    have := P.isMaximal
    apply HeightOneSpectrum.ext
    rw [equiv_asIdeal]
    have hle : P.asIdeal.map (finEquiv g) ≤ P.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap]
      have h1 := h b
      have h2 : b ^ (p ^ k) ∈ P.asIdeal := Ideal.pow_mem_of_mem _ hb _ hpk
      have h3 : finEquiv g b = (g • b - b ^ (p ^ k)) + b ^ (p ^ k) := by
        rw [sub_add_cancel]; rfl
      rw [h3]; exact Ideal.add_mem _ h1 h2
    exact (Ideal.map_isMaximal_of_equiv (finEquiv g) (p := P.asIdeal)).eq_of_le P.isMaximal.ne_top hle
  have hv : ∀ x : E, P.valuation E (g x) = P.valuation E x := by
    intro x
    have := valuation_equiv (finEquiv g) (g : E →+* E) (fun r => rfl) P x
    rwa [hfixP] at this
  obtain ⟨a, ha⟩ := P.exists_valuation_sub_lt_of_integer hf (1 : (ℤᵐ⁰)ˣ)
  obtain ⟨e, he, hfe⟩ : ∃ e : E, P.valuation E e < 1 ∧ f = algebraMap (Places.Rfin Fq E) E a + e :=
    ⟨f - algebraMap (Places.Rfin Fq E) E a, by rw [Valuation.map_sub_swap]; simpa using ha, by ring⟩
  subst hfe
  have hfrob : ∀ x y : E, (x + y) ^ (p ^ k) = x ^ (p ^ k) + y ^ (p ^ k) := fun x y => add_pow_char_pow x y p k
  have h1 : P.valuation E (algebraMap (Places.Rfin Fq E) E (g • a - a ^ (p ^ k))) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact h a
  have h2 : P.valuation E (g e - e ^ (p ^ k)) < 1 := by
    refine Valuation.map_sub_lt _ (by rw [hv]; exact he) ?_
    rw [map_pow]; exact pow_lt_one₀ zero_le he hpk.ne'
  have hsplit : g (algebraMap (Places.Rfin Fq E) E a + e) - (algebraMap (Places.Rfin Fq E) E a + e) ^ (p ^ k) =
      algebraMap (Places.Rfin Fq E) E (g • a - a ^ (p ^ k)) + (g e - e ^ (p ^ k)) := by
    rw [hfrob, map_add, map_sub, map_pow]
    change g (a : E) + g e - ((a : E) ^ (p ^ k) + e ^ (p ^ k)) =
      ((g • a : Places.Rfin Fq E) : E) - (a : E) ^ (p ^ k) + (g e - e ^ (p ^ k))
    rw [coe_gal_smul]; ring
  rw [hsplit]; exact Valuation.map_add_lt _ h1 h2

variable (L : Type*) [Field L] [Algebra Fq L] [Finite L]

/-- The kernel of a twisted Frobenius point satisfies the congruence of `valuation_twist_lt`. -/
theorem sub_mem_kerPlace (g : E ≃ₐ[RatFunc Fq] E) (Q : ℕ) (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ Q)
    (y : Places.Rfin Fq E →ₐ[Fq] L) (hy : twist y g = φ.comp y) (b : Places.Rfin Fq E) :
    g • b - b ^ Q ∈ (Places.kerPlace Fq L y).asIdeal := by
  change g • b - b ^ Q ∈ RingHom.ker y
  rw [RingHom.mem_ker, map_sub, map_pow]
  have := congrArg (fun z : Places.Rfin Fq E →ₐ[Fq] L => z b) hy
  simp only [twist_apply, AlgHom.comp_apply, hφ] at this
  rw [this, sub_self]

/-- Twisted points are at most the total degree of their kernels. -/
theorem card_twisted_le_sum [Fintype (Places.Rfin Fq E →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq E →ₐ[Fq] L)]
    [DecidableEq (HeightOneSpectrum (Places.Rfin Fq E))] (g : E ≃ₐ[RatFunc Fq] E) (φ : L →ₐ[Fq] L) :
    (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card ≤
      ∑ P ∈ (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).image
        (Places.kerPlace Fq L), Places.deg Fq P := by
  classical
  rw [Finset.card_eq_sum_card_image (Places.kerPlace Fq L)]
  refine Finset.sum_le_sum fun P _ => ?_
  calc _ ≤ (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => Places.kerPlace Fq L y = P).card :=
        Finset.card_le_card fun y hy => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact hy.2
    _ = Nat.card {y : Places.Rfin Fq E →ₐ[Fq] L // Places.kerPlace Fq L y = P} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ Places.deg Fq P := by
        rw [Places.card_fiber]; split_ifs <;> simp

/-- **Twisted point bound.** `N(g) ≤ ℓ0 (Q0 ^ 2 + (2 g + 1) Q0)` when `φ = Frob_{Q0 ^ 2}`, `Q0 = p ^ k`,
`E` has a place `P0` of degree `ℓ0 = ℓ(0)` and `(g + ℓ0) ^ 2 < ℓ0 ^ 2 Q0`. -/
theorem card_twisted_le [Fintype (Places.Rfin Fq E →ₐ[Fq] L)] [DecidableEq (Places.Rfin Fq E →ₐ[Fq] L)]
    (g : E ≃ₐ[RatFunc Fq] E) (p : ℕ) [hp : Fact p.Prime] [CharP E p] (k Q0 : ℕ) (hQ0def : Q0 = p ^ k)
    (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ (Q0 ^ 2))
    (P0 : Places.Place Fq E) (hP0 : P0.deg = ellF Fq E 0)
    (hQ0 : (genusF Fq E + ellF Fq E 0) ^ 2 < ellF Fq E 0 ^ 2 * Q0) :
    (Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y).card ≤
      ellF Fq E 0 * (Q0 ^ 2 + (2 * genusF Fq E + 1) * Q0) := by
  classical
  set s := Finset.univ.filter fun y : Places.Rfin Fq E →ₐ[Fq] L => twist y g = φ.comp y with hs
  set T := s.image (Places.kerPlace Fq L) with hT
  set T' : Finset (Places.Place Fq E) := T.map Function.Embedding.inl with hT'
  set ℓ0 := ellF Fq E 0 with hℓ0
  set gE := genusF Fq E with hgE
  have hQ2 : Q0 ^ 2 = p ^ (k * 2) := by rw [hQ0def, ← pow_mul]
  have hℓpos : 1 ≤ ℓ0 := by
    rcases Nat.eq_zero_or_pos ℓ0 with h0 | h0
    · rw [h0] at hQ0; simp at hQ0
    · exact h0
  have hB : ℓ0 * Q0 + 2 * gE ≤ ℓ0 * (Q0 + 2 * gE) := by rw [mul_add]; nlinarith
  have hmain := twisted_stepanovF g p k Q0 hQ0def P0 hP0 (Q0 + 2 * gE) hB hQ0 T' (by
      intro P hP _ f hf
      rw [hT', Finset.mem_map] at hP
      obtain ⟨P', hP', rfl⟩ := hP
      rw [hT, Finset.mem_image] at hP'
      obtain ⟨y, hy, rfl⟩ := hP'
      rw [hs, Finset.mem_filter] at hy
      change (Places.kerPlace Fq L y).valuation E (g f - f ^ (Q0 ^ 2)) < 1
      rw [hQ2]
      refine valuation_twist_lt g _ p (k * 2) (fun b => ?_) f hf
      rw [← hQ2]
      exact sub_mem_kerPlace L g (Q0 ^ 2) φ hφ y hy.2 b)
  have hle := card_twisted_le_sum L g φ
  rw [← hs, ← hT] at hle
  have hsumT : ∑ P ∈ T, Places.deg Fq P = ∑ P ∈ T', P.deg := by
    rw [hT', Finset.sum_map]; rfl
  have hsplit : ∑ P ∈ T', P.deg ≤ ∑ P ∈ T'.erase P0, P.deg + ℓ0 := by
    by_cases hP0T : P0 ∈ T'
    · rw [← Finset.add_sum_erase _ _ hP0T, hP0, add_comm]
    · rw [Finset.erase_eq_of_notMem hP0T]; exact Nat.le_add_right _ _
  have hQ0pos : 0 < Q0 := hQ0def ▸ pow_pos hp.out.pos k
  have hS : ∑ P ∈ T'.erase P0, P.deg ≤ ℓ0 * ((Q0 - 1) + Q0 * (Q0 + 2 * gE)) := by
    refine Nat.le_of_mul_le_mul_left ?_ hQ0pos
    calc Q0 * ∑ P ∈ T'.erase P0, P.deg ≤ ℓ0 * (Q0 * (Q0 - 1) + Q0 ^ 2 * (Q0 + 2 * gE)) := hmain
      _ = Q0 * (ℓ0 * ((Q0 - 1) + Q0 * (Q0 + 2 * gE))) := by ring
  have hX : ℓ0 * (Q0 ^ 2 + (2 * gE + 1) * Q0) = ℓ0 * ((Q0 - 1) + Q0 * (Q0 + 2 * gE)) + ℓ0 := by
    obtain ⟨Q1, rfl⟩ : ∃ Q1, Q0 = Q1 + 1 := ⟨Q0 - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; ring
  rw [hX]
  calc s.card ≤ ∑ P ∈ T, Places.deg Fq P := hle
    _ ≤ _ := by rw [hsumT]; exact hsplit.trans (Nat.add_le_add_right hS _)

/-- If `ℓ0 ∣ m`, a twisted Frobenius point forces `g` to fix the constant field. -/
theorem fix_const_of_twist {m : ℕ} (hm : Module.finrank Fq (Places.constField Fq E) ∣ m)
    (g : E ≃ₐ[RatFunc Fq] E) (φ : L →ₐ[Fq] L) (hφ : ∀ x, φ x = x ^ (Fintype.card Fq ^ m))
    (y : Places.Rfin Fq E →ₐ[Fq] L) (hy : twist y g = φ.comp y) (c : Places.constField Fq E) :
    g (c : E) = c := by
  classical
  have hgc : IsIntegral Fq (g (c : E)) := by
    have hc := Places.isIntegral_of_mem_constField Fq E c
    exact hc.map ((g : E →ₐ[RatFunc Fq] E).restrictScalars Fq)
  let gc : Places.constField Fq E := ⟨g c, mem_algebraicClosure_iff.mpr hgc.isAlgebraic⟩
  let ψ : Places.constField Fq E →ₐ[Fq] L := y.comp (Places.constToRfin Fq E)
  have hconst : ∀ x : Places.constField Fq E, x ^ (Fintype.card Fq ^ m) = x := by
    intro x
    have : Finite (Places.constField Fq E) := Module.finite_of_finite Fq
    let _ : Fintype (Places.constField Fq E) := Fintype.ofFinite _
    obtain ⟨j, hj⟩ := hm
    have hcard : Fintype.card (Places.constField Fq E) =
        Fintype.card Fq ^ Module.finrank Fq (Places.constField Fq E) := Module.card_eq_pow_finrank
    rw [hj, pow_mul, ← hcard]
    exact Places.pow_card_pow_eq x j
  have hψ : ψ gc = ψ c := by
    have h1 : Places.constToRfin Fq E gc = g • Places.constToRfin Fq E c := Subtype.ext rfl
    change y (Places.constToRfin Fq E gc) = y (Places.constToRfin Fq E c)
    rw [h1, ← twist_apply, hy, AlgHom.comp_apply, hφ, ← map_pow, ← map_pow, hconst]
  have := ψ.toRingHom.injective hψ
  exact congrArg Subtype.val this

end FF

end RamanujanPetersson.ZetaSB


