-- Prove2me | Definitions.Def_RPLib_S4_PicDescentD2
-- name    : RPLib_S4_PicDescentD2
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:20:32.344241+00:00
-- url     : https://prove2.me/theorems/e1340e88-4e50-4ca6-ba45-b678db8c8f4f
-- title:
--   Unramified Dedekind extensions: valuations and fibres
-- statement:
--   Let $A \to B$ be a finite, torsion-free, formally unramified extension of Dedekind domains with fraction fields $K \subseteq L$. The file proves that every place $w$ of $B$ has ramification index $1$ over $v = w \cap A$, so $$v_v(x) = v_w(x) \qquad (x \in K),$$ that the fibre over $v$ is finite and nonempty with $\sum_{w \mid v} f(w|v) = [B : A]$ and $\#(A/v)^{f} = \#(B/w)$, and that for a ring automorphism $\sigma$ of $B$ the pulled-back place $\sigma^{-1}(w)$ satisfies $v_{\sigma^{-1}w}(x) = v_w(\sigma x)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Sections 8 and 9

import Definitions.Def_RPLib_S4_PicDescentD1

/-!
# S4-PicDescent, part D2: unramified Dedekind extensions, generic

* `A → B` Dedekind, finite, torsion free, formally unramified (`B ≅ A ⊗ L` for a separable `L`):
  every place `w` of `B` has ramification index `1` over `w.under A`, so
  `valuation_under : (w.under A).valuation K x = w.valuation L x'` (orders agree);
  the fibre over `v` is finite and nonempty, `Σ_{w | v} f(w|v) = [B : A]`, `#(A/v)^f = #(B/w)`.
* `pullH σ w = σ⁻¹(w)` for a ring automorphism `σ` of `B`: `valuation_pullH`
  (`(σ⁻¹ w).valuation x = w.valuation (σ x)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson.PicDescent

section Unram

variable {A B : Type*} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] [Module.IsTorsionFree A B] [Algebra.IsIntegral A B]

instance liesOver_under' (w : HeightOneSpectrum B) : w.asIdeal.LiesOver (w.under A).asIdeal := ⟨rfl⟩

theorem ramificationIdx'_under [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    (w : HeightOneSpectrum B) : (w.under A).asIdeal.ramificationIdx' w.asIdeal = 1 := by
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (w.under A).asIdeal w.asIdeal (w.under A).ne_bot]
  exact Ideal.ramificationIdx_eq_one w.asIdeal A

/-- **Orders agree** in an unramified extension. -/
theorem valuation_under [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra A K] [IsFractionRing A K] [Algebra A L]
    [IsScalarTower A K L] [Algebra B L] [IsFractionRing B L] [IsScalarTower A B L]
    (w : HeightOneSpectrum B) (x : K) :
    (w.under A).valuation K x = w.valuation L (algebraMap K L x) := by
  have h := HeightOneSpectrum.valuation_liesOver L (w.under A) w x
  rwa [ramificationIdx'_under, pow_one] at h

theorem finite_under (v : HeightOneSpectrum A) : {w : HeightOneSpectrum B | w.under A = v}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal B).preimage
    (f := HeightOneSpectrum.asIdeal) fun _ _ _ _ h => HeightOneSpectrum.ext h).subset ?_
  intro w hw
  refine ⟨w.isPrime, ⟨?_⟩⟩
  have hw' : w.under A = v := hw
  rw [← hw']
  rfl

theorem exists_under_eq (v : HeightOneSpectrum A) : ∃ w : HeightOneSpectrum B, w.under A = v := by
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) v.asIdeal ⊥ (by
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (Module.isTorsionFree_iff_algebraMap_injective.1 inferInstance)]
    exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (Module.isTorsionFree_iff_algebraMap_injective.1 inferInstance)]
  exact ⟨⟨Q, hQ, hQ0⟩, HeightOneSpectrum.ext hQv⟩

/-- **`Σ_{w | v} f(w | v) = [B : A]`** (all `e = 1`). -/
theorem sum_inertiaDeg [Module.Finite A B] [Module.Flat A B] [Algebra.EssFiniteType A B]
    [Algebra.FormallyUnramified A B] (v : HeightOneSpectrum A) :
    ∑ w ∈ (finite_under (B := B) v).toFinset, w.asIdeal.inertiaDeg A = Module.finrank A B := by
  classical
  letI : Fintype (v.asIdeal.primesOver B) := (IsDedekindDomain.primesOver_finite v.asIdeal B).fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank v.asIdeal B]
  refine Finset.sum_bij (fun w hw => ⟨w.asIdeal, w.isPrime, ⟨?_⟩⟩) (fun _ _ => Finset.mem_univ _)
    (fun w1 _ w2 _ h => HeightOneSpectrum.ext (congrArg Subtype.val h)) (fun q _ => ?_) (fun w _ => ?_)
  · have hw' := (Set.Finite.mem_toFinset _).1 hw
    simp only [Set.mem_ofPred_eq] at hw'
    rw [← hw']
    rfl
  · have hq0 : q.1 ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver v.ne_bot q.2
    haveI := q.2.1
    haveI := q.2.2
    refine ⟨⟨q.1, q.2.1, hq0⟩, (Set.Finite.mem_toFinset _).2 ?_, rfl⟩
    exact HeightOneSpectrum.ext (Ideal.LiesOver.over (P := q.1) (p := v.asIdeal)).symm
  · show _ = w.asIdeal.ramificationIdx A * w.asIdeal.inertiaDeg A
    rw [Ideal.ramificationIdx_eq_one w.asIdeal A, one_mul]

/-- `#(A / v)^f = #(B / w)`. -/
theorem card_quot_pow [Module.Finite A B] (w : HeightOneSpectrum B) :
    Nat.card (A ⧸ (w.under A).asIdeal) ^ w.asIdeal.inertiaDeg A = Nat.card (B ⧸ w.asIdeal) := by
  have h := Ideal.cardQuot_pow_inertiaDeg (w.under A).asIdeal w.asIdeal
  rwa [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h

end Unram

section Equiv

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

/-- `σ⁻¹(w)` for a ring automorphism `σ`. -/
def pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) : HeightOneSpectrum B :=
  HeightOneSpectrum.comap (σ : B →+* B) σ.surjective w

theorem pullH_asIdeal (σ : B ≃+* B) (w : HeightOneSpectrum B) :
    (pullH σ w).asIdeal = w.asIdeal.comap (σ : B →+* B) := rfl

theorem mem_pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) (b : B) :
    b ∈ (pullH σ w).asIdeal ↔ σ b ∈ w.asIdeal := Iff.rfl

theorem pow_pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) (n : ℕ) :
    (pullH σ w).asIdeal ^ n = (w.asIdeal ^ n).comap (σ : B →+* B) := by
  change (w.asIdeal.comap σ) ^ n = (w.asIdeal ^ n).comap σ
  rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

theorem intValuation_pullH (σ : B ≃+* B) (w : HeightOneSpectrum B) (b : B) :
    (pullH σ w).intValuation b = w.intValuation (σ b) := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hσb : σ b ≠ 0 := fun h => hb (σ.injective (h.trans (map_zero σ).symm))
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hb,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hσb]
  congr 3
  apply multiplicity_eq_of_emultiplicity_eq
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_le, Ideal.span_le, Set.singleton_subset_iff,
    Set.singleton_subset_iff, pow_pullH]
  exact Iff.rfl

/-- **Transport of valuations**: `(σ⁻¹ w)(x) = w(σ x)`. -/
theorem valuation_pullH {L : Type*} [Field L] [Algebra B L] [IsFractionRing B L] (σ : B ≃+* B)
    (σL : L ≃+* L) (hσ : ∀ b, algebraMap B L (σ b) = σL (algebraMap B L b))
    (w : HeightOneSpectrum B) (x : L) :
    (pullH σ w).valuation L x = w.valuation L (σL x) := by
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  rw [map_div₀, map_div₀, map_div₀, ← hσ, ← hσ, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_pullH, intValuation_pullH]

end Equiv

end RamanujanPetersson.PicDescent


