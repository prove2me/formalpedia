-- Prove2me | Definitions.Def_RPLib_S2_LevelRaise
-- name    : RPLib_S2_LevelRaise
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:28.4804+00:00
-- url     : https://prove2.me/theorems/a65892d9-a7dd-47c1-87cf-4bb830591810
-- title:
--   Level raising for Hecke eigen-systems on $\Gamma_1(L)$
-- statement:
--   A normalized Hecke eigen-system with nebentypus $\chi$ on $\Gamma_1(L)$ is also one on $\Gamma_1(Lr)$ with the character lifted to modulus $Lr$, for a prime $r \ge 5$ different from a given prime $p \nmid L$. Consequently root bounds at primes $p \nmid L$ for all levels follow from the case $L \ge 4$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.6

import Mathlib

/-!
# Level raising for the Deligne / Deligne-Serre root bounds (RP project, unit S2-LevelRaise)

Pure Mathlib (0df444a). Given a normalized eigen-system `F` on `Γ₁(L)` with nebentypus `χ`
(the hypotheses of N4 `deligne_hecke_root_bound` / N5 `deligne_serre_hecke_root_bound`) and a
prime `p ∤ L`, we pick a prime `r ≥ 5`, `r ≠ p`, and view `F` on `Γ₁(L * r)` with the character
`χ.changeLevel`. All N4/N5 hypotheses transfer, `p ∤ L * r` and `4 ≤ L * r`. Consequently it
suffices to prove N4 and N5 for levels `L ≥ 4`
(`deligne_hecke_root_bound_of_four_le`, `deligne_serre_hecke_root_bound_of_four_le`).
-/

open UpperHalfPlane Filter Asymptotics MatrixGroups ModularForm

set_option autoImplicit false

namespace RamanujanPetersson.LevelRaise

open CongruenceSubgroup

/-- Restriction of a cusp form to a smaller group (same underlying function). -/
noncomputable def cuspFormRestrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : CuspForm Γ k) : CuspForm Γ' k where
  toFun := ⇑f
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := CuspFormClass.holo f
  zero_at_cusps' := fun hc => CuspFormClass.zero_at_cusps f (hc.mono hle)

@[simp]
lemma coe_cuspFormRestrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : CuspForm Γ k) : ⇑(cuspFormRestrict hle f) = ⇑f := rfl

lemma qExpansion_cuspFormRestrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : CuspForm Γ k) (h : ℝ) : qExpansion h (cuspFormRestrict hle f) = qExpansion h f := rfl

lemma zmod_intCast_eq_one_of_dvd {m n : ℕ} (h : n ∣ m) {a : ℤ} (ha : (a : ZMod m) = 1) :
    (a : ZMod n) = 1 := by
  have := congrArg (ZMod.castHom h (ZMod n)) ha
  rwa [map_intCast, map_one] at this

lemma zmod_intCast_eq_zero_of_dvd {m n : ℕ} (h : n ∣ m) {a : ℤ} (ha : (a : ZMod m) = 0) :
    (a : ZMod n) = 0 := by
  have := congrArg (ZMod.castHom h (ZMod n)) ha
  simpa using this

lemma Gamma1_le_of_dvd {n m : ℕ} (h : n ∣ m) : Gamma1 m ≤ Gamma1 n := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  exact ⟨zmod_intCast_eq_one_of_dvd h hA.1, zmod_intCast_eq_one_of_dvd h hA.2.1,
    zmod_intCast_eq_zero_of_dvd h hA.2.2⟩

lemma Gamma0_le_of_dvd {n m : ℕ} (h : n ∣ m) : Gamma0 m ≤ Gamma0 n := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  exact zmod_intCast_eq_zero_of_dvd h hA

lemma Gamma1_GL_le_of_dvd {n m : ℕ} (h : n ∣ m) :
    ((Gamma1 m : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 n : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, Gamma1_le_of_dvd h hx, rfl⟩

/-- The lower-right entry of an element of `Γ₀(N)` is coprime to `N`. -/
lemma isCoprime_of_mem_Gamma0 {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    IsCoprime (γ 1 1) (N : ℤ) := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
  obtain ⟨t, ht⟩ := hγ
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet
  exact ⟨γ 0 0, -(γ 0 1 * t), by linear_combination hdet + (γ 0 1) * ht⟩

/-- `χ.changeLevel` agrees with `χ` on primes not dividing the new level. -/
lemma changeLevel_natCast_of_prime {n m : ℕ} (hm : n ∣ m) (χ : DirichletCharacter ℂ n)
    {q : ℕ} (hq : q.Prime) (hqm : ¬ q ∣ m) :
    DirichletCharacter.changeLevel hm χ (q : ZMod m) = χ (q : ZMod n) := by
  have hcop : IsCoprime (q : ℤ) (m : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr hqm
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hm hcop
  simpa using this

/-- The nebentypus condition transfers to `Γ₀(M)` (for `L ∣ M`) with `χ.changeLevel`. -/
lemma nebentypus_changeLevel {L M : ℕ} (hLM : L ∣ M) {k : ℤ} (χ : DirichletCharacter ℂ L)
    (f : ℍ → ℂ)
    (hχ : ∀ γ ∈ Gamma0 L, (f ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • f) :
    ∀ γ ∈ Gamma0 M, (f ∣[k] γ) =
      DirichletCharacter.changeLevel hLM χ ((γ 1 1 : ℤ) : ZMod M) • f := by
  intro γ hγ
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hLM (isCoprime_of_mem_Gamma0 hγ)]
  exact hχ γ (Gamma0_le_of_dvd hLM hγ)

/-- An auxiliary prime `r ≥ 5` different from `p`. -/
lemma exists_aux_prime (p : ℕ) : ∃ r : ℕ, r.Prime ∧ r ≠ p ∧ 5 ≤ r := by
  by_cases hp5 : p = 5
  · exact ⟨7, by norm_num, by omega, by norm_num⟩
  · exact ⟨5, by norm_num, fun h => hp5 h.symm, le_refl 5⟩

lemma not_dvd_mul_prime {p L r : ℕ} (hp : p.Prime) (hr : r.Prime) (hrp : r ≠ p)
    (hpL : ¬ p ∣ L) : ¬ p ∣ L * r := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact hpL h
  · exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp h).symm

/-- Level raising, weight `k` (N4 form): all hypotheses of `deligne_hecke_root_bound` at level
`L` transfer to level `L * r` for an auxiliary prime `r ≥ 5`, `r ≠ p`. -/
theorem exists_levelRaise (L : ℕ) (hL : 0 < L) (k : ℤ)
    (χ : DirichletCharacter ℂ L)
    (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k)
    (hχ : ∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F)
    (h1 : (qExpansion 1 F).coeff 1 = 1)
    (hrec : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
      (qExpansion 1 F).coeff (q * n) =
        (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
          χ (q : ZMod L) * (q : ℂ) ^ (k - 1) *
            (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0))
    (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ L) :
    ∃ r : ℕ, r.Prime ∧ r ≠ p ∧ 5 ≤ r ∧ 4 ≤ L * r ∧ ¬ p ∣ L * r ∧
      ∃ F' : CuspForm ((CongruenceSubgroup.Gamma1 (L * r) : Subgroup SL(2, ℤ)) :
          Subgroup (GL (Fin 2) ℝ)) k,
        ⇑F' = ⇑F ∧ qExpansion 1 F' = qExpansion 1 F ∧
        (∀ γ ∈ CongruenceSubgroup.Gamma0 (L * r), (⇑F' ∣[k] γ) =
          DirichletCharacter.changeLevel (Nat.dvd_mul_right L r) χ
            ((γ 1 1 : ℤ) : ZMod (L * r)) • ⇑F') ∧
        (qExpansion 1 F').coeff 1 = 1 ∧
        (∀ q n : ℕ, q.Prime → ¬ q ∣ L * r →
          (qExpansion 1 F').coeff (q * n) =
            (qExpansion 1 F').coeff q * (qExpansion 1 F').coeff n -
              DirichletCharacter.changeLevel (Nat.dvd_mul_right L r) χ (q : ZMod (L * r)) *
                (q : ℂ) ^ (k - 1) *
                (if q ∣ n then (qExpansion 1 F').coeff (n / q) else 0)) ∧
        DirichletCharacter.changeLevel (Nat.dvd_mul_right L r) χ (p : ZMod (L * r)) =
          χ (p : ZMod L) := by
  obtain ⟨r, hr, hrp, hr5⟩ := exists_aux_prime p
  have hdvd : L ∣ L * r := Nat.dvd_mul_right L r
  have hpLr : ¬ p ∣ L * r := not_dvd_mul_prime hp hr hrp hpL
  have h4 : 4 ≤ L * r := by nlinarith
  refine ⟨r, hr, hrp, hr5, h4, hpLr, cuspFormRestrict (Gamma1_GL_le_of_dvd hdvd) F, rfl, rfl,
    ?_, h1, ?_, changeLevel_natCast_of_prime hdvd χ hp hpLr⟩
  · exact nebentypus_changeLevel hdvd χ ⇑F hχ
  · intro q n hq hqLr
    have hqL : ¬ q ∣ L := fun h => hqLr (dvd_mul_of_dvd_left h r)
    rw [qExpansion_cuspFormRestrict, changeLevel_natCast_of_prime hdvd χ hq hqLr]
    exact hrec q n hq hqL

/-- Level raising, weight `1` (N5 form). -/
theorem exists_levelRaise_wt1 (L : ℕ) (hL : 0 < L)
    (χ : DirichletCharacter ℂ L)
    (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) 1)
    (hχ : ∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[(1 : ℤ)] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F)
    (h1 : (qExpansion 1 F).coeff 1 = 1)
    (hrec : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
      (qExpansion 1 F).coeff (q * n) =
        (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
          χ (q : ZMod L) * (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0))
    (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ L) :
    ∃ r : ℕ, r.Prime ∧ r ≠ p ∧ 5 ≤ r ∧ 4 ≤ L * r ∧ ¬ p ∣ L * r ∧
      ∃ F' : CuspForm ((CongruenceSubgroup.Gamma1 (L * r) : Subgroup SL(2, ℤ)) :
          Subgroup (GL (Fin 2) ℝ)) 1,
        ⇑F' = ⇑F ∧ qExpansion 1 F' = qExpansion 1 F ∧
        (∀ γ ∈ CongruenceSubgroup.Gamma0 (L * r), (⇑F' ∣[(1 : ℤ)] γ) =
          DirichletCharacter.changeLevel (Nat.dvd_mul_right L r) χ
            ((γ 1 1 : ℤ) : ZMod (L * r)) • ⇑F') ∧
        (qExpansion 1 F').coeff 1 = 1 ∧
        (∀ q n : ℕ, q.Prime → ¬ q ∣ L * r →
          (qExpansion 1 F').coeff (q * n) =
            (qExpansion 1 F').coeff q * (qExpansion 1 F').coeff n -
              DirichletCharacter.changeLevel (Nat.dvd_mul_right L r) χ (q : ZMod (L * r)) *
                (if q ∣ n then (qExpansion 1 F').coeff (n / q) else 0)) ∧
        DirichletCharacter.changeLevel (Nat.dvd_mul_right L r) χ (p : ZMod (L * r)) =
          χ (p : ZMod L) := by
  obtain ⟨r, hr, hrp, hr5⟩ := exists_aux_prime p
  have hdvd : L ∣ L * r := Nat.dvd_mul_right L r
  have hpLr : ¬ p ∣ L * r := not_dvd_mul_prime hp hr hrp hpL
  have h4 : 4 ≤ L * r := by nlinarith
  refine ⟨r, hr, hrp, hr5, h4, hpLr, cuspFormRestrict (Gamma1_GL_le_of_dvd hdvd) F, rfl, rfl,
    ?_, h1, ?_, changeLevel_natCast_of_prime hdvd χ hp hpLr⟩
  · exact nebentypus_changeLevel hdvd χ ⇑F hχ
  · intro q n hq hqLr
    have hqL : ¬ q ∣ L := fun h => hqLr (dvd_mul_of_dvd_left h r)
    rw [qExpansion_cuspFormRestrict, changeLevel_natCast_of_prime hdvd χ hq hqLr]
    exact hrec q n hq hqL

/-- **Reduction of N4 to levels `L ≥ 4`.** If the Deligne root bound holds (at weight `k`) for
every eigen-system of level `L ≥ 4`, it holds at every level `L > 0`. -/
theorem deligne_hecke_root_bound_of_four_le (k : ℤ)
    (H : ∀ (L : ℕ), 4 ≤ L → ∀ (χ : DirichletCharacter ℂ L)
      (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k),
      (∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F) →
      (qExpansion 1 F).coeff 1 = 1 →
      (∀ q n : ℕ, q.Prime → ¬ q ∣ L →
        (qExpansion 1 F).coeff (q * n) =
          (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
            χ (q : ZMod L) * (q : ℂ) ^ (k - 1) *
              (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0)) →
      ∀ p : ℕ, p.Prime → ¬ p ∣ L → ∀ α : ℂ,
        α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) * (p : ℂ) ^ (k - 1) = 0 →
          ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2))
    (L : ℕ) (hL : 0 < L)
    (χ : DirichletCharacter ℂ L)
    (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k)
    (hχ : ∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F)
    (h1 : (qExpansion 1 F).coeff 1 = 1)
    (hrec : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
      (qExpansion 1 F).coeff (q * n) =
        (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
          χ (q : ZMod L) * (q : ℂ) ^ (k - 1) *
            (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0))
    (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ L) (α : ℂ)
    (hα : α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) * (p : ℂ) ^ (k - 1) = 0) :
    ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) := by
  obtain ⟨r, _, _, _, h4, hpLr, F', _, hq, hχ', h1', hrec', hχp⟩ :=
    exists_levelRaise L hL k χ F hχ h1 hrec p hp hpL
  refine H (L * r) h4 _ F' hχ' h1' hrec' p hp hpLr α ?_
  rw [hq, hχp]
  exact hα

/-- **Reduction of N5 to levels `L ≥ 4`.** If the Deligne-Serre root bound holds for every
weight-one eigen-system of level `L ≥ 4`, it holds at every level `L > 0`. -/
theorem deligne_serre_hecke_root_bound_of_four_le
    (H : ∀ (L : ℕ), 4 ≤ L → ∀ (χ : DirichletCharacter ℂ L)
      (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) 1),
      (∀ γ ∈ CongruenceSubgroup.Gamma0 L,
        (⇑F ∣[(1 : ℤ)] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F) →
      (qExpansion 1 F).coeff 1 = 1 →
      (∀ q n : ℕ, q.Prime → ¬ q ∣ L →
        (qExpansion 1 F).coeff (q * n) =
          (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
            χ (q : ZMod L) * (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0)) →
      ∀ p : ℕ, p.Prime → ¬ p ∣ L → ∀ α : ℂ,
        α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) = 0 → ‖α‖ ≤ 1)
    (L : ℕ) (hL : 0 < L)
    (χ : DirichletCharacter ℂ L)
    (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) 1)
    (hχ : ∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[(1 : ℤ)] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F)
    (h1 : (qExpansion 1 F).coeff 1 = 1)
    (hrec : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
      (qExpansion 1 F).coeff (q * n) =
        (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
          χ (q : ZMod L) * (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0))
    (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ L) (α : ℂ)
    (hα : α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) = 0) :
    ‖α‖ ≤ 1 := by
  obtain ⟨r, _, _, _, h4, hpLr, F', _, hq, hχ', h1', hrec', hχp⟩ :=
    exists_levelRaise_wt1 L hL χ F hχ h1 hrec p hp hpL
  refine H (L * r) h4 _ F' hχ' h1' hrec' p hp hpLr α ?_
  rw [hq, hχp]
  exact hα

/-- N4 in its exact R0 form follows from N4 at levels `L ≥ 4` (all weights `k ≥ 2`). -/
theorem deligne_hecke_root_bound_of_four_le'
    (H : ∀ (L : ℕ), 4 ≤ L → ∀ (k : ℤ), 2 ≤ k → ∀ (χ : DirichletCharacter ℂ L)
      (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
        Subgroup (GL (Fin 2) ℝ)) k),
      (∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F) →
      (qExpansion 1 F).coeff 1 = 1 →
      (∀ q n : ℕ, q.Prime → ¬ q ∣ L →
        (qExpansion 1 F).coeff (q * n) =
          (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
            χ (q : ZMod L) * (q : ℂ) ^ (k - 1) *
              (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0)) →
      ∀ p : ℕ, p.Prime → ¬ p ∣ L → ∀ α : ℂ,
        α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) * (p : ℂ) ^ (k - 1) = 0 →
          ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2))
    (L : ℕ) (hL : 0 < L) (k : ℤ) (hk : 2 ≤ k)
    (χ : DirichletCharacter ℂ L)
    (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k)
    (hχ : ∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F)
    (h1 : (qExpansion 1 F).coeff 1 = 1)
    (hrec : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
      (qExpansion 1 F).coeff (q * n) =
        (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
          χ (q : ZMod L) * (q : ℂ) ^ (k - 1) *
            (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0))
    (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ L) (α : ℂ)
    (hα : α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) * (p : ℂ) ^ (k - 1) = 0) :
    ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) :=
  deligne_hecke_root_bound_of_four_le k (fun L' hL' => H L' hL' k hk) L hL χ F hχ h1 hrec
    p hp hpL α hα

end RamanujanPetersson.LevelRaise

-- axiom audit
#print axioms RamanujanPetersson.LevelRaise.deligne_hecke_root_bound_of_four_le'
#print axioms RamanujanPetersson.LevelRaise.deligne_serre_hecke_root_bound_of_four_le


