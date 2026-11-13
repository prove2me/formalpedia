-- Prove2me | Definitions.Def_RPLib_S1_Newforms
-- name    : RPLib_S1_Newforms
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:31:01.992833+00:00
-- url     : https://prove2.me/theorems/ee0b97a1-3ffe-4160-be26-23bd72b53bd9
-- title:
--   Old and new subspaces of $S_k(\Gamma_1(M))$ and newforms
-- statement:
--   The old subspace of $S_k(\Gamma_1(M))$ is the span of $\mathrm{incl}\, S_k(\Gamma_1(M/p))$ and $\iota_p S_k(\Gamma_1(M/p))$ over primes $p \mid M$; the new subspace is its Petersson orthogonal complement. Both are stable under $T_q$ ($q \nmid M$) and the diamond operators. A newform is a normalised simultaneous eigenform in the new subspace. The file proves that every eigenform in $S_k^{\mathrm{new}}(M,\chi)$ has $a_1 \neq 0$, that a normalised one is an eigenform of every $T_n$ and $U_p$ with $T_n f = a_n(f) f$, strong multiplicity one, that newforms span the new subspace, and the full Hecke recursion for their coefficients.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Theorem 5.8.2; A. O. L. Atkin and J. Lehner, Hecke operators on Gamma_0(m), Math. Ann. 185 (1970) 134-160, doi:10.1007/BF01359701; W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975) 285-315, doi:10.1007/BF01344468

import Mathlib
import Definitions.Def_RPLib_S1_Eigenbasis
import Definitions.Def_RPLib_S1_MainLemma

/-!
# Old and new subspaces, newforms and multiplicity one (DS §5.6-5.8)

`oldSpace M k = Σ_{p ∣ M} (incl S_k(Γ₁(M/p)) + ι_p S_k(Γ₁(M/p)))`, `newSpace M k = oldSpace^⊥` (Petersson).
Main results: stability under `T_q` (`q ∤ M`), `⟨d⟩`, `U_q` (`q ∣ M`, old space); DS Thm 5.8.2
(`a_1 ≠ 0`, `U_p`-eigen with eigenvalue `a_p`, multiplicity one) via the Main Lemma; a spanning set of
normalised newforms of `S^new(M, χ)`; the full N2 recursion for newforms.
-/

set_option autoImplicit false

open UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups

noncomputable section

namespace RP.Newforms

open RamanujanPetersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke
  RamanujanPetersson.HeckeAlgebra RP.Petersson RP.Adjoint RP.Eigenbasis

/-! ## Definitions -/

section defs

variable (M : ℕ) (k : ℤ)

/-- `incl : S_k(Γ₁(M/p)) → S_k(Γ₁(M))` when `p ∣ M` (else `0`). -/
def inclP (p : ℕ) : S1 (M / p) k →ₗ[ℂ] S1 M k :=
  if hp : p ∣ M then Level.inclCF (Nat.div_dvd_of_dvd hp) k else 0

lemma inclP_eq {p : ℕ} (hp : p ∣ M) : inclP M k p = Level.inclCF (Nat.div_dvd_of_dvd hp) k := by
  rw [inclP, dif_pos hp]

/-- The old space `Σ_{p ∣ M} (incl S_k(Γ₁(M/p)) + ι_p S_k(Γ₁(M/p)))`. -/
def oldSpace : Submodule ℂ (S1 M k) :=
  ⨆ p ∈ M.primeFactors, (LinearMap.range (inclP M k p) ⊔ LinearMap.range (MainLemma.iotaP M p k))

variable [NeZero M]

/-- The new space: the Petersson orthogonal complement of the old space. -/
def newSpace : Submodule ℂ (S1 M k) := perp k (oldSpace M k)

end defs

variable {M : ℕ} {k : ℤ}

lemma inclP_mem_oldSpace {p : ℕ} (hp : p ∈ M.primeFactors) (g : S1 (M / p) k) :
    inclP M k p g ∈ oldSpace M k :=
  Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem hp
    (Submodule.mem_sup_left (LinearMap.mem_range_self _ g)))

lemma iotaP_mem_oldSpace {p : ℕ} (hp : p ∈ M.primeFactors) (g : S1 (M / p) k) :
    MainLemma.iotaP M p k g ∈ oldSpace M k :=
  Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem hp
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ g)))

/-- A linear map preserving the generators preserves the old space. -/
theorem map_mem_oldSpace (T : S1 M k →ₗ[ℂ] S1 M k)
    (h1 : ∀ p ∈ M.primeFactors, ∀ g, T (inclP M k p g) ∈ oldSpace M k)
    (h2 : ∀ p ∈ M.primeFactors, ∀ g, T (MainLemma.iotaP M p k g) ∈ oldSpace M k)
    {f : S1 M k} (hf : f ∈ oldSpace M k) : T f ∈ oldSpace M k := by
  have hle : oldSpace M k ≤ (oldSpace M k).comap T := by
    refine iSup₂_le fun p hp => sup_le ?_ ?_
    · rintro _ ⟨g, rfl⟩; exact h1 p hp g
    · rintro _ ⟨g, rfl⟩; exact h2 p hp g
  exact hle hf

lemma neZero_div {p : ℕ} [NeZero M] (hp : p ∈ M.primeFactors) : NeZero (M / p) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.dvd_of_mem_primeFactors hp))
    (Nat.prime_of_mem_primeFactors hp).pos).ne'⟩

/-- Every form with vanishing coefficients at all `n` coprime to `M` is old (Main Lemma). -/
theorem mem_oldSpace_of_coeff [NeZero M] (f : S1 M k)
    (hf : ∀ n : ℕ, Nat.Coprime n M → (qExpansion 1 f).coeff n = 0) : f ∈ oldSpace M k := by
  have h := MainLemma.mainLemma_mem_iSup M k f hf
  have hle : (⨆ p ∈ M.primeFactors, LinearMap.range (MainLemma.iotaP M p k)) ≤ oldSpace M k :=
    iSup₂_le fun p hp => by rintro _ ⟨g, rfl⟩; exact iotaP_mem_oldSpace hp g
  exact hle h

/-! ## Stability -/

section stability

variable [NeZero M]

/-- The old space is stable under every `⟨d⟩`. -/
theorem diamond_mem_oldSpace (d : (ZMod M)ˣ) {f : S1 M k} (hf : f ∈ oldSpace M k) :
    diamond k d f ∈ oldSpace M k := by
  refine map_mem_oldSpace (diamond k d) (fun p hp g => ?_) (fun p hp g => ?_) hf
  · haveI := neZero_div hp
    have hpM := Nat.dvd_of_mem_primeFactors hp
    rw [inclP_eq M k hpM, diamond_inclCF, ← inclP_eq M k hpM]
    exact inclP_mem_oldSpace hp _
  · haveI := neZero_div hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpM := Nat.dvd_of_mem_primeFactors hp
    haveI : NeZero p := ⟨hpp.ne_zero⟩
    rw [MainLemma.iotaP_eq M k hpp hpM, diamond_iotaCF, ← MainLemma.iotaP_eq M k hpp hpM]
    exact iotaP_mem_oldSpace hp _

/-- The old space is stable under every `T_q`, `q ∤ M`. -/
theorem heckeT_mem_oldSpace_of_not_dvd (q : ℕ) [Fact q.Prime] (hqM : ¬ q ∣ M) {f : S1 M k}
    (hf : f ∈ oldSpace M k) : heckeT q k f ∈ oldSpace M k := by
  refine map_mem_oldSpace (heckeT q k) (fun p hp g => ?_) (fun p hp g => ?_) hf
  · haveI := neZero_div hp
    have hpM := Nat.dvd_of_mem_primeFactors hp
    rw [inclP_eq M k hpM, heckeT_inclCF _ k q hqM, ← inclP_eq M k hpM]
    exact inclP_mem_oldSpace hp _
  · haveI := neZero_div hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpM := Nat.dvd_of_mem_primeFactors hp
    haveI : NeZero p := ⟨hpp.ne_zero⟩
    rw [MainLemma.iotaP_eq M k hpp hpM, heckeT_iotaCF p _ k q hqM, ← MainLemma.iotaP_eq M k hpp hpM]
    exact iotaP_mem_oldSpace hp _

/-- `U_q ∘ ι_q = incl` (coefficients). -/
lemma heckeT_iotaP_self (q : ℕ) [hq : Fact q.Prime] (hqM : q ∣ M) (g : S1 (M / q) k) :
    haveI : NeZero (M / q) := neZero_div (Nat.mem_primeFactors.2 ⟨hq.out, hqM, NeZero.ne M⟩)
    heckeT q k (MainLemma.iotaP M q k g) = inclP M k q g := by
  haveI : NeZero (M / q) := neZero_div (Nat.mem_primeFactors.2 ⟨hq.out, hqM, NeZero.ne M⟩)
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  apply eq_of_csL
  funext n
  rw [csL_apply, csL_apply, coeff_heckeT_of_dvd k hqM, MainLemma.iotaP_eq M k hq.out hqM,
    Level.coeff_iotaCF_mul, inclP_eq M k hqM, Level.coeff_inclCF]

/-- `U_q ∘ ι_p = ι_p ∘ U_q` for primes `q ≠ p`, `q ∣ M/p`. -/
lemma heckeT_iotaP_of_ne (q : ℕ) [hq : Fact q.Prime] {p : ℕ} (hp : p ∈ M.primeFactors)
    (hqp : q ≠ p) (hqL : q ∣ M / p) (g : S1 (M / p) k) :
    haveI : NeZero (M / p) := neZero_div hp
    heckeT q k (MainLemma.iotaP M p k g) = MainLemma.iotaP M p k (heckeT q k g) := by
  haveI : NeZero (M / p) := neZero_div hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpM := Nat.dvd_of_mem_primeFactors hp
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have hqM : q ∣ M := hqL.trans (Nat.div_dvd_of_dvd hpM)
  have hcop : p.Coprime q := (Nat.coprime_primes hpp hq.out).2 (Ne.symm hqp)
  apply eq_of_csL
  funext n
  rw [csL_apply, csL_apply, coeff_heckeT_of_dvd k hqM, MainLemma.iotaP_eq M k hpp hpM,
    Level.coeff_iotaCF, Level.coeff_iotaCF, coeff_heckeT_of_dvd k hqL]
  exact ite_dvd_mul_div hcop (fun m => (qExpansion 1 g).coeff m) n

/-- `U_p ∘ incl = incl ∘ T_p - p^(k-1) ι_p ∘ ⟨p⟩` when `p ∥ M` (`p ∤ M/p`). -/
lemma heckeT_inclP_self (q : ℕ) [hq : Fact q.Prime] (hqM : q ∣ M) (hqL : ¬ q ∣ M / q)
    (g : S1 (M / q) k) :
    haveI : NeZero (M / q) := neZero_div (Nat.mem_primeFactors.2 ⟨hq.out, hqM, NeZero.ne M⟩)
    heckeT q k (inclP M k q g) = inclP M k q (heckeT q k g) -
      ((q : ℂ) ^ (k - 1)) • MainLemma.iotaP M q k (diamond k (unitP hqL) g) := by
  haveI : NeZero (M / q) := neZero_div (Nat.mem_primeFactors.2 ⟨hq.out, hqM, NeZero.ne M⟩)
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  apply eq_of_csL
  funext n
  rw [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, csL_apply, csL_apply, csL_apply,
    coeff_heckeT_of_dvd k hqM, inclP_eq M k hqM, Level.coeff_inclCF, Level.coeff_inclCF,
    coeff_heckeT_of_not_dvd k hqL, MainLemma.iotaP_eq M k hq.out hqM, Level.coeff_iotaCF, smul_eq_mul]
  ring

/-- The old space is stable under `U_q`, `q ∣ M`. -/
theorem heckeT_mem_oldSpace_of_dvd (q : ℕ) [hq : Fact q.Prime] (hqM : q ∣ M) {f : S1 M k}
    (hf : f ∈ oldSpace M k) : heckeT q k f ∈ oldSpace M k := by
  have hqmem : q ∈ M.primeFactors := Nat.mem_primeFactors.2 ⟨hq.out, hqM, NeZero.ne M⟩
  refine map_mem_oldSpace (heckeT q k) (fun p hp g => ?_) (fun p hp g => ?_) hf
  · haveI := neZero_div hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpM := Nat.dvd_of_mem_primeFactors hp
    by_cases hqL : q ∣ M / p
    · rw [inclP_eq M k hpM, heckeT_inclCF_of_dvd _ k q hqL, ← inclP_eq M k hpM]
      exact inclP_mem_oldSpace hp _
    · have hqp : q = p := by
        have h1 : q ∣ p * (M / p) := by rwa [Nat.mul_div_cancel' hpM]
        rcases (Nat.Prime.dvd_mul hq.out).1 h1 with h | h
        · exact (Nat.prime_dvd_prime_iff_eq hq.out hpp).1 h
        · exact absurd h hqL
      subst hqp
      rw [heckeT_inclP_self q hqM hqL]
      exact Submodule.sub_mem _ (inclP_mem_oldSpace hp _)
        (Submodule.smul_mem _ _ (iotaP_mem_oldSpace hp _))
  · by_cases hqp : q = p
    · subst hqp
      rw [heckeT_iotaP_self q hqM]
      exact inclP_mem_oldSpace hp _
    · have hpp := Nat.prime_of_mem_primeFactors hp
      have hpM := Nat.dvd_of_mem_primeFactors hp
      have hqL : q ∣ M / p := by
        have h1 : q ∣ p * (M / p) := by rwa [Nat.mul_div_cancel' hpM]
        rcases (Nat.Prime.dvd_mul hq.out).1 h1 with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hq.out hpp).1 h) hqp
        · exact h
      rw [heckeT_iotaP_of_ne q hp hqp hqL]
      exact iotaP_mem_oldSpace hp _

/-- The old space is stable under every `T_q` (`U_q` included). -/
theorem heckeT_mem_oldSpace (q : ℕ) [Fact q.Prime] {f : S1 M k} (hf : f ∈ oldSpace M k) :
    heckeT q k f ∈ oldSpace M k := by
  by_cases hqM : q ∣ M
  · exact heckeT_mem_oldSpace_of_dvd q hqM hf
  · exact heckeT_mem_oldSpace_of_not_dvd q hqM hf

/-- The new space is stable under every `T_q` (`q ∤ M`) and every `⟨d⟩`. -/
theorem newSpace_stable :
    (∀ (q : ℕ) [Fact q.Prime], ¬ q ∣ M → ∀ g ∈ newSpace M k, heckeT q k g ∈ newSpace M k) ∧
      (∀ d : (ZMod M)ˣ, ∀ g ∈ newSpace M k, diamond k d g ∈ newSpace M k) :=
  perp_stable (fun q _ hqM _ hf => heckeT_mem_oldSpace_of_not_dvd q hqM hf)
    (fun d _ hf => diamond_mem_oldSpace d hf)

theorem heckeT_mem_newSpace (q : ℕ) [Fact q.Prime] (hqM : ¬ q ∣ M) {f : S1 M k}
    (hf : f ∈ newSpace M k) : heckeT q k f ∈ newSpace M k :=
  newSpace_stable.1 q hqM f hf

theorem diamond_mem_newSpace (d : (ZMod M)ˣ) {f : S1 M k} (hf : f ∈ newSpace M k) :
    diamond k d f ∈ newSpace M k :=
  newSpace_stable.2 d f hf

/-! ### Compatibility with the `χ`-decomposition -/

/-- A submodule stable under all diamonds is stable under every `e_χ`. -/
theorem proj_mem_of_diamond {W : Submodule ℂ (S1 M k)} (hW : ∀ d : (ZMod M)ˣ, ∀ f ∈ W, diamond k d f ∈ W)
    (χ : DirichletCharacter ℂ M) {f : S1 M k} (hf : f ∈ W) : proj k χ f ∈ W := by
  rw [proj_apply]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (hW d f hf))

theorem proj_mem_oldSpace (χ : DirichletCharacter ℂ M) {f : S1 M k} (hf : f ∈ oldSpace M k) :
    proj k χ f ∈ oldSpace M k :=
  proj_mem_of_diamond (fun d _ h => diamond_mem_oldSpace d h) χ hf

theorem proj_mem_newSpace (χ : DirichletCharacter ℂ M) {f : S1 M k} (hf : f ∈ newSpace M k) :
    proj k χ f ∈ newSpace M k ⊓ chiSubspace k χ :=
  ⟨proj_mem_of_diamond (fun d _ h => diamond_mem_newSpace d h) χ hf, proj_mem k χ f⟩

/-- `S^new = ⨁_χ S^new(M, χ)` (spanning form): `f = Σ_χ e_χ f` with `e_χ f ∈ S^new(M, χ)`. -/
theorem newSpace_eq_sum_proj {f : S1 M k} (hf : f ∈ newSpace M k) :
    f = ∑ χ : DirichletCharacter ℂ M, proj k χ f ∧
      ∀ χ : DirichletCharacter ℂ M, proj k χ f ∈ newSpace M k ⊓ chiSubspace k χ :=
  ⟨(sum_proj k f).symm, fun χ => proj_mem_newSpace χ hf⟩

theorem oldSpace_eq_sum_proj {f : S1 M k} (hf : f ∈ oldSpace M k) :
    f = ∑ χ : DirichletCharacter ℂ M, proj k χ f ∧
      ∀ χ : DirichletCharacter ℂ M, proj k χ f ∈ oldSpace M k ⊓ chiSubspace k χ :=
  ⟨(sum_proj k f).symm, fun χ => ⟨proj_mem_oldSpace χ hf, proj_mem k χ f⟩⟩

theorem chiSubspace_newSpace_stable (χ : DirichletCharacter ℂ M) (q : ℕ) [Fact q.Prime] (hqM : ¬ q ∣ M)
    {f : S1 M k} (hf : f ∈ newSpace M k ⊓ chiSubspace k χ) :
    heckeT q k f ∈ newSpace M k ⊓ chiSubspace k χ :=
  ⟨heckeT_mem_newSpace q hqM hf.1, heckeT_mem_chiSubspace k hf.2⟩

end stability

/-! ## Old ∩ new = 0 -/

section inter

variable [NeZero M]

theorem eq_zero_of_mem_old_new {f : S1 M k} (ho : f ∈ oldSpace M k) (hn : f ∈ newSpace M k) : f = 0 :=
  eq_zero_of_peterssonInner_self_eq_zero (Γ := Gamma1 M) f (hn f ho)

/-- Coefficients: `a_0 = 0` for cusp forms. -/
lemma coeff_zero_eq (f : S1 M k) : (qExpansion 1 f).coeff 0 = 0 :=
  CuspFormClass.qExpansion_coeff_zero f one_pos (Level.one_mem_strictPeriods_G1 M)

/-- A good eigenform in `S_k(M, χ)` with `a_1 = 0` has `a_n = 0` for every `n` coprime to `M`. -/
theorem coeff_coprime_eq_zero {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : f ∈ chiSubspace k χ)
    (he : IsGoodEigen k f) (h1 : (qExpansion 1 f).coeff 1 = 0) :
    ∀ n : ℕ, Nat.Coprime n M → (qExpansion 1 f).coeff n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · exact coeff_zero_eq f
      · exact h1
    · obtain ⟨q, hqp, hqn⟩ : ∃ q, q.Prime ∧ q ∣ n :=
        ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
      haveI : Fact q.Prime := ⟨hqp⟩
      have hqM : ¬ q ∣ M := fun h => by
        have h2 := Nat.dvd_gcd hqn h
        rw [Nat.Coprime.gcd_eq_one hn] at h2
        exact hqp.one_lt.ne' (Nat.dvd_one.1 h2)
      obtain ⟨m, rfl⟩ := hqn
      obtain ⟨c, hc⟩ := he q hqM
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hge)
      have hmlt : m < q * m := lt_mul_left hm0 hqp.one_lt
      have hmc : Nat.Coprime m M := Nat.Coprime.coprime_dvd_left (dvd_mul_left m q) hn
      have key := coeff_heckeT_chi (p := q) k hf m
      rw [hc, coeff_smul_Gamma1, ih m hmlt hmc] at key
      have hrest : (if q ∣ m then (qExpansion 1 f).coeff (m / q) else 0) = 0 := by
        split_ifs with hqm
        · exact ih (m / q) (lt_of_le_of_lt (Nat.div_le_self m q) hmlt)
            (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hqm) hmc)
        · rfl
      rw [hrest] at key
      linear_combination -key
/-- **DS Thm 5.8.2 (a)**: a nonzero good eigenform in `S^new(M, χ)` has `a_1 ≠ 0`. -/
theorem coeff_one_ne_zero {χ : DirichletCharacter ℂ M} {f : S1 M k} (hn : f ∈ newSpace M k)
    (hf : f ∈ chiSubspace k χ) (he : IsGoodEigen k f) (h0 : f ≠ 0) : (qExpansion 1 f).coeff 1 ≠ 0 :=
  fun h1 => h0 (eq_zero_of_mem_old_new (mem_oldSpace_of_coeff f (coeff_coprime_eq_zero hf he h1)) hn)

end inter

/-! ## Newforms -/

section newform

variable [NeZero M]

/-- A **normalised newform** of level `M` and character `χ`. -/
structure IsNewform (χ : DirichletCharacter ℂ M) (f : S1 M k) : Prop where
  mem_new : f ∈ newSpace M k
  mem_chi : f ∈ chiSubspace k χ
  eigen : IsGoodEigen k f
  coeff_one : (qExpansion 1 f).coeff 1 = 1

/-- The good-prime eigenvalue of a newform is `a_q`. -/
theorem IsNewform.heckeT_eq {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : IsNewform χ f)
    (q : ℕ) [Fact q.Prime] (hqM : ¬ q ∣ M) : heckeT q k f = (qExpansion 1 f).coeff q • f := by
  obtain ⟨c, hc⟩ := hf.eigen q hqM
  rw [hc, (eigen_coeff k hf.mem_chi hc hf.coeff_one).1]

/-- Forms sharing the good-prime eigenvalues of `f`. -/
def EigenLike (f : S1 M k) (h : S1 M k) : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], ¬ q ∣ M → heckeT q k h = (qExpansion 1 f).coeff q • h

lemma EigenLike.isGoodEigen {f h : S1 M k} (hh : EigenLike f h) : IsGoodEigen k h :=
  fun q _ hqM => ⟨_, hh q hqM⟩

lemma EigenLike.hecke {f h : S1 M k} (hh : EigenLike f h) (p : ℕ) [Fact p.Prime] :
    EigenLike f (Hecke.heckeT p k h) := by
  intro q _ hqM
  have hc : Hecke.heckeT q k (Hecke.heckeT p k h) = Hecke.heckeT p k (Hecke.heckeT q k h) := by
    have := heckeT_commute (M := M) k q p
    rw [Commute, SemiconjBy] at this
    exact LinearMap.congr_fun this h
  rw [hc, hh q hqM, map_smul]

lemma EigenLike.sub {f h h' : S1 M k} (hh : EigenLike f h) (hh' : EigenLike f h') :
    EigenLike f (h - h') := by
  intro q _ hqM
  rw [map_sub, hh q hqM, hh' q hqM, smul_sub]

lemma EigenLike.smul {f h : S1 M k} (hh : EigenLike f h) (c : ℂ) : EigenLike f (c • h) := by
  intro q _ hqM
  rw [map_smul, hh q hqM, smul_comm]

/-- **Key lemma**: no nonzero old form in `S_k(M, χ)` shares the good-prime eigenvalues of a newform. -/
theorem eq_zero_of_old_eigenLike {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : IsNewform χ f)
    {h : S1 M k} (ho : h ∈ oldSpace M k) (hc : h ∈ chiSubspace k χ) (hh : EigenLike f h) : h = 0 := by
  -- Step 1: every such form has `a_1 = 0`.
  have step1 : ∀ g : S1 M k, g ∈ oldSpace M k → g ∈ chiSubspace k χ → EigenLike f g →
      (qExpansion 1 g).coeff 1 = 0 := by
    intro g hgo hgc hg
    by_contra hg1
    set G : S1 M k := ((qExpansion 1 g).coeff 1)⁻¹ • g with hG
    have hGo : G ∈ oldSpace M k := Submodule.smul_mem _ _ hgo
    have hG1 : (qExpansion 1 G).coeff 1 = 1 := by
      rw [hG, coeff_smul_Gamma1, inv_mul_cancel₀ hg1]
    have hfG : f - G ∈ oldSpace M k := by
      refine mem_oldSpace_of_coeff _ (coeff_coprime_eq_zero
        (Submodule.sub_mem _ hf.mem_chi (Submodule.smul_mem _ _ hgc)) ?_ ?_)
      · exact EigenLike.isGoodEigen (EigenLike.sub (fun q _ hqM => hf.heckeT_eq q hqM) (hg.smul _))
      · have := congrArg (fun F => F 1) (map_sub (csL M k) f G)
        simp only [Pi.sub_apply, csL_apply] at this
        rw [this, hf.coeff_one, hG1, sub_self]
    have hfo : f ∈ oldSpace M k := by
      have := Submodule.add_mem _ hfG hGo
      rwa [sub_add_cancel] at this
    have h0 := eq_zero_of_mem_old_new hfo hf.mem_new
    have := hf.coeff_one
    rw [h0] at this
    have h00 : (qExpansion 1 ⇑(0 : S1 M k)).coeff 1 = 0 := by
      have := congrFun (map_zero (csL M k)) 1
      simpa only [csL_apply, Pi.zero_apply] using this
    rw [h00] at this
    exact zero_ne_one this
  -- Step 2: all coefficients vanish, by strong induction on `n`.
  have step2 : ∀ n : ℕ, ∀ g : S1 M k, g ∈ oldSpace M k → g ∈ chiSubspace k χ → EigenLike f g →
      (qExpansion 1 g).coeff n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro g hgo hgc hg
      by_cases hn : Nat.Coprime n M
      · exact coeff_coprime_eq_zero hgc hg.isGoodEigen (step1 g hgo hgc hg) n hn
      · rcases Nat.eq_zero_or_pos n with rfl | hpos
        · exact coeff_zero_eq g
        · obtain ⟨q, hqp, hqn, hqM⟩ := Nat.Prime.not_coprime_iff_dvd.1 hn
          haveI : Fact q.Prime := ⟨hqp⟩
          obtain ⟨m, rfl⟩ := hqn
          have hm0 : 0 < m := Nat.pos_of_mul_pos_left hpos
          rw [← coeff_heckeT_of_dvd k hqM g m]
          exact ih m (lt_mul_left hm0 hqp.one_lt) _ (heckeT_mem_oldSpace q hgo)
            (heckeT_mem_chiSubspace k hgc) (hg.hecke q)
  apply eq_of_csL
  funext n
  rw [csL_apply, step2 n h ho hc hh, map_zero]
  rfl

/-- **DS Thm 5.8.2 (b)**: a newform is a `U_p`-eigenvector with eigenvalue `a_p` for every `p ∣ M`. -/
theorem IsNewform.heckeT_eq_of_dvd {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : IsNewform χ f)
    (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) : heckeT p k f = (qExpansion 1 f).coeff p • f := by
  have hfe : EigenLike f f := fun q _ hqM => hf.heckeT_eq q hqM
  set o : S1 M k := heckeT p k f - (qExpansion 1 f).coeff p • f with ho
  have hoc : o ∈ chiSubspace k χ :=
    Submodule.sub_mem _ (heckeT_mem_chiSubspace k hf.mem_chi) (Submodule.smul_mem _ _ hf.mem_chi)
  have hoe : EigenLike f o := (hfe.hecke p).sub (hfe.smul _)
  have ho1 : (qExpansion 1 o).coeff 1 = 0 := by
    have := congrArg (fun F => F 1) (map_sub (csL M k) (heckeT p k f) ((qExpansion 1 f).coeff p • f))
    simp only [Pi.sub_apply, csL_apply] at this
    rw [this, coeff_heckeT_of_dvd k hpM, mul_one, coeff_smul_Gamma1, hf.coeff_one, mul_one, sub_self]
  have hoo : o ∈ oldSpace M k :=
    mem_oldSpace_of_coeff o (coeff_coprime_eq_zero hoc hoe.isGoodEigen ho1)
  have := eq_zero_of_old_eigenLike hf hoo hoc hoe
  rwa [ho, sub_eq_zero] at this

/-- A newform is an eigenvector of every `T_p` (`U_p` included). -/
theorem IsNewform.heckeT_eq_all {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : IsNewform χ f)
    (p : ℕ) [Fact p.Prime] : heckeT p k f = (qExpansion 1 f).coeff p • f := by
  by_cases hpM : p ∣ M
  · exact hf.heckeT_eq_of_dvd p hpM
  · exact hf.heckeT_eq p hpM

theorem IsNewform.eigen_all {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : IsNewform χ f) :
    ∀ p : ℕ, p.Prime → ∃ c : ℂ, heckeTP k p f = c • f := by
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨_, by rw [heckeTP_eq]; exact hf.heckeT_eq_all p⟩

/-- **`T_n f = a_n f`** for every `n ≥ 1` (all Hecke operators, `U_p` included). -/
theorem IsNewform.heckeTn_eq {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : IsNewform χ f)
    {n : ℕ} (hn : 0 < n) : heckeTn k n f = (qExpansion 1 f).coeff n • f :=
  heckeTn_eigen k hf.mem_chi hf.coeff_one hf.eigen_all hn

/-- **The full N2 recursion** for a newform, at every prime. -/
theorem IsNewform.recursion {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : IsNewform χ f) :
    ∀ p n : ℕ, p.Prime → (qExpansion 1 f).coeff (p * n) =
      (qExpansion 1 f).coeff p * (qExpansion 1 f).coeff n -
        (if p ∣ M then 0 else χ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then (qExpansion 1 f).coeff (n / p) else 0)) :=
  eigen_recursion k hf.mem_chi hf.coeff_one hf.eigen_all

/-- **Multiplicity one**: a newform is determined by its good-prime eigenvalues. -/
theorem IsNewform.eq_of_coeff_prime {χ : DirichletCharacter ℂ M} {f g : S1 M k} (hf : IsNewform χ f)
    (hg : IsNewform χ g) (h : ∀ q : ℕ, q.Prime → ¬ q ∣ M → (qExpansion 1 f).coeff q = (qExpansion 1 g).coeff q) :
    f = g := by
  have hoc : f - g ∈ chiSubspace k χ := Submodule.sub_mem _ hf.mem_chi hg.mem_chi
  have hoe : EigenLike f (f - g) := by
    refine EigenLike.sub (fun q _ hqM => hf.heckeT_eq q hqM) (fun q hq hqM => ?_)
    rw [hg.heckeT_eq q hqM, h q hq.out hqM]
  have ho1 : (qExpansion 1 ⇑(f - g)).coeff 1 = 0 := by
    have := congrArg (fun F => F 1) (map_sub (csL M k) f g)
    simp only [Pi.sub_apply, csL_apply] at this
    rw [this, hf.coeff_one, hg.coeff_one, sub_self]
  have hoo := mem_oldSpace_of_coeff _ (coeff_coprime_eq_zero hoc hoe.isGoodEigen ho1)
  exact sub_eq_zero.1 (eq_zero_of_mem_old_new hoo (Submodule.sub_mem _ hf.mem_new hg.mem_new))

/-- Normalising a nonzero good eigenform of `S^new(M, χ)`. -/
theorem isNewform_normalize {χ : DirichletCharacter ℂ M} {f : S1 M k} (hn : f ∈ newSpace M k)
    (hc : f ∈ chiSubspace k χ) (he : IsGoodEigen k f) (h0 : f ≠ 0) :
    IsNewform χ ((((qExpansion 1 f).coeff 1)⁻¹ • f : S1 M k)) := by
  have h1 := coeff_one_ne_zero hn hc he h0
  refine ⟨Submodule.smul_mem _ _ hn, Submodule.smul_mem _ _ hc, fun q _ hqM => ?_, ?_⟩
  · obtain ⟨c, hcq⟩ := he q hqM
    exact ⟨c, by rw [map_smul, hcq, smul_comm]⟩
  · rw [coeff_smul_Gamma1, inv_mul_cancel₀ h1]

/-- **Newform basis**: `S^new(M, χ)` is spanned by finitely many normalised newforms. -/
theorem exists_newform_span (χ : DirichletCharacter ℂ M) :
    ∃ s : Set (S1 M k), s.Finite ∧ (∀ f ∈ s, IsNewform χ f) ∧
      Submodule.span ℂ s = newSpace M k ⊓ chiSubspace k χ := by
  obtain ⟨s, hsf, hs, -, hspan⟩ := exists_goodEigen_basis_chi χ (newSpace M k ⊓ chiSubspace k χ)
    inf_le_right (fun q _ hqM f hf => chiSubspace_newSpace_stable χ q hqM hf)
  refine ⟨(fun f : S1 M k => (((qExpansion 1 f).coeff 1)⁻¹ • f : S1 M k)) '' s, hsf.image _, ?_, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨⟨hfn, hfc⟩, h0, he⟩ := hs f hf
    exact isNewform_normalize hfn hfc he h0
  · rw [← hspan]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 fun f hf => ?_)
    · rintro _ ⟨f, hf, rfl⟩
      exact Submodule.smul_mem _ _ (Submodule.subset_span hf)
    · obtain ⟨⟨hfn, hfc⟩, h0, he⟩ := hs f hf
      have h1 := coeff_one_ne_zero hfn hfc he h0
      have : f = (((qExpansion 1 f).coeff 1) • (((qExpansion 1 f).coeff 1)⁻¹ • f) : S1 M k) := by
        rw [smul_smul, mul_inv_cancel₀ h1, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, hf, rfl⟩)

end newform

end RP.Newforms


