-- Prove2me | Definitions.Def_RPLib_S3_Wt2RPA
-- name    : RPLib_S3_Wt2RPA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:21:13.0718+00:00
-- url     : https://prove2.me/theorems/5ba5e2a7-f22f-4c7c-b8ff-fe7d3c079606
-- title:
--   Weight-two Ramanujan-Petersson library: from `PhiEigenBound k` to the N4 root bound at weight `k`
-- statement:
--   From `PhiEigenBound k` to the N4 root bound at weight `k`.
--
--   * `heckeT_eq_of_hrec`, `diamond_eq_of_chi`: N4's hypotheses make `F` a joint `T_p`, `⟨p⟩` eigenform.
--   * `n4_of_phiEigenBound_four_le`: N4 at weight `k` for levels `L ≥ 4`, from `PhiEigenBound k`.
--   * `n4_of_phiEigenBound`: N4 at weight `k` for every level `L > 0` (level raising, `LevelRaise`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211

import Mathlib
import Definitions.Def_RPLib_S3_MatchingA
import Definitions.Def_RPLib_S2_LevelRaise

/-!
# S3-Wt2RP, part A: from `PhiEigenBound k` to the N4 root bound at weight `k`

* `heckeT_eq_of_hrec`, `diamond_eq_of_chi`: N4's hypotheses make `F` a joint `T_p`, `⟨p⟩` eigenform.
* `n4_of_phiEigenBound_four_le`: N4 at weight `k` for levels `L ≥ 4`, from `PhiEigenBound k`.
* `n4_of_phiEigenBound`: N4 at weight `k` for every level `L > 0` (level raising, `LevelRaise`).
-/

set_option autoImplicit false

open UpperHalfPlane ModularForm CongruenceSubgroup MatrixGroups

namespace RamanujanPetersson.S3.Wt2

open RamanujanPetersson.Diamond RamanujanPetersson.Hecke RamanujanPetersson.QExp

/-- `T_p F = a_p F` from the Hecke recursion at `p` (for `F ∈ S_k(M, χ)`). -/
theorem heckeT_eq_of_hrec {M : ℕ} [NeZero M] (k : ℤ) (χ : DirichletCharacter ℂ M) (F : S1 M k)
    (hχ : ∀ γ ∈ Gamma0 M, (⇑F ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod M) • ⇑F)
    (p : ℕ) [Fact p.Prime]
    (hrec : ∀ n : ℕ, (qExpansion 1 F).coeff (p * n) = (qExpansion 1 F).coeff p * (qExpansion 1 F).coeff n -
        χ (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then (qExpansion 1 F).coeff (n / p) else 0)) :
    heckeT p k F = (qExpansion 1 F).coeff p • F := by
  have hf : F ∈ chiSubspace k χ := hχ
  apply qExpansionGamma1_injective M k
  refine PowerSeries.ext fun n => ?_
  rw [qExpansionGamma1_apply, qExpansionGamma1_apply]
  rw [coeff_heckeT_chi (p := p) k hf n, coeff_smul_Gamma1, hrec n]
  ring

/-- `⟨p⟩ F = χ(p) F` for `F ∈ S_k(M, χ)`. -/
theorem diamond_eq_of_chi {M : ℕ} [NeZero M] (k : ℤ) (χ : DirichletCharacter ℂ M) (F : S1 M k)
    (hχ : ∀ γ ∈ Gamma0 M, (⇑F ∣[k] γ) = χ ((γ 1 1 : ℤ) : ZMod M) • ⇑F)
    (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) :
    diamond k (unitP hpM) F = χ (p : ZMod M) • F := by
  have hf : F ∈ chiSubspace k χ := hχ
  rw [(mem_chiSubspace_iff_diamond k χ F).1 hf (unitP hpM)]
  have hu : ((unitP hpM : (ZMod M)ˣ) : ZMod M) = p := ZMod.coe_unitOfCoprime _ _
  rw [hu]

/-- `√p ^ (k - 1) = p ^ ((k - 1)/2)` for `k ≥ 1`. -/
theorem sqrt_pow_eq_rpow (p : ℕ) (k : ℕ) (hk : 1 ≤ k) :
    Real.sqrt p ^ (k - 1) = (p : ℝ) ^ (((k : ℝ) - 1) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
  congr 1
  rw [Nat.cast_sub hk, Nat.cast_one]
  ring

/-- **N4 at weight `k`, levels `L ≥ 4`**, from `PhiEigenBound k`. -/
theorem n4_of_phiEigenBound_four_le (k : ℕ) (hk : 1 ≤ k) (H : PhiEigenBound k)
    (L : ℕ) (hL : 4 ≤ L) (χ : DirichletCharacter ℂ L)
    (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (hχ : ∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[(k : ℤ)] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F)
    (h1 : (qExpansion 1 F).coeff 1 = 1)
    (hrec : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
      (qExpansion 1 F).coeff (q * n) =
        (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
          χ (q : ZMod L) * (q : ℂ) ^ ((k : ℤ) - 1) *
            (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0))
    (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ L) (α : ℂ)
    (hα : α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) * (p : ℂ) ^ ((k : ℤ) - 1) = 0) :
    ‖α‖ ≤ (p : ℝ) ^ (((k : ℝ) - 1) / 2) := by
  have : NeZero L := ⟨by omega⟩
  have : Fact p.Prime := ⟨hp⟩
  have hF0 : (F : S1 L (k : ℤ)) ≠ 0 := by
    intro h0
    have h2 := coeff_smul_Gamma1 (M := L) (k : ℤ) 0 F 1
    rw [zero_smul, zero_mul] at h2
    rw [h0] at h1
    rw [h2] at h1
    exact zero_ne_one h1
  have hT := heckeT_eq_of_hrec (k : ℤ) χ F hχ p (fun n => hrec p n hp hpL)
  have hD := diamond_eq_of_chi (k : ℤ) χ F hχ p hpL
  have hE := Match.rootOfPhi L p hpL (k : ℤ) F _ _ α hF0 hT hD hα
  rw [← sqrt_pow_eq_rpow p k hk]
  exact H L hL p hpL α hE

/-- **N4 at weight `k`, every level `L > 0`**, from `PhiEigenBound k` (level raising). -/
theorem n4_of_phiEigenBound (k : ℕ) (hk : 1 ≤ k) (H : PhiEigenBound k)
    (L : ℕ) (hL : 0 < L) (χ : DirichletCharacter ℂ L)
    (F : CuspForm ((CongruenceSubgroup.Gamma1 L : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) (k : ℤ))
    (hχ : ∀ γ ∈ CongruenceSubgroup.Gamma0 L, (⇑F ∣[(k : ℤ)] γ) = χ ((γ 1 1 : ℤ) : ZMod L) • ⇑F)
    (h1 : (qExpansion 1 F).coeff 1 = 1)
    (hrec : ∀ q n : ℕ, q.Prime → ¬ q ∣ L →
      (qExpansion 1 F).coeff (q * n) =
        (qExpansion 1 F).coeff q * (qExpansion 1 F).coeff n -
          χ (q : ZMod L) * (q : ℂ) ^ ((k : ℤ) - 1) *
            (if q ∣ n then (qExpansion 1 F).coeff (n / q) else 0))
    (p : ℕ) (hp : p.Prime) (hpL : ¬ p ∣ L) (α : ℂ)
    (hα : α ^ 2 - (qExpansion 1 F).coeff p * α + χ (p : ZMod L) * (p : ℂ) ^ ((k : ℤ) - 1) = 0) :
    ‖α‖ ≤ (p : ℝ) ^ ((((k : ℤ) : ℝ) - 1) / 2) := by
  have e : (((k : ℤ) : ℝ)) = (k : ℝ) := by push_cast; rfl
  exact LevelRaise.deligne_hecke_root_bound_of_four_le (k : ℤ)
    (fun L' hL' χ' F' hχ' h1' hrec' p' hp' hpL' α' hα' => by
      rw [e]; exact n4_of_phiEigenBound_four_le k hk H L' hL' χ' F' hχ' h1' hrec' p' hp' hpL' α' hα')
    L hL χ F hχ h1 hrec p hp hpL α hα

end RamanujanPetersson.S3.Wt2


