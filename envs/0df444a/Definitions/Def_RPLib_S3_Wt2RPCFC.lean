-- Prove2me | Definitions.Def_RPLib_S3_Wt2RPCFC
-- name    : RPLib_S3_Wt2RPCFC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:52:53.281415+00:00
-- url     : https://prove2.me/theorems/23df9bc7-6bb5-4b7b-a466-45c82f18bf19
-- title:
--   Weight-two Ramanujan-Petersson library: the Hasse-Weil bound for an arbitrary constant field
-- statement:
--   The Hasse-Weil bound for an arbitrary constant field.
--
--   For a function field `F / Fq` with full constant field `k` of degree `r` over `Fq` (`q = #Fq`):
--   `N_m = [r ∣ m] · r · q ^ m + O(√q ^ m)` (`hw_general`). Proof: `Hom_Fq(Rfin, L)` splits over the `r` (or `0`)
--   embeddings `σ : k → L` (`homSigmaEquiv`), each fiber is `Hom_k(Rfin_k, L_σ)` (`card_fiber_eq`), which Hasse-Weil
--   over `k` (`constField_KF_eq_bot`) puts within `1 + O(1) + 2 g √q ^ m` of `q ^ m` (`fiber_card_bound`); the
--   infinite places contribute `O(1)` (`card_algHom_Rinf_le'`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_Wt2RPCFB
import Definitions.Def_RPLib_S3_HasseWeilB
import Definitions.Def_RPLib_S3_SBGalB

/-!
# S3-Wt2RP, O2 part C: the Hasse-Weil bound for an arbitrary constant field

For a function field `F / Fq` with full constant field `k` of degree `r` over `Fq` (`q = #Fq`):
`N_m = [r ∣ m] · r · q ^ m + O(√q ^ m)` (`hw_general`). Proof: `Hom_Fq(Rfin, L)` splits over the `r` (or `0`)
embeddings `σ : k → L` (`homSigmaEquiv`), each fiber is `Hom_k(Rfin_k, L_σ)` (`card_fiber_eq`), which Hasse-Weil
over `k` (`constField_KF_eq_bot`) puts within `1 + O(1) + 2 g √q ^ m` of `q ^ m` (`fiber_card_bound`); the
infinite places contribute `O(1)` (`card_algHom_Rinf_le'`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial Module

namespace RamanujanPetersson.S3.Wt2

open RamanujanPetersson.Places CF

/-- `√(q ^ r) = √q ^ r`. -/
theorem sqrt_pow_nat (q : ℝ) (hq : 0 ≤ q) (r : ℕ) : Real.sqrt (q ^ r) = Real.sqrt q ^ r := by
  rw [show q ^ r = (Real.sqrt q ^ r) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hq]]
  exact Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)

section HWG

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The infinite part is bounded independently of `L`. -/
theorem exists_card_algHom_Rinf_le : ∃ C : ℕ, ∀ (L : Type) [Field L] [Finite L] [Algebra Fq L],
    Nat.card (Rinf Fq F →ₐ[Fq] L) ≤ C := ⟨_, fun L _ _ _ => card_algHom_Rinf_le' Fq F L⟩

/-- The fiber of `homSigmaEquiv` over `σ`. -/
abbrev Fib (L : Type) [Field L] [Algebra Fq L] (σ : KF Fq F →ₐ[Fq] L) : Type :=
  {ψ : FunctionField.ringOfIntegers (KF Fq F) F →+* L //
    ∀ c, ψ (algebraMap (KF Fq F) (FunctionField.ringOfIntegers (KF Fq F) F) c) = σ c}

/-- An embedding of the constants into `L` forces `[k : Fq] ∣ [L : Fq]`. -/
theorem finrank_dvd_of_algHom (L : Type) [Field L] [Algebra Fq L] (σ : KF Fq F →ₐ[Fq] L) :
    finrank Fq (KF Fq F) ∣ finrank Fq L := by
  letI : Algebra (KF Fq F) L := σ.toRingHom.toAlgebra
  haveI : IsScalarTower Fq (KF Fq F) L := IsScalarTower.of_algebraMap_eq fun a => (σ.commutes a).symm
  exact Dvd.intro _ (Module.finrank_mul_finrank Fq (KF Fq F) L)

/-- One fiber: `|#Fib σ - q ^ m| ≤ 1 + C_∞(k) + 2 g_k √q ^ m` (Hasse-Weil over `k`). -/
theorem fiber_card_bound (Ck : ℕ) (hCk : ∀ (L : Type) [Field L] [Finite L] [Algebra (KF Fq F) L],
      Nat.card (Rinf (KF Fq F) F →ₐ[KF Fq F] L) ≤ Ck)
    (L : Type) [Field L] [Algebra Fq L] [Finite L] (σ : KF Fq F →ₐ[Fq] L) :
    |(Nat.card (Fib Fq F L σ) : ℝ) - (Fintype.card Fq : ℝ) ^ finrank Fq L| ≤
      1 + (Ck : ℝ) + 2 * (RR.genusF (KF Fq F) F : ℝ) * Real.sqrt (Fintype.card Fq) ^ finrank Fq L := by
  letI : Algebra (KF Fq F) L := σ.toRingHom.toAlgebra
  haveI : IsScalarTower Fq (KF Fq F) L := IsScalarTower.of_algebraMap_eq fun a => (σ.commutes a).symm
  haveI : Module.Finite (KF Fq F) L := Module.Finite.of_finite
  rw [Fib, card_fiber_eq Fq F (KF Fq F) L σ (fun _ => rfl)]
  have hN := numPoints_eq_card_algHom (KF Fq F) F L
  have hinf := hCk L
  have hm : finrank Fq (KF Fq F) * finrank (KF Fq F) L = finrank Fq L :=
    Module.finrank_mul_finrank Fq (KF Fq F) L
  have hj : 1 ≤ finrank (KF Fq F) L := Module.finrank_pos
  have hHW := ZetaSB.hasse_weil (KF Fq F) F (constField_KF_eq_bot Fq F) _ hj
  have hcard : (Fintype.card (KF Fq F) : ℝ) = (Fintype.card Fq : ℝ) ^ finrank Fq (KF Fq F) := by
    exact_mod_cast Module.card_eq_pow_finrank (K := Fq) (V := KF Fq F)
  rw [hcard, sqrt_pow_nat _ (Nat.cast_nonneg _), ← pow_mul, ← pow_mul, hm, hN] at hHW
  push_cast at hHW
  have h0 : (0 : ℝ) ≤ Nat.card (Rinf (KF Fq F) F →ₐ[KF Fq F] L) := Nat.cast_nonneg _
  have hinf' : (Nat.card (Rinf (KF Fq F) F →ₐ[KF Fq F] L) : ℝ) ≤ (Ck : ℝ) := by
    exact_mod_cast hinf
  rw [abs_le] at hHW ⊢
  constructor <;> linarith [hHW.1, hHW.2]

/-- **Hasse-Weil for an arbitrary constant field**: with `r = [k : Fq]` (`k` the full constant field),
`|N_m - [r ∣ m] r q ^ m| ≤ C √q ^ m` for every finite extension `L / Fq` of degree `m`. -/
theorem hw_general : ∃ r : ℕ, 1 ≤ r ∧ ∃ C : ℝ, ∀ (L : Type) [Field L] [Algebra Fq L] [Finite L],
    |(numPoints Fq F (finrank Fq L) : ℝ) -
        (if r ∣ finrank Fq L then (r : ℝ) * (Fintype.card Fq : ℝ) ^ finrank Fq L else 0)| ≤
      C * Real.sqrt (Fintype.card Fq) ^ finrank Fq L := by
  classical
  obtain ⟨Ck, hCk⟩ := exists_card_algHom_Rinf_le (KF Fq F) F
  obtain ⟨Ci, hCi⟩ := exists_card_algHom_Rinf_le Fq F
  refine ⟨finrank Fq (KF Fq F), Module.finrank_pos,
    finrank Fq (KF Fq F) * (1 + (Ck : ℝ)) + (Ci : ℝ) +
      2 * finrank Fq (KF Fq F) * (RR.genusF (KF Fq F) F : ℝ), fun L _ _ _ => ?_⟩
  have hb := fiber_card_bound Fq F Ck hCk L
  set r := finrank Fq (KF Fq F) with hr
  set g : ℝ := (RR.genusF (KF Fq F) F : ℝ) with hg
  set S : ℝ := Real.sqrt (Fintype.card Fq) ^ finrank Fq L with hS
  have hS1 : 1 ≤ S := one_le_pow₀ (Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr Fintype.card_pos))
  have hCk0 : (0 : ℝ) ≤ Ck := Nat.cast_nonneg _
  have hCi0 : (0 : ℝ) ≤ Ci := Nat.cast_nonneg _
  have hg0 : 0 ≤ g := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hN := numPoints_eq_card_algHom Fq F L
  have hinf : (Nat.card (Rinf Fq F →ₐ[Fq] L) : ℝ) ≤ Ci := by exact_mod_cast hCi L
  have hinf0 : (0 : ℝ) ≤ Nat.card (Rinf Fq F →ₐ[Fq] L) := Nat.cast_nonneg _
  haveI : Finite (Rfin Fq F →ₐ[Fq] L) := ZetaSB.finite_algHom_of_pow (fun N hN => X_pow_ne_self Fq F hN) L
  have e := homSigmaEquiv Fq F (KF Fq F) L (hxk Fq F)
  haveI : Finite (KF Fq F →ₐ[Fq] L) := Finite.of_injective _ DFunLike.coe_injective
  letI : Fintype (KF Fq F →ₐ[Fq] L) := Fintype.ofFinite _
  haveI : Finite (Σ σ : KF Fq F →ₐ[Fq] L, Fib Fq F L σ) := Finite.of_equiv _ e
  haveI : ∀ σ : KF Fq F →ₐ[Fq] L, Finite (Fib Fq F L σ) :=
    fun σ => Finite.of_injective (Sigma.mk σ) sigma_mk_injective
  have hA : (Nat.card (Rfin Fq F →ₐ[Fq] L) : ℝ) = ∑ σ : KF Fq F →ₐ[Fq] L, (Nat.card (Fib Fq F L σ) : ℝ) := by
    rw [Nat.card_congr e, Nat.card_sigma]
    push_cast
    rfl
  rw [hN]
  push_cast
  rw [hA]
  have hC0 : 0 ≤ (r : ℝ) * (1 + Ck) + Ci + 2 * r * g := by positivity
  have hCS := mul_le_mul_of_nonneg_left hS1 hC0
  split_ifs with hdvd
  · have hcardσ : (Finset.univ : Finset (KF Fq F →ₐ[Fq] L)).card = r := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact FiniteField.natCard_algHom_of_finrank_dvd hdvd
    have hsum : |∑ σ : KF Fq F →ₐ[Fq] L, (Nat.card (Fib Fq F L σ) : ℝ) -
        (r : ℝ) * (Fintype.card Fq : ℝ) ^ finrank Fq L| ≤ r * (1 + Ck + 2 * g * S) := by
      have h1 : ∑ σ : KF Fq F →ₐ[Fq] L, (Nat.card (Fib Fq F L σ) : ℝ) -
          (r : ℝ) * (Fintype.card Fq : ℝ) ^ finrank Fq L =
          ∑ σ : KF Fq F →ₐ[Fq] L, ((Nat.card (Fib Fq F L σ) : ℝ) - (Fintype.card Fq : ℝ) ^ finrank Fq L) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, hcardσ, nsmul_eq_mul]
      rw [h1]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun σ _ => hb σ).trans ?_
      rw [Finset.sum_const, hcardσ, nsmul_eq_mul]
    have h2 : (r : ℝ) * (1 + Ck) ≤ r * (1 + Ck) * S := le_mul_of_one_le_right (by positivity) hS1
    have h3 : (Ci : ℝ) ≤ Ci * S := le_mul_of_one_le_right hCi0 hS1
    rw [abs_le] at hsum ⊢
    constructor <;> nlinarith [hsum.1, hsum.2]
  · haveI : IsEmpty (KF Fq F →ₐ[Fq] L) := ⟨fun σ => hdvd (finrank_dvd_of_algHom Fq F L σ)⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, zero_add, sub_zero, abs_of_nonneg hinf0]
    nlinarith

end HWG

end RamanujanPetersson.S3.Wt2


