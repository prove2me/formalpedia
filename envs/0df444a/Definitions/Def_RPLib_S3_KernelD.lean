-- Prove2me | Definitions.Def_RPLib_S3_KernelD
-- name    : RPLib_S3_KernelD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:04:35.811389+00:00
-- url     : https://prove2.me/theorems/14f39be5-d28f-482a-bad1-c5ed3ee30307
-- title:
--   The Eichler-Selberg trace formula, kernel part D: the trace as an integral
-- statement:
--   For $M \ge 3$, $k \ge 3$ and $\gcd(n, M) = 1$:
--   $$\operatorname{Tr}\big(T_n \langle \delta \rangle \mid S_k(\Gamma_1(M))\big) = \frac{n^{k-1}}{B_k} \int_{\Gamma_1(M) \backslash \mathbb{H}} \overline{\omega(z, -\bar z)}\, y^{k}\, d\mu(z),$$
--   where $B_k$ is the Bergman constant, obtained from an orthonormal basis for the Petersson inner product and the reproducing identity.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_KernelC

/-!
# S3-Kernel, part D: `Tr(T_n ⟨δ⟩)` as an integral

* `trace_eq_integral` (`M ≥ 3`, `k ≥ 3`, `gcd(n, M) = 1`):
  `Tr(T_n ⟨δ⟩) = n^(k-1) / bergmanConst k · ∫_{fdom Γ₁(M)} conj(ω(z, -conj z)) y^k dμ`,
  via an orthonormal basis of `PeterssonSpace (Γ₁(M)) k` and the reproducing identity.
-/

open Filter Complex UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Topology Manifold ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Kernel

open RP.FundDomain RP.Petersson RamanujanPetersson.Bergman RamanujanPetersson.Diamond
  RamanujanPetersson.Hecke
open RamanujanPetersson.HeckeAlgebra (heckeTn coeff_heckeTn_chi)

variable {M : ℕ} [NeZero M]

/-! ### The trace as an integral -/

variable (M) in
/-- `S1 M k ≃ PeterssonSpace (Γ₁(M)) k` (identity). -/
def toPS' (k : ℤ) : S1 M k ≃ₗ[ℂ] PeterssonSpace (Gamma1 M) k where
  toFun := PeterssonSpace.ofCuspForm
  invFun := PeterssonSpace.toCuspForm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable (M) in
/-- Evaluation at a point on the Petersson space. -/
def evalE (k : ℤ) (z : ℍ) : PeterssonSpace (Gamma1 M) k →ₗ[ℂ] ℂ where
  toFun f := PeterssonSpace.toCuspForm f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [NeZero M] in
@[simp] lemma evalE_apply (k : ℤ) (z : ℍ) (f : PeterssonSpace (Gamma1 M) k) :
    evalE M k z f = PeterssonSpace.toCuspForm f z := rfl

lemma bergmanConst_ne_zero {k : ℕ} (hk : 2 ≤ k) : bergmanConst k ≠ 0 := by
  unfold bergmanConst
  have h1 : ((k : ℂ) - 1) ≠ 0 := by
    rw [sub_ne_zero]; exact_mod_cast (by omega : k ≠ 1)
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) (pow_ne_zero _ Complex.I_ne_zero))
    (mul_ne_zero h1 (pow_ne_zero _ (by norm_num)))

/-- **`Tr(T_n ⟨δ⟩ | S_k(Γ₁(M)))` as an integral** (`M ≥ 3`, `k ≥ 3`, `gcd(n, M) = 1`). -/
theorem trace_eq_integral {k : ℕ} (hk : 3 ≤ k) (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n) (hnM : n.Coprime M)
    (δ : (ZMod M)ˣ) :
    LinearMap.trace ℂ (S1 M k) (heckeTn (k : ℤ) n * diamond (k : ℤ) δ) =
      (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
        ∫ z in fdom (Gamma1 M), conj (omega M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z
          (-conj (z : ℂ))) * ((z.im : ℂ) ^ k) := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hB : bergmanConst k ≠ 0 := bergmanConst_ne_zero (by omega)
  have repro : ∀ (g : S1 M k) (z : ℍ),
      ((heckeTn (k : ℤ) n * diamond (k : ℤ) δ : Module.End ℂ (S1 M k)) g) z =
      (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
        peterssonInner (Gamma1 M) k
          (omegaH M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) (-conj (z : ℂ))) g := by
    intro g z
    rw [reproducing_abstract hM hn' hk (alphaHNF n (unitOf M n * δ)) (alphaHNF_mem hnM _)
      (repMap_HNF_bijective hn hnM _) g z, Module.End.mul_apply, ← cosetSum_eq (by omega) hn hnM δ g z,
      mul_assoc, inv_mul_cancel_left₀ hB]
    rfl
  have : FiniteDimensional ℂ (PeterssonSpace (Gamma1 M) (k : ℤ)) := by
    have := RamanujanPetersson.FinDim.finiteDimensional_cuspForm_Gamma1 M (k : ℤ)
    exact LinearEquiv.finiteDimensional (toPS' M (k : ℤ))
  let b := stdOrthonormalBasis ℂ (PeterssonSpace (Gamma1 M) (k : ℤ))
  let T : PeterssonSpace (Gamma1 M) (k : ℤ) →ₗ[ℂ] PeterssonSpace (Gamma1 M) (k : ℤ) :=
    heckeTn (k : ℤ) n * diamond (k : ℤ) δ
  have htr : LinearMap.trace ℂ (S1 M k) (heckeTn (k : ℤ) n * diamond (k : ℤ) δ) =
      LinearMap.trace ℂ _ T := rfl
  have hpt : ∀ z : ℍ, ∑ j, petersson (k : ℤ) (PeterssonSpace.toCuspForm (b j))
      (PeterssonSpace.toCuspForm (T (b j))) z =
      (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
        (conj (omega M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z (-conj (z : ℂ))) *
          ((z.im : ℂ) ^ k)) := by
    intro z
    have hv : 0 < (-conj (z : ℂ)).im := by simpa using z.im_pos
    let ω : PeterssonSpace (Gamma1 M) (k : ℤ) :=
      PeterssonSpace.ofCuspForm (omegaCF M k hn' ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) hk (-conj (z : ℂ)) hv)
    have hrep := congrArg (evalE M (k : ℤ) z) (b.sum_repr' ω)
    rw [map_sum] at hrep
    simp only [map_smul, smul_eq_mul] at hrep
    have hω : evalE M (k : ℤ) z ω = omega M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z (-conj (z : ℂ)) :=
      rfl
    have hT : ∀ j, PeterssonSpace.toCuspForm (T (b j)) z =
        (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ * conj (inner ℂ (b j) ω) := by
      intro j
      rw [show PeterssonSpace.toCuspForm (T (b j)) z =
        ((heckeTn (k : ℤ) n * diamond (k : ℤ) δ : Module.End ℂ (S1 M k))
          (PeterssonSpace.toCuspForm (b j))) z from rfl, repro]
      congr 1
      rw [← peterssonInner_conj_symm]
      all_goals rfl
    simp only [petersson_nat, hT]
    rw [← hω, ← hrep]
    simp only [evalE_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [htr, LinearMap.trace_eq_sum_inner T b]
  calc ∑ j, inner ℂ (b j) (T (b j))
      = ∑ j, ∫ z in fdom (Gamma1 M), petersson (k : ℤ) (PeterssonSpace.toCuspForm (b j))
          (PeterssonSpace.toCuspForm (T (b j))) z := rfl
    _ = ∫ z in fdom (Gamma1 M), ∑ j, petersson (k : ℤ) (PeterssonSpace.toCuspForm (b j))
          (PeterssonSpace.toCuspForm (T (b j))) z :=
        by
          rw [integral_finsetSum]
          intro j _
          exact integrableOn_petersson _ _
    _ = ∫ z in fdom (Gamma1 M), (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
          (conj (omega M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z (-conj (z : ℂ))) *
            ((z.im : ℂ) ^ k)) := by
        congr 1; funext z; exact hpt z
    _ = _ := integral_const_mul _ _

end RamanujanPetersson.Kernel


