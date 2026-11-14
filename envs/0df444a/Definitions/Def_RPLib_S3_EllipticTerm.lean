-- Prove2me | Definitions.Def_RPLib_S3_EllipticTerm
-- name    : RPLib_S3_EllipticTerm
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:09:38.10051+00:00
-- url     : https://prove2.me/theorems/b5ba4fd2-5d0d-49ca-bafd-0a9ba52bcc4b
-- title:
--   The Eichler-Selberg trace formula, scalar and elliptic contributions
-- statement:
--   For $M \ge 3$, $k \ge 3$, $n \ge 1$ coprime to $M$: the kernel diagonal splits into scalar, elliptic and remaining (hyperbolic and parabolic) parts, all integrable over $\Gamma_1(M) \backslash \mathbb{H}$, and $\operatorname{Tr}(T_n \langle \delta \rangle)$ equals the scalar term plus the elliptic term $A_2$ plus the integral of the remaining part.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_KernelD
import Definitions.Def_RPLib_S3_EllipticTermC
import Definitions.Def_RPLib_S3_EllipticTermD

/-!
# S3-EllCentralTerms: scalar and elliptic contributions to `Tr(T_n ⟨δ⟩ | S_k(Γ₁(M)))`

Umbrella of `EllipticTerm_A` .. `EllipticTerm_D`.

* `diag_eq_tsum`: the kernel diagonal `conj(ω(z, -conj z)) y^k` is `Σ'_{g ∈ Δ} φ_g(z)`.
* `restPart`: the sum over the non-scalar, non-elliptic `g` (hyperbolic and parabolic classes);
  `diag_split`: diagonal = `scalPart + ellPart + restPart`.
* `integrableOn_diag`: the diagonal is integrable on `fdom Γ₁(M)` (finite sum of Petersson products).
* **`trace_eq_central_add_rest`** (`M ≥ 3`, `k ≥ 3`, `n > 0`, `gcd(n, M) = 1`): `restPart` is integrable on
  `fdom Γ₁(M)` and
  `Tr(T_n ⟨δ⟩) = [SL₂(ℤ) : ±Γ₁(M)] · scalTrace M k n δ + ellG1 M k n δ + n^{k-1} B_k⁻¹ ∫_{fdom} restPart`.
-/

open MeasureTheory Set Filter Complex UpperHalfPlane CongruenceSubgroup
open scoped Real ComplexConjugate NNReal Manifold MatrixGroups

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EllTerm

open RP.FundDomain RP.Petersson RamanujanPetersson.Bergman RamanujanPetersson.Kernel
  RamanujanPetersson.Diamond RamanujanPetersson.Hecke
open RamanujanPetersson.HeckeAlgebra (heckeTn)

/-- The kernel diagonal as a sum of the `φ_g`. -/
lemma diag_eq_tsum {M k : ℕ} {n : ℤ} (δ' : ZMod M) (z : ℍ) :
    conj (omega M k n δ' z (-conj (z : ℂ))) * ((z.im : ℂ) ^ k) = ∑' g : DeltaSet M n δ', phiG k g z := by
  rw [omega, Complex.conj_tsum, ← tsum_mul_right]
  rfl

/-- The non-scalar, non-elliptic part (hyperbolic and parabolic `g`). -/
def restPart (k M : ℕ) (n : ℤ) (δ' : ZMod M) (z : ℍ) : ℂ :=
  ∑' g : DeltaSet M n δ', if ¬ (((g : S3.Conj.Mat) 1 0 = 0 ∧ (g : S3.Conj.Mat) 0 1 = 0 ∧
      (g : S3.Conj.Mat) 0 0 = (g : S3.Conj.Mat) 1 1) ∨
      ((g : S3.Conj.Mat) 0 0 + (g : S3.Conj.Mat) 1 1) ^ 2 < 4 * (g : S3.Conj.Mat).det)
    then phiG k g z else 0

lemma summable_ite {M k : ℕ} (hk : 3 ≤ k) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (z : ℍ)
    (P : S3.Conj.Mat → Prop) [DecidablePred P] :
    Summable fun g : DeltaSet M n δ' => if P g then phiG k g z else 0 := by
  have h := (summable_phiG_sub k hk hn δ' (X := DeltaSet M n δ') Subtype.val Subtype.val_injective
    (fun x => x.2) z).indicator {g : DeltaSet M n δ' | P g}
  refine h.congr fun g => ?_
  by_cases hP : P g
  · rw [indicator_of_mem (show g ∈ {g : DeltaSet M n δ' | P g} from hP), if_pos hP]
  · rw [indicator_of_notMem (show g ∉ {g : DeltaSet M n δ' | P g} from hP), if_neg hP]

lemma not_ell_of_scal {g : S3.Conj.Mat} (h : g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1) :
    ¬ (g 0 0 + g 1 1) ^ 2 < 4 * g.det := by
  obtain ⟨h10, h01, hd⟩ := h
  rw [Matrix.det_fin_two, h10, h01, ← hd]
  nlinarith

theorem diag_split {M k : ℕ} (hk : 3 ≤ k) {n : ℤ} (hn : 0 < n) (δ' : ZMod M) (z : ℍ) :
    conj (omega M k n δ' z (-conj (z : ℂ))) * ((z.im : ℂ) ^ k) =
      scalPart k M n δ' z + ellPart k M n δ' z + restPart k M n δ' z := by
  have h1 : Summable fun g : DeltaSet M n δ' => if (g : S3.Conj.Mat) 1 0 = 0 ∧ (g : S3.Conj.Mat) 0 1 = 0 ∧
      (g : S3.Conj.Mat) 0 0 = (g : S3.Conj.Mat) 1 1 then phiG k g z else 0 :=
    summable_ite hk hn δ' z (fun g : S3.Conj.Mat => g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1)
  have h2 : Summable fun g : DeltaSet M n δ' =>
      if ((g : S3.Conj.Mat) 0 0 + (g : S3.Conj.Mat) 1 1) ^ 2 < 4 * (g : S3.Conj.Mat).det
      then phiG k g z else 0 :=
    summable_ite hk hn δ' z (fun g : S3.Conj.Mat => (g 0 0 + g 1 1) ^ 2 < 4 * g.det)
  have h3 : Summable fun g : DeltaSet M n δ' => if ¬ (((g : S3.Conj.Mat) 1 0 = 0 ∧ (g : S3.Conj.Mat) 0 1 = 0 ∧
      (g : S3.Conj.Mat) 0 0 = (g : S3.Conj.Mat) 1 1) ∨
      ((g : S3.Conj.Mat) 0 0 + (g : S3.Conj.Mat) 1 1) ^ 2 < 4 * (g : S3.Conj.Mat).det)
      then phiG k g z else 0 :=
    summable_ite hk hn δ' z (fun g : S3.Conj.Mat => ¬ ((g 1 0 = 0 ∧ g 0 1 = 0 ∧ g 0 0 = g 1 1) ∨
      (g 0 0 + g 1 1) ^ 2 < 4 * g.det))
  rw [diag_eq_tsum]
  refine (tsum_congr fun g => ?_).trans (((h1.add h2).tsum_add h3).trans
    (congrArg (· + _) (h1.tsum_add h2)))
  try dsimp only
  by_cases hS : (g : S3.Conj.Mat) 1 0 = 0 ∧ (g : S3.Conj.Mat) 0 1 = 0 ∧
      (g : S3.Conj.Mat) 0 0 = (g : S3.Conj.Mat) 1 1
  · rw [if_pos hS, if_neg (not_ell_of_scal hS), if_neg (fun h => h (Or.inl hS))]
    ring
  · by_cases hE : ((g : S3.Conj.Mat) 0 0 + (g : S3.Conj.Mat) 1 1) ^ 2 < 4 * (g : S3.Conj.Mat).det
    · rw [if_neg hS, if_pos hE, if_neg (fun h => h (Or.inr hE))]
      ring
    · rw [if_neg hS, if_neg hE, if_pos (fun h => h.elim hS hE)]
      ring

/-- The kernel diagonal is integrable on `fdom Γ₁(M)` (route of `Kernel_D.trace_eq_integral`). -/
theorem integrableOn_diag {M : ℕ} [NeZero M] {k : ℕ} (hk : 3 ≤ k) (hM : 3 ≤ M) {n : ℕ} (hn : 0 < n)
    (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    IntegrableOn (fun z : ℍ => conj (omega M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z
      (-conj (z : ℂ))) * ((z.im : ℂ) ^ k)) (fdom (Gamma1 M)) := by
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
  have hc : (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn.ne')) (inv_ne_zero hB)
  have hsum : IntegrableOn (fun z => ∑ j, petersson (k : ℤ) (PeterssonSpace.toCuspForm (b j))
      (PeterssonSpace.toCuspForm (T (b j))) z) (fdom (Gamma1 M)) :=
    integrable_finsetSum _ (fun j _ => integrableOn_petersson _ _)
  have hsum' : IntegrableOn (fun z => ((n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹)⁻¹ *
      ∑ j, petersson (k : ℤ) (PeterssonSpace.toCuspForm (b j)) (PeterssonSpace.toCuspForm (T (b j))) z)
      (fdom (Gamma1 M)) := hsum.const_mul _
  refine IntegrableOn.congr_fun hsum' (fun z _ => ?_) (measurableSet_fdom _)
  rw [hpt z, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- **S3-EllCentralTerms (main).** For `M ≥ 3`, `k ≥ 3`, `n > 0` with `gcd(n, M) = 1` and `δ ∈ (ℤ/M)ˣ`:
the non-scalar, non-elliptic part of the kernel diagonal is integrable on `Γ₁(M)\ℍ`, and
`Tr(T_n ⟨δ⟩ | S_k(Γ₁(M))) = [SL₂(ℤ) : ±Γ₁(M)] · scalTrace + ellG1 + n^{k-1} B_k⁻¹ ∫_{Γ₁(M)\ℍ} restPart`. -/
theorem trace_eq_central_add_rest {M : ℕ} [NeZero M] (hM : 3 ≤ M) {k : ℕ} (hk : 3 ≤ k) {n : ℕ}
    (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) :
    IntegrableOn (restPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M)) (fdom (Gamma1 M)) ∧
      LinearMap.trace ℂ (S1 M k) (heckeTn (k : ℤ) n * diamond (k : ℤ) δ) =
        ((pmSL (Gamma1 M)).index : ℂ) * scalTrace M k n (δ : ZMod M) +
          ((S3.ellG1 M k n (δ : ZMod M) : ℚ) : ℂ) +
          (n : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
            ∫ z in fdom (Gamma1 M), restPart k M n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) z := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  set δ'' : ZMod M := ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) with hδ''
  obtain ⟨hSi, hSv⟩ := scal_trace_term (M := M) hk hn hnM δ
  obtain ⟨hEi, hEv⟩ := ell_trace_term hM hk hn hnM δ
  have hD := integrableOn_diag hk hM hn hnM δ
  rw [← hδ''] at hSi hSv hEi hEv hD
  have hsplit : (fun z : ℍ => conj (omega M k n δ'' z (-conj (z : ℂ))) * ((z.im : ℂ) ^ k)) =
      fun z => scalPart k M n δ'' z + ellPart k M n δ'' z + restPart k M n δ'' z :=
    funext fun z => diag_split hk hn' δ'' z
  have hRi : IntegrableOn (restPart k M n δ'') (fdom (Gamma1 M)) := by
    rw [hsplit] at hD
    refine ((hD.sub hSi).sub hEi).congr_fun (fun z _ => ?_) (measurableSet_fdom _)
    simp only [Pi.sub_apply]
    ring
  refine ⟨hRi, ?_⟩
  have hI : ∫ z in fdom (Gamma1 M), (scalPart k M n δ'' z + ellPart k M n δ'' z + restPart k M n δ'' z) =
      (∫ z in fdom (Gamma1 M), scalPart k M n δ'' z) + (∫ z in fdom (Gamma1 M), ellPart k M n δ'' z) +
        ∫ z in fdom (Gamma1 M), restPart k M n δ'' z :=
    (integral_add (hSi.add hEi) hRi).trans (congrArg (· + _) (integral_add hSi hEi))
  rw [trace_eq_integral hk hM hn hnM δ, ← hδ'', hsplit, hI, mul_add, mul_add, hSv, hEv]
end RamanujanPetersson.EllTerm


