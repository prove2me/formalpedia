-- Prove2me | Definitions.Def_RPLib_S3_KernelSC
-- name    : RPLib_S3_KernelSC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T12:31:02.5332+00:00
-- url     : https://prove2.me/theorems/0af89e52-2ff7-4144-bab5-4af256bd5e3d
-- title:
--   The Eichler-Selberg trace formula in weight two: the trace with the holomorphic projection of `ω_s`
-- statement:
--   The trace with the holomorphic projection of `ω_s`.
--
--   With an orthonormal basis `b_j` of `S_k(Γ₁(M))` (Petersson product):
--   * `Hdiag z = Σ_j conj(b_j z) (T b_j)(z) y^k` (independent of `s`), `trace_eq_integral_Hdiag`: `Tr T = ∫_{fdom} Hdiag`.
--   * `projS z = Σ_j b_j(z) conj⟪ω_s(·, -conj z), b_j⟫` (the projection of `ω_s(·, -conj z)` onto `S_k`, at `z`).
--   * `Hdiag_eq_projS`: `Hdiag z = n^(k-1) C_k(s)⁻¹ conj(projS z) y^k` (every `s` with `k/2 + s > 1`).
--   * `diag_split`: `n^(k-1) C_k(s)⁻¹ conj(ω_s(z, -conj z)) y^k = Hdiag z + n^(k-1) C_k(s)⁻¹ conj(ω_s(z, -conj z) - projS z) y^k`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer in weight two: the Eichler-Selberg / Cohen-Oesterlé trace formula for $T_n \langle \delta \rangle$ on $S_2(\Gamma_1(M))$, $M \ge 4$, proved by Zagier's kernel method with Hecke's convergence trick $|cz+d|^{-2s}$, $s \to 0^+$). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   H. Cohen, Trace des opérateurs de Hecke sur Γ0(N), Séminaire de Théorie des Nombres de Bordeaux 1976-1977, exp. 4; J. Oesterlé, Sur la trace des opérateurs de Hecke, Thèse de 3e cycle, Université Paris-Sud (Orsay) 1977; D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976; H. Cohen and F. Strömberg, Modular Forms: A Classical Approach, Graduate Studies in Mathematics 179, AMS 2017, Section 12.4; E. Hecke, Theorie der Eisensteinschen Reihen höherer Stufe und ihre Anwendung auf Funktionentheorie und Arithmetik, Abh. Math. Sem. Univ. Hamburg 5 (1927), 199-224; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, Chapter 5

import Mathlib
import Definitions.Def_RPLib_S3_KernelSB
import Definitions.Def_RPLib_S3_KernelD

/-!
# S3-ES-Wt2 (O3): the trace with the holomorphic projection of `ω_s`

With an orthonormal basis `b_j` of `S_k(Γ₁(M))` (Petersson product):
* `Hdiag z = Σ_j conj(b_j z) (T b_j)(z) y^k` (independent of `s`), `trace_eq_integral_Hdiag`: `Tr T = ∫_{fdom} Hdiag`.
* `projS z = Σ_j b_j(z) conj⟪ω_s(·, -conj z), b_j⟫` (the projection of `ω_s(·, -conj z)` onto `S_k`, at `z`).
* `Hdiag_eq_projS`: `Hdiag z = n^(k-1) C_k(s)⁻¹ conj(projS z) y^k` (every `s` with `k/2 + s > 1`).
* `diag_split`: `n^(k-1) C_k(s)⁻¹ conj(ω_s(z, -conj z)) y^k = Hdiag z + n^(k-1) C_k(s)⁻¹ conj(ω_s(z, -conj z) - projS z) y^k`.
-/

open Filter Complex UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Topology Manifold ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.KernelS

open RP.FundDomain RP.Petersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke
  RamanujanPetersson.Kernel RamanujanPetersson.Bergman RamanujanPetersson.BergmanS
open RamanujanPetersson.HeckeAlgebra (heckeTn)

variable {M : ℕ} [NeZero M]

lemma finiteDimensional_PS (k : ℤ) : FiniteDimensional ℂ (PeterssonSpace (Gamma1 M) k) := by
  have := RamanujanPetersson.FinDim.finiteDimensional_cuspForm_Gamma1 M k
  exact LinearEquiv.finiteDimensional (toPS' M k)

variable (M) in
/-- The fixed orthonormal basis of `S_k(Γ₁(M))`. -/
def onb (k : ℤ) :
    OrthonormalBasis (Fin (Module.finrank ℂ (PeterssonSpace (Gamma1 M) k))) ℂ (PeterssonSpace (Gamma1 M) k) :=
  haveI := finiteDimensional_PS (M := M) k
  stdOrthonormalBasis ℂ (PeterssonSpace (Gamma1 M) k)

variable (M) in
/-- `b_j` as a cusp form. -/
def bj (k : ℕ) (j : Fin (Module.finrank ℂ (PeterssonSpace (Gamma1 M) (k : ℤ)))) : S1 M k :=
  PeterssonSpace.toCuspForm (onb M (k : ℤ) j)

variable (M) in
/-- `Hdiag z = Σ_j conj(b_j z) (T_n ⟨δ⟩ b_j)(z) y^k`. -/
def Hdiag (k n : ℕ) (δ : (ZMod M)ˣ) (z : ℍ) : ℂ :=
  ∑ j, conj (bj M k j z) * ((heckeTn (k : ℤ) n * diamond (k : ℤ) δ : Module.End ℂ (S1 M k)) (bj M k j)) z *
    ((z.im : ℂ) ^ k)

/-- **`Tr(T_n ⟨δ⟩) = ∫_{fdom} Hdiag`.** -/
theorem trace_eq_integral_Hdiag (k n : ℕ) (δ : (ZMod M)ˣ) :
    LinearMap.trace ℂ (S1 M k) (heckeTn (k : ℤ) n * diamond (k : ℤ) δ) =
      ∫ z in fdom (Gamma1 M), Hdiag M k n δ z := by
  have := finiteDimensional_PS (M := M) (k : ℤ)
  let b := onb M (k : ℤ)
  let T : PeterssonSpace (Gamma1 M) (k : ℤ) →ₗ[ℂ] PeterssonSpace (Gamma1 M) (k : ℤ) :=
    heckeTn (k : ℤ) n * diamond (k : ℤ) δ
  have htr : LinearMap.trace ℂ (S1 M k) (heckeTn (k : ℤ) n * diamond (k : ℤ) δ) =
      LinearMap.trace ℂ _ T := rfl
  rw [htr, LinearMap.trace_eq_sum_inner T b]
  calc ∑ j, inner ℂ (b j) (T (b j))
      = ∑ j, ∫ z in fdom (Gamma1 M), petersson (k : ℤ) (PeterssonSpace.toCuspForm (b j))
          (PeterssonSpace.toCuspForm (T (b j))) z := rfl
    _ = ∫ z in fdom (Gamma1 M), ∑ j, petersson (k : ℤ) (PeterssonSpace.toCuspForm (b j))
          (PeterssonSpace.toCuspForm (T (b j))) z := by
        rw [integral_finsetSum]
        intro j _
        exact integrableOn_petersson _ _
    _ = ∫ z in fdom (Gamma1 M), Hdiag M k n δ z := rfl

variable (M) in
/-- The projection of `ω_s(·, -conj z)` onto `S_k`, evaluated at `z`. -/
def projS (k n : ℕ) (δ : (ZMod M)ˣ) (s : ℝ) (z : ℍ) : ℂ :=
  ∑ j, bj M k j z * conj (peterssonInner (Gamma1 M) k
    (omegaSH M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s (-conj (z : ℂ))) (bj M k j))

/-- **`Hdiag z = n^(k-1) C_k(s)⁻¹ conj(projS z) y^k`.** -/
theorem Hdiag_eq_projS (hM : 3 ≤ M) {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hσ : 1 < (k : ℝ) / 2 + s) {n : ℕ}
    (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) (z : ℍ) :
    Hdiag M k n δ z = (n : ℂ) ^ (k - 1) * (bergmanConstS k s)⁻¹ * conj (projS M k n δ s z) *
      ((z.im : ℂ) ^ k) := by
  simp only [Hdiag, projS, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [reproducingS hM hk hσ hn hnM δ (bj M k j) z]
  ring

/-- **The pointwise split of the diagonal** into the `s`-independent part and the projection defect. -/
theorem diag_split (hM : 3 ≤ M) {k : ℕ} (hk : 2 ≤ k) {s : ℝ} (hσ : 1 < (k : ℝ) / 2 + s) {n : ℕ}
    (hn : 0 < n) (hnM : n.Coprime M) (δ : (ZMod M)ˣ) (z : ℍ) :
    (n : ℂ) ^ (k - 1) * (bergmanConstS k s)⁻¹ *
        (conj (omegaS M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s z (-conj (z : ℂ))) * ((z.im : ℂ) ^ k)) =
      Hdiag M k n δ z + (n : ℂ) ^ (k - 1) * (bergmanConstS k s)⁻¹ *
        (conj (omegaS M k n ((unitOf M n * δ : (ZMod M)ˣ) : ZMod M) s z (-conj (z : ℂ)) -
          projS M k n δ s z) * ((z.im : ℂ) ^ k)) := by
  rw [Hdiag_eq_projS hM hk hσ hn hnM δ z, map_sub]
  ring

end RamanujanPetersson.KernelS


