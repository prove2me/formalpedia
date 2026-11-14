-- Prove2me | Definitions.Def_RPLib_S3_Kernel
-- name    : RPLib_S3_Kernel
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T21:07:32.286987+00:00
-- url     : https://prove2.me/theorems/2d4dbacb-8637-43f3-b8fc-2250f41fe35a
-- title:
--   The Eichler-Selberg trace formula, the kernel method, assembled
-- statement:
--   Umbrella of the kernel construction: the operators $T_{p^m}$ expressed through $T_n$, and the trace of $T_{p^m} \langle \delta \rangle$ on $S_k(\Gamma_1(M))$ as the integral of the kernel diagonal over a fundamental domain of $\Gamma_1(M)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings)

import Mathlib
import Definitions.Def_RPLib_S3_KernelD
import Definitions.Def_RPLib_S3_Statements

/-!
# S3-Kernel: the Hecke kernel and `Tr(T_n ⟨δ⟩)` as an integral (umbrella)

* `Kernel_A`, `Kernel_A2`: the kernel `ω_{k,n,δ'}(z, w)` over `Δ_n(M)`, convergence, holomorphy, `omegaCF`
  (`ω(·, w) ∈ S_k(Γ₁(M))` for `k ≥ 3`);
* `Kernel_B1`: the reproducing identity with abstract coset representatives (`reproducing_abstract`);
* `Kernel_B2`: Hermite-normal-form representatives of `Γ₁(M) \ Δ_n(M)` (`repMap_HNF_bijective`);
* `Kernel_C`: the coset sum is `n^(1-k) T_n ⟨δ⟩ f` (`cosetSum_eq`);
* `Kernel_D`: `Tr(T_n ⟨δ⟩) = n^(k-1) / bergmanConst k · ∫_{fdom Γ₁(M)} conj ω(z, -conj z) y^k`
  (`trace_eq_integral`);
* here: `Tpow p hpM k m = T_{p^m}` (`Tpow_eq_heckeTn`) and the `Tpow` form of the trace integral
  (`trace_Tpow_eq_integral`), the shape used by `EichlerSelbergG1`.
-/

open Complex UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Kernel

open RP.FundDomain RP.Petersson RamanujanPetersson.Bergman RamanujanPetersson.Diamond
  RamanujanPetersson.Hecke
open RamanujanPetersson.HeckeAlgebra (heckeTn heckeTn_one heckeTn_prime heckeTn_prime_pow_succ_succ
  heckeTP_eq heckeCorr_of_not_dvd)

/-- The recursion `Tpow` of `S3.Statements` is `T_{p^m}` (`p ∤ M`). -/
theorem Tpow_eq_heckeTn {M : ℕ} [NeZero M] (p : ℕ) [hp : Fact p.Prime] (hpM : ¬ p ∣ M) (k : ℤ) :
    ∀ m : ℕ, S3.Tpow p hpM k m = heckeTn (M := M) k (p ^ m)
  | 0 => by rw [S3.Tpow, pow_zero, heckeTn_one]
  | 1 => by rw [S3.Tpow, pow_one, heckeTn_prime k hp.out, heckeTP_eq]
  | (m + 2) => by
      rw [S3.Tpow, heckeTn_prime_pow_succ_succ k hp.out m, heckeTP_eq, heckeCorr_of_not_dvd k hpM,
        Tpow_eq_heckeTn p hpM k (m + 1), Tpow_eq_heckeTn p hpM k m]

/-- **`Tr(T_{p^m} ⟨δ⟩ | S_k(Γ₁(M)))` as an integral** (`M ≥ 3`, `k ≥ 3`, `p ∤ M`). -/
theorem trace_Tpow_eq_integral {M : ℕ} [NeZero M] (hM : 3 ≤ M) {k : ℕ} (hk : 3 ≤ k) (p : ℕ)
    [hp : Fact p.Prime] (hpM : ¬ p ∣ M) (m : ℕ) (δ : (ZMod M)ˣ) :
    LinearMap.trace ℂ (S1 M (k : ℤ)) (S3.Tpow p hpM (k : ℤ) m * diamond (k : ℤ) δ) =
      ((p ^ m : ℕ) : ℂ) ^ (k - 1) * (bergmanConst k)⁻¹ *
        ∫ z in fdom (Gamma1 M), conj (omega M k (p ^ m : ℕ)
          ((unitOf M (p ^ m) * δ : (ZMod M)ˣ) : ZMod M) z (-conj (z : ℂ))) * ((z.im : ℂ) ^ k) := by
  rw [Tpow_eq_heckeTn]
  exact trace_eq_integral hk hM (pow_pos hp.out.pos m)
    (Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpM)) δ

end RamanujanPetersson.Kernel


