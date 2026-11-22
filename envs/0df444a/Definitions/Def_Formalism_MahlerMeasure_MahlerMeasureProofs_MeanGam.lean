-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:23.69411+00:00
-- url     : https://prove2.me/theorems/f6bcfd5d-7d79-4f7c-8d45-f9c97e1cca70
-- title:
--   Mean Gam
-- statement:
--   Definitions and structural lemmas for Mean Gam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/MeanGam.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply


set_option autoImplicit false
namespace Formalism.GM.MeanGammaLemmas
open Polynomial Finset
end Formalism.GM.MeanGammaLemmas
namespace Formalism.GM.MeanGammaLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
lemma coeff_initPart (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) (m : σ →₀ ℕ) :
    (initPart v e f).coeff m = if m v = e then f.coeff m else 0 := by
  classical
  simp only [initPart, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single m]
  · by_cases h : m v = e <;> simp [h]
  · intro b _ hb
    by_cases h : b v = e <;> simp [h, MvPolynomial.coeff_monomial, hb]
  · intro hm
    have h0 : f.coeff m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
    by_cases h : m v = e <;> simp [h, h0]
noncomputable def initL (p : ℕ) [Fact p.Prime] (v : σ) (e : ℕ) :
    MvPolynomial σ ℚ_[p] →ₗ[ℤ_[p]] MvPolynomial σ ℚ_[p] where
  toFun := initPart v e
  map_add' x y := by
    ext m; simp only [coeff_initPart, coeff_add]; split_ifs <;> simp
  map_smul' a x := by
    ext m
    simp only [coeff_initPart, RingHom.id_apply]
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, coeff_initPart]
    split_ifs <;> simp
end Formalism.GM.MeanGammaLemmas
namespace Formalism.GM.MeanGammaLemmas
open Finset
end Formalism.GM.MeanGammaLemmas
namespace Formalism.GM.MeanGammaLemmas
open Finset
end Formalism.GM.MeanGammaLemmas
namespace Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M
end Formalism.GM.MeanGammaLemmas
namespace Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M
noncomputable def betaT (p : ℕ) [Fact p.Prime] (m z o S e : ℕ) : ℚ_[p] :=
  (p : ℚ_[p]) ^ m * ((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) / ((o.factorial * S.factorial : ℕ) : ℚ_[p])
noncomputable def gramT (p : ℕ) [Fact p.Prime] {K r n : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r)
    (f : Fin n → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (ord : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℚ_[p] :=
  Matrix.of fun x y => fock p (initPart (Fin.last K, ρ) (ord x) (f x)) (initPart (Fin.last K, ρ) (ord x) (f y)) /
    ∏ i, ((LLw.deg i).factorial : ℚ_[p])
noncomputable def coefT (p : ℕ) [Fact p.Prime] {n : ℕ} (D0 m : ℕ) (cc : Fin n → Fin n → ℕ → ℤ_[p]) :
    Fin n → Fin n → ℕ → ℚ_[p] :=
  fun x y k => if k ≤ D0 then (p : ℚ_[p]) ^ m * (cc x y k : ℚ_[p]) else 0
end Formalism.GM.MeanGammaLemmas
namespace Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M
end Formalism.GM.MeanGammaLemmas
namespace Formalism.GM
open Polynomial Finset Formalism.GM.M Formalism.GM.MeanGammaLemmas
end Formalism.GM


