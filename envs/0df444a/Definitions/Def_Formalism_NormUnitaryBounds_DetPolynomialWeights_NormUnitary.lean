-- Prove2me | Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary
-- name    : Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:34.053352+00:00
-- url     : https://prove2.me/theorems/086684a4-ab41-40fe-b227-288e54be5e8d
-- title:
--   Norm Unitary
-- statement:
--   Definitions and structural lemmas for Norm Unitary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormUnitary.lean

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
namespace Formalism.NormUnitaryCountingLemmas.NU
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
def cnt {d : ℕ} (t : Fin d → σ) : σ →₀ ℕ := ∑ m, Finsupp.single (t m) 1
def fct (e : σ →₀ ℕ) : ℕ := ∏ i, (e i).factorial
def P {d : ℕ} (S : (Fin d → σ) → ℂ) : MvPolynomial σ ℂ := ∑ t, monomial (cnt t) (S t)
def T (d : ℕ) (F : MvPolynomial σ ℂ) (t : Fin d → σ) : ℂ :=
  coeff (cnt t) F * (fct (cnt t) : ℂ) / (d.factorial : ℂ)
def ip (F G : MvPolynomial σ ℂ) : ℂ :=
  ∑ e ∈ F.support, coeff e F * star (coeff e G) * (fct e : ℂ)
def sub (V : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun i => ∑ l, C (V i l) * X l
def act {d : ℕ} (V : Matrix σ σ ℂ) (S : (Fin d → σ) → ℂ) (t : Fin d → σ) : ℂ :=
  ∑ s, S s * ∏ m, V (s m) (t m)
def FR (F : MvPolynomial σ ℂ) : ℝ := ∑ e ∈ F.support, ‖coeff e F‖ ^ 2 * (fct e : ℝ)
def blk {N n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin N × Fin n) (Fin N × Fin n) ℂ :=
  fun p q => if p.1 = q.1 then U p.2 q.2 else 0
end Formalism.NormUnitaryCountingLemmas.NU
namespace Formalism.NormUnitaryCountingLemmas
end Formalism.NormUnitaryCountingLemmas


