-- Prove2me | solution 1 for ArtinKP.X.X.l2Rep_of_mem_core
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:29:24.453876+00:00
-- url     : https://prove2.me/submissions/aa364d8f-0f14-42e5-ba00-af0d8e9bf504

import Mathlib
import Definitions.Def_ArtinKPB010
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_smooth_of_mem_core

section
-- module Solutions.Artin.KP.X2_H1
/-! # WP-X2, file 5: the geometric core and the energy space `H¹(Γ \ X)`

* `X.toL2 Γ f h : L²(Γ\X)` — the class of a measurable `Γ`-invariant function that is square
  integrable modulo `Γ` (`X.L2Rep Γ f`), with `X.inner_toL2`, `X.norm_sq_toL2`;
* `X.core Γ` — the functions `∑_{γ ∈ Γ} φ ∘ γ`, `φ ∈ C_c^∞(X)` (equivalently: smooth,
  `Γ`-invariant, support compact modulo `Γ`; see `X.mem_core_of_tsupport` in `X2_Weak`);
* `X.symmOp Γ : SymmOp (L²(Γ\X))` — the Laplacian on the core: dense domain, symmetric,
  nonnegative, with `⟪w, Δw⟫ = ∫_{Γ\X} ∑_w v_w² |∇_w w|²` (`X.inner_coreL2_coreLap_self`);
* `X.H1 Γ`, `X.energy Γ : CAbs.EnergySpace (X.H1 Γ) (X.L2 Γ)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] (Γ : Subgroup (SL(2, 𝓞 F)))

/-! ### Classes of invariant functions -/

variable {Γ}

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

variable (Γ)

variable {Γ}

lemma X.l2Rep_of_mem_core_oai {w : X F → ℂ} (hw : w ∈ X.core Γ) : X.L2Rep Γ w := by
  have hs := X.smooth_of_mem_core hw
  have hinv := X.isInv_of_mem_core hw
  obtain ⟨φ, hφ, hc, rfl⟩ := hw
  refine X.L2Rep.of_lintegral hs.continuous.measurable hinv ?_
  have h1 : ∀ P, ‖X.avg Γ φ P‖ₑ ^ (2 : ℝ) * X.pou Γ P =
      ‖X.avg Γ (fun P => φ P * X.avg Γ φ P) P‖ₑ * X.pou Γ P := by
    intro P
    rw [X.avg_mul_inv hinv, enorm_mul, ← sq, ← ENNReal.rpow_natCast]
    norm_num
  simp_rw [h1]
  refine ne_top_of_le_ne_top ?_ (lintegral_avg_le (X.isPOU_pou Γ)
    (hφ.continuous.mul hs.continuous).measurable)
  exact lintegral_ne_top_of_continuous (hφ.continuous.mul hs.continuous) hc.mul_right

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.l2Rep_of_mem_core_oai.{u_1} := @ArtinKP.X.X.l2Rep_of_mem_core_oai.{u_1}
