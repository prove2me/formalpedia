-- Prove2me | solution 1 for ArtinKP.X.X.inner_coreL2_coreLap_self
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:33:45.66858+00:00
-- url     : https://prove2.me/submissions/6441ed0c-0bb0-4779-b7be-da728bdaf33f

import Mathlib
import Definitions.Def_ArtinKPB011
import Definitions.Def_ArtinKPB013
import Definitions.Def_ArtinKPB014
import Theorems.Thm_ArtinKP_X_X_inner_coreL2_coreLap

section
-- module Solutions.Artin.KP.X2_Calc
/-! # WP-X2, file 2: calculus in the logarithmic chart

On `Coord F = InfinitePlace F → ℂ × ℝ` (coordinates `(x_w, t_w)`, `v_w = exp t_w`):

* `pd w k U` — partial derivative in the direction `bvec w k` (`k = 0, 1`: real and imaginary
  part of `x_w`; `k = 2`: `t_w`);
* `lapE U = ∑_w (-(e^{2t_w}(∂₀² + ∂₁²) + ∂₂²) U + 2 ∂₂ U)` — the Laplacian
  `∑_w (-v_w²(∂²_{x₁} + ∂²_{x₂} + ∂²_v) + v_w ∂_v)` in the chart;
* `gamE U W = ∑_w (e^{2t_w}(∂₀U ∂₀W + ∂₁U ∂₁W) + ∂₂U ∂₂W)` — the (bilinear) carré du champ
  `∑_w v_w² ∇_w U · ∇_w W`;
* `green_E`: `∫ ρ T ΔU = ∫ ρ Γ(T, U)` when one of `T`, `U` has compact support;
* Leibniz rules, compatibility with conjugation.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-! ### Regularity -/

/-! ### Algebraic rules -/

lemma pd_conj (U : Coord F → ℂ) (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    pd w k (fun y => conj (U y)) y = conj (pd w k U y) := by
  unfold pd
  have h : (fun y => conj (U y)) = Complex.conjCLE ∘ U := rfl
  rw [h, Complex.conjCLE.comp_fderiv]
  rfl

/-! ### The weights `ρ · a_k` -/

/-! ### Green's identity on the chart -/

end

end ArtinKP.X
end

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

variable (Γ)

variable {Γ}

lemma X.gam_conj_self (u : X F → ℂ) (P : X F) :
    X.gam (fun P => conj (u P)) u P = (X.grad2 u P : ℂ) := by
  unfold X.gam X.grad2 gamE
  push_cast
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => ?_
  rw [pd_conj, Complex.conj_mul']

/-- `⟪a, Δa⟫ = ∫_{Γ\X} ∑_w v_w² |∇_w a|²`. -/
theorem X.inner_coreL2_coreLap_self_oai (a : X.core Γ) :
    ⟪X.coreL2 Γ a, X.coreL2 Γ (X.coreLap Γ a)⟫_ℂ =
      ((∫ P, (X.pou Γ P).toReal * X.grad2 a P ∂X.vol F : ℝ) : ℂ) := by
  rw [X.inner_coreL2_coreLap, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  simp only [X.gam_conj_self]
  push_cast
  rfl

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.inner_coreL2_coreLap_self_oai.{u_1} := @ArtinKP.X.X.inner_coreL2_coreLap_self_oai.{u_1}
