-- Prove2me | Definitions.Def_ArtinKPB013
-- name    : ArtinKPB013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:24:15.735196+00:00
-- url     : https://prove2.me/theorems/b1437fc2-da3b-4dbd-8659-0b2c04747d15
-- title:
--   Definitions bundle ArtinKPB013 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 6 declarations of that development: 2 definitions and 4 theorems. The definitions and types are `ArtinKP.X.X.coreLap`, `ArtinKP.X.X.gam`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.X2_Calc`, `KP.X2_Core`, `KP.X2_H1`, `KP.X2_Isom`.
--
--   **Imports.** It imports the bundle `ArtinKPB006` of this split; the published statements `ArtinKP.X.X.lap_mem_core` and `ArtinKP.X.X.smooth_of_mem_core`.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB015`; the statements `ArtinKP.X.X.inner_coreL2_coreLap`, `ArtinKP.X.X.inner_coreL2_coreLap_self`, `ArtinKP.X.X.inner_coreLap_coreL2`, `ArtinKP.X.X.inner_coreLap_eq` and `ArtinKP.X.X.qgreen`; the proofs of `ArtinKP.X.X.inner_coreL2_coreLap`, `ArtinKP.X.X.inner_coreL2_coreLap_self`, `ArtinKP.X.X.inner_coreLap_coreL2`, `ArtinKP.X.X.inner_coreLap_eq` and `ArtinKP.X.X.qgreen`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinKPB006
import Theorems.Thm_ArtinKP_X_X_lap_mem_core
import Theorems.Thm_ArtinKP_X_X_smooth_of_mem_core

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

lemma pd_const_mul {U : Coord F → ℂ} {y : Coord F} (hU : DifferentiableAt ℝ U y) (c : ℂ)
    (w : InfinitePlace F) (k : Fin 3) :
    pd w k (fun y => c * U y) y = c * pd w k U y := by
  unfold pd
  rw [fderiv_const_mul hU]
  rfl

lemma lapE_const_mul {U : Coord F → ℂ} (hU : ContDiff ℝ 2 U) (c : ℂ) (y : Coord F) :
    lapE (fun y => c * U y) y = c * lapE U y := by
  have hd : Differentiable ℝ U := hU.differentiable (by simp)
  have hpd : ∀ w k, Differentiable ℝ (pd w k U) :=
    fun w k => (contDiff_pd (m := 1) hU (by norm_num) w k).differentiable (by simp)
  unfold lapE
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : ∀ k, pd w k (fun y => c * U y) = fun y => c * pd w k U y :=
    fun k => funext fun z => pd_const_mul (hd z) c w k
  simp_rw [h1]
  have h2 : ∀ k, pd w k (fun y => c * pd w k U y) y = c * pd w k (pd w k U) y :=
    fun k => pd_const_mul (hpd w k y) c w k
  simp_rw [h2, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · ring

/-! ### The weights `ρ · a_k` -/

/-! ### Green's identity on the chart -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Isom
attribute [-instance] _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX
/-! # WP-X2, file 3: the group acts by isometries; the Laplacian commutes with it

* `Iso1 φ`: a smooth self-map of one factor (in the chart) whose derivative is conformal for the
  hyperbolic metric; translations and the inversion `Jmap` (the chart form of the Weyl element)
  are such, hence every element of `SL(2,ℂ)` acts by one (`mem_iso1`).
* `IsoHalf Φ`: a smooth self-map of `Coord F` preserving the carré du champ.
* `lapE_comp_of_iso`: a measure-preserving `IsoHalf` bijection with `IsoHalf` inverse commutes
  with the Laplacian.  The proof is weak: test against `C_c^∞`, use Green twice — no second
  derivative of the Möbius action is ever computed.
* On `X`: `X.Smooth`, `X.lap`, `X.gam`, and their invariance under `G∞ = SL(2,ℂ)^r`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

/-! ### One factor -/

/-! ### Every element of `SL(2,ℂ)` acts by an `Iso1` -/

/-! ### Isometries of the chart -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### The action of `G∞` in the chart -/

/-! ### Calculus on `X` -/

/-- The bilinear carré du champ `Γ(u, w) = ∑_w v_w² ∇_w u · ∇_w w` on `X`. -/
def X.gam (u w : X F → ℂ) (P : X F) : ℂ :=
  gamE (fun y => u (chart F y)) (fun y => w (chart F y)) ((chart F).symm P)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Core
/-! # WP-X2, file 4: Green's identity on `X` and averaging over `Γ`

* `X.green`: `∫_X φ Δu = ∫_X Γ(φ, u)` when `φ` or `u` has compact support;
* `X.avg Γ φ = ∑_{γ ∈ Γ} φ ∘ γ` for compactly supported `φ`: locally finite, smooth,
  `Δ (avg φ) = avg (Δ φ)`, `Γ(avg φ, u) = avg Γ(φ, u)` for `Γ`-invariant `u`;
* unfolding `∫ η · avg φ · g = ∫_X φ g` for invariant `g` (`integral_avg_mul`);
* **Green's identity on `Γ \ X`** for `w = avg φ` and any smooth invariant `u`
  (`X.qgreen`, `X.qgreen'`): `∫ η w Δu = ∫ η Γ(w, u) = ∫ η u Δw`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-! ### Measure-theoretic instances -/

/-! ### Calculus on `X`: basic rules -/

lemma X.lap_add {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) (P : X F) :
    X.lap (fun P => u P + w P) P = X.lap u P + X.lap w P := by
  unfold X.lap
  rw [lapE_add (hu.contDiff.of_le two_le_top) (hw.contDiff.of_le two_le_top)]

lemma X.lap_const_mul {u : X F → ℂ} (hu : X.Smooth u) (c : ℂ) (P : X F) :
    X.lap (fun P => c * u P) P = c * X.lap u P := by
  unfold X.lap
  rw [lapE_const_mul (hu.contDiff.of_le two_le_top)]

/-! ### Invariance -/

/-! ### Local finiteness and averaging -/

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

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

/-- The Laplacian on the core. -/
def X.coreLap : X.core Γ →ₗ[ℂ] X.core Γ where
  toFun w := ⟨X.lap w, X.lap_mem_core w.2⟩
  map_add' w w' := Subtype.ext (funext fun P =>
    X.lap_add (X.smooth_of_mem_core w.2) (X.smooth_of_mem_core w'.2) P)
  map_smul' c w := Subtype.ext (funext fun P =>
    X.lap_const_mul (X.smooth_of_mem_core w.2) c P)

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end


