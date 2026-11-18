-- Prove2me | Definitions.Def_ArtinKPB011
-- name    : ArtinKPB011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:32:03.836215+00:00
-- url     : https://prove2.me/theorems/26290ab9-771e-44c6-b495-7247d909e000
-- title:
--   Definitions bundle ArtinKPB011 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 12 declarations of that development: 5 definitions and 7 theorems. The definitions and types are `ArtinKP.X.X.L2`, `ArtinKP.X.X.coreL2`, `ArtinKP.X.X.lift`, `ArtinKP.X.X.toL2`, `ArtinKP.X.liftQ`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.X2_H1`, `KP.X_Discrete`, `KP.X_Fourier`, `KP.X_L2`, `KP.X_Quot`.
--
--   **Imports.** It imports the bundle `ArtinKPB010` of this split; the published statement `ArtinKP.X.X.l2Rep_of_mem_core`.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB012`; the statements `ArtinKP.N2.integrable_lift_pou`, `ArtinKP.N2.lintegral_lift_pou_ne_top`, `ArtinKP.X.X.coreL2_injective`, `ArtinKP.X.X.dense_range_coreL2`, `ArtinKP.X.X.inner_coreL2_coreLap`, `ArtinKP.X.X.inner_coreL2_coreLap_self`, `ArtinKP.X.X.inner_coreLap_coreL2` and `ArtinKP.X.X.inner_coreLap_eq`; the proofs of `ArtinKP.X.X.coreL2_injective`, `ArtinKP.X.X.inner_coreL2_coreLap`, `ArtinKP.X.X.inner_coreL2_coreLap_self`, `ArtinKP.X.X.inner_coreLap_coreL2` and `ArtinKP.X.X.inner_coreLap_eq`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinKPB010
import Theorems.Thm_ArtinKP_X_X_l2Rep_of_mem_core

section
-- module Solutions.Artin.KP.X_Quot
/-! # WP-X, file 5: quotient measures and unfolding without fundamental domains

Abstract setting: a countable group `G` acting measurably on `(α, μ)` and preserving `μ`.
A *partition of unity* for the action is a measurable `η : α → ℝ≥0∞` with
`∑_g η (g • a) = 1` for all `a` (the indicator of a strict fundamental domain is one; in a
properly discontinuous situation an everywhere positive one always exists, `exists_isPOU`).
The quotient measure on `G \ α` is the push-forward of `η μ`; it does not depend on `η`
(`quotMeasure_eq`).  Everything is Tonelli:

* `lintegral_tsum_swap` : `∫ φ · Σ_g ψ∘g = ∫ ψ · Σ_g φ∘g`;
* `lintegral_mul_pou_eq` : independence of `η`;
* `lintegral_autom_mul_eq` : unfolding `∫_{G\α} (Σ_{H\G} f∘γ) u = ∫_{H\α} f u`;
* `setLIntegral_le_mul_lintegral_pou` : a set meeting each orbit at most `m` times has
  `∫_B f ≤ m ∫_{G\α} f`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

/-- A `G`-invariant set which is null for `η μ` is `μ`-null. -/
theorem measure_eq_zero_of_invariant {η : α → ℝ≥0∞} (hη : IsPOU G η) {N : Set α}
    (hN : MeasurableSet N) (hinv : ∀ (g : G) (a : α), g • a ∈ N ↔ a ∈ N)
    (h0 : ∫⁻ a in N, η a ∂μ = 0) : μ N = 0 := by
  have h1 : Measurable (N.indicator fun _ : α => (1 : ℝ≥0∞)) := measurable_const.indicator hN
  have h := lintegral_tsum_swap (G := G) (μ := μ) h1 hη.measurable
  simp only [hη.tsum_eq, mul_one] at h
  rw [lintegral_indicator hN, setLIntegral_const, one_mul] at h
  rw [h]
  have h2 : ∀ a, η a * ∑' g : G, N.indicator (fun _ : α => (1 : ℝ≥0∞)) (g • a) =
      N.indicator η a * ∑' _g : G, (1 : ℝ≥0∞) := by
    intro a
    by_cases ha : a ∈ N
    · have : ∀ g : G, N.indicator (fun _ : α => (1 : ℝ≥0∞)) (g • a) = 1 := fun g => by
        simp [(hinv g a).mpr ha]
      simp [this, ha]
    · have : ∀ g : G, N.indicator (fun _ : α => (1 : ℝ≥0∞)) (g • a) = 0 := fun g => by
        have hga : g • a ∉ N := fun h => ha ((hinv g a).mp h)
        simp [hga]
      simp [this, ha]
  simp_rw [h2]
  rw [lintegral_mul_const _ (hη.measurable.indicator hN), lintegral_indicator hN, h0, zero_mul]

/-! ### The quotient measure -/

/-- The projection to the quotient is quasi-measure-preserving (null sets pull back to null
sets). -/
theorem quasiMeasurePreserving_mk {η : α → ℝ≥0∞} (hη : IsPOU G η) :
    Measure.QuasiMeasurePreserving (Quotient.mk (MulAction.orbitRel G α)) μ
      (quotMeasure G η μ) := by
  refine ⟨measurable_mk, Measure.AbsolutelyContinuous.mk fun A hA h0 => ?_⟩
  rw [Measure.map_apply measurable_mk hA]
  refine measure_eq_zero_of_invariant hη (measurable_mk hA) (fun g a => ?_) ?_
  · simp only [mem_preimage, mk_smul]
  · unfold quotMeasure at h0
    rw [Measure.map_apply measurable_mk hA, withDensity_apply _ (measurable_mk hA)] at h0
    exact h0

/-! ### Unfolding -/

/-! ### Multiplicity and existence of partitions of unity -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol
/-! # WP-X, file 6: discreteness of `SL(2, 𝓞_F)` on `X`, the quotient measure, `L²(Γ\X)`

* `entries_bounded`: if `Q` and `g • Q` lie in a box of `H3` the entries of `g` are bounded;
* `finite_return_box`: a box of `X` meets only finitely many of its `SL(2,𝓞_F)`-translates
  (`𝓞_F` is discrete in `ℂ^r`); the same for compact sets (`finite_return_of_isCompact`);
* a positive partition of unity for every subgroup `Γ ≤ SL(2,𝓞_F)`, the quotient measure
  `X.quotVol Γ` on `Γ \ X` (independent of the partition), `X.L2 Γ = L²(Γ\X)`;
* the cusp stabilizer `GammaInf Γ` and its action in coordinates.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### One factor -/

/-! ### The integral group -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-- The Hilbert space `L²(Γ \ X)`. -/
abbrev X.L2 (Γ : Subgroup (SL(2, 𝓞 F))) : Type _ := Lp ℂ 2 (X.quotVol Γ)

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_L2
/-! # WP-X, file 7: `L²` of the quotient and local restriction maps (abstract)

For a partition of unity `η` and a measurable set `B` meeting each orbit at most `m < ∞` times,
pulling back and restricting is a bounded operator
`restrictL2 : L²(G \ α) →L[ℂ] L²(B, μ)` of norm `≤ √m`.  Every functional
`u ↦ ∫_B conj ψ · u` with `ψ ∈ L²(B)` is therefore continuous on `L²(G \ α)`
(`pairingL2`).  This is the continuity of Fourier-coefficient functionals (MATH (C6)).
-/

open scoped ENNReal ComplexConjugate InnerProductSpace
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] {η : α → ℝ≥0∞}

/-- The pull-back to `α` of an `L²` function on the quotient. -/
def liftQ (u : Lp ℂ 2 (quotMeasure G η μ)) (a : α) : ℂ :=
  u (Quotient.mk (MulAction.orbitRel G α) a)

/-- a.e. equalities on the quotient pull back. -/
lemma liftQ_ae_eq (hη : IsPOU G η) {f f' : Quotient (MulAction.orbitRel G α) → ℂ}
    (h : f =ᵐ[quotMeasure G η μ] f') :
    (fun a => f (Quotient.mk (MulAction.orbitRel G α) a)) =ᵐ[μ]
      fun a => f' (Quotient.mk (MulAction.orbitRel G α) a) :=
  (quasiMeasurePreserving_mk hη).ae_eq_comp h

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol
/-! # WP-X, file 9: local restriction and coefficient functionals on `L²(Γ\X)`

* `X.vol_box_lt_top`: boxes have finite measure;
* `X.restrictBox Γ n : L²(Γ\X) →L[ℂ] L²(box n)`, bounded;
* `X.coeffFunctional Γ n ψ … : L²(Γ\X) →L[ℂ] ℂ`, `u ↦ ∫_{box n} conj ψ · u`, for bounded measurable
  `ψ`.  The Fourier-coefficient functional `ℓ_{ν,φ}` of MATH (C6) is the case
  `ψ(P) = 1_D(x) · conj(e_∞(-ν x) φ(v))` with `D` a fundamental set of the translation lattice
  and `supp φ` compact (so that `D × supp φ` lies in a box).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- The pull-back to `X` of an element of `L²(Γ\X)`: a `Γ`-invariant function. -/
def X.lift (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) : X F → ℂ := liftQ u

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

lemma X.L2Rep.add {f g : X F → ℂ} (hf : X.L2Rep Γ f) (hg : X.L2Rep Γ g) :
    X.L2Rep Γ fun P => f P + g P :=
  ⟨hf.meas.add hg.meas, fun γ P => by rw [hf.inv γ P, hg.inv γ P], hf.memLp.add hg.memLp⟩

lemma X.L2Rep.const_mul {f : X F → ℂ} (hf : X.L2Rep Γ f) (c : ℂ) :
    X.L2Rep Γ fun P => c * f P :=
  ⟨hf.meas.const_mul c, fun γ P => by rw [hf.inv γ P], hf.memLp.const_smul c⟩

variable (Γ)

/-- The class in `L²(Γ\X)` of an invariant square integrable function. -/
def X.toL2 (f : X F → ℂ) (h : X.L2Rep Γ f) : X.L2 Γ := h.memLp.toLp _

variable {Γ}

lemma X.toL2_add {f g : X F → ℂ} (hf : X.L2Rep Γ f) (hg : X.L2Rep Γ g) :
    X.toL2 Γ (fun P => f P + g P) (hf.add hg) = X.toL2 Γ f hf + X.toL2 Γ g hg :=
  MemLp.toLp_add hf.memLp hg.memLp

lemma X.toL2_const_mul {f : X F → ℂ} (hf : X.L2Rep Γ f) (c : ℂ) :
    X.toL2 Γ (fun P => c * f P) (hf.const_mul c) = c • X.toL2 Γ f hf :=
  MemLp.toLp_const_smul c hf.memLp

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

variable (Γ)

variable {Γ}

variable (Γ)

/-- The class of a core function in `L²(Γ\X)`. -/
def X.coreL2 : X.core Γ →ₗ[ℂ] X.L2 Γ where
  toFun w := X.toL2 Γ w (X.l2Rep_of_mem_core w.2)
  map_add' w w' := X.toL2_add (X.l2Rep_of_mem_core w.2) (X.l2Rep_of_mem_core w'.2)
  map_smul' c w := X.toL2_const_mul (X.l2Rep_of_mem_core w.2) c

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end


