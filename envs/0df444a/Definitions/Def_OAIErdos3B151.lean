-- Prove2me | Definitions.Def_OAIErdos3B151
-- name    : OAIErdos3B151
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T00:09:39.060559+00:00
-- url     : https://prove2.me/theorems/59dfae96-d7d7-44a9-b382-b8e448b5390b
-- title:
--   OpenAI Erdős-3 split, definitions bundle 152 of 177
-- statement:
--   Definitions bundle 152 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B150`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 152 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.ForecastSingleDeckResidues`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.correlation_after_freezing`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eraseEmptyTags`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eraseEmptyTags_cover`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eraseEmptyTags_mask`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eraseEmptyTags_modulus`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eraseEmptyTags_smooth`, `OAI.Erdos3.VectorPolynomial.NormalizedPolynomialTwist.eval_eraseEmptyTags`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSpatial_cutoff`, `OAI.Erdos3.VectorPolynomial.forecastBufferedCoveredSiteFactor`, `OAI.Erdos3.VectorPolynomial.forecastBufferedFullResidue`, `OAI.Erdos3.VectorPolynomial.forecastCoverCutoffInput`, `OAI.Erdos3.VectorPolynomial.forecastRawGridEquiv`, `OAI.Erdos3.VectorPolynomial.forecastRawSpatialEquiv`, `OAI.Erdos3.VectorPolynomial.forecastSingleDeckEquiv`, `OAI.Erdos3.VectorPolynomial.forecastSingleMixedRawEquiv`, `OAI.Erdos3.VectorPolynomial.forecastSingleMixedRawPoint`, `OAI.Erdos3.VectorPolynomial.instDecidableEqUnit`, `OAI.Erdos3.VectorPolynomial.mixedCoveredJetDeckReference`, `OAI.Erdos3.VectorPolynomial.physicalGridFactorInput_of_isEmpty`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B130
import Definitions.Def_OAIErdos3B150

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def forecastCoverCutoffInput (period : ℕ)
    (z : (Σ j, J j) → UnitAddCircle) :
    JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle :=
  fun a => period • z ⟨a.1, a.2.2⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3
open scoped NNReal

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]
variable {Y : Type*} [PseudoMetricSpace Y]

local notation "single" => (fun _ : Fin m => Unit)
local notation "chart" => mixedCoveredJetChart (O := single) U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := single) (E := E) U o b d
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))

noncomputable def forecastBufferedFullResidue (w : MixedCoveredJetSource I single E n d) :
    ∀ j, Fin (n j) ⊕ E j → ZMod period :=
  fun j => Sum.elim (fun i => ((w.1 j).2 i () : ZMod period))
    (fun i => ((w.2 j () i).val : ZMod period))

noncomputable def forecastBufferedCoveredSiteFactor
    (F : (∀ j, Fin (n j) ⊕ E j → ZMod period) → Y × (LayerSamplerAxis I n → ℝ) → ℂ)
    (s : Y) : EuclideanJetLayers U single → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun w =>
    allocatedBufferedMixedSiteFactor B U b S r hr (fun _ => 1)
      (fun j => mixedArrayRegroup _ _ _ (w.1 j) ()) *
    F (forecastBufferedFullResidue d period w)
      (s, allocatedFullMixedSiteValue (R := R) U b
        (fun j => mixedArrayRegroup _ _ _ (w.1 j) ())))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (r : ℝ≥0) (hr : 0 < r) (period : ℕ) [NeZero period]
variable {X : Type*} [Fintype X]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable (m Dmod d : ℕ)
variable {P D pcap Pscale Pbad Ppres E Pτ PK PF : ℝ}
variable (hP : 1 ≤ P) (hD : 0 ≤ D) (hpcap : 0 ≤ pcap) (hscale : 0 ≤ Pscale)
variable (hbad : 0 ≤ Pbad) (hpres : 0 ≤ Ppres) (hE : 0 ≤ E)
variable (hPτ : 0 ≤ Pτ) (hPK : 0 ≤ PK) (hPF : 0 ≤ PF)

include hP hD hpcap hscale hbad hpres hE hPτ hPK hPF

include hP hD hpcap hscale hbad hpres hE hPτ hPK hPF

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastRawSpatialBoxReorder
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

noncomputable def mixedCoveredJetDeckReference {m : ℕ} (O E : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (E j)] (N : ℕ) [NeZero N] :
    Measure (∀ j, O j → E j → ZMod N) :=
  (PMF.uniformOfFintype (∀ j, O j → E j → ZMod N)).toMeasure

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (n : Fin m → ℕ) (N : ℕ) [NeZero N]

abbrev ForecastSingleDeckResidues (E : Fin m → Type*) (N : ℕ) :=
  ∀ j, Unit → E j → ZMod N

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "IntAxis" => (Σ j, Fin (n j))

noncomputable def forecastSingleMixedRawEquiv :
    MixedCoveredJetSource I single E n N ≃ᵐ
      (((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N)) where
  toFun z := ((fun a => (z.1 a.1).1 a.2 (), fun a => (z.1 a.1).2 a.2 ()), z.2)
  invFun p := (fun j => (fun i _ => p.1.1 ⟨j, i⟩, fun i _ => p.1.2 ⟨j, i⟩), p.2)
  left_inv z := by
    apply Prod.ext
    · funext j
      apply Prod.ext <;> funext i t <;> cases t <;> rfl
    · rfl
  right_inv p := rfl
  measurable_toFun := by
    change Measurable (fun z : MixedCoveredJetSource I single E n N =>
      ((fun a : RealAxis => (z.1 a.1).1 a.2 (),
        fun a : IntAxis => (z.1 a.1).2 a.2 ()), z.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ((RealAxis → ℝ) × (IntAxis → ℤ)) × (∀ j, Unit → E j → ZMod N) =>
      (fun j => (fun i (_ : Unit) => p.1.1 ⟨j, i⟩,
        fun i (_ : Unit) => p.1.2 ⟨j, i⟩), p.2))
    fun_prop

noncomputable def forecastSingleMixedRawPoint (v : RealAxis → ℝ) (k : IntAxis → ℤ)
    (deck : (∀ j, Unit → E j → ZMod N)) : MixedCoveredJetSource I single E n N :=
  (fun j => (fun i _ => v ⟨j, i⟩, fun i _ => k ⟨j, i⟩), deck)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

noncomputable local instance : DecidableEq Unit := Classical.decEq Unit

variable {m : ℕ} (E : Fin m → Type*) (N : ℕ)

def forecastSingleDeckEquiv :
    ForecastSingleDeckResidues E N ≃ ((Σ j, E j) → ZMod N) where
  toFun deck a := deck a.1 () a.2
  invFun r j _ e := r ⟨j, e⟩
  left_inv deck := by funext j u e; cases u; rfl
  right_inv r := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (R : Fin m → ℝ) (hR : ∀ j, 0 < R j)

local notation "single" => (fun _ : Fin m => Unit)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "Deck" => ForecastSingleDeckResidues E N
local notation "deckLaw" => mixedCoveredJetDeckReference single E N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L

noncomputable def forecastRawGridEquiv : MixedCoveredJetSource I single E n N ≃ᵐ
    (((short → ℤ) × Deck) × ((RealAxis → ℝ) × (active → ℤ))) where
  toFun z := (((fun a => (z.1 a.val.1).2 a.val.2 ()), z.2),
    ((fun a => (z.1 a.1).1 a.2 ()), fun a => (z.1 a.val.1).2 a.val.2 ()))
  invFun p := forecastSingleMixedRawPoint I E n N p.2.1
    (forecastIntegerAxisMerge U basis L p.1.1 p.2.2) p.1.2
  left_inv z := by
    apply Prod.ext
    · funext j
      apply Prod.ext
      · funext i t
        cases t
        rfl
      · funext i t
        cases t
        simp only [forecastSingleMixedRawPoint, forecastIntegerAxisMerge]
        split <;> rfl
    · rfl
  right_inv p := by
    apply Prod.ext
    · apply Prod.ext
      · funext a
        exact forecastIntegerAxisMerge_short U basis L p.1.1 p.2.2 a
      · rfl
    · apply Prod.ext
      · rfl
      · funext a
        exact forecastIntegerAxisMerge_active U basis L p.1.1 p.2.2 a
  measurable_toFun := by
    change Measurable (fun z : MixedCoveredJetSource I single E n N =>
      (((fun a : short => (z.1 a.val.1).2 a.val.2 ()), z.2),
        ((fun a : RealAxis => (z.1 a.1).1 a.2 ()),
          fun a : active => (z.1 a.val.1).2 a.val.2 ())))
    fun_prop
  measurable_invFun := by
    unfold forecastSingleMixedRawPoint
    have hm := (forecastIntegerAxisSplit U basis L).symm.measurable
    change Measurable (fun p : ((short → ℤ) × Deck) × ((RealAxis → ℝ) × (active → ℤ)) => (fun j =>
      (fun i (_ : Unit) => p.2.1 ⟨j, i⟩,
        fun i (_ : Unit) => (forecastIntegerAxisSplit U basis L).symm (p.1.1, p.2.2) ⟨j, i⟩), p.1.2))
    fun_prop

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical BigOperators

variable {m : ℕ} (I E : Fin m → Type*) [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (N : ℕ) [NeZero N]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ) (X : Type*) [Fintype X]

local notation "single" => (fun _ : Fin m => Unit)
local notation "RealAxis" => (Σ j, I j)
local notation "Deck" => ForecastSingleDeckResidues E N
local notation "RawSource" => MixedCoveredJetSource I single E n N
local notation "deckLaw" => mixedCoveredJetDeckReference single E N
local notation "short" => AllocatedShortIntegerAxis U basis L
local notation "active" => AllocatedActiveIntegerAxis U basis L
local notation "Target" => Deck × ((RealAxis → ℝ) × ((short → ℤ) × ((X ⊕ active) → ℤ)))

noncomputable def forecastRawSpatialEquiv : ((X → ℤ) × RawSource) ≃ᵐ Target where
  toFun p := (p.2.2, ((fun a => (p.2.1 a.1).1 a.2 ()),
    ((fun a => (p.2.1 a.val.1).2 a.val.2 ()),
      Sum.elim p.1 (fun a => (p.2.1 a.val.1).2 a.val.2 ()))))
  invFun p := ((fun x => p.2.2.2 (Sum.inl x)),
    forecastSingleMixedRawPoint I E n N p.2.1
      (forecastIntegerAxisMerge U basis L p.2.2.1 (fun a => p.2.2.2 (Sum.inr a))) p.1)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext j
        apply Prod.ext
        · funext i t
          cases t
          rfl
        · funext i t
          cases t
          simp only [forecastSingleMixedRawPoint, forecastIntegerAxisMerge]
          split <;> rfl
      · rfl
  right_inv p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply Prod.ext
        · funext a
          exact forecastIntegerAxisMerge_short U basis L p.2.2.1
            (fun a => p.2.2.2 (Sum.inr a)) a
        · funext a
          cases a with
          | inl x => rfl
          | inr a =>
            exact forecastIntegerAxisMerge_active U basis L p.2.2.1
              (fun a => p.2.2.2 (Sum.inr a)) a
  measurable_toFun := by
    change Measurable (fun p : (X → ℤ) × RawSource =>
      (p.2.2, ((fun a : RealAxis => (p.2.1 a.1).1 a.2 ()),
        ((fun a : short => (p.2.1 a.val.1).2 a.val.2 ()),
          Sum.elim p.1 (fun a : active => (p.2.1 a.val.1).2 a.val.2 ())))))
    apply Measurable.prodMk measurable_snd.snd
    apply Measurable.prodMk
    · fun_prop
    apply Measurable.prodMk
    · fun_prop
    apply measurable_pi_iff.mpr
    intro a
    cases a <;> fun_prop
  measurable_invFun := by
    have hm := (forecastIntegerAxisSplit U basis L).symm.measurable
    change Measurable (fun p : Target => ((fun x => p.2.2.2 (Sum.inl x)),
      (fun j => (fun i (_ : Unit) => p.2.1 ⟨j,i⟩,
        fun i (_ : Unit) => (forecastIntegerAxisSplit U basis L).symm
          (p.2.2.1, fun a => p.2.2.2 (Sum.inr a)) ⟨j,i⟩), p.1)))
    fun_prop

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedTwistAffineCells
namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K X : Type*} [Fintype K] [Fintype X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem correlation_after_freezing {T : Type*} [Fintype T]
    (μ : FiniteProbabilityWeights T) (twist signal : T → ℂ) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (hsignal : ∀ t, ‖signal t‖ ≤ 1)
    {ε δ : ℝ} (hfreeze : ∀ t, μ.weight t ≠ 0 → ‖twist t - c‖ ≤ ε)
    (hbias : δ ≤ ‖μ.complexMean (fun t => star (twist t) * signal t)‖) :
    δ - ε ≤ ‖μ.complexMean signal‖ := by
  have he := μ.norm_complexMean_sub_le
    (fun t => star (twist t) * signal t) (fun t => star c * signal t)
    (fun _ => ε) (fun t ht => by
      rw [← sub_mul, ← star_sub, norm_mul, norm_star]
      exact (mul_le_mul (hfreeze t ht) (hsignal t) (norm_nonneg _) (by
        exact (norm_nonneg _).trans (hfreeze t ht))).trans_eq (mul_one _))
  rw [μ.mean_const] at he
  have hconst : μ.complexMean (fun t => star c * signal t) = star c * μ.complexMean signal := by
    simp only [FiniteProbabilityWeights.complexMean, Finset.mul_sum]
    congr 1
    funext t
    ring
  have hb : ‖μ.complexMean (fun t => star c * signal t)‖ ≤ ‖μ.complexMean signal‖ := by
    rw [hconst, norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
  have ht := norm_le_norm_sub_add
    (μ.complexMean (fun t => star (twist t) * signal t))
    (μ.complexMean (fun t => star c * signal t))
  linarith

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedCanonicalSpatialCoarseSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_allocatedCanonicalSpatial_cutoff (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
      {X : Type*} [Fintype X] {dim : ℕ} (selection : Fin dim ↪ G)
      {P p target Ecap Qstride Etau : ℝ},
      0 ≤ P → p ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P →
      Ecap ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P → Etau ∈ Set.Icc 0 P →
      ((dim + 1 : ℕ) : ℝ) ≤ P →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P →
      (Fintype.card X : ℝ) ≤ P →
      let l := allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau
      normalizedTupleSideLog X (PrincipalTupleIndex B (layerSamplerDegree I n))
        selection p target l ≤ (P + C) ^ C := by
  obtain ⟨a, _, hlate⟩ := exists_allocatedSpatialLateLog_bound m
  let Xpoly : Polynomial ℕ := Polynomial.X
  let latePoly := (Xpoly + Polynomial.C a) ^ a + 3 * Xpoly
  let poly := tupleSideLogEnvelope Xpoly Xpoly latePoly
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ I _ n B _ X _ dim selection P p target Ecap Qstride Etau
    hP hp htarget hEcap hQstride hEtau hdim hvars hX l
  have hl₀ := allocatedSpatialLateLog_nonneg (G := G) B hP hP
  have hl : 0 ≤ l := by dsimp [l]; linarith only [hl₀, hEcap.1, hQstride.1, hEtau.1]
  have hlbound : l ≤ (P + a) ^ a + 3 * P := by
    have hb := hlate B hP hP le_rfl le_rfl hvars
    dsimp only [l]
    linarith only [hb, hEcap.2, hQstride.2, hEtau.2]
  have hG : (Fintype.card G : ℝ) ≤ P := by
    change (Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ P at hvars
    simp only [Fintype.card_sum, Nat.cast_add] at hvars
    linarith only [hvars, Nat.cast_nonneg (α := ℝ)
      (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))]
  have hindices : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ P := by
    change (Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ P at hvars
    simp only [Fintype.card_sum, Nat.cast_add] at hvars
    linarith only [hvars, Nat.cast_nonneg (α := ℝ) (Fintype.card G)]
  have hqdim : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ P := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
      Nat.add_comm 1] using hdim
  have hs := (normalizedTuple_log_envelopes_of_le X
    (PrincipalTupleIndex B (layerSamplerDegree I n)) selection hp.1 htarget.1 hl
    hp.2 hqdim hG hindices hX).2
  apply (hs.trans (tupleSideLogEnvelope_mono hP htarget.1 hl le_rfl htarget.2 hlbound)).trans
  simpa [poly, Xpoly, latePoly, tupleSideLogEnvelope, tupleLateLogEnvelope,
    tupleWidthLogEnvelope, tupleEarlyLogEnvelope, spatialTupleToleranceLog,
    spatialDiscretizationEnvelope, spatialMeshEnvelope, spatialLipschitzCostEnvelope,
    spatialLipschitzEnvelope, spatialDisplacementEnvelope, spatialFixedProfileEnvelope,
    anisotropicSpatialCapLog, coefficientErrorVolumeLog, Polynomial.eval₂_pow] using hbound P hP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uX uJ uO uG uI uB
open BooleanCubeKernel MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (Cproj Vproj : Fin m → ℝ≥0)
variable {dim : ℕ}

local notation "sides" => allocatedPrincipalSides B U b S

variable (X : Type uX) [Fintype X] [DecidableEq X] (modulus : ℕ) (q : X → ℕ)
local notation "refined" => residueRefinedPeriod modulus q
local notation "labels" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod refined)

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) →
  ZMod (residueRefinedPeriod modulus q))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel (residueRefinedPeriod modulus q) y = label₀)))
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
  hH hsubset (residueRefinedPeriod modulus q) label₀ hcell).weight y₀)

variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable [NeZero modulus] {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable (hcanonical : modulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (N : X → ℕ) {τ p target E : ℝ}
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
local notation "O" => (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (Fin.val j + 1) : Type))
local notation "rows" => (fun j => (Subtype.val : O j → Finset (Fin dim)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
variable (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
variable (signal : (X → ℤ) → ℂ) (hsignal : ∀ u, ‖signal u‖ ≤ 1)


variable (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t) (hτ : 0 < τ)
variable [CompactSpace (CoefficientTorus (K := Fin dim) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin dim) U)]
variable [BorelSpace (CoefficientTorus (K := Fin dim) U)]
variable (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)]
variable [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
variable (μcoeff : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μcoeff.IsAddLeftInvariant] [IsProbabilityMeasure μcoeff]

variable {Pproj Pk : ℝ}

local notation "W" => allocatedPhysicalRootBudget B U b S (fun _ => 0)
local notation "C₀" => 1 + (S.value : ℝ) + W
local notation "Centry" => allocatedPhysicalEntryBudget B U b S (fun _ => 0)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeDetectionEmptyTags
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

@[simp] theorem physicalGridFactorInput_of_isEmpty
    {X : Type*} {m : ℕ} {J : Fin m → Type*} [IsEmpty (Σ j, J j)]
    (period : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (t : X → ℝ) :
    physicalGridFactorInput period p t = 0 := by
  funext a
  exact isEmptyElim a

namespace NormalizedPolynomialTwist

variable {X Y : Type*} [Fintype X] [Fintype Y]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def eraseEmptyTags
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] [IsEmpty Y] :
    NormalizedPolynomialTwist X Y' periodCap coverCap L where
  modulus := W.modulus
  modulus_pos := W.modulus_pos
  modulus_bound := W.modulus_bound
  cover := W.cover
  cover_pos := W.cover_pos
  cover_bound := W.cover_bound
  mask := W.mask
  mask_bound := W.mask_bound
  smooth := fun z => W.smooth (z.1, 0)
  smooth_bound := fun z => W.smooth_bound _
  smooth_lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := W.smooth_lipschitz.dist_le_mul (x.1, 0) (y.1, 0)
    simp only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (show dist x.1 y.1 ≤ dist x y from le_max_left _ _) L.coe_nonneg)

variable [IsEmpty Y]

@[simp] theorem eraseEmptyTags_modulus
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] : (W.eraseEmptyTags Y').modulus = W.modulus := rfl

@[simp] theorem eraseEmptyTags_cover
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] : (W.eraseEmptyTags Y').cover = W.cover := rfl

@[simp] theorem eraseEmptyTags_mask
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] : (W.eraseEmptyTags Y').mask = W.mask := rfl

@[simp] theorem eraseEmptyTags_smooth
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (Y' : Type*) [Fintype Y'] (z : (X → ℝ) × (Y' → UnitAddCircle)) :
    (W.eraseEmptyTags Y').smooth z = W.smooth (z.1, 0) := rfl

@[simp] theorem eval_eraseEmptyTags
    {m m' : ℕ} {J : Fin m → Type*} {J' : Fin m' → Type*}
    [∀ j, Fintype (J j)] [∀ j, Fintype (J' j)] [IsEmpty (Σ j, J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (p' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ)) (u : X → ℤ) :
    (W.eraseEmptyTags (Σ j, J' j)).eval N p' u = W.eval N p u := by
  simp only [eval, eraseEmptyTags, physicalGridFactorInput_of_isEmpty]
  rfl

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

end Erdos3.VectorPolynomial

end

end OAI

end


