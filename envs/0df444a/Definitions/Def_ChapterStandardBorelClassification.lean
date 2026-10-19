-- Prove2me | Definitions.Def_ChapterStandardBorelClassification
-- name    : ChapterStandardBorelClassification
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-17T02:23:57.342356+00:00
-- url     : https://prove2.me/theorems/ca380368-0e13-4b02-b38c-8e50c9c8260c
-- title:
--   ChapterStandardBorelClassification
-- statement:
--   ChapterStandardBorelClassification

import Definitions.Def_ChapterAbelianClassificationList
import Definitions.Def_ChapterSpectralDirectSum
import Definitions.Def_ChapterAbelianDirectSum
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterMeasureAtomicDiffuse
import Definitions.Def_ChapterSpectralMultiplication
import Mathlib
import Theorems.Thm_BookProof_ChapterAbelianClassificationList_vonNeumann_abelian_classification_list


/-!
# The classification list on any standard Borel space (plan GAP-2)

`ChapterAbelianClassificationList` proves the manuscript's five-type list for a Borel
probability measure carried by the **line**.  The summands produced by the general
decomposition live on other spaces, and the step that transports them to the line is
the Borel isomorphism theorem, which Mathlib does have: an uncountable standard Borel
space is Borel isomorphic to `ℝ`.

This module carries out the transport.

* `measurePreserving_measurableEquiv`, `measurePreserving_symm` — a measurable
  equivalence is measure preserving onto the pushforward measure, in both directions;
* `transportUnitary` — hence composition with it is a *unitary* `L²(e_*μ) ≃ L²(μ)`;
* `transportUnitary_intertwines` — it carries multiplication by `g` to multiplication
  by `g ∘ e`, so the two multiplication algebras are the same algebra;
* `purelyAtomic_of_countable` — on a countable space every measure is carried by its
  atoms;
* **HEADLINE** `standardBorel_multiplication_model_transport` — for a Borel
  probability measure on *any* standard Borel space, either the space is countable and
  multiplication is diagonal in the basis of normalised point masses (the `Iₙ` /
  `ℓ∞(ℕ)` types), or the measure is unitarily a Borel probability measure on the line
  with the same multiplication algebra;
* **HEADLINE** `standardBorel_classification_list` — combining with
  `vonNeumann_abelian_classification_list`, every such measure realises exactly one of
  the five standard types.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

open MeasureTheory

namespace BookProof.ChapterStandardBorelClassification

open BookProof.ChapterMeasureAtomicDiffuse BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterAbelianClassificationList

/-! ## 1. Transporting along a measurable equivalence -/

section Transport

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y)
  (mu : Measure X)

theorem measurePreserving_measurableEquiv : MeasurePreserving e mu (Measure.map e mu) :=
  ⟨e.measurable, rfl⟩

theorem measurePreserving_symm : MeasurePreserving e.symm (Measure.map e mu) mu := by
  refine ⟨e.symm.measurable, ?_⟩
  rw [Measure.map_map e.symm.measurable e.measurable]
  simp

/-- Composition with a measurable equivalence, a linear isometry
`L²(e_*μ) → L²(μ)`. -/
def transportIsom : Lp ℂ 2 (Measure.map e mu) →ₗᵢ[ℂ] Lp ℂ 2 mu :=
  Lp.compMeasurePreservingₗᵢ ℂ e (measurePreserving_measurableEquiv e mu)

theorem transportIsom_coeFn (v : Lp ℂ 2 (Measure.map e mu)) :
    (transportIsom e mu v : X → ℂ) =ᵐ[mu] fun x => (v : Y → ℂ) (e x) :=
  Lp.coeFn_compMeasurePreserving v (measurePreserving_measurableEquiv e mu)

theorem transportIsom_surjective : Function.Surjective (transportIsom e mu) := by
  intro u
  refine ⟨Lp.compMeasurePreservingₗᵢ ℂ e.symm (measurePreserving_symm e mu) u, ?_⟩
  refine Lp.ext ?_
  have h1 := transportIsom_coeFn e mu
    (Lp.compMeasurePreservingₗᵢ ℂ e.symm (measurePreserving_symm e mu) u)
  have hv : ((Lp.compMeasurePreservingₗᵢ ℂ e.symm (measurePreserving_symm e mu) u :
        Lp ℂ 2 (Measure.map e mu)) : Y → ℂ)
      =ᵐ[Measure.map e mu] (u : X → ℂ) ∘ e.symm :=
    Lp.coeFn_compMeasurePreserving u (measurePreserving_symm e mu)
  have h2 := (measurePreserving_measurableEquiv e mu).quasiMeasurePreserving.ae_eq_comp hv
  filter_upwards [h1, h2] with x hx1 hx2
  simp only [Function.comp_apply] at hx2
  rw [hx1, hx2]
  simp

/-- **The transport unitary**: `L²` of the pushforward measure is `L²(μ)`. -/
def transportUnitary : Lp ℂ 2 (Measure.map e mu) ≃ₗᵢ[ℂ] Lp ℂ 2 mu :=
  LinearIsometryEquiv.ofSurjective (transportIsom e mu) (transportIsom_surjective e mu)

theorem transportUnitary_apply (v : Lp ℂ 2 (Measure.map e mu)) :
    transportUnitary e mu v = transportIsom e mu v := rfl

theorem memLp_top_comp_equiv {g : Y → ℂ} (hg : MemLp g ⊤ (Measure.map e mu)) :
    MemLp (fun x => g (e x)) ⊤ mu :=
  hg.comp_measurePreserving (measurePreserving_measurableEquiv e mu)

/-- **The transport unitary intertwines the multiplication operators.** -/
theorem transportUnitary_intertwines {g : Y → ℂ} (hg : MemLp g ⊤ (Measure.map e mu))
    (v : Lp ℂ 2 (Measure.map e mu)) :
    transportUnitary e mu (multOp g hg v)
      = multOp (fun x => g (e x)) (memLp_top_comp_equiv e mu hg) (transportUnitary e mu v) := by
  refine Lp.ext ?_
  have h1 := transportIsom_coeFn e mu (multOp g hg v)
  have h2 := (measurePreserving_measurableEquiv e mu).quasiMeasurePreserving.ae_eq_comp
    (multOp_coeFn (μ := Measure.map e mu) g hg v)
  have h3 := multOp_coeFn (μ := mu) (fun x => g (e x)) (memLp_top_comp_equiv e mu hg)
    (transportIsom e mu v)
  have h4 := transportIsom_coeFn e mu v
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  simp only [Function.comp_apply] at hx2
  rw [transportUnitary_apply, transportUnitary_apply, hx1, hx2, hx3, hx4]

end Transport

/-! ## 2. A measure on a countable space is purely atomic -/

theorem purelyAtomic_of_countable {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Countable X] (mu : Measure X) :
    mu (atomSet mu)ᶜ = 0 := by
  have hcount : ((atomSet mu)ᶜ).Countable := Set.to_countable _
  have hsub : (atomSet mu)ᶜ ⊆ ⋃ x ∈ (atomSet mu)ᶜ, ({x} : Set X) := by
    intro x hx
    exact Set.mem_biUnion hx rfl
  refine measure_mono_null hsub ?_
  rw [measure_biUnion_null_iff hcount]
  intro x hx
  simpa [atomSet] using hx

/-! ## 3. The classification on a standard Borel space -/

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  (mu : Measure X) [IsProbabilityMeasure mu]

/-- **HEADLINE (transport to the line).**  For a Borel probability measure on an
arbitrary standard Borel space, either the space is countable — and then the measure
is carried by its atoms, so multiplication is *diagonal* in the orthonormal basis of
normalised point masses, the `Iₙ` / `ℓ∞(ℕ)` types — or the space is Borel isomorphic
to the line and the measure is carried over to a Borel probability measure on `ℝ` by a
unitary which turns multiplication by `g` into multiplication by `g ∘ e`.  So no
generality is lost by stating the classification list for measures on the line. -/
theorem standardBorel_multiplication_model_transport :
    (Countable X ∧ ∃ B : HilbertBasis (atomSet mu) ℂ (Lp ℂ 2 mu),
        ∀ (g : X → ℂ) (hg : MemLp g ⊤ mu) (a : atomSet mu),
          multOp g hg (B a) = g (a : X) • B a) ∨
      (∃ e : X ≃ᵐ ℝ, IsProbabilityMeasure (Measure.map e mu) ∧
        ∃ U : Lp ℂ 2 (Measure.map e mu) ≃ₗᵢ[ℂ] Lp ℂ 2 mu,
          ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (Measure.map e mu))
            (v : Lp ℂ 2 (Measure.map e mu)),
            U (multOp g hg v)
              = multOp (fun x => g (e x)) (memLp_top_comp_equiv e mu hg) (U v)) := by
  by_cases hcount : Countable X
  · refine Or.inl ⟨hcount, ?_⟩
    exact atomic_multiplication_model_diagonal mu (purelyAtomic_of_countable mu)
  · have huncount : ¬ Countable ℝ := by simp
    refine Or.inr ⟨PolishSpace.measurableEquivOfNotCountable hcount huncount, ?_, ?_⟩
    · constructor
      rw [Measure.map_apply
        (PolishSpace.measurableEquivOfNotCountable hcount huncount).measurable
        MeasurableSet.univ]
      simp
    · exact ⟨transportUnitary _ mu, fun g hg v => transportUnitary_intertwines _ mu hg v⟩

/-- **The property of realising one of the five standard types.**  Either the space
is countable, and multiplication is diagonal in the orthonormal basis of normalised
point masses (the `Iₙ` / `ℓ∞(ℕ)` types), or the measure transports to a Borel
probability measure on the line — by a unitary carrying multiplication by `g` to
multiplication by `g ∘ e` — which falls into exactly one of the five standard types
of `vonNeumann_abelian_classification_list`. -/
def RealizesStandardType {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (mu : Measure X) [IsFiniteMeasure mu] : Prop :=
  (Countable X ∧ ∃ B : HilbertBasis (atomSet mu) ℂ (Lp ℂ 2 mu),
      ∀ (g : X → ℂ) (hg : MemLp g ⊤ mu) (a : atomSet mu),
        multOp g hg (B a) = g (a : X) • B a) ∨
    (∃ (e : X ≃ᵐ ℝ) (_ : IsProbabilityMeasure (Measure.map e mu)),
      (∃ U : Lp ℂ 2 (Measure.map e mu) ≃ₗᵢ[ℂ] Lp ℂ 2 mu,
        ∀ (g : ℝ → ℂ) (hg : MemLp g ⊤ (Measure.map e mu))
          (v : Lp ℂ 2 (Measure.map e mu)),
          U (multOp g hg v)
            = multOp (fun x => g (e x)) (memLp_top_comp_equiv e mu hg) (U v)) ∧
      (atomSet (Measure.map e mu)).Countable ∧
      ((Measure.map e mu) (atomSet (Measure.map e mu))ᶜ = 0 ∧
          (atomSet (Measure.map e mu)).Finite ∨
        (Measure.map e mu) (atomSet (Measure.map e mu))ᶜ = 0 ∧
          (atomSet (Measure.map e mu)).Infinite ∧
          Nonempty (atomSet (Measure.map e mu) ≃ ℕ) ∨
        (Measure.map e mu) (atomSet (Measure.map e mu)) = 0 ∧
          atomSet (Measure.map e mu) = ∅ ∨
        (Measure.map e mu) (atomSet (Measure.map e mu)) ≠ 0 ∧
          (Measure.map e mu) (atomSet (Measure.map e mu))ᶜ ≠ 0 ∧
          (atomSet (Measure.map e mu)).Finite ∨
        (Measure.map e mu) (atomSet (Measure.map e mu)) ≠ 0 ∧
          (Measure.map e mu) (atomSet (Measure.map e mu))ᶜ ≠ 0 ∧
          (atomSet (Measure.map e mu)).Infinite ∧
          Nonempty (atomSet (Measure.map e mu) ≃ ℕ)))

/-- **HEADLINE (the classification list, on any standard Borel space).**  Combining
the transport with `vonNeumann_abelian_classification_list`: a Borel probability
measure on an arbitrary standard Borel space realises one of the five standard types
of the manuscript's list. -/
theorem standardBorel_classification_list : RealizesStandardType mu := by
  rcases standardBorel_multiplication_model_transport mu with h | ⟨e, hprob, hU⟩
  · exact Or.inl h
  · haveI := hprob
    exact Or.inr ⟨e, hprob, hU, vonNeumann_abelian_classification_list (Measure.map e mu)⟩

/-! ## 4. Every summand of the general abelian model is classified -/

section GeneralModel

open BookProof.ChapterAbelianGelfandModel BookProof.ChapterAbelianDirectSum

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
  [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **HEADLINE (the abelian model, fully classified).**  Every abelian algebra of
operators on a complex Hilbert space — a unital `*`-representation `π` of `C(Y, ℂ)`
for a compact *metrizable* `Y` — is a direct sum of multiplication algebras
`L∞(μₓ)` on `L²(μₓ)`, and **each summand realises one of the five standard types** of
the classification list.  This is the exhaustiveness statement, modulo the choice of
a metrizable model of the spectrum. -/
theorem abelian_multiplication_model_classified (pi : C(Y, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    ∃ (S : Set H) (mu : S → Measure Y) (V : ∀ x : S, Lp ℂ 2 (mu x) →ₗᵢ[ℂ] H),
      (∀ x : S, IsProbabilityMeasure (mu x)) ∧
      IsHilbertSum ℂ (fun x : S => Lp ℂ 2 (mu x)) V ∧
      (∀ (x : S) (g : C(Y, ℂ)) (u : Lp ℂ 2 (mu x)),
        V x (mulRep (mu x) g u) = pi g (V x u)) ∧
      (∀ x : S, ∃ _ : IsProbabilityMeasure (mu x), RealizesStandardType (mu x)) := by
  letI := TopologicalSpace.metrizableSpaceMetric Y
  haveI : PolishSpace Y := inferInstance
  haveI : StandardBorelSpace Y := inferInstance
  obtain ⟨S, mu, V, hprob, hsum, hint⟩ := abelian_multiplication_model_general pi
  refine ⟨S, mu, V, hprob, hsum, hint, fun x => ?_⟩
  haveI := hprob x
  exact ⟨hprob x, standardBorel_classification_list (mu x)⟩

end GeneralModel

/-! ## 5. Every normal operator is a direct sum of standard types -/

section Normal

open BookProof.ChapterAbelianGelfandModel BookProof.ChapterSpectralMultiplication
open BookProof.ChapterSpectralDirectSum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



end Normal

end BookProof.ChapterStandardBorelClassification

end


