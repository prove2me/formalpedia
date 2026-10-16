-- Prove2me | Definitions.Def_OAIErdos3B1327
-- name    : OAIErdos3B1327
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T18:12:34.409464+00:00
-- url     : https://prove2.me/theorems/4c936e15-cc54-46b2-a907-fc9aaa754815
-- title:
--   OpenAI Erdős-3 split, definitions bundle 1328 of 1334
-- statement:
--   Definitions bundle 1328 of 1334 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B1326`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 1328 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.AllocatedCenteredRecoveredSampleReadAt`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.sides_continuous`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateSampler.sides_free`, `OAI.Erdos3.VectorPolynomial.AllocatedPhysicalRankReadCertificate`, `OAI.Erdos3.VectorPolynomial.AllocatedPhysicalRankReadCertificate.modulusBad_congr`, `OAI.Erdos3.VectorPolynomial.AllocatedPhysicalRankReadCertificate.primeBad_congr`, `OAI.Erdos3.VectorPolynomial.AllocatedPhysicalRankReadCertificate.primePowerEvent_iff`, `OAI.Erdos3.VectorPolynomial.AllocatedSlicedSourceProjection`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalPrimePowerEvent`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalPrimePowerEvent_center_measurableSet`, `OAI.Erdos3.VectorPolynomial.allocatedPhysicalRankReadCertificate_of_event_read`, `OAI.Erdos3.VectorPolynomial.allocatedReplaceReadNoise`, `OAI.Erdos3.VectorPolynomial.allocatedReplaceReadNoise_chart`, `OAI.Erdos3.VectorPolynomial.allocatedReplaceReadNoise_deck`, `OAI.Erdos3.VectorPolynomial.allocatedReplaceReadNoise_noise`, `OAI.Erdos3.VectorPolynomial.allocatedReplaceReadNoise_projection`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCentered_recovered_sample_read`, `OAI.Erdos3.VectorPolynomial.exists_allocatedCentered_recovered_sample_reads`, `OAI.Erdos3.VectorPolynomial.exists_allocatedPhysical_recovered_sample_read`, `OAI.Erdos3.VectorPolynomial.exists_allocated_canonical_constructed_projection`, `OAI.Erdos3.VectorPolynomial.exists_allocated_sliced_constructed_projection`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointAmbientLog`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointGoodCutoff`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointGoodLog`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointMinimumLog`, `OAI.Erdos3.VectorPolynomial.preparedRelativeEndpointMinimumScale`, `OAI.Erdos3.VectorPolynomial.selectedResidueDensityPMF_certifiedRead_badProduct_congr`, `_private.Lattices.AllocatedCenteredBadPrimeSurrogate.0.OAI.Erdos3.VectorPolynomial.singleton_prime_neZero`, `_private.Lattices.AllocatedCenteredBadPrimeSurrogate.0.OAI.Erdos3.VectorPolynomial.singleton_prime_power_dvd`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B162
import Definitions.Def_OAIErdos3B200
import Definitions.Def_OAIErdos3B1324

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedAnchoredRecoveredSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)

def AllocatedPhysicalRankReadCertificate
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  ∀ (P : Finset ℕ) (hP : ∀ p : P, NeZero p.val), letI := hP
    ∀ (A : ℕ → ℕ) (M : ℕ) (hM : 0 < M), letI : NeZero M := ⟨hM.ne'⟩
      ∀ hdiv : ∀ p : P, p.val ^ A p.val ∣ M,
        coefficientDeckChartEvent U bW b hb o M
          (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
            (fun v => (z v : ZMod M)))
          (affineCoefficientCoverSample U poly hm M (fun k x => (z (k,x) : ℝ))) ↔
        ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f

theorem allocatedPhysicalRankReadCertificate_of_event_read
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hnoise : allocatedReadNoise f = z)
    (hevent : ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
      ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
        coefficientDeckChartEvent U bW b hb o q event
          (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
        event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)))) :
    AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z f := by
  intro P hP
  let := hP
  intro A M hM
  let : NeZero M := ⟨hM.ne'⟩
  intro hdiv
  have he := hevent M hM (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
    (fun v => (z v : ZMod M)))
  apply he.trans
  have hn : allocatedReadNoise (fun i => (f i : ZMod M)) = fun v => (z v : ZMod M) := by
    funext v
    change ((allocatedReadNoise f v : ℤ) : ZMod M) = _
    rw [hnoise]
  rw [← hn]
  exact allocatedChartResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A M hdiv f

theorem AllocatedPhysicalRankReadCertificate.modulusBad_congr
    {z : Option (LayerSamplerVariables G I n B) × X → ℤ}
    {f g : AllocatedActualCoefficientIndex G X I E n B → ℤ}
    (hf : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z f)
    (hg : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z g)
    (p a : ℕ) [NeZero p] :
    allocatedActualModulusBad inactive spatial kernel block C (p ^ a) f ↔
      allocatedActualModulusBad inactive spatial kernel block C (p ^ a) g := by
  let P : Finset ℕ := {p}
  have hP : ∀ q : P, NeZero q.val := by
    intro q
    have hq : q.val = p := Finset.mem_singleton.mp q.property
    rw [hq]
    infer_instance
  let := hP
  have hpa : 0 < p ^ a := pow_pos (Nat.pos_of_ne_zero (NeZero.ne p)) _
  let : NeZero (p ^ a) := ⟨hpa.ne'⟩
  have hdiv : ∀ q : P, q.val ^ (fun _ => a) q.val ∣ p ^ a := by
    intro q
    have hq : q.val = p := Finset.mem_singleton.mp q.property
    simp only [hq, dvd_refl]
  have he := (hf P hP (fun _ => a) (p ^ a) hpa hdiv).symm.trans
    (hg P hP (fun _ => a) (p ^ a) hpa hdiv)
  constructor
  · intro h
    apply (he.mp ?_) ⟨p, Finset.mem_singleton_self p⟩
    intro q
    obtain ⟨q, hq⟩ := q
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    exact h
  · intro h
    apply (he.mpr ?_) ⟨p, Finset.mem_singleton_self p⟩
    intro q
    obtain ⟨q, hq⟩ := q
    have hqp : q = p := Finset.mem_singleton.mp hq
    subst q
    exact h

theorem AllocatedPhysicalRankReadCertificate.primeBad_congr
    {z : Option (LayerSamplerVariables G I n B) × X → ℤ}
    {f g : AllocatedActualCoefficientIndex G X I E n B → ℤ}
    (hf : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z f)
    (hg : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z g)
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (p : P) (a : ℕ) :
    allocatedActualPrimeBad inactive spatial kernel block P C p.val a f ↔
      allocatedActualPrimeBad inactive spatial kernel block P C p.val a g := by
  rw [allocatedActualPrimeBad_iff_modulusBad, allocatedActualPrimeBad_iff_modulusBad]
  exact hf.modulusBad_congr B U bW b hb o poly hm inactive spatial kernel block C hg p.val a

theorem selectedResidueDensityPMF_certifiedRead_badProduct_congr
    (modulus : X → ℕ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X modulus))
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells width z)
    (D : (Option (LayerSamplerVariables G I n B) × X → ℤ) → ℝ) (hD0 : ∀ z, 0 ≤ D z)
    (hD : 0 < selectedResidueDensityMass modulus cells width D)
    (read other : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ z, D z ≠ 0 →
      AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z (read z))
    (hother : ∀ z, D z ≠ 0 →
      AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block C z (other z))
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (threshold : ℕ) :
    (∑' z, (selectedResidueDensityPMF modulus cells width hwidth hZ D hD0 hD z).toReal *
      (if threshold < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (read z)) p z
      then (1 : ℝ) else 0)) =
    ∑' z, (selectedResidueDensityPMF modulus cells width hwidth hZ D hD0 hD z).toReal *
      (if threshold < ∏ p ∈ P, p ^ largestTestedBadDepth A
        (fun p a z => allocatedActualPrimeBad inactive spatial kernel block P C p a (other z)) p z
      then (1 : ℝ) else 0) := by
  apply selectedResidueDensityPMF_badProduct_event_congr
  intro z hz p hp a _ _
  exact (hread z hz).primeBad_congr B U bW b hb o poly hm inactive spatial kernel block C
    (hother z hz) P ⟨p, hp⟩ a

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem exists_allocatedPhysical_recovered_sample_read :
    ∃ (sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ),
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o (sample z) =
          affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection (read z) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) := by
  have hex (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      ∃ (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (f : AllocatedActualCoefficientIndex G X I E n B → ℤ),
        allocatedReadNoise f = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        (canonicalCoefficientSample U b hb o x =
          affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ∧
        (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (x j) ∧
          mixedArraySupported (allocatedLayerCenters B U b S j)
            (allocatedLayerWidths B U b S j)
            (allocatedLayerIntegerPMFs B U b hR hσ S j) (x j)) ∧
        (∀ (j : Fin m) (i : Fin (n j))
          (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
          allocatedReadProjection f ⟨j, Sum.inr i⟩ e = (x j).2 i e) ∧
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)))) := by
    by_cases hz : allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) = 0
    · refine ⟨fun _ => (0, 0),
        allocatedMixedFullArray (Sum.elim z (fun _ => 0)) (fun _ => 0) (fun _ => 0), rfl, ?_⟩
      intro h
      exact (h hz).elim
    · obtain ⟨x, hx, _⟩ := canonicalCoefficientDensity_recover_unique U b hb o
        (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) hz
      have hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2 := by
        intro a
        exact (hx.2 a.1.1).1 a.1.2 a.2
      obtain ⟨f, hfnoise, hfint, hfevent⟩ := exists_allocatedCoefficient_integer_event_read
        U bW b hb o (affineSampleCoefficientArray U poly hm (fun k x => (z (k,x) : ℝ)))
        x hx.1 hsmall z
      exact ⟨x, f, hfnoise, fun _ => ⟨hx.1, hx.2, hfint, hfevent⟩⟩
  choose sample read hread using hex
  exact ⟨sample, read, hread⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

def allocatedReplaceReadNoise
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    AllocatedActualCoefficientIndex G X I E n B → ℤ :=
  Sum.elim z (fun i => read (.inr i))

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_noise
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadNoise (allocatedReplaceReadNoise B z read) = z := rfl

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_deck
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadDeck (allocatedReplaceReadNoise B z read) = allocatedReadDeck read := rfl

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_projection
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) :
    allocatedReadProjection (allocatedReplaceReadNoise B z read) = allocatedReadProjection read := rfl

omit [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in
@[simp] theorem allocatedReplaceReadNoise_chart
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ) (q : ℕ) :
    allocatedReadCoefficientChartResidues
      (fun i => (allocatedReplaceReadNoise B z read i : ZMod q)) =
      allocatedReadCoefficientChartResidues (fun i => (read i : ZMod q)) := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
variable (C : ℝ)

def AllocatedCenteredRecoveredSampleReadAt
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j) (a : X → ℤ)
    (sample : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ) : Prop :=
  ∀ z, allocatedReadNoise (read z) = z ∧
    (allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center a z ≠ 0 →
      (canonicalCoefficientSample U b hb o (sample z) =
        affineSampleCoefficientTorus U (allocatedCenteredConditionalPolynomial U poly c a)
          (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
          (fun k x => (z (k,x) : ℝ))) ∧
      (∀ j, mixedArrayInChart (euclideanSubspace (U j)) (b j) (o j) (sample z j) ∧
        mixedArraySupported (allocatedLayerCenters B U b S j)
          (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j) (sample z j)) ∧
      (∀ d, |coefficientSamplerAmbientPoint U b o (sample z) d| < 1/2) ∧
      (∀ (j : Fin m) (i : Fin (n j))
        (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
        allocatedReadProjection (read z) ⟨j, Sum.inr i⟩ e = (sample z j).2 i e) ∧
      (∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
          coefficientDeckChartEvent U bW b hb o q event
            (affineCoefficientCoverSample U (allocatedCenteredConditionalPolynomial U poly c a)
              (allocatedCenteredConditionalPolynomial_mem U poly hm c a) q
              (fun k x => (z (k,x) : ℝ))) ↔
          event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) ∧
      AllocatedPhysicalRankReadCertificate B U bW b hb o
        (allocatedCenteredConditionalPolynomial U poly c a)
        (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
        inactive spatial kernel block C z (read z))

theorem exists_allocatedCentered_recovered_sample_read
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (c : ∀ j, U j)
    (hc : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1)))) (a : X → ℤ) :
    ∃ sample read, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center c a sample read := by
  obtain ⟨sample, read, hread⟩ := exists_allocatedPhysical_recovered_sample_read B U bW b hb o S hR hσ
    (allocatedCenteredConditionalPolynomial U poly c a)
    (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
  refine ⟨sample, read, ?_⟩
  intro z
  refine ⟨(hread z).1, ?_⟩
  intro hz
  have hdensity := allocatedCenteredConditionalPolynomial_density U poly hm c a B b hb o hR hσ S center hc z
  have hrec := (hread z).2 (hdensity.trans_ne hz)
  refine ⟨hrec.1, hrec.2.1, ?_, hrec.2.2.1, hrec.2.2.2, ?_⟩
  · intro d
    exact (hrec.2.1 d.1.1).1 d.1.2 d.2
  · exact allocatedPhysicalRankReadCertificate_of_event_read B U bW b hb o
      (allocatedCenteredConditionalPolynomial U poly c a)
      (allocatedCenteredConditionalPolynomial_mem U poly hm c a)
      inactive spatial kernel block C z (read z) (hread z).1 hrec.2.2.2

theorem exists_allocatedCentered_recovered_sample_reads
    (c : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ∀ j, U j)
    (hc : ∀ center, coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c center s.1)))) :
    ∃
      (sample : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
        (Option (LayerSamplerVariables G I n B) × X → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : CoefficientTorus (K := LayerSamplerVariables G I n B) U → (X → ℤ) →
        (Option (LayerSamplerVariables G I n B) × X → ℤ) →
          AllocatedActualCoefficientIndex G X I E n B → ℤ),
      ∀ center a, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
        inactive spatial kernel block C center (c center) a (sample center a) (read center a) := by
  choose sample read hread using fun center a =>
    exists_allocatedCentered_recovered_sample_read B U bW b hb o S hR hσ poly hm
      inactive spatial kernel block C center (c center) (hc center) a
  exact ⟨sample, read, hread⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCenteredBadPrimeSurrogate
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable (inactive : LayerSamplerAxis I n → Prop) (rankC : ℝ)

theorem singleton_prime_neZero (p : ℕ) [NeZero p] (r : ({p} : Finset ℕ)) : NeZero r.val := by
  have hr : r.val = p := Finset.mem_singleton.mp r.property
  rw [hr]
  infer_instance

theorem singleton_prime_power_dvd (p a : ℕ) (r : ({p} : Finset ℕ)) : r.val ^ a ∣ p ^ a := by
  have hr : r.val = p := Finset.mem_singleton.mp r.property
  simp only [hr, dvd_refl]

def allocatedPhysicalPrimePowerEvent
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) (p a : ℕ) [NeZero p] : Prop :=
  letI : ∀ r : ({p} : Finset ℕ), NeZero r.val := singleton_prime_neZero p
  coefficientDeckChartEvent U bW b hb o (p ^ a)
    (allocatedChartResiduePrimePowerWitness inactive rankC {p} (fun _ => a) (p ^ a)
      (singleton_prime_power_dvd p a) (fun v => (z v : ZMod (p ^ a))))
    (affineCoefficientCoverSample U poly hm (p ^ a) (fun k x => (z (k,x) : ℝ)))

variable {L : ℕ} (spatial : Fin L ↪ G)
variable (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)

theorem AllocatedPhysicalRankReadCertificate.primePowerEvent_iff
    {z : Option (LayerSamplerVariables G I n B) × X → ℤ}
    {f : AllocatedActualCoefficientIndex G X I E n B → ℤ}
    (hf : AllocatedPhysicalRankReadCertificate B U bW b hb o poly hm inactive spatial kernel block rankC z f)
    (p a : ℕ) [NeZero p] :
    allocatedPhysicalPrimePowerEvent B U bW b hb o poly hm inactive rankC z p a ↔
      allocatedActualModulusBad inactive spatial kernel block rankC (p ^ a) f := by
  have hpa : 0 < p ^ a := pow_pos (NeZero.pos p) a
  have he := hf {p} (singleton_prime_neZero p) (fun _ => a) (p ^ a) hpa
    (singleton_prime_power_dvd p a)
  refine he.trans ?_
  constructor
  · intro h
    exact h ⟨p, Finset.mem_singleton_self p⟩
  · intro h r
    have hr : r.val = p := Finset.mem_singleton.mp r.property
    rcases r with ⟨r, hrmem⟩
    have hrp : r = p := Finset.mem_singleton.mp hrmem
    subst r
    exact h

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem allocatedPhysicalPrimePowerEvent_center_measurableSet
    {T : Type*} [MeasurableSpace T] (c : T → ∀ j, U j) (hc : Measurable c)
    (base : X → ℤ) (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (p a : ℕ) [NeZero p] :
    MeasurableSet {center | allocatedPhysicalPrimePowerEvent B U bW b hb o
      (fun j => translate (fun x => (base x : ℝ)) (subtractConstant (c center j).val (poly j)))
      (fun j => coefficients_translate_mem (U j) (fun x => (base x : ℝ)) _
        (coefficients_subtractConstant_mem (U j) (c center j) (poly j) (hm j)))
      inactive rankC z p a} := by
  unfold allocatedPhysicalPrimePowerEvent
  exact coefficientDeckChartEvent_center_measurableSet U bW b hb o poly hm c hc base z (p ^ a) _

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedRelativeEndpointSourceBounds
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

@[simp] theorem sides_free (g : G) : A.sides (.inl g) = S.value := rfl

@[simp] theorem sides_continuous (j : Fin m) (i : I j)
    (a : B ⟨j, .inl i⟩) (r : Fin (j.val + 1)) :
    A.sides (.inr ⟨⟨j, .inl i⟩, a, r⟩) = S.value := rfl

end AllocatedExternalCandidateSampler
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (sampler : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedRelativeEndpointMinimumScale
    (seed periodLog childLog cost comparisonLog : ℝ) : ℕ :=
  max ⌈Real.exp seed⌉₊
    (preparedSlicedForecastCommonFloor periodLog childLog cost comparisonLog)

noncomputable def preparedRelativeEndpointMinimumLog
    (seed periodLog childLog cost comparisonLog : ℝ) : ℝ :=
  max (seed + 1)
    (preparedSlicedForecastCommonFloorExponent periodLog childLog cost comparisonLog + 1)

noncomputable def preparedRelativeEndpointGoodCutoff (Ptest : ℝ) : ℕ :=
  ⌈Real.exp (2 * Ptest)⌉₊

def preparedRelativeEndpointGoodLog (Ptest : ℝ) : ℝ := 2 * Ptest + 1

def preparedRelativeEndpointAmbientLog (modelRequired nativeAmbient gridAmbient : ℝ) : ℝ :=
  max modelRequired (max nativeAmbient gridAmbient)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedCanonicalSlicedConstructedProjection
namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal
universe uX

def AllocatedSlicedSourceProjection {m q : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (d : ℕ)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S) →
      EuclideanJetLayers U (fun j => {t : Finset (Fin q) // t ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}) → ℝ)
    (Asample : ℕ) (P : ℝ) : Prop :=
    ∀ {W : ℝ}, 1 ≤ P → ∀ (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hWP : W ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (_hsize : ∀ d, Real.exp ((P + Asample) ^ Asample) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + Asample) ^ Asample) ≤ rank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty),
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let Z := selectedJointDensityMass bases stride T widths
      (allocatedJointBaseDensity B U b hb o hR hσ S X p hm)
    ∃ hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z,
      (|Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) ∧
      ∀ (law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S))) (signal : (X → ℤ) → ℂ),
      (∀ v, ‖signal v‖ ≤ 1) → ∀ {κ : ℝ},
      κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X p hm
        N hN _hW _hτ _hξ stride T hmass bases x y signal)).re →
      ∃ base ∈ bases,
        let projected := fun y => ∑' z,
          ((selectedResidueSmoothPMF stride T widths
            (narrowTrimmedSpatialWidths_pos _hW _hτ _hξ N hN) hmass z).toReal : ℂ) *
            (physicalCubeSiteTest (integerSelfSiteTest q signal) (physicalCubeRootDifferences
              (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
              (allocatedPhysicalCubeDirections B U b S x y) base z) *
            (g y (physicalCubeRowSample U d (fun j =>
              (Subtype.val : {t : Finset (Fin q) // t ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} → Finset (Fin q))) p hm
              (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
                (allocatedPhysicalCubeDirections B U b S x y) base z)) : ℂ))
        κ - Real.exp (-P) ≤ (law.complexMean projected / (Z : ℂ)).re

theorem exists_allocated_sliced_constructed_projection (m q : ℕ) :
    ∃ A Asample : ℕ, 2 ≤ A ∧ 2 ≤ Asample ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M),
    ∀ (period : ℕ), 0 < period → (period : ℝ) ≤ Real.exp P →
    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection.{_, _, uX, 0} U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      (∀ y, ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
        LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
        (∀ z, ‖F z‖ ≤ cap) ∧
        ∀ z, (g y z : ℂ) = F (coveredJetAmbientTorus U 1 z)) ∧
      (∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
      AllocatedSlicedSourceProjection.{uX} B U b S x hb o hR hσ C V d g Asample P := by
  obtain ⟨A, hA, hcover⟩ := exists_allocated_rows_ambient_projected_family_multiple m q
  obtain ⟨An, hAn, hnorm⟩ := exists_allocated_narrow_normalization m
  obtain ⟨Ap, hAp, hprojectSource⟩ := exists_allocated_sliced_rows_projected_source.{uX} m q
  refine ⟨A, max An Ap, hA, hAn.trans (le_max_left _ _), ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ S x P hP hG hL M hperiod period hp hpP
  obtain ⟨d, hdiv, hd, hdb, hconstruct⟩ := hcover B U b S (fun _ => 0) x hP hG
    (fun _ => by simpa using Real.exp_nonneg P) hL hperiod period hp hpP
  refine ⟨d, hdiv, hd, hdb, ?_⟩
  intro _ _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    _ _ _ μrows _ _ density cap cover ξhaar densityLip sectionLip reconstructionLip Row Tuple
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hambient, hmean⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν μrows
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hambient, hmean, ?_⟩
  unfold AllocatedSlicedSourceProjection
  intro W hPone hmSize hK hW hroot hWP hRP hσP hcount hI hn hJ hAP hCP hVP
    X _ _ hX hdim p hpoly hm stride hs hsP τ ξ hτ hτP hξ hξ1 hξP N hN hsize
    rank hrank hRank T hT bases hbases widths Z
  have hnCut := Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega : 1 ≤ An)
    (le_max_left An Ap))
  have hpCut := Real.exp_le_exp.mpr (shifted_power_self_mono hP (by omega : 1 ≤ Ap)
    (le_max_right An Ap))
  obtain ⟨hwidths, hmass, _, hglobal⟩ := hnorm B U b S hb o μ ν hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall hP hmSize hK hX hdim hRP hσP hcount hI hn hJ hAP hL hCP hVP
    p hpoly hm stride hs hsP hW hWP hτ hτP hξ hξ1 hξP N (fun i => hnCut.trans (hsize i))
    hrank (hnCut.trans hRank) T hT
  have hnormal := hglobal bases hbases
  change |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
    0 < Z ∧ Z⁻¹ ≤ 2 at hnormal
  refine ⟨hmass, hnormal, ?_⟩
  intro law signal hsignal κ hsource
  have hZi : Z⁻¹ ≤ Real.exp P := hnormal.2.2.2.trans
    (by linarith [Real.add_one_le_exp P])
  exact hprojectSource B U b S x hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall
    hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ hAP hCP hVP hperiod hX hdim
    p hpoly hm stride hs hsP hτ hτP hξ hξ1 hξP N hN (fun i => hpCut.trans (hsize i))
    hrank (hpCut.trans hRank) signal hsignal T hT bases hbases d g hprojection hwidths hmass law
    hnormal.2.2.1 hZi hsource

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal
universe uX

theorem exists_allocated_canonical_constructed_projection (m q : ℕ) :
    ∃ A Asample : ℕ, 2 ≤ A ∧ 2 ≤ Asample ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (selection : Fin q ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    {Pk : ℝ} (_hMk : (M : ℝ) ≤ Real.exp Pk) (_hPk : ((m + 1 : ℕ) : ℝ) * Pk ≤ P),
    let period := kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m)

    ∃ d : ℕ, period ∣ d ∧ 0 < d ∧ (d : ℝ) ≤ Real.exp ((P + (q + 2 : ℕ) + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)]
    [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μrows : Measure (CoefficientTorus (K := Fin q) U))
    [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows],
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} => ν j))
    let densityLip := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
      allocatedAmbientFactorCap (G := G) B R σ S.value V ^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let sectionLip := (Fintype.card (Finset (Fin q)) : ℝ≥0) *
      Real.toNNReal (Real.exp ((P + (q + 2 : ℕ) + A) ^ A))
    let reconstructionLip := ∑ j : Fin m, (Fintype.card (BoundedBooleanJet (Fin q) (j.val + 1)) : ℝ≥0)
    let Row := fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}
    let Tuple := PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U b S)
    ∃ g : Tuple → EuclideanJetLayers U Row → ℝ,
      (∀ y, Continuous (g y)) ∧
      (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧
      (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : Row j → Finset (Fin q)))) = realDensityMeasure ξ (g y)) ∧
      (∀ y, physicalDensityProjection.{_, _, uX, 0} U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
        (allocatedPhysicalCubeDirections B U b S x y) d density
        (fun z => g y ((physicalRowsStandardEquiv U).symm z))) ∧
      (∀ y, ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
        LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
        (∀ z, ‖F z‖ ≤ cap) ∧
        ∀ z, (g y z : ℂ) = F (coveredJetAmbientTorus U 1 z)) ∧
      (∀ law : FiniteProbabilityWeights Tuple,
        ∃ F : (JetAmbientIndex Row J → UnitAddCircle) → ℂ,
          LipschitzWith (densityLip * sectionLip * reconstructionLip) F ∧
          (∀ z, ‖F z‖ ≤ cap) ∧
          ∀ z, law.complexMean (fun y => (g y z : ℂ)) = F (coveredJetAmbientTorus U 1 z)) ∧
      AllocatedSlicedSourceProjection.{uX} B U b S x hb o hR hσ C V d g Asample P := by
  obtain ⟨A, Asample, hA, hAsample, hconstruct⟩ := exists_allocated_sliced_constructed_projection.{uX} m q
  refine ⟨A, Asample, hA, hAsample, ?_⟩
  intro G _ _ I _ n B _ J _ U b R σ S x P hP hG hL M selection hx Pk hMk hPk period
  exact hconstruct B U b S x hP hG hL hx.2 period (kernelPeriodCandidate_pos _ _)
    ((kernelPeriodCandidate_le_exp hMk _ _).trans (Real.exp_le_exp.mpr hPk))

end Erdos3.VectorPolynomial

end

end OAI

end


