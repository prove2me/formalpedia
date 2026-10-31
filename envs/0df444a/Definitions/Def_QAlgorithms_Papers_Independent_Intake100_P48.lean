-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P48
-- name    : QAlgorithms_Papers_Independent_Intake100_P48
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:22:52.187741+00:00
-- url     : https://prove2.me/theorems/4047ba28-8184-4248-bb96-529e4f6abd0b
-- title:
--   Definitions for Topological entanglement entropy
-- statement:
--   The objects the formalized statements of *Topological entanglement entropy* (arXiv:hep-th/0510092) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tripartite`: PDF p.2, (5): seven-region inclusion-exclusion, with A,B,C numbered 0,1,2.
--   - `diskWedge`: PDF p.2, Fig.1(a): three closed wedges of one planar disk of radius t. A and B are the upper quadrants; C is the lower semicircle. Intersections are common interfaces; boundary points do not contribute length twice to a union.
--   - `regionUnion`: PDF pp.2,4: union of the selected actual planar pieces. The empty union is empty.
--   - `boundaryLength`: PDF pp.1–2: boundary length is one-dimensional Hausdorff measure, in the Euclidean metric on the plane. The geometric statements establish finiteness before this real-valued length is used; toReal at infinity is otherwise 0.
--   - `boundaryCount`: PDF p.4: actual number of connected components of the boundary. Nat.card is 0 on an infinite type; the geometric conclusions establish finiteness.
--   - `SpatialState`: PDF p.1: a finite spatial regulator of a normalized pure ground state. Only purity and normalization are needed for the conditional inference. A mass gap or a microscopic area law is not asserted or inferred from this interface.
--   - `RegionBasis`: PDF pp.1–2: tensor factor selected by membership of each regulated site in R.
--   - `ExteriorBasis`: PDF pp.1–2: complementary tensor factor at the same regulator.
--   - `joinConfiguration`: PDF p.1: assemble an interior and exterior configuration into one global one.
--   - `spatialMarginal`: PDF pp.1–2: actual partial trace of the normalized global pure state. Every region uses the same state and the same placement of tensor factors.
--   - `spatialEntropy`: PDF p.2: entropy of the actual regulated region marginal, in nats.
--   - `scaledRectangle`: PDF p.4, Fig.3: closed rectangles [a,b]×[c,d] at common scale t.
--   - `figureThreePiece`: PDF p.4, Fig.3: A and C are side bars, B is two disjoint caps; the unselected central square belongs to the exterior. ABC is a square annulus.
--   - `effectiveEntropy`: PDF p.4: the explicitly conditional effective entropy, one -gamma per boundary component, with a common coefficient of actual boundary length.
--   - `FusionData`: PDF pp.1,3: the finite commutative rigid fusion algebra and its positive dimension character. N a b c counts the outgoing c-channel, not vacuum multiplicity Nabc. These are structural charge data, with no entropy axiom.
--   - `totalDimension`: PDF p.1, (3): total quantum dimension of finitely many sectors. Physical uses have a vacuum sector, so the sector type is nonempty.
--   - `vacuumCycle`: PDF p.3, (9): canonical positive vacuum row of the modular S matrix, viewed as the effective vacuum state in the complementary charge basis.
--   - `punctureProbability`: PDF p.3, (9): Born probability for the constructed vacuum-cycle vector.
--   - `PairFusionBasis`: PDF p.3, (10): basis of the full a tensor b fusion space, with outgoing charge.
--   - `TripleFusionBasis`: PDF p.3, (13): a tensor b tensor c basis with its internal channel and both fusion multiplicity labels.
--   - `chargeProjector`: PDF p.3, (10),(13): a charge projector in a specified fusion basis.
--   - `quantumTrace`: PDF p.3: quantum trace assigns each simple outgoing sector its dimension. An ordinary trace would omit the d_c factor in (10).
--   - `fusionProbability`: PDF p.3, (10): normalized quantum trace of the outgoing-charge projector. The dimension character gives positive denominator d_a d_b, as a conclusion.
--   - `tripleFusionProbability`: PDF p.3, (13): the three-input fusion experiment, including internal channels.
--   - `vacuumMultiplicityThree`: PDF p.3, (10)–(12): vacuum multiplicity, retaining the conjugate of c.
--   - `vacuumMultiplicityFour`: PDF p.3, (13): vacuum multiplicity composed through the internal x-channel.
--   - `jointThree`: PDF p.3, (11): independent a,b puncture draws followed by fusion to bar(c).
--   - `jointFour`: PDF p.3, (13): independent a,b,c draws followed by fusion to bar(d).
--   - `ThreeBasis`: PDF p.3, (12): distinguishable vacuum fusion states of a three-punctured sphere. Zero multiplicities provide no basis labels.
--   - `FourBasis`: PDF p.3, (14): distinguishable four-puncture vacuum fusion states; the internal channel and both multiplicity labels are retained.
--   - `threeDensity`: PDF p.3, (11)–(12): canonical effective density, diagonal in the fusion basis. Every distinguishable state with external labels a,b,c has weight d_a d_b d_c/D^4. Normalization and the entropy formula are conclusions, never hypotheses.
--   - `fourDensity`: PDF p.3, (13)–(14): canonical effective four-puncture density with weight d_a d_b d_c d_d/D^6 per distinguishable fusion basis state.
--   - `meanLogDimension`: PDF p.3: mean log quantum dimension in the puncture charge law.
--   - `vacuumOnly`: Vacuum-only structural example: no sectors or probabilities are supplied by an axiom.
-- source:
--   Topological entanglement entropy, arXiv:hep-th/0510092v2, https://arxiv.org/abs/hep-th/0510092v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
Kitaev and Preskill, arXiv:hep-th/0510092v2, PDF pp.1–4.
Only the conditional geometric calculations and the finite effective charge
calculation are stated here. No identification with an unspecified microscopic
phase, adiabatic wormhole construction, or heuristic CFT limit is assumed.
All paper-local definitions have complete bodies; entropies are in nats.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P48

open Filter
open scoped Topology ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF p.2, (5): seven-region inclusion-exclusion, with A,B,C numbered 0,1,2. -/
def tripartite (s : Finset (Fin 3) → ℝ) : ℝ :=
  s {0} + s {1} + s {2} - s {0, 1} - s {1, 2} - s {0, 2} + s {0, 1, 2}

/-- PDF p.2, Fig.1(a): three closed wedges of one planar disk of radius t.
A and B are the upper quadrants; C is the lower semicircle. Intersections
are common interfaces; boundary points do not contribute length twice to a union. -/
def diskWedge (t : ℝ) (i : Fin 3) : Set ℂ :=
  {z | ‖z‖ ≤ t ∧ if i = 0 then 0 ≤ z.im ∧ 0 ≤ z.re
    else if i = 1 then 0 ≤ z.im ∧ z.re ≤ 0 else z.im ≤ 0}

/-- PDF pp.2,4: union of the selected actual planar pieces. The empty union is empty. -/
def regionUnion (pieces : Fin 3 → Set ℂ) (u : Finset (Fin 3)) : Set ℂ :=
  ⋃ i ∈ u, pieces i

/-- PDF pp.1–2: boundary length is one-dimensional Hausdorff measure, in the
Euclidean metric on the plane. The geometric statements establish finiteness
before this real-valued length is used; toReal at infinity is otherwise 0. -/
def boundaryLength (r : Set ℂ) : ℝ :=
  (MeasureTheory.Measure.hausdorffMeasure 1 (frontier r)).toReal

/-- PDF p.4: actual number of connected components of the boundary.
Nat.card is 0 on an infinite type; the geometric conclusions establish finiteness. -/
def boundaryCount (r : Set ℂ) : ℕ := Nat.card (ConnectedComponents (frontier r))

/-- PDF p.1: a finite spatial regulator of a normalized pure ground state.
Only purity and normalization are needed for the conditional inference. A mass
gap or a microscopic area law is not asserted or inferred from this interface. -/
structure SpatialState where
  sites : ℕ
  localDim : ℕ
  localDim_pos : 0 < localDim
  location : Fin sites → ℂ
  amplitude : (Fin sites → Fin localDim) → ℂ
  normalized : ∑ x, Complex.normSq (amplitude x) = 1

/-- PDF pp.1–2: tensor factor selected by membership of each regulated site in R. -/
abbrev RegionBasis (s : SpatialState) (r : Set ℂ) :=
  {i : Fin s.sites // s.location i ∈ r} → Fin s.localDim

/-- PDF pp.1–2: complementary tensor factor at the same regulator. -/
abbrev ExteriorBasis (s : SpatialState) (r : Set ℂ) :=
  {i : Fin s.sites // s.location i ∉ r} → Fin s.localDim

/-- PDF p.1: assemble an interior and exterior configuration into one global one. -/
def joinConfiguration (s : SpatialState) (r : Set ℂ)
    (x : RegionBasis s r) (y : ExteriorBasis s r) (i : Fin s.sites) :
    Fin s.localDim :=
  if h : s.location i ∈ r then x ⟨i, h⟩ else y ⟨i, h⟩

/-- PDF pp.1–2: actual partial trace of the normalized global pure state.
Every region uses the same state and the same placement of tensor factors. -/
def spatialMarginal (s : SpatialState) (r : Set ℂ) :
    Matrix (RegionBasis s r) (RegionBasis s r) ℂ :=
  fun x y => ∑ e : ExteriorBasis s r,
    s.amplitude (joinConfiguration s r x e) *
      conj (s.amplitude (joinConfiguration s r y e))

/-- PDF p.2: entropy of the actual regulated region marginal, in nats. -/
def spatialEntropy (s : SpatialState) (r : Set ℂ) : ℝ :=
  (Real.log 2 * QAlgorithms.vnEntropy (spatialMarginal s r))

/-- PDF p.4, Fig.3: closed rectangles [a,b]×[c,d] at common scale t. -/
def scaledRectangle (t a b c d : ℝ) : Set ℂ :=
  {z | t * a ≤ z.re ∧ z.re ≤ t * b ∧ t * c ≤ z.im ∧ z.im ≤ t * d}

/-- PDF p.4, Fig.3: A and C are side bars, B is two disjoint caps; the
unselected central square belongs to the exterior. ABC is a square annulus. -/
def figureThreePiece (t : ℝ) (i : Fin 3) : Set ℂ :=
  if i = 0 then scaledRectangle t 0 1 0 3
  else if i = 1 then scaledRectangle t 1 2 0 1 ∪ scaledRectangle t 1 2 2 3
  else scaledRectangle t 2 3 0 3

/-- PDF p.4: the explicitly conditional effective entropy, one -gamma per
boundary component, with a common coefficient of actual boundary length. -/
def effectiveEntropy (alpha gamma : ℝ) (r : Set ℂ) : ℝ :=
  alpha * boundaryLength r - gamma * boundaryCount r

example (pieces : Fin 3 → Set ℂ) : regionUnion pieces ∅ = ∅ := by
  simp [regionUnion]

example (s : SpatialState) (r : Set ℂ) (x : RegionBasis s r)
    (e : ExteriorBasis s r) (i : Fin s.sites) (h : s.location i ∈ r) :
    joinConfiguration s r x e i = x ⟨i, h⟩ := by
  simp [joinConfiguration, h]

example (alpha gamma : ℝ) : effectiveEntropy alpha gamma ∅ = 0 := by
  haveI : IsEmpty (ConnectedComponents (∅ : Set ℂ)) :=
    ConnectedComponents.isEmpty_iff_isEmpty.mpr (by infer_instance)
  have hcount : boundaryCount (∅ : Set ℂ) = 0 := by
    unfold boundaryCount
    rw [frontier_empty]
    exact Nat.card_of_isEmpty
  simp [effectiveEntropy, hcount, boundaryLength, frontier_empty]

/-- PDF pp.1,3: the finite commutative rigid fusion algebra and its positive
dimension character. N a b c counts the outgoing c-channel, not vacuum
multiplicity Nabc. These are structural charge data, with no entropy axiom. -/
structure FusionData (A : Type*) [Fintype A] [DecidableEq A] where
  vacuum : A
  dual : A → A
  dual_involutive : Function.Involutive dual
  dual_vacuum : dual vacuum = vacuum
  mult : A → A → A → ℕ
  comm : ∀ a b c, mult a b c = mult b a c
  unit : ∀ a c, mult vacuum a c = if a = c then 1 else 0
  vacuum_mult : ∀ a b, mult a b vacuum = if dual a = b then 1 else 0
  assoc : ∀ a b c e,
    ∑ x, mult a b x * mult x c e = ∑ y, mult b c y * mult a y e
  reciprocity : ∀ a b c, mult a b c = mult (dual a) c b
  dim : A → ℝ
  dim_pos : ∀ a, 0 < dim a
  dim_vacuum : dim vacuum = 1
  dim_dual : ∀ a, dim (dual a) = dim a
  dim_character : ∀ a b, ∑ c, (mult a b c : ℝ) * dim c = dim a * dim b

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- PDF p.1, (3): total quantum dimension of finitely many sectors.
Physical uses have a vacuum sector, so the sector type is nonempty. -/
def totalDimension (dim : A → ℝ) : ℝ := Real.sqrt (∑ a, dim a ^ 2)

/-- PDF p.3, (9): canonical positive vacuum row of the modular S matrix,
viewed as the effective vacuum state in the complementary charge basis. -/
def vacuumCycle (f : FusionData A) (a : A) : ℂ :=
  (f.dim a / totalDimension f.dim : ℝ)

/-- PDF p.3, (9): Born probability for the constructed vacuum-cycle vector. -/
def punctureProbability (f : FusionData A) (a : A) : ℝ :=
  Complex.normSq (vacuumCycle f a)

/-- PDF p.3, (10): basis of the full a tensor b fusion space, with outgoing charge. -/
abbrev PairFusionBasis (f : FusionData A) (a b : A) := Σ c : A, Fin (f.mult a b c)

/-- PDF p.3, (13): a tensor b tensor c basis with its internal channel and
both fusion multiplicity labels. -/
abbrev TripleFusionBasis (f : FusionData A) (a b c : A) :=
  Σ x : A, Σ mu : Fin (f.mult a b x), Σ y : A, Fin (f.mult x c y)

/-- PDF p.3, (10),(13): a charge projector in a specified fusion basis. -/
def chargeProjector {I : Type*} [DecidableEq I] (charge : I → A) (a : A) :
    Matrix I I ℂ := Matrix.diagonal (fun i => if charge i = a then 1 else 0)

/-- PDF p.3: quantum trace assigns each simple outgoing sector its dimension.
An ordinary trace would omit the d_c factor in (10). -/
def quantumTrace {I : Type*} [Fintype I] (weight : I → ℝ)
    (m : Matrix I I ℂ) : ℝ := ∑ i, weight i * (m i i).re

/-- PDF p.3, (10): normalized quantum trace of the outgoing-charge projector.
The dimension character gives positive denominator d_a d_b, as a conclusion. -/
def fusionProbability (f : FusionData A) (a b c : A) : ℝ :=
  let weight : PairFusionBasis f a b → ℝ := fun i => f.dim i.1
  quantumTrace weight (chargeProjector (fun i => i.1) c) /
    quantumTrace weight (1 : Matrix (PairFusionBasis f a b) (PairFusionBasis f a b) ℂ)

/-- PDF p.3, (13): the three-input fusion experiment, including internal channels. -/
def tripleFusionProbability (f : FusionData A) (a b c d : A) : ℝ :=
  let weight : TripleFusionBasis f a b c → ℝ := fun i => f.dim i.2.2.1
  quantumTrace weight (chargeProjector (fun i => i.2.2.1) d) /
    quantumTrace weight
      (1 : Matrix (TripleFusionBasis f a b c) (TripleFusionBasis f a b c) ℂ)

/-- PDF p.3, (10)–(12): vacuum multiplicity, retaining the conjugate of c. -/
def vacuumMultiplicityThree (f : FusionData A) (a b c : A) : ℕ :=
  f.mult a b (f.dual c)

/-- PDF p.3, (13): vacuum multiplicity composed through the internal x-channel. -/
def vacuumMultiplicityFour (f : FusionData A) (a b c d : A) : ℕ :=
  ∑ x, f.mult a b x * f.mult x c (f.dual d)

/-- PDF p.3, (11): independent a,b puncture draws followed by fusion to bar(c). -/
def jointThree (f : FusionData A) (a b c : A) : ℝ :=
  punctureProbability f a * punctureProbability f b * fusionProbability f a b (f.dual c)

/-- PDF p.3, (13): independent a,b,c draws followed by fusion to bar(d). -/
def jointFour (f : FusionData A) (a b c d : A) : ℝ :=
  punctureProbability f a * punctureProbability f b * punctureProbability f c *
    tripleFusionProbability f a b c (f.dual d)

/-- PDF p.3, (12): distinguishable vacuum fusion states of a three-punctured sphere.
Zero multiplicities provide no basis labels. -/
abbrev ThreeBasis (f : FusionData A) :=
  Σ a : A, Σ b : A, Σ c : A, Fin (vacuumMultiplicityThree f a b c)

/-- PDF p.3, (14): distinguishable four-puncture vacuum fusion states;
the internal channel and both multiplicity labels are retained. -/
abbrev FourBasis (f : FusionData A) :=
  Σ a : A, Σ b : A, Σ c : A, Σ d : A, Σ x : A,
    Fin (f.mult a b x) × Fin (f.mult x c (f.dual d))

/-- PDF p.3, (11)–(12): canonical effective density, diagonal in the fusion basis.
Every distinguishable state with external labels a,b,c has weight d_a d_b d_c/D^4.
Normalization and the entropy formula are conclusions, never hypotheses. -/
def threeDensity (f : FusionData A) : Matrix (ThreeBasis f) (ThreeBasis f) ℂ :=
  Matrix.diagonal (fun i =>
    ((f.dim i.1 * f.dim i.2.1 * f.dim i.2.2.1 / totalDimension f.dim ^ 4 : ℝ) : ℂ))

/-- PDF p.3, (13)–(14): canonical effective four-puncture density with weight
 d_a d_b d_c d_d/D^6 per distinguishable fusion basis state. -/
def fourDensity (f : FusionData A) : Matrix (FourBasis f) (FourBasis f) ℂ :=
  Matrix.diagonal (fun i =>
    ((f.dim i.1 * f.dim i.2.1 * f.dim i.2.2.1 * f.dim i.2.2.2.1 /
      totalDimension f.dim ^ 6 : ℝ) : ℂ))

/-- PDF p.3: mean log quantum dimension in the puncture charge law. -/
def meanLogDimension (f : FusionData A) : ℝ :=
  ∑ a, punctureProbability f a * Real.log (f.dim a)

/-- Vacuum-only structural example: no sectors or probabilities are supplied by an axiom. -/
def vacuumOnly : FusionData Unit where
  vacuum := ()
  dual := id
  dual_involutive := fun _ => rfl
  dual_vacuum := rfl
  mult := fun _ _ _ => 1
  comm := fun _ _ _ => rfl
  unit := by intros; simp
  vacuum_mult := by intros; simp
  assoc := by intros; simp
  reciprocity := fun _ _ _ => rfl
  dim := fun _ => 1
  dim_pos := fun _ => by norm_num
  dim_vacuum := rfl
  dim_dual := fun _ => rfl
  dim_character := by intros; simp

example : totalDimension vacuumOnly.dim = 1 := by
  simp [totalDimension, vacuumOnly]

example : punctureProbability vacuumOnly () = 1 := by
  simp [punctureProbability, vacuumCycle, totalDimension, vacuumOnly]

example (f : FusionData A) (a b c : A)
    (h : vacuumMultiplicityThree f a b c = 0) :
    IsEmpty (Fin (vacuumMultiplicityThree f a b c)) := by
  rw [h]
  infer_instance

example {I : Type*} [Fintype I] [DecidableEq I] :
    (Real.log 2 * QAlgorithms.vnEntropy (1 : Matrix I I ℂ)) = 0 := by
  simp [QAlgorithms.vnEntropy, cfc_one]

end QAlgorithms.Papers.Independent.Intake100.P48


