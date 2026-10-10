-- Prove2me | Definitions.Def_OAIErdos3B146
-- name    : OAIErdos3B146
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T17:14:16.835619+00:00
-- url     : https://prove2.me/theorems/6ae349be-dab5-420f-9010-6bb6704037ef
-- title:
--   OpenAI Erdős-3 split, definitions bundle 147 of 152
-- statement:
--   Definitions bundle 147 of 152 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B145`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 147 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.allocatedClippedPrefactorSiteMask`, `OAI.Erdos3.VectorPolynomial.exists_preparedModularGeneralDetector_early_native_budget`, `OAI.Erdos3.VectorPolynomial.exists_preparedModularGeneralDetector_resource_budget`, `OAI.Erdos3.VectorPolynomial.fullGridCoverAxisDecidableEq`, `OAI.Erdos3.VectorPolynomial.generalDetectorCoefficientCost`, `OAI.Erdos3.VectorPolynomial.preparedModularGeneralDetectorResources`, `_private.Estimates.PreparedModularGeneralDetectorNativeBounds.0.OAI.Erdos3.VectorPolynomial.generalResources_bounds_of_list`, `_private.Estimates.PreparedModularGeneralDetectorNativeBounds.0.OAI.Erdos3.VectorPolynomial.generalResources_map`, `_private.Estimates.PreparedModularGeneralDetectorNativeBounds.0.OAI.Erdos3.VectorPolynomial.generalResources_total_map`, `_private.Estimates.PreparedModularGeneralDetectorNativeBounds.0.OAI.Erdos3.VectorPolynomial.natMv_eval_mono`, `_private.Estimates.PreparedModularGeneralDetectorNativeBounds.0.OAI.Erdos3.VectorPolynomial.natMv_eval_nonneg`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B138
import Definitions.Def_OAIErdos3B145

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridIdealCover
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} (d : ℕ) (T : Fin m → ℝ)

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid

variable [∀ j, Fintype (E j)] [NeZero d]
variable (hR : ∀ j, 0 < R j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

@[instance_reducible]
noncomputable def fullGridCoverAxisDecidableEq :
    DecidableEq {a // allocatedGridAxis (I := I) U b S.value a} := Classical.decEq _

attribute [local instance 2000] fullGridCoverAxisDecidableEq

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)] (d : ℕ) [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "O" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductPrefactorMasks
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y₀
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

noncomputable def allocatedClippedPrefactorSiteMask
    (r : Finset α → (∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ :=
  allocatedKernelSiteMask B U b S rowSets x q residue period (fun s => (r s).1) *
    coefficientDeckSiteMask root dirs rows d period (fun s => (r s).2)

variable (T : Fin m → ℝ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit rowTypes I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y₀
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x y₀
local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)

variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : rowTypes j) => standardLatticeClosedQuarterBox (J j))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedModularGeneralDetectorNativeBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def generalDetectorCoefficientCost (m dim : ℕ) : ℕ :=
  ∑ j : Fin m, Fintype.card (BoundedCoefficientExponent (Fin dim) (j.val + 1))

noncomputable def preparedModularGeneralDetectorResources {α : Type*} [Semiring α]
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) (P L : α) :
    PreparedModularCanonicalDetectorResources α :=
  let Q : α := (P + K.Cperiod) ^ K.Cperiod
  let v : α := P + 8
  let w : α := P + 1
  let Dg : α := 2 * P + K.m * P + (layerTailDegree K.m + 1 : ℕ) + K.m + comparisonProfileBound + 8
  let Pproj : α := 4 * (L + 8) ^ 2
  let coverLog : α := (Pproj + (dim + 2 : ℕ) + K.Acover) ^ K.Acover
  let Pmass : α := (Pproj + K.Asample) ^ K.Asample
  let Vlog : α := L ^ 2 * ((layerTailDegree K.m + 1 : ℕ) * L + 1)
  let Nlog : α := (K.m * 2 ^ dim : ℕ) * (P + 8) * (1 + 4 * P)
  let Pbox : α := 2 * P ^ 2 + 8
  let Banalytic : α := Dg + 4 * P + 32
  let baseAmbient : α := Pproj + coverLog + Vlog + Nlog + Q + (layerTailDegree K.m + 1 : ℕ) * L + 3 * P + comparisonProfileBound + (2 ^ dim : ℕ) + 32
  let tq : α := dim + Q + (P + 1) + 1
  let pq : α := K.Cgrid + (dim + 1 : ℕ) * Q + (P + 1) + 4
  let gridlog : α := slicedGridGeometryLog Dg v w tq + pq
  let Fpref : α := (P + K.Cpref) ^ K.Cpref
  let sumlog : α := Pbox + P + Vlog + Nlog + Q + P
  let idealQ : α := dim + P * sumlog + (P + comparisonProfileBound + (P + 1) * sumlog) + sumlog + 1
  let ambient : α := affineAmbientPrimitiveBudget baseAmbient idealQ
  let Psample : α := Pmass + ambient + Pproj + 2 * P +
    generalDetectorCoefficientCost K.m dim + (P + (K.m + dim + 2 : ℕ)) ^ (K.m + dim + 2) + 8
  let Pside : α := Psample + Pproj + Pmass + 2 * L
  let Pnative : α := Dg + gridlog + v + Fpref + 6 * P + Banalytic
  let nativeBudget : α := ((Pnative + K.Cnative) ^ K.Cnative + K.Anorm) ^ K.Anorm
  let E : α := 3 * P + nativeBudget + 30
  let full : α := 4 * (L + 8) ^ 2
  let required : α := (Psample + K.Apert) ^ K.Apert + (Pmass + K.AmassWindow) ^ K.AmassWindow + (Pproj + K.Aproj) ^ K.Aproj + (Pside + K.Aside) ^ K.Aside + (full + E + K.Amarginal) ^ K.Amarginal
  { Q, v, w, Dg, Pproj, coverLog, Pmass, Vlog, Nlog, Pbox, Banalytic, baseAmbient, tq, pq, gridlog, Fpref, sumlog, idealQ, ambient, Psample, Pside, Pnative, nativeBudget, E, full, required }

theorem generalResources_map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) (K : PreparedModularCanonicalDetectorResourceConstants)
    (dim : ℕ) (P L : α) :
    (preparedModularGeneralDetectorResources K dim P L).map f =
      preparedModularGeneralDetectorResources K dim (f P) (f L) := by
  simp [preparedModularGeneralDetectorResources,
    PreparedModularCanonicalDetectorResources.map, slicedGridGeometryLog,
    affineAmbientPrimitiveBudget, affineAmbientMassLog, map_ofNat]

theorem generalResources_total_map {α β : Type*} [Semiring α] [Semiring β]
    (f : α →+* β) (r : PreparedModularCanonicalDetectorResources α) :
    (r.map f).total = f r.total := by
  simp [PreparedModularCanonicalDetectorResources.total,
    PreparedModularCanonicalDetectorResources.toList,
    PreparedModularCanonicalDetectorResources.map]

theorem generalResources_bounds_of_list
    {r : PreparedModularCanonicalDetectorResources ℝ} {budget : ℝ}
    (h : ∀ x ∈ r.toList, x ∈ Set.Icc 0 budget) : r.Bounds budget := by
  constructor <;> apply h <;>
    simp only [PreparedModularCanonicalDetectorResources.toList, List.mem_cons] <;> tauto

theorem natMv_eval_nonneg {ι : Type*} (p : MvPolynomial ι ℕ)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ p.eval₂ (Nat.castRingHom ℝ) x := by
  induction p using MvPolynomial.induction_on with
  | C n => simp only [MvPolynomial.eval₂_C]; exact Nat.cast_nonneg _
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using add_nonneg hp hq
  | mul_X p i hp =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using mul_nonneg hp (hx i)

theorem natMv_eval_mono {ι : Type*} (p : MvPolynomial ι ℕ)
    {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    p.eval₂ (Nat.castRingHom ℝ) x ≤ p.eval₂ (Nat.castRingHom ℝ) y := by
  have hy (i) : 0 ≤ y i := (hx i).trans (hxy i)
  induction p using MvPolynomial.induction_on with
  | C n => simp only [MvPolynomial.eval₂_C, le_refl]
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using add_le_add hp hq
  | mul_X p i hp =>
    simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using
      mul_le_mul hp (hxy i) (hx i) (natMv_eval_nonneg p hy)

theorem exists_preparedModularGeneralDetector_resource_budget
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P L : ℝ}, 0 ≤ P → P ≤ L →
      let resources := preparedModularGeneralDetectorResources K dim P L
      resources.Bounds ((P + L + C) ^ C) ∧ resources.total ≤ (P + L + C) ^ C := by
  let diagonal := preparedModularGeneralDetectorResources K dim
    (Polynomial.X : Polynomial ℕ) Polynomial.X
  let bivariate := preparedModularGeneralDetectorResources K dim
    (MvPolynomial.X false : MvPolynomial Bool ℕ) (MvPolynomial.X true)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget diagonal.total
  refine ⟨C, hC, ?_⟩
  intro P L hP hPL resources
  have hL : 0 ≤ L := hP.trans hPL
  let values : Bool → ℝ := fun b => if b then L else P
  let ev : MvPolynomial Bool ℕ →+* ℝ := MvPolynomial.eval₂Hom (Nat.castRingHom ℝ) values
  let evSum : MvPolynomial Bool ℕ →+* ℝ := MvPolynomial.eval₂Hom (Nat.castRingHom ℝ) (fun _ => P + L)
  let evDiag : Polynomial ℕ →+* ℝ := Polynomial.eval₂RingHom (Nat.castRingHom ℝ) (P + L)
  have hmap : bivariate.map ev = resources := by
    simpa [bivariate, resources, ev, values] using
      generalResources_map ev K dim (MvPolynomial.X false) (MvPolynomial.X true)
  have hmapSum : bivariate.map evSum = preparedModularGeneralDetectorResources K dim (P + L) (P + L) := by
    simpa [bivariate, evSum] using
      generalResources_map evSum K dim (MvPolynomial.X false) (MvPolynomial.X true)
  have hmapDiag : diagonal.map evDiag = preparedModularGeneralDetectorResources K dim (P + L) (P + L) := by
    simpa [diagonal, evDiag] using generalResources_map evDiag K dim Polynomial.X Polynomial.X
  have hvalues (i) : 0 ≤ values i := by cases i <;> assumption
  have hdom (i) : values i ≤ P + L := by cases i <;> dsimp [values] <;> linarith
  have hmono : resources.total ≤ (preparedModularGeneralDetectorResources K dim (P + L) (P + L)).total := by
    rw [← hmap, ← hmapSum, generalResources_total_map, generalResources_total_map]
    exact natMv_eval_mono bivariate.total hvalues hdom
  have htotal : resources.total ≤ (P + L + C) ^ C := by
    apply hmono.trans
    rw [← hmapDiag, generalResources_total_map]
    exact hbound (P + L) (add_nonneg hP hL)
  have hnonneg : ∀ x ∈ resources.toList, 0 ≤ x := by
    rw [← hmap]
    change ∀ x ∈ bivariate.toList.map ev, 0 ≤ x
    intro x hx
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hx
    exact natMv_eval_nonneg q hvalues
  refine ⟨generalResources_bounds_of_list ?_, htotal⟩
  intro x hx
  exact ⟨hnonneg x hx, (List.single_le_sum hnonneg x hx).trans htotal⟩

theorem exists_preparedModularGeneralDetector_early_native_budget
    (K : PreparedModularCanonicalDetectorResourceConstants) (dim : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P : ℝ}, 0 ≤ P → ∀ L : ℝ,
      let r := preparedModularGeneralDetectorResources K dim P L
      r.Pnative ∈ Set.Icc 0 ((2 * P + C) ^ C) ∧
      r.nativeBudget ∈ Set.Icc 0 ((2 * P + C) ^ C) ∧
      r.E ∈ Set.Icc 0 ((2 * P + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_preparedModularGeneralDetector_resource_budget K dim
  refine ⟨C, hC, ?_⟩
  intro P hP L r
  have h := (hbound (P := P) (L := P) hP le_rfl).1
  change (preparedModularGeneralDetectorResources K dim P P).Pnative ∈ _ ∧
    (preparedModularGeneralDetectorResources K dim P P).nativeBudget ∈ _ ∧
    (preparedModularGeneralDetectorResources K dim P P).E ∈ _
  simpa only [two_mul] using And.intro h.Pnative (And.intro h.nativeBudget h.E)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

end Erdos3.VectorPolynomial

end

end OAI

end


