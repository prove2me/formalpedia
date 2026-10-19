-- Prove2me | Definitions.Def_OAIE3v2B278
-- name    : OAIE3v2B278
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T07:13:50.02821+00:00
-- url     : https://prove2.me/theorems/f0bfbe43-6c77-4928-98b3-deba3e85841e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 290 of 311
-- statement:
--   Definitions bundle 290 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B306`, `OAIE3v2B269`, `OAIE3v2B270`, `OAIE3v2B272` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateTaggedPairLongUniformFactors.lean`, `Estimates/AllocatedExternalCandidateTaggedPairUniformFactors.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeBudget.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B306
import Definitions.Def_OAIE3v2B269
import Definitions.Def_OAIE3v2B270
import Definitions.Def_OAIE3v2B272

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

noncomputable section

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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

theorem selectedCorrelation_localLaw
    (V : ∀ j, (F.native j).model.Niltest (fullTaggedVariableWeight (X := X) J))
    (a : Ω) (j : Pivot)
    (hcorr : Real.exp (-p) ≤
      ‖((F.chart a).slice.fullSliceLaw
        ((F.chart a).slice.length_pos_of_dense (F.chart a).dense)).complexMean (fun u =>
        star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
          ((F.localTest a j).eval u.val *
            (V j).eval (fullTaggedPhysicalIntegerPoint J poly
              (fun k => ((F.chart a).centerLift k).val) (F.physicalBox a u).val)))‖) :
    Real.exp (-p) ≤ ‖(F.sourceChart a).localLaw.complexMean (fun site =>
      star ((F.twist a j).eval N poly (A.physical (F.sourceChart a).path site)) *
        ((F.reference a j).observable
            ((F.candidate a).value ((F.chart a).retainedParameter site.val)) *
          (V j).eval (fullTaggedPhysicalIntegerPoint J poly
            (fun k => ((F.sourceChart a).centerLift k).val)
            (A.physical (F.sourceChart a).path site))))‖ := by
  have hm := (F.chart a).localLaw_complexMean_eq_fullSliceLaw_site (fun site =>
    star ((F.twist a j).eval N poly (A.physical (F.sourceChart a).path site)) *
      ((F.reference a j).observable
          ((F.candidate a).value ((F.chart a).retainedParameter site.val)) *
        (V j).eval (fullTaggedPhysicalIntegerPoint J poly
          (fun k => ((F.sourceChart a).centerLift k).val)
          (A.physical (F.sourceChart a).path site))))
  rw [F.chart_localLaw] at hm
  rw [hm]
  convert hcorr using 2
  congr 1
  funext u
  change star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
      ((F.reference a j).observable
          ((F.candidate a).value ((F.chart a).retainedParameter ((F.chart a).parameter u.val))) *
        (V j).eval (fullTaggedPhysicalIntegerPoint J poly
          (fun k => ((F.chart a).centerLift k).val) (F.physicalBox a u).val)) = _
  rw [(F.chart a).retainedParameter_parameter]
  rfl

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct Classical

theorem exists_allocatedFrozenTaggedFamily_common_factors (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A K T : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {Pivot α Ω : Type*} [Fintype Pivot] [Fintype α] [Fintype Ω]
      {LG : Type u} {MG : Pivot → Type u}
      [LieRing LG] [LieAlgebra ℚ LG] [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
      {d₀ : ℕ} {d : Pivot → ℕ}
      (D : RationalFilteredNilmanifold LG s d₀)
      (E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j))
      {pGeo p bnd : ℝ}, 0 ≤ pGeo → 0 ≤ p → 0 ≤ bnd →
      (∀ j, (pi (pairModels D (E j))).GeometryComplexityLE pGeo) →
      pGeo ≤ bnd → (pGeo + 3) ^ 5 ≤ bnd →
      (Fintype.card α : ℝ) ≤ bnd → (Fintype.card Pivot : ℝ) ≤ bnd →
    ∀ (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG MG i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i})),
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ bnd) →
      (∀ i k, rationalLogHeight ((optionProduct D E).basis.repr (e i) k) ≤ bnd) →
      let localCost := allocatedFrozenTaggedPairBudget s C A pGeo p
      let r := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := r + (r + K) ^ K
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
      {I Jgeo : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (Jgeo j)]
      {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
      (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := Jgeo) B)
      (Deck : Fin m → Type*) (keep : LayerSamplerVariables G I n B → Prop)
      [Nonempty {i // keep i}], (Fintype.card {i // keep i} : ℝ) ≤ bnd →
      (∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (Γ.sides keep i : ℝ)) →
      (∀ i, Real.exp ((P + 2) ^ T) ≤ (Γ.sides keep i : ℝ)) →
    ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
    ∀ (g : Ω → ∀ i : Option Pivot,
        (optionFactors D E i).filtration.realification.PolynomialOrbit
          (fun _ : {i // keep i} => 1))
      (eta : Pivot → LG →ₗ[ℚ] ℚ) (theta : ∀ j, MG j →ₗ[ℚ] ℚ)
      (input : ∀ _a : {a // a ∈ H}, ∀ j,
        AllocatedFrozenTaggedPairInput Γ Deck keep D (E j) p),
      (∀ a j
        (c : Basis (Fin (finrank ℚ (PairAlgebra LG (MG j)))) ℚ (PairAlgebra LG (MG j)))
        (w : Fin (finrank ℚ (PairAlgebra LG (MG j))) → ℕ)
        (hc : ∀ k, (pi (pairModels D (E j))).filtration.layer k =
          Submodule.span ℚ (c '' {i | k ≤ w i})),
        pairOrbitSymbol D (E j) (input a j).V.orbit (input a j).W.orbit c w hc =
          pairOrbitSymbol D (E j) (g a.val none) (g a.val (some j)) c w hc) →
      (∀ a j, (input a j).η = eta j) →
      (∀ a j, (input a j).θ = theta j) →
      let q := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      ∃ (W : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
        (v : Fin (Fintype.card α) → (optionProduct D E).filtration.AssociatedGraded)
        (den : ℕ) (H' : Finset Ω),
        H' ⊆ H ∧ 0 < outer.mass H' ∧
        Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e ω hF)
          ω W.toSubmodule ∧
        (∀ i k, rationalLogHeight
          (((optionProduct D E).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
        (∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer W s →
          realifyFunctional ((pairFrequency (eta j) (theta j)).comp
            (optionPairProjection j).toLinearMap) x = 0) ∧
        0 < den ∧ (den : ℝ) ≤ Real.exp q ∧
        ∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
          e ω hF (fun i => (Γ.sides keep i : ℝ)) q den W
          ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
            (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩ := by
  obtain ⟨C, A, hC, hA, hstep⟩ := exists_allocatedFrozenTaggedPairInput_fixed_basis_step_drop s hs
  obtain ⟨K, T, hK, hT, hcommon⟩ := exists_nativeOptionPair_weighted_common_orbit_factors s
  refine ⟨C, A, K, T, hC, hA, hK, hT, ?_⟩
  intro Pivot α Ω _ _ _ LG MG _ _ _ _ _ _ _ _ _ _ _ _ d₀ d D E
    pGeo p bnd hpGeo hp hbnd hGeo hpGeoB hInvB hα hPivot e ω hF hstructure he
    localCost r P m G X _ _ I Jgeo _ _ n B _ Γ Deck keep _ hkeep hlong hcommonLong
    outer H hH g eta theta input hsymbol heta htheta
  classical
  choose b ν hG _hforward hinverse hlocal using fun j => hstep D (E j) hpGeo (hGeo j)
  have hcost : 0 ≤ localCost := by
    dsimp [localCost, allocatedFrozenTaggedPairBudget, fixedAdaptedSymbolTransferInput]
    positivity
  have hbndR : bnd ≤ r := by
    dsimp [r, allocatedFrozenTaggedFamilyInputBudget]
    linarith [pow_nonneg (show 0 ≤ bnd + 3 by linarith) 4]
  have hcostR : localCost ≤ r := by
    dsimp [r, allocatedFrozenTaggedFamilyInputBudget]
    linarith [pow_nonneg (show 0 ≤ bnd + 3 by linarith) 4]
  have hheightR : (bnd + 3) ^ 4 + 1 ≤ r := by
    dsimp [r, allocatedFrozenTaggedFamilyInputBudget]
    linarith
  have hdim (j) : (Fintype.card (Σ i : Bool, Fin (Bool.rec (d j) d₀ i)) : ℝ) ≤ bnd :=
    (hGeo j).1.trans hpGeoB
  have hβ (j) : (Fintype.card (Fin (finrank ℚ (PairAlgebra LG (MG j)))) : ℝ) ≤ bnd := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis (pi (pairModels D (E j))).basis]
      using hdim j
  have hentries (j i k) : RationalHeightLE
      ((b j).repr (optionPairProjection j (e k)) i) ⌈Real.exp ((bnd + 3) ^ 4)⌉₊ :=
    rationalHeightLE_ceil_exp (optionPairProjection_adapted_logHeight D E j e (b j)
      hbnd (hdim j) he (fun i k => (hinverse j i k).trans hInvB) k i)
  have hheight : (⌈Real.exp ((bnd + 3) ^ 4)⌉₊ : ℝ) ≤ Real.exp r :=
    (ceil_exp_le_exp_add_one (by positivity)).trans (Real.exp_le_exp.mpr hheightR)
  have hsidepos (i) : 0 < (Γ.sides keep i : ℝ) := (Real.exp_pos _).trans_le (hlong i)
  apply hcommon D E e ω hF b ν hG (one_le_ceil_exp _) hentries
    (hbnd.trans hbndR) (hα.trans hbndR) (fun j => (hβ j).trans hbndR)
    (hkeep.trans hbndR) (hPivot.trans hbndR) hheight
    (fun i j k => (hstructure i j k).trans hbndR)
    (fun i => (Γ.sides keep i : ℝ)) hcommonLong outer H hH g eta theta
  intro a ha j
  have hfactor := hlocal j B Γ Deck keep (input ⟨a, ha⟩ j) hlong
  have hfactor' : (pi (pairModels D (E j))).filtration.ControlledSymbolFactorization
      (b j) (ν j) (hG j) (pairFrequency (eta j) (theta j))
      (fun i => (Γ.sides keep i : ℝ))
      (pairOrbitSymbol D (E j) (g a none) (g a (some j)) (b j) (ν j) (hG j)) localCost := by
    simpa only [heta, htheta, hsymbol, allocatedFrozenTaggedPairBudget, localCost]
      using hfactor
  exact hfactor'.mono (pi (pairModels D (E j))).filtration (b j) (ν j) (hG j)
    hcostR hsidepos

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairLongUniformFactors
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "Γ" => A.frozenTaggedContext hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  periodCap coverCap Lip

namespace AllocatedFrozenTaggedPairInput

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)
    {LG MG LM : Type u} [LieRing LG] [LieAlgebra ℚ LG]
    [LieRing MG] [LieAlgebra ℚ MG] [LieRing LM] [LieAlgebra ℚ LM]
    {s d e t : ℕ} {D : RationalFilteredNilmanifold LG s d}
    {E : RationalFilteredNilmanifold MG s e} {Fmark : NilpotentLieFiltration LM t}
    {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (reference : D.Niltest (fullTaggedVariableWeight (X := X) J))
    (partner : E.Niltest (fullTaggedVariableWeight (X := X) J))
    (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    {p : ℝ} (hp : 0 ≤ p) (hretained : ∀ i : C.Variables,
      Real.exp (-p) * (A.sides i.val : ℝ) ≤ C.slice.length i)
    (hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hV : reference.ComplexityLE p) (hW : partner.ComplexityLE p)
    (hWnorm : partner.normBound ≤ 1)
    (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      reference.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * reference.observable x)
    (hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
      partner.observable (z • x) = CircleFourier.character
        ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * partner.observable x)
    (hK : (Fintype.card C.Variables : ℝ) ≤ p)

variable (hcorr : Real.exp (-p) ≤
  ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
    star (twist.eval N poly (C.physical t.val)) *
      (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖)

def ofCandidate_of_retainedLength_of_localLaw
    (hcorr : Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
      star (twist.eval N poly (A.physical C.path site)) *
        (reference.observable (candidate.value (C.retainedParameter site.val)) *
          partner.eval (fullTaggedPhysicalIntegerPoint J poly
            (fun j => (C.centerLift j).val) (A.physical C.path site))))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p := by
  apply ofCandidate_of_retainedLength A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall C candidate
    reference partner twist hp hretained hperiod hvariation hV hW hWnorm
    η θ hηheight hθheight hη hθ hK
  have he := C.localLaw_complexMean_eq_fullSliceLaw (fun x =>
    star (twist.eval N poly (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter x)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))))
  change Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
    star (twist.eval N poly (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter site.val)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val)))))‖ at hcorr
  rw [he] at hcorr
  have hf : (fun t : integerBox (fun i : C.Variables => A.sides i.val) =>
      star (twist.eval N poly (C.physical t.val)) *
        (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val))) =
      (fun t => star (twist.eval N poly
        (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))) *
          (reference.observable (candidate.value (C.retainedParameter (C.parameter t.val))) *
            partner.eval (fullTaggedPhysicalIntegerPoint J poly
              (fun j => (C.centerLift j).val)
              (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))))) := by
    funext t
    rw [C.retainedParameter_parameter,
      C.chartValues_eq_physicalIntegerPoint hσ1 Cgeo hCgeo hchart hsmall hpoly t.val t.property]
    rfl
  rw [hf]
  exact hcorr

end AllocatedFrozenTaggedPairInput

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit

noncomputable section

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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateTaggedPairFamily

variable {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Ω Pivot D E Fmark φ marked
      keep cost p periodCap coverCap Lip)

theorem exists_long_pair_inputs
    (keepLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ i, keepLong i → keep i) :
    ∃ input : ∀ _a : Ω, ∀ j : Pivot,
        AllocatedFrozenTaggedPairInput F.context Deck keepLong D (E j) p,
      ∀ a j, (input a j).η = F.η j ∧ (input a j).θ = F.θ j ∧
        ∀ (c : Basis (Fin (finrank ℚ (PairAlgebra LG (MG j)))) ℚ
            (PairAlgebra LG (MG j)))
          (w : Fin (finrank ℚ (PairAlgebra LG (MG j))) → ℕ)
          (hc : ∀ k, (pi (pairModels D (E j))).filtration.layer k =
            Submodule.span ℚ (c '' {i | k ≤ w i})),
          pairOrbitSymbol D (E j) (input a j).V.orbit (input a j).W.orbit c w hc =
            pairOrbitSymbol D (E j)
              ((F.candidate a).axisOrbit keepLong (fun _ => 0))
              ((E j).filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
                ((F.chart a).axisPolynomial keepLong (fun _ => 0))
                ((F.chart a).axisPolynomial_support keepLong (fun _ => 0))
                (F.jointOrbit a (some j))) c w hc := by
  classical
  have hKlong : (Fintype.card {i // keepLong i} : ℝ) ≤ p := by
    have hcard : Fintype.card {i // keepLong i} ≤ Fintype.card {i // keep i} :=
      Fintype.card_le_of_injective
        (fun i : {i // keepLong i} => (⟨i.val, hsub i.val i.property⟩ : {i // keep i}))
        (fun i j h => Subtype.ext
          (congrArg (fun k : {i // keep i} => k.val) h))
    exact (Nat.cast_le.mpr hcard).trans F.hK
  suffices hsingle : ∀ a : Ω, ∀ j : Pivot,
      ∃ input : AllocatedFrozenTaggedPairInput F.context Deck keepLong D (E j) p,
        input.η = F.η j ∧ input.θ = F.θ j ∧
          ∀ (c : Basis (Fin (finrank ℚ (PairAlgebra LG (MG j)))) ℚ
              (PairAlgebra LG (MG j)))
            (w : Fin (finrank ℚ (PairAlgebra LG (MG j))) → ℕ)
            (hc : ∀ k, (pi (pairModels D (E j))).filtration.layer k =
              Submodule.span ℚ (c '' {i | k ≤ w i})),
            pairOrbitSymbol D (E j) input.V.orbit input.W.orbit c w hc =
              pairOrbitSymbol D (E j)
                ((F.candidate a).axisOrbit keepLong (fun _ => 0))
                ((E j).filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
                  ((F.chart a).axisPolynomial keepLong (fun _ => 0))
                  ((F.chart a).axisPolynomial_support keepLong (fun _ => 0))
                  (F.jointOrbit a (some j))) c w hc by
    choose input hinput using hsingle
    exact ⟨input, hinput⟩
  intro a j
  let C := F.chart a
  let candidate := F.candidate a
  have hkeep : ∀ i, keepLong i → C.keep i := hsub
  let test : A.Site → D.Space → ℂ := fun site x =>
    star ((F.twist a j).eval N poly (A.physical C.path site)) *
      ((F.reference a j).observable x *
        (F.selected j).eval (fullTaggedPhysicalIntegerPoint J poly
          (fun k => (C.centerLift k).val) (A.physical C.path site)))
  have hstart : Real.exp (-p) ≤
      ‖C.localLaw.complexMean (fun site => test site (candidate.siteValue site))‖ := by
    change Real.exp (-p) ≤ ‖(F.chart a).localLaw.complexMean _‖
    rw [F.chart_localLaw]
    exact F.hcorr a j
  obtain ⟨fixed, hfixed, hfiber⟩ :=
    candidate.exists_restrictAxes_site_norm keepLong hkeep test
  let C' := C.restrictAxes keepLong hkeep fixed hfixed
  let candidate' := candidate.restrictAxes keepLong hkeep fixed hfixed
  have hcorr : Real.exp (-p) ≤ ‖C'.localLaw.complexMean (fun site =>
      star ((F.twist a j).eval N poly (A.physical C'.path site)) *
        ((F.reference a j).observable (candidate'.value (C'.retainedParameter site.val)) *
          (F.selected j).eval (fullTaggedPhysicalIntegerPoint J poly
            (fun k => (C'.centerLift k).val) (A.physical C'.path site))))‖ :=
    hstart.trans hfiber
  let input := AllocatedFrozenTaggedPairInput.ofCandidate_of_retainedLength_of_localLaw A
    F.hpoly F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    C' candidate' (F.reference a j) (F.selected j) (F.twist a j)
    F.hp (C'.retainedLength_of_densityBudget C'.dense F.hcost)
    (F.hperiod a j) F.hvariation (F.hV a j) (F.hW j) (F.hWnorm j)
    (F.η j) (F.θ j) (F.hηheight j) (F.hθheight j) (F.hη a j) (F.hθ j) hKlong hcorr
  refine ⟨input, rfl, rfl, ?_⟩
  intro c w hc
  change pairOrbitSymbol D (E j) (candidate.axisOrbit keepLong fixed)
    ((F.selected j).integerChartPullback (fun _ => 1)
      C'.integerChart C'.integerChart_support).orbit c w hc = _
  rw [(F.selected j).integerChartPullback_orbit_eq_of_orbit_eq (fun _ => 1)
    C'.integerChart C'.integerChart_support (F.ambient j) (F.selected_orbit j)]
  simp only [Niltest.integerChartPullback_orbit]
  rw [C.restrictAxes_polynomialOrbitRealChart keepLong hkeep fixed hfixed
    (E j).filtration (F.ambient j).orbit]
  exact candidate.pairOrbitSymbol_axisOrbit_independent (E j) keepLong fixed (fun _ => 0)
    (F.jointOrbit a (some j)) c w hc

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

end OAI
end


