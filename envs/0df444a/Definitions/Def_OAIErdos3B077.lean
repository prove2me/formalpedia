-- Prove2me | Definitions.Def_OAIErdos3B077
-- name    : OAIErdos3B077
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-15T23:42:12.40922+00:00
-- url     : https://prove2.me/theorems/84386833-416e-482b-8f84-8965b07804e8
-- title:
--   OpenAI Erdős-3 split, definitions bundle 78 of 1378
-- statement:
--   Definitions bundle 78 of 1378 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B076`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 78 available.
--
--   Modules: `OAI.Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors.markedMiddleOn`, `OAI.Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors.markedMiddleOn_log`, `OAI.Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors.markedMiddleOn_values`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.ofGlobalMarkedNativeMiddle`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.ofGlobalMarkedNativeMiddle_orbit_log`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.ofNativeRefilteredMiddle`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalCandidate.ofRefilteredIncludedMark`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.finiteFreezing_of_selection`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.freezingFrozenValue`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.freezingNativeOrbit`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.freezingNativeOrbit_value`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.freezingOriginalValue`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.freezingOriginalValue_eq`, `OAI.Erdos3.VectorPolynomial.AllocatedExternalLocalChart.globalMarked_middle_values`, `OAI.Erdos3.VectorPolynomial.PreparedCenteredMarginalProjectionBounds.recOn`, `OAI.Erdos3.VectorPolynomial.preparedCenteredMarginalProjectionBounds`, `OAI.Erdos3.VectorPolynomial.preparedConcreteSlicedForecastCapLog`, `OAI.Erdos3.VectorPolynomial.preparedConcreteSlicedForecastMassLog`, `OAI.Erdos3.VectorPolynomial.preparedConcreteSlicedForecastNativeLog`, `OAI.Erdos3.VectorPolynomial.preparedConcreteSlicedForecastOutputLog`, `OAI.Erdos3.VectorPolynomial.preparedConcreteSlicedForecastPeriodLog`, `OAI.Erdos3.VectorPolynomial.preparedConcreteSlicedForecastTailSiteLog`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B165
import Definitions.Def_OAIErdos3B1340
import Definitions.Def_OAIErdos3B1343

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalLocalFiniteFreezing
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : F.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D F φ marked)

noncomputable def freezingNativeOrbit :
    (D.filtration.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group :=
  D.filtration.realification.polynomialOrbitCoordinates (fun _ : C.Variables => 1) candidate.orbit

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in

theorem freezingNativeOrbit_value (u : C.Variables → ℤ) :
    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom
      (fun _ : C.Variables => 1) (fun i => (u i : ℝ)) (C.freezingNativeOrbit candidate)) : D.Space) =
      candidate.value u := by
  rw [freezingNativeOrbit, D.filtration.nativeFrozenMarkedOrbitCoordinates_realValue,
    polynomialOrbitRealEval_integer]
  rfl

noncomputable def freezingOriginalValue
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1)) (u : C.Variables → ℤ) : ℂ :=
  (tests (C.physical u)).observable (QuotientGroup.mk
    (D.filtration.adaptedPolynomialRealValueHom (fun _ : C.Variables => 1)
      (fun i => (u i : ℝ)) (C.freezingNativeOrbit candidate)))

@[simp] theorem freezingOriginalValue_eq
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1)) (u : C.Variables → ℤ) :
    C.freezingOriginalValue candidate tests u =
      (tests (C.physical u)).observable (candidate.value u) := by
  unfold freezingOriginalValue
  rw [C.freezingNativeOrbit_value candidate]

variable (sectionMap : M →ₗ[ℚ] L)
    (hsectionLayer : ∀ j, ∀ y ∈ F.layer j, sectionMap y ∈ D.filtration.layer j)
    (EF RF : (F.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)
    (middle : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)

noncomputable def freezingFrozenValue
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1))
    (left right : D.RealGroup) (u : C.Variables → ℤ) : ℂ :=
  (tests (C.physical u)).markedFrozenValue F (fun _ : C.Variables => 1)
    sectionMap hsectionLayer EF RF middle left right u

theorem finiteFreezing_of_selection
    {Left Right : Type*} (Q modulus : ℕ) (hQ : 0 < Q) (hmodulus : 0 < modulus)
    (left : Left → D.RealGroup) (right : Right → D.RealGroup)
    (tests : (X → ℤ) → D.Niltest (fun _ : C.Variables => 1)) (weight : (X → ℤ) → ℂ)
    {budget Bweight Lip ε τ θ Sscore : ℝ}
    (hQbound : (Q : ℝ) ≤ max 1 budget) (hmodulusBound : (modulus : ℝ) ≤ budget)
    (htwo : ∀ i, 2 ≤ C.slice.length i)
    (hlong : ∀ i, 2 * budget * max 1 budget ≤ (C.slice.length i : ℝ))
    {densityCost : ℝ}
    (hsourceDense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      densityCost C.slice.integerPoints)
    (hθ : 0 < θ) (herr : 0 ≤ Bweight * (Lip * ε))
    (hscore : Sscore ≤ candidate.score (fun x value => (tests x).observable value) weight)
    (hselect :
      (∀ i, 0 < C.slice.length i) →
      (∀ i v, v < C.slice.length i →
        |((C.slice.start i : ℤ) : ℝ) + C.step * v| ≤ (A.sides i.val : ℝ)) →
      (∀ i, (C.step : ℝ) * C.slice.length i ≤ 2 * (A.sides i.val : ℝ)) →
      (∀ i, 2 * (modulus : ℝ) ≤ (1 / (Q : ℝ)) * C.slice.length i) →
      (Sscore ≤ 𝔼 x : (∀ i, Fin (C.slice.length i)),
        (weight (C.physical (affineParentIntegerPoint C.slice.length
            (fun i => (C.slice.start i : ℤ)) C.step x)) *
          C.freezingOriginalValue candidate tests (affineParentIntegerPoint C.slice.length
            (fun i => (C.slice.start i : ℤ)) C.step x)).re) →
      ∃ T : ResidueBoxSlice C.slice.length modulus, (∀ i, 0 < T.length i) ∧
        (∀ i, θ * C.slice.length i /
          (4 * modulus * Q * (Fintype.card C.Variables + 1 : ℝ)) ≤ T.length i) ∧
        ∃ i j,
          (∀ x : ∀ k, Fin (T.length k),
            ‖C.freezingOriginalValue candidate tests
                (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x) -
              C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
                (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)‖ ≤ Lip * ε) ∧
          (∀ x : ∀ k, Fin (T.length k),
            ‖weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
                C.freezingOriginalValue candidate tests
                  (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x) -
              weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
                C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
                  (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)‖ ≤ Bweight * (Lip * ε)) ∧
          τ < 𝔼 x : (∀ k, Fin (T.length k)),
            (weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
              C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
                (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)).re) :
    ∃ slice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) (C.step * modulus),
      IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
        (densityCost + Real.log ((4 * modulus * Q * (Fintype.card C.Variables + 1 : ℝ)) / θ))
        slice.integerPoints ∧
      slice.integerPoints ⊆ C.slice.integerPoints ∧
      ∃ i j,
        (∀ u ∈ slice.integerPoints,
          ‖(tests (C.physical u)).observable (candidate.value u) -
            C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j) u‖ ≤ Lip * ε) ∧
        (∀ u ∈ slice.integerPoints,
          ‖weight (C.physical u) * (tests (C.physical u)).observable (candidate.value u) -
            weight (C.physical u) *
              C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j) u‖ ≤
            Bweight * (Lip * ε)) ∧
        τ < (𝔼 u ∈ slice.integerPoints, weight (C.physical u) *
          C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j) u).re ∧
        τ - Bweight * (Lip * ε) ≤
          (𝔼 u ∈ slice.integerPoints, weight (C.physical u) *
            (tests (C.physical u)).observable (candidate.value u)).re := by
  have hparent (i) (v : ℕ) (hv : v < C.slice.length i) :
      |((C.slice.start i : ℤ) : ℝ) + C.step * v| ≤ (A.sides i.val : ℝ) := by
    simp only [Int.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    exact_mod_cast (C.slice.inside i v hv).le
  have hwidth (i) : (C.step : ℝ) * C.slice.length i ≤ 2 * (A.sides i.val : ℝ) := by
    exact_mod_cast C.slice.stride_mul_length_le_twice i (htwo i)
  have hlarge (i) : 2 * (modulus : ℝ) ≤ (1 / (Q : ℝ)) * C.slice.length i := by
    have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    have hmnonneg : (0 : ℝ) ≤ modulus := Nat.cast_nonneg _
    have hBnonneg : 0 ≤ budget := hmnonneg.trans hmodulusBound
    have hprod : (2 * (modulus : ℝ)) * Q ≤ (C.slice.length i : ℝ) := by
      calc
        _ ≤ (2 * budget) * max 1 budget :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmodulusBound (by norm_num)) hQbound
            (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hBnonneg)
        _ ≤ _ := hlong i
    have hdiv := (le_div_iff₀ hQpos).mpr hprod
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm (C.slice.length i : ℝ)] using hdiv
  have hindexed : Sscore ≤ 𝔼 x : (∀ i, Fin (C.slice.length i)),
      (weight (C.physical (affineParentIntegerPoint C.slice.length
          (fun i => (C.slice.start i : ℤ)) C.step x)) *
        C.freezingOriginalValue candidate tests (affineParentIntegerPoint C.slice.length
          (fun i => (C.slice.start i : ℤ)) C.step x)).re := by
    rw [AllocatedExternalLocalCandidate.score, C.slice.expect_integerPoints C.step_pos,
      Complex.re_expect] at hscore
    have hpoint (x : ∀ i, Fin (C.slice.length i)) :
        affineParentIntegerPoint C.slice.length (fun i => (C.slice.start i : ℤ)) C.step x =
          C.slice.integerPoint x := by
      funext i
      simp only [affineParentIntegerPoint, ResidueBoxSlice.integerPoint,
        ResidueBoxSlice.point, Nat.cast_add, Nat.cast_mul]
    simpa only [C.freezingOriginalValue_eq candidate tests, hpoint] using hscore
  obtain ⟨T, hTlen, hTlong, i, j, herror, hweighted, hfrozen⟩ :=
    hselect (C.slice.length_pos_of_dense hsourceDense) hparent hwidth hlarge hindexed
  have hdenom : (0 : ℝ) < 4 * modulus * Q * (Fintype.card C.Variables + 1) := by
    have hmpos : (0 : ℝ) < modulus := Nat.cast_pos.mpr hmodulus
    have hQpos : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
    positivity
  refine ⟨C.slice.composeSlice T,
    C.slice.composeSlice_isDenseCommonStrideBox_of_fraction T C.step_pos hmodulus hsourceDense
      hθ hdenom hTlong,
    C.slice.composeSlice_integerPoints_subset T, i, j, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [C.slice.composeSlice_integerPoints_eq_affine_image T] at hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    simpa only [C.freezingOriginalValue_eq candidate tests] using herror x
  · intro u hu
    rw [C.slice.composeSlice_integerPoints_eq_affine_image T] at hu
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hu
    simpa only [C.freezingOriginalValue_eq candidate tests] using hweighted x
  · rw [C.slice.expect_composeSlice_integerPoints T C.step_pos hmodulus, Complex.re_expect]
    exact hfrozen
  · rw [C.slice.expect_composeSlice_integerPoints T C.step_pos hmodulus, Complex.re_expect]
    let orig := fun x : ∀ k, Fin (T.length k) =>
      weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
        C.freezingOriginalValue candidate tests
          (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)
    let froz := fun x : ∀ k, Fin (T.length k) =>
      weight (C.physical (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)) *
        C.freezingFrozenValue sectionMap hsectionLayer EF RF middle tests (left i) (right j)
          (T.affineIntegerPoint (fun k => (C.slice.start k : ℤ)) C.step x)
    have he := complex_expect_error_le Finset.univ froz orig herr (by
      intro x _
      simpa only [norm_sub_rev] using hweighted x)
    have hre := (Complex.re_le_norm _).trans he
    rw [Complex.sub_re, Complex.re_expect, Complex.re_expect] at hre
    have hmean : τ - Bweight * (Lip * ε) ≤ 𝔼 x, (orig x).re := by
      change τ < 𝔼 x, (froz x).re at hfrozen
      linarith
    simpa only [orig, C.freezingOriginalValue_eq candidate tests] using hmean

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalLocalGlobalMarkedCandidate
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalLocalCandidate
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (orbit : Dref.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))

noncomputable def ofRefilteredIncludedMark
    (hincluded : ∀ u ∈ C.slice.integerPoints,
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
        (realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u orbit)) =
      realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot)
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl
        (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          (C.chartValues u) markedMiddle)) :
    AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle where
  orbit := orbit
  mark_on_slice u hu := by
    apply realificationMap_incl_injective (hnil := Fmark.filtration.lowerCentralSeries_eq_bot)
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    rw [← D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref]
    exact hincluded u hu

noncomputable def ofNativeRefilteredMiddle
    (nativeMiddle : (D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : C.Variables => 1)).Group)
    (nativeMark : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fun _ : C.Variables => 1)).Group)
    (hprojection : D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) nativeMiddle = nativeMark)
    (hinclusion : ∀ u ∈ C.slice.integerPoints,
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u orbit) =
      D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ)) nativeMiddle)
    (hmarked : ∀ u ∈ C.slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ)) nativeMark =
      realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot)
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl
        (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          (C.chartValues u) markedMiddle)) :
    AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle :=
  ofRefilteredIncludedMark C D Fmark φ hφ W Dref Fref markedMiddle orbit
    (fun point hpoint =>
      (congrArg (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ)
        (hinclusion point hpoint)).trans
      ((D.filtration.realPolynomialGroupMap_value Fmark.filtration φ hφ
        (fun _ => 1) nativeMiddle (fun index => (point index : ℝ))).symm.trans
      ((congrArg (Fmark.filtration.adaptedPolynomialRealValueHom
        (fun _ : C.Variables => 1) (fun index => (point index : ℝ))) hprojection).trans
        (hmarked point hpoint))))

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
    {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
    {w : σ → ℕ} {W : LieSubalgebra ℚ F.AssociatedGraded}
    {g : (F.realification.adaptedPolynomialFiltration w).Group}
    {E R : F.RealPolynomialSymbolGroup w}
    (A : GlobalMarkedNativeFactors F b ω hF w W g E R)
    (Fref : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s d)
    (hFref : Fref.filtration = F.gradedRefiltration W)

noncomputable def markedMiddleOn : Fref.filtration.realification.PolynomialOrbit w :=
  (F.gradedRefiltration W).realPolynomialOrbitChangeFiltration
    Fref.filtration hFref w A.markedMiddle

@[simp] theorem markedMiddleOn_log :
    (A.markedMiddleOn Fref hFref).log = A.markedMiddle.log := rfl

theorem markedMiddleOn_values (t : σ → ℝ) :
    realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
      (Fref.filtration.realification.polynomialOrbitRealEval w t
        (A.markedMiddleOn Fref hFref)) =
      F.adaptedPolynomialRealValueHom w t A.middle := by
  apply NilpotentLieBCHGroup.ext
  exact congrArg NilpotentLieBCHGroup.coord (A.middle_values t)

end Erdos3.NilpotentLieFiltration.GlobalMarkedNativeFactors

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

namespace AllocatedExternalLocalChart

variable {M κ : Type*} [LieRing M] [LieAlgebra ℚ M] {s f : ℕ}
    {F : NilpotentLieFiltration M s} {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})}
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    {g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors F c ν hF (fullTaggedVariableWeight J) W g EF RF)
    (Fref : RationalFilteredNilmanifold (F.gradedRefiltrationSubalgebra W) s f)
    (hFref : Fref.filtration = F.gradedRefiltration W)

theorem globalMarked_middle_values (u : C.Variables → ℤ) :
    F.adaptedPolynomialRealValueHom (fun _ : C.Variables => 1) (fun i => (u i : ℝ))
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support factors.middle) =
      realificationMap (hnil := Fref.filtration.lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          (C.chartValues u) (factors.markedMiddleOn Fref hFref)) := by
  rw [F.adaptedPolynomialRealValueHom_weightedChart]
  have heval : (fun i => MvPolynomial.eval (fun j => (u j : ℝ))
      (integerSampledRealChart C.integerChart i)) =
      (fun i => (C.chartValues u i : ℝ)) := by
    funext i
    exact integerSampledRealChart_eval C.integerChart u i
  rw [heval, ← factors.markedMiddleOn_values Fref hFref,
    polynomialOrbitRealEval_integer]

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})}
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    (nativeMiddle : (D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : C.Variables => 1)).Group)
    (native : (D.filtration.gradedRefiltration W).realification.PolynomialOrbit
      (fun _ : C.Variables => 1))
    (hprojection : D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) nativeMiddle =
      Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support factors.middle)
    (hlog : map
      (realLieHomToRat (realificationLieHom
        (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap native.log =
      (nativeMiddle.coord : VectorPolynomial C.Variables ℚ (ℝ ⊗[ℚ] L)))

noncomputable def ofGlobalMarkedNativeMiddle :
    AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (factors.markedMiddleOn Fref hFref) :=
  ofNativeRefilteredMiddle C D Fmark φ hφ W Dref Fref
    (factors.markedMiddleOn Fref hFref)
    ((D.filtration.gradedRefiltration W).realPolynomialOrbitChangeFiltration
      Dref.filtration hDref (fun _ : C.Variables => 1) native)
    nativeMiddle _ hprojection
    (by
      intro u _
      rw [← polynomialOrbitRealEval_integer]
      apply NilpotentLieBCHGroup.ext
      exact congrArg NilpotentLieBCHGroup.coord
        (D.filtration.native_refiltered_orbit_real_value W
          (fun _ : C.Variables => 1) native _ hlog (fun i => (u i : ℝ))))
    (by
      intro u _
      exact C.globalMarked_middle_values factors Fref hFref u)

@[simp] theorem ofGlobalMarkedNativeMiddle_orbit_log :
    (ofGlobalMarkedNativeMiddle C D Fmark φ hφ W Dref hDref Fref hFref
      factors nativeMiddle native hprojection hlog).orbit.log = native.log := rfl

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedConcreteSlicedForecastModelLogs
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def preparedConcreteSlicedForecastCapLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog : ℝ) : ℝ :=
  preparedSlicedForecastCapLog m M nX Jalloc Pdim cost pRadius gainLog Qstride Pchart
    (cost + 1) (preparedSlicedForecastTailLog cost) cost (childLog + 1)

noncomputable def preparedConcreteSlicedForecastPeriodLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog E : ℝ) : ℝ :=
  actualSlicedForecastModelPeriodLog m (nX + m * M) nX
    (preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost)
    (allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
    (preparedSlicedForecastBadLog m nX Qstride gainLog) (cost + 1)
    (preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart)
    (cost + 1) (preparedSlicedForecastTailLog cost) cost (childLog + 1) E

noncomputable def preparedConcreteSlicedForecastTailSiteLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius childLog : ℝ) : ℝ :=
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + (allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
  slicedFixedUniformSiteLog m
    (preparedSlicedForecastTailLog cost + slicedFixedZeroGeometryLog D v cost 0 (childLog + 1)) 0

noncomputable def preparedConcreteSlicedForecastOutputLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog E : ℝ) : ℝ :=
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let v := P + (allocatedComparisonDimension m
    (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ) + pRadius + 1)
  let Pκ := preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart
  let Psm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let Esite := E + Pκ + Psm + 1 + ((nX + m * M + 1 : ℕ) : ℝ) * V
  let pAll := preparedSlicedForecastTailLog cost + V +
    slicedFixedZeroGeometryLog D v cost V (childLog + 1)
  let Q := slicedFixedUniformSiteLog m pAll (slicedFixedUniformAccuracyLog m D pAll Esite)
  siteExponentialOutputLog 1 Q

noncomputable def preparedConcreteSlicedForecastNativeLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride PF Pchart childLog E : ℝ) : ℝ :=
  let Dbase := allocatedComparisonDimension m (enlargedPreparedCommonSamplerDimension m M Jalloc : ℝ)
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let Psm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let O := preparedConcreteSlicedForecastOutputLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let Pspatial := (gainLog + nX + 8) + 8
  let Pcoord := pRadius + PF + Dbase
  let Pcut := pRadius + PF + 2 * Dbase + normalizedSiteCutoffBound + 1
  (V + D * O) + (Psm + D + O + 1 + Pspatial) + Pcoord + Pcut + 1

noncomputable def preparedConcreteSlicedForecastMassLog (m M nX Jalloc : ℕ)
    (Pdim cost pRadius gainLog Qstride Pchart childLog E : ℝ) : ℝ :=
  let P := preparedSlicedForecastSpatialBudget m M nX Jalloc Pdim cost
  let D := P + (layerTailDegree m + 1 : ℕ) + 1
  let Psm := forecastOriginalSmoothBudget m (P + (nX + 1) * (cost + 1))
  let V := preparedConcreteSlicedForecastPeriodLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  let O := preparedConcreteSlicedForecastOutputLog m M nX Jalloc
    Pdim cost pRadius gainLog Qstride Pchart childLog E
  preparedSlicedForecastJacobianLog m M nX pRadius gainLog Pchart +
    (Psm + ((nX + m * M + 1 : ℕ) : ℝ) * V + D * O + 1)

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j : Fin m, Submodule ℝ ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («J» := (fun j : Fin m => RankPreparationLayer.Coord (L j))) («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice ((fun j : Fin m => RankPreparationLayer.Coord (L j)) j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (L j))) (euclideanSubspace (U j)))]

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedCenteredMarginalProjectionBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

structure PreparedCenteredMarginalProjectionBounds (nX : ℕ) (Pmaster Plate Pproj : ℝ) : Prop where
  Pproj_nonneg : 0 ≤ Pproj
  master_projection : Pmaster ≤ Pproj
  late_projection : Plate ≤ Pproj
  m_projection : (m : ℝ) ≤ Pproj
  variables_projection : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj
  X_projection : (Fintype.card (Fin nX) : ℝ) ≤ Pproj
  frame_projection : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj
  coefficient_projection : ∀ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj
  I_projection : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj
  n_projection : ∀ j, (n j : ℝ) ≤ Pproj
  J_projection : ∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj
  Rinv_projection : ∀ j, (R j)⁻¹ ≤ Real.exp Pproj
  σinv_projection : ∀ j, (σ j)⁻¹ ≤ Real.exp Pproj
  S_projection : (S.value : ℝ) ≤ Real.exp Pproj
  root_projection : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ Real.exp Pproj
  profile_projection : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj

theorem preparedCenteredMarginalProjectionBounds
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {s : ℕ} {Pmaster Plate D : ℝ} (hMaster : 0 ≤ Pmaster) (hLate : Pmaster ≤ Plate)
    (hd : AllocatedComparisonDimensions (G := G) B (Fin (s + 1))
      (fun j : Fin m => (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1) : Type)) D)
    (hD : D ≤ Pmaster) {nX : ℕ} (hnX : (nX : ℝ) ≤ Pmaster)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp Pmaster)
    (hσLate : ∀ j, (σ j)⁻¹ ≤ Real.exp Plate)
    (hLLate : (S.value : ℝ) ≤ Real.exp Plate) :
    let r := preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m s)
      (s + 1) Pmaster Plate
    PreparedCenteredMarginalProjectionBounds B U basis S nX Pmaster Plate r.Pproj := by
  intro r
  have hproj : r.Pproj = 4 * (Plate + 8) ^ 2 := rfl
  have hPlate : 0 ≤ Plate := hMaster.trans hLate
  have hLproj : Plate ≤ r.Pproj := by
    nlinarith only [hproj, hPlate, sq_nonneg Plate]
  have hExpLate := Real.exp_le_exp.mpr hLproj
  have hPproj : Pmaster ≤ r.Pproj := hLate.trans hLproj
  have h2Pproj : 2 * Pmaster ≤ r.Pproj := by
    nlinarith only [hproj, hPlate, hLate, sq_nonneg Plate]
  have hframeProj : (2 * Pmaster + 1) * Pmaster ≤ r.Pproj := by
    have hsq : Pmaster^2 ≤ Plate^2 := pow_le_pow_left₀ hMaster hLate 2
    nlinarith only [hproj, hPlate, hLate, hsq, sq_nonneg Plate]
  have hExp := Real.exp_le_exp.mpr hPproj
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * Pmaster :=
    (preparedModularGeneralDetector_variable_count B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd).trans
        (by linarith only [hD])
  have hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ r.Pproj := by
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact (mul_le_mul (add_le_add_left hvars 1) hnX (Nat.cast_nonneg _) (by positivity)).trans
      (by simpa only [add_comm] using hframeProj)
  obtain ⟨hI, hn⟩ := preparedModularGeneralDetector_layer_axes B
    (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) hd
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ r.Pproj :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U basis o j)).trans
      (hd.axes.trans (hD.trans hPproj))
  have hWproj : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ Real.exp r.Pproj :=
    (preparedModularGeneralDetector_physical_root B
      (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)) U basis S hd
        (hD.trans hLate) hLLate).trans
      (Real.exp_le_exp.mpr (by nlinarith only [hproj, hPlate, hLate, sq_nonneg Plate]))
  exact {
    Pproj_nonneg := hMaster.trans hPproj
    master_projection := hPproj
    late_projection := hLproj
    m_projection := hd.degree.trans (hD.trans hPproj)
    variables_projection := hvars.trans h2Pproj
    X_projection := by simpa only [Fintype.card_fin] using hnX.trans hPproj
    frame_projection := hframe
    coefficient_projection := fun j => (hd.coefficients j).trans (hD.trans hPproj)
    I_projection := fun j => (hI j).trans (hD.trans hPproj)
    n_projection := fun j => (hn j).trans (hD.trans hPproj)
    J_projection := hJ
    Rinv_projection := fun j => (hRP j).trans hExp
    σinv_projection := fun j => (hσLate j).trans hExpLate
    S_projection := hLLate.trans hExpLate
    root_projection := hWproj
    profile_projection := ((hd.profile.trans (hD.trans hPproj)).trans
      (by linarith [Real.add_one_le_exp r.Pproj])) }

end Erdos3.VectorPolynomial

end

end OAI

end


