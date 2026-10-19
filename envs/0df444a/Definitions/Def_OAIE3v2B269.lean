-- Prove2me | Definitions.Def_OAIE3v2B269
-- name    : OAIE3v2B269
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:51:22.601699+00:00
-- url     : https://prove2.me/theorems/54a35e17-bfbc-44ae-8c3b-9eba88acd821
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 279 of 311
-- statement:
--   Definitions bundle 279 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B305` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateAdaptedOptionQuotientFactors.lean`, `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidateTaggedPairUniformFactors.lean`, `Lattices/AllocatedCertifiedAffinePhysicalSlowBound.lean`, `Lattices/CertifiedAffineCutoffCost.lean`, `Linear/ActualCandidateSlowProjectionMass.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B305

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
namespace OAI

section

namespace Erdos3

theorem ResidueBoxSlice.integerPoints_classical_eq {V : Type*} [Finite V]
    {N : V → ℕ} {q : ℕ} (t : Fintype V) (d : DecidableEq V) (slice : ResidueBoxSlice N q) :
    @ResidueBoxSlice.integerPoints V N q t d slice =
      @ResidueBoxSlice.integerPoints V N q (Fintype.ofFinite V) (Classical.decEq V) slice := by
  cases Subsingleton.elim t (Fintype.ofFinite V)
  cases Subsingleton.elim d (Classical.decEq V)
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAdaptedOptionQuotientFactors
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t u d n : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (I : LieIdeal ℚ L) (hI : D.filtration.layer (t + 1) ≤ I.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ I) t n)
    (hQ : Q.filtration = D.filtration.quotientLie I hI)
    (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0) {w : σ → ℕ}

theorem exists_prescribed_marked_quotientOrbit_lift
    (G : NilpotentLieFiltration M u)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hmarked : map
      ((realificationLieHom (quotientInducedMark I π hker)).toLinearMap.restrictScalars ℚ)
      q.log = marked.log) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.quotientOrbit I hI Q hQ g = q ∧
      map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log = marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot) (lieQuotientMap I)
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot) (hM := G.lowerCentralSeries_eq_bot) π
          (D.filtration.realification.polynomialOrbitRealEval w z g) =
            G.realification.polynomialOrbitRealEval w z marked := by
  obtain ⟨g, hq⟩ := D.quotientOrbit_surjective I hI Q hQ q
  have hformal : map ((realificationLieHom π).toLinearMap.restrictScalars ℚ) g.log =
      marked.log := by
    rw [← D.quotientOrbit_mark I hI Q hQ π hker g, hq]
    exact hmarked
  refine ⟨g, hq, hformal, ?_, ?_⟩
  · intro z
    rw [← hq]
    exact (D.quotientOrbit_realEval I hI Q hQ g z).symm
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom π (eval₂ z g.log) = eval₂ z marked.log
    rw [← hformal]
    exact (eval₂_map (realificationLieHom π).toLinearMap z g.log).symm

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d dQ : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)

include hQ in

theorem quotientMap_mem_layer (j : ℕ) (x : L) (hx : x ∈ D.filtration.layer j) :
    lieQuotientMap ideal x ∈ Q.filtration.layer j := by
  rw [hQ]
  exact D.filtration.quotientLie_mem ideal hI hx

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration

variable {Pivot : Type v} [Fintype Pivot]
    {L : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ideal : LieIdeal ℚ L) (hI : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hI)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))

include hQ in

theorem optionQuotientMap_mem_layer (k : ℕ)
    (x : ∀ i : Option Pivot, optionLieSpace L P i)
    (hx : x ∈ (optionProduct D partners).filtration.layer k) :
    optionMarkedLieMap (lieQuotientMap ideal) x ∈
      (optionProduct Q partners).filtration.layer k := by
  apply (mem_pi_layer (fun i => (optionFactors Q partners i).filtration) k _).mpr
  intro i
  cases i with
  | none =>
    exact D.quotientMap_mem_layer ideal hI Q hQ k (x none)
      ((mem_pi_layer (fun i => (optionFactors D partners i).filtration) k x).mp hx none)
  | some i =>
    exact (mem_pi_layer (fun i => (optionFactors D partners i).filtration) k x).mp hx (some i)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairUniformFactors
namespace OAI

universe u

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_nativeOptionPair_weighted_common_orbit_factors (s : ℕ) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧
    ∀ {J α σ Ω : Type*} [Fintype J] [Fintype α] [Fintype σ] [Fintype Ω]
      {β : J → Type*} [∀ j, Fintype (β j)]
      {L : Type u} {M : J → Type u}
      [LieRing L] [LieAlgebra ℚ L] [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
      {d₀ : ℕ} {d : J → ℕ}
      (D : RationalFilteredNilmanifold L s d₀)
      (E : ∀ j, RationalFilteredNilmanifold (M j) s (d j))
      (e : Basis α ℚ (∀ i : Option J, optionLieSpace L M i)) (ω : α → ℕ)
      (hF : ∀ k, (optionProduct D E).filtration.layer k =
        Submodule.span ℚ (e '' {i | k ≤ ω i}))
      (b : ∀ j, Basis (β j) ℚ (PairAlgebra L (M j))) (ν : ∀ j, β j → ℕ)
      (hG : ∀ j k, (pi (pairModels D (E j))).filtration.layer k =
        Submodule.span ℚ (b j '' {i | k ≤ ν j i}))
      {height : ℕ}, 1 ≤ height →
      (∀ j i k, RationalHeightLE ((b j).repr (optionPairProjection j (e k)) i) height) →
    ∀ {p : ℝ}, 0 ≤ p → (Fintype.card α : ℝ) ≤ p →
      (∀ j, (Fintype.card (β j) : ℝ) ≤ p) →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (height : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ p) →
      let P := p + (p + C) ^ C
      ∀ side : σ → ℝ, (∀ i, Real.exp ((P + 2) ^ A) ≤ side i) →
      ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      ∀ (g : Ω → ∀ i : Option J,
          (optionFactors D E i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (η : J → L →ₗ[ℚ] ℚ) (θ : ∀ j, M j →ₗ[ℚ] ℚ),
        (∀ a ∈ H, ∀ j,
          (pi (pairModels D (E j))).filtration.ControlledSymbolFactorization
            (b j) (ν j) (hG j) (pairFrequency (η j) (θ j)) side
            (pairOrbitSymbol D (E j) (g a none) (g a (some j)) (b j) (ν j) (hG j)) p) →
        let q := (P + 2) ^ A + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
        ∃ (W : LieSubalgebra ℚ (optionProduct D E).filtration.AssociatedGraded)
          (v : Fin (Fintype.card α) → (optionProduct D E).filtration.AssociatedGraded)
          (m : ℕ) (H' : Finset Ω),
          H' ⊆ H ∧ 0 < outer.mass H' ∧
          Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
          Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
          BasisGradedSubmodule ((optionProduct D E).filtration.associatedGradedBasis e ω hF)
            ω W.toSubmodule ∧
          (∀ i k, rationalLogHeight
            (((optionProduct D E).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
          (∀ j x, x ∈ (optionProduct D E).filtration.realGradedRefiltrationLayer W s →
            realifyFunctional ((pairFrequency (η j) (θ j)).comp
              (optionPairProjection j).toLinearMap) x = 0) ∧
          0 < m ∧ (m : ℝ) ≤ Real.exp q ∧
          ∀ a ∈ H', (optionProduct D E).filtration.HasCommonRefilteredOrbitFactors
            e ω hF side q m W
            ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
              (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩ := by
  obtain ⟨C, hC, hbudget⟩ := exists_controlledProjectionUniformBudget_power s
  obtain ⟨A, hA, hcommon⟩ := exists_weighted_common_refiltered_orbit_factors s
  refine ⟨C, A, hC, hA, ?_⟩
  intro J α σ Ω _ _ _ _ β _ L M _ _ _ _ d₀ d D E e ω hF b ν hG
    height hheight hentries p hp hα hβ hσ hJ hheightp hstructure P side hside
    outer H hH g η θ hfactor
  have hpP : p ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_right (by positivity)
  have hliftP : (p + C) ^ C ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_left hp
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  apply hcommon (optionProduct D E).filtration e ω hF
    (fun j => (pairFrequency (η j) (θ j)).comp (optionPairProjection j).toLinearMap)
    (hp.trans hpP) (hα.trans hpP) (hσ.trans hpP) (hJ.trans hpP)
    (fun i j k => (hstructure i j k).trans hpP) side hside outer H hH
    (fun a => ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
      (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩)
  intro a ha j
  obtain ⟨U, hU⟩ := (hfactor a ha j).exists_fastWitness
    (pi (pairModels D (E j))).filtration (b j) (ν j) (hG j)
  have hpull := (optionProduct D E).filtration.controlledSymbolFactorizationAtFast_projection_of_dimensions
    e ω hF (pi (pairModels D (E j))).filtration (b j) (ν j) (hG j)
    (optionPairProjection j) (optionPairProjection_layers D E j)
    (optionPairProjection_layer_surjective D E j) hheight (hentries j)
    hp hα (hβ j) hσ hheightp side hsidepos
    ((optionProduct D E).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
      ⟨⟨(piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).log,
        (piRealOrbit (fun i => (optionFactors D E i).filtration) (g a)).property⟩⟩)
    (pairFrequency (η j) (θ j)) U
    (by rw [optionPairProjection_jointOrbitSymbol D E j e ω hF (b j) (ν j) (hG j)]; exact hU)
  obtain ⟨m, E₀, P₀, R₀, v₀, hdata⟩ := hpull.mono
    (optionProduct D E).filtration e ω hF ((hbudget p hp).trans hliftP) hsidepos
  exact ⟨m, E₀, P₀, R₀, _, v₀, hdata⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedAffineCutoffCost
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_quotient_bound
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ))
    (hQU : U j ≤ LinearMap.ker Q) {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (x : LayerSamplerVariables G I n B → ℝ)
    (hx : ∀ k, |x k| ≤ layerSamplerBox B U b S k) (t : T) :
    |Q (fun i => MvPolynomial.eval x (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample)
        (Sum.inr ⟨j, i⟩))) t| ≤
      CQ * (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) := by
  let mixed : J j → ℝ := fun i => mixedPolynomialPoint (euclideanSubspace (U j))
    (b j) (o j) Subtype.val (sample j).1 (sample j).2 x i
  let integer : J j → ℝ := fun i => MvPolynomial.eval x (integerSampledRealChart
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) (Sum.inr ⟨j, i⟩))
  have hrem : eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) - (c j).val =
      mixed + integer := by
    funext i
    exact h.integerFullChart_remainder B U b hb o S hR hσ poly hm hp c a v sample read x j i
  have hretained : eval (fun z => (jointIntegerFrame (a, v) none z : ℝ) +
      ∑ k, (jointIntegerFrame (a, v) (some k) z : ℝ) * x k) (poly j) - (c j).val ∈ U j :=
    (U j).sub_mem ((eval_mem_iff_coefficients (U j) (poly j)).mpr (hm j) _) (c j).property
  have hsum : Q mixed + Q integer = 0 := by
    rw [← map_add, ← hrem]
    exact hQU hretained
  have hquotient : Q integer = -Q mixed := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using hsum
  have hnonneg : 0 ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * R j) :=
    mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j).le)
  have hnorm : ‖mixed‖ ≤ C j * (((Fintype.card (I j) : ℝ) + 1) * R j) := by
    apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
    intro i
    simpa only [mixed, Real.norm_eq_abs] using
      allocatedLayerSupported_polynomial_bound B U b o hR hσ S hσ1 C hC hchart
        j (sample j) (h.2.2.1 j).2 x hx i
  change |Q integer t| ≤ _
  calc
    _ = |Q mixed t| := by rw [hquotient]; simp
    _ ≤ CQ * ‖mixed‖ := hQ mixed t
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm hCQ

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFrozenFullChart_anchor_bound
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) {T : Type*} (Q : (J j → ℝ) →ₗ[ℝ] (T → ℝ))
    (hQU : U j ≤ LinearMap.ker Q) {CQ : ℝ} (hCQ : 0 ≤ CQ)
    (hQ : ∀ x t, |Q x t| ≤ CQ * ‖x‖)
    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, |(fixed i : ℝ)| ≤ layerSamplerBox B U b S i.val) (t : T) :
    |Q (fun i => MvPolynomial.eval (0 : {k // keep k} → ℝ) (integerSampledRealChart
      (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
        (Sum.inr ⟨j, i⟩))) t| ≤
      CQ * (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) := by
  have heval (i : J j) : MvPolynomial.eval (0 : {k // keep k} → ℝ)
      (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed)
          (Sum.inr ⟨j, i⟩)) =
      MvPolynomial.eval (finiteSplitPoint keep 0 (fun i => (fixed i : ℝ)))
        (integerSampledRealChart
          (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample)
            (Sum.inr ⟨j, i⟩)) := by
    change MvPolynomial.eval _ (integerSampledRealChart
      (fun z => freezePolynomial keep fixed
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) _) = _
    rw [integerSampledRealChart_freeze, freezePolynomial_eval]
  simp_rw [heval]
  apply h.integerFullChart_quotient_bound B U b hb o S hR hσ poly hm hσ1 C hC hchart hp
    c a v sample read j Q hQU hCQ hQ _ _ t
  intro k
  by_cases hk : keep k
  · simpa [finiteSplitPoint, hk] using
      (zero_le_one.trans (layerSamplerBox_one_le B U b S k))
  · simpa [finiteSplitPoint, hk] using hfixed ⟨k, hk⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalLocalChart
variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem fixed_abs_le_box (i : {i // ¬C.keep i}) :
    |(C.fixed i : ℝ)| ≤ layerSamplerBox B U b S i.val := by
  rw [abs_of_nonneg (by exact_mod_cast (C.fixed_in_box i).1),
    allocatedParameterBox_side_eq B U b S]
  exact_mod_cast (C.fixed_in_box i).2.le

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

omit [Fintype X] [∀ j, Fintype (J j)]
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem retained_tag_le_of_product_constraint
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
    (V : ∀ j, Submodule ℝ (J j → ℝ))
    (hK : K = {t | ∀ j, (fun i => t (Sum.inr ⟨j,i⟩)) ∈ V j})
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j,i⟩)) ∈ U j) → t ∈ K)
    (j : Fin m) : U j ≤ V j := by
  intro x hx
  let t : X ⊕ (Σ k, J k) → ℝ :=
    Sum.elim (fun _ => 0) (fun i => (Pi.single j x : ∀ k, J k → ℝ) i.1 i.2)
  have ht : ∀ k, (fun i => t (Sum.inr ⟨k,i⟩)) ∈ U k := by
    intro k
    by_cases hk : k = j
    · subst k
      simpa only [t, Sum.elim_inr, Pi.single_eq_same] using hx
    · simpa only [t, Sum.elim_inr, Pi.single_eq_of_ne hk, Pi.zero_apply, Pi.zero_def] using (U k).zero_mem
  have htK := hretained t ht
  rw [hK] at htK
  simpa only [t, Sum.elim_inr, Pi.single_eq_same] using htK j

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

structure CertifiedAffineRefinement
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (p : ℝ) where
  space : ∀ j, Submodule ℚ (J j → ℚ)
  projection : ∀ j, Matrix (J j) (J j) ℚ
  denominator : Fin m → ℕ
  constraint : K = {t | ∀ j, (fun i => t (Sum.inr ⟨j,i⟩)) ∈ realRationalCoordinateSpan (space j)}
  range_eq : ∀ j, LinearMap.range (fullTaggedRealMatrixProjection J projection j) =
    realRationalCoordinateSpan (space j)
  fixes_space : ∀ j x, x ∈ realRationalCoordinateSpan (space j) →
    fullTaggedRealMatrixProjection J projection j x = x
  projection_height : ∀ j i a, rationalLogHeight (projection j i a) ≤
    ((p + ((p+2)^2+2)^63) + 2)^8
  denominator_pos : ∀ j, 0 < denominator j
  denominator_bound : ∀ j, (denominator j : ℝ) ≤ Real.exp (certifiedAffineCenterBudget p)
  projection_grid : ∀ j i a, ∃ z : ℤ, (denominator j : ℝ) * (projection j i a : ℝ) = z
  translate : ∀ j, J j → ℝ
  translate_bound : ∀ j i, |translate j i| ≤ Real.exp (certifiedAffineCenterBudget p)
  translate_grid : ∀ j i, ∃ z : ℤ, (denominator j : ℝ) * translate j i = z
  translate_fixed : ∀ j, rationalTagProjectionComplement (projection j) (translate j) = translate j
  refinement : P.Refinement cost
    (Real.exp (-((2*certifiedAffineCenterBudget p+3)^3)) * massThreshold) scoreThreshold
  slice_points : ∀ z : refinement.problem.productive,
    (refinement.problem.chart z).slice.integerPoints =
      (P.chart ⟨z.val, refinement.subset z.property⟩).slice.integerPoints
  chart_fixed : ∀ z : refinement.problem.productive, ∀ x : (refinement.problem.chart z).Variables → ℝ,
    (fun v => MvPolynomial.eval
      (fun i => MvPolynomial.eval x (integerSampledRealChart (refinement.problem.chart z).integerChart i))
      (fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J projection) translate v)) =
      (fun i => MvPolynomial.eval x (integerSampledRealChart (refinement.problem.chart z).integerChart i))

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ActualCandidateSlowProjectionMass
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def fullTaggedCenteredCoordinates
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (a : Σ j, J j) : MvPolynomial X ℝ :=
  coordinate (LinearMap.proj a.2 : (J a.1 → ℝ) →ₗ[ℝ] ℝ).toAddMonoidHom (poly a.1) -
    C (c a.1 a.2)

noncomputable def fullTaggedSlowProjectionChart
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (z : X ⊕ (Σ j, J j)) : MvPolynomial (X ⊕ (Σ j, J j)) ℝ :=
  aeval (fullTaggedLinearMapChart J P)
    (normalizedRealPolynomialChart N (fullTaggedCenteredCoordinates J poly c) z)

@[simp] theorem fullTaggedSlowProjectionChart_inl
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ) (x : X) :
    fullTaggedSlowProjectionChart J P N poly c (Sum.inl x) =
      C ((N x)⁻¹) * MvPolynomial.X (Sum.inl x) := by
  simp [fullTaggedSlowProjectionChart, fullTaggedLinearMapChart]

@[simp] theorem fullTaggedSlowProjectionChart_inr
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (j : Fin m) (i : J j) :
    fullTaggedSlowProjectionChart J P N poly c (Sum.inr ⟨j, i⟩) =
      fullTaggedLinearMapChart J P (Sum.inr ⟨j, i⟩) -
        rename Sum.inl (fullTaggedCenteredCoordinates J poly c ⟨j, i⟩) := by
  rw [fullTaggedSlowProjectionChart, normalizedRealPolynomialChart_inr,
    map_sub, aeval_X, aeval_rename, rename_eq_aeval]
  rfl

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem allocatedRecoveredIntegerFullChart_slowProjection_spatial
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : X) :
    aeval (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
      (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inl x)) =
      C ((N x)⁻¹) *
        affineFramePolynomial (fun k z => (jointIntegerFrame (a, v) k z : ℝ)) x := by
  rw [fullTaggedSlowProjectionChart_inl, map_mul, aeval_C, aeval_X]
  change C ((N x)⁻¹) * MvPolynomial.map (Int.castRingHom ℝ)
    (affineFramePolynomial (jointIntegerFrame (a, v)) x) = _
  rw [affineFramePolynomial_map]
  rfl

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_slowProjection_tag
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ U j → P j x = x) (N : X → ℝ)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (j : Fin m) (i : J j) :
    aeval (integerSampledRealChart
      (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
      (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inr ⟨j, i⟩)) =
      -(∑ k : J j, P j (Pi.single k 1) i •
        mixedLiftPolynomial (euclideanSubspace (U j)) (b j) (o j) Subtype.val (sample j) k) := by
  rw [fullTaggedSlowProjectionChart_inr, map_sub, aeval_rename]
  simp only [fullTaggedLinearMapChart, map_sum, map_smul, aeval_X]
  exact sum_projection_remainder_eq (P j) (U j) (hP j) (poly j) (hm j)
    (c j).val (c j).property _ _ _
    (fun k => h.integerFullChart_polynomial_remainder B U b hb o S hR hσ poly hm
      hp c a v sample read j k) i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem allocatedRecoveredIntegerFullChart_slowProjection_spatial_mass
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℝ)
    (hN : ∀ x, 0 < N x) (T : LayerSamplerVariables G I n B → ℝ)
    (hT : ∀ k, 0 ≤ T k)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes T
      (aeval (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
        (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inl x)))) ≤
      |(jointIntegerFrame (a, v) none x : ℝ)| / N x +
        (N x)⁻¹ * ∑ k, |(jointIntegerFrame (a, v) (some k) x : ℝ)| * T k := by
  rw [allocatedRecoveredIntegerFullChart_slowProjection_spatial]
  exact spatialAffineFull_scaled_inv_mul_mass_le _ T hT x (N x) (hN x)

theorem allocatedRecoveredIntegerFullChart_slowProjection_spatial_mass_of_support
    [Fintype X]
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (x : X) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
        (fullTaggedSlowProjectionChart J P (fun x => (N x : ℝ)) poly
          (fun j => (c j).val) (Sum.inl x)))) ≤
      |(jointIntegerFrame (a, v) none x : ℝ)| / (N x : ℝ) + τ / 8 := by
  have hT : ∀ k, 0 ≤ layerSamplerBox B U b S k :=
    fun k => (by norm_num : (0 : ℝ) ≤ 1).trans (layerSamplerBox_one_le B U b S k)
  have hn : ∀ x, (0 : ℝ) < N x := fun x => by exact_mod_cast hN x
  apply (allocatedRecoveredIntegerFullChart_slowProjection_spatial_mass B U b o poly hm P
    (fun x => (N x : ℝ)) hn (layerSamplerBox B U b S) hT c a v sample x).trans
  apply add_le_add le_rfl
  have hsum := narrowSpatial_frame_slope_sum
    (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hξ N hN
    (layerSamplerBox B U b S) hT (layerSamplerBox_sum_le_zero_root_budget B U b S) v hv x
  change (N x : ℝ)⁻¹ * (∑ k, |(v (some k, x) : ℝ)| * layerSamplerBox B U b S k) ≤ _
  calc
    _ ≤ (N x : ℝ)⁻¹ * (τ * (N x : ℝ) / 8) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (hn x).le)
    _ = τ / 8 := by field_simp [(hn x).ne']

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_slowProjection_tag_mass
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ U j → P j x = x) (N : X → ℝ)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (j : Fin m) (i : J j) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
        (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inr ⟨j, i⟩)))) ≤
      (∑ k : J j, |P j (Pi.single k 1) i|) *
        (((m + 1 : ℕ) : ℝ) *
          ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) := by
  rw [h.integerFullChart_slowProjection_tag B U b hb o S hR hσ poly hm P hP N
    hp c a v sample read j i]
  apply normalizedMass_neg_linearCombination_le
  intro k
  exact allocatedLayerSupported_normalized_mass_uniform B U b o hR hσ S hσ1 C hC hchart
    hsmall j (sample j) (h.2.2.1 j).2 k

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_slowProjection_mass
    [Fintype X]
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ U j → P j x = x)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (M : ℝ)
    (hcenter : ∀ x, |(jointIntegerFrame (a, v) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤ M)
    (hrows : ∀ j i, (∑ k : J j, |P j (Pi.single k 1) i|) *
      (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ≤ M)
    (z : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (layerSamplerBox B U b S)
      (aeval (integerSampledRealChart
        (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample))
        (fullTaggedSlowProjectionChart J P (fun x => (N x : ℝ)) poly
          (fun j => (c j).val) z))) ≤ M := by
  cases z with
  | inl x =>
    exact (allocatedRecoveredIntegerFullChart_slowProjection_spatial_mass_of_support B U b o S
      poly hm P N hN hτ hξ c a v hv sample x).trans (hcenter x)
  | inr z =>
    exact (h.integerFullChart_slowProjection_tag_mass B U b hb o S hR hσ poly hm P hP
      (fun x => (N x : ℝ)) hp c a v sample read hσ1 C hC hchart hsmall z.1 z.2).trans
      (hrows z.1 z.2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_slowProjection_mass
    [Fintype X]
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j x, x ∈ U j → P j x = x)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (M : ℝ)
    (hcenter : ∀ x, |(jointIntegerFrame (a, v) none x : ℝ)| / (N x : ℝ) + τ / 8 ≤ M)
    (hrows : ∀ j i, (∑ k : J j, |P j (Pi.single k 1) i|) *
      (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ≤ M)
    (keep : LayerSamplerVariables G I n B → Prop)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, |(fixed i : ℝ)| ≤ layerSamplerBox B U b S i.val)
    (z : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
      (aeval (integerSampledRealChart
        (allocatedFrozenIntegerFullChart B U b o poly hm c a v sample keep fixed))
        (fullTaggedSlowProjectionChart J P (fun x => (N x : ℝ)) poly
          (fun j => (c j).val) z))) ≤ M := by
  have hT : ∀ k, 0 < layerSamplerBox B U b S k :=
    fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  apply (normalizedMass_aeval_frozen_integer_chart_le
    (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample) keep
    (layerSamplerBox B U b S) hT fixed hfixed _).trans
  exact h.integerFullChart_slowProjection_mass B U b hb o S hR hσ poly hm P hP N hN
    hτ hξ hp c a v hv sample read hσ1 C hC hchart hsmall M hcenter hrows z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedSlowProjectionChart_physical_spatial
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X → ℤ) (a : X) :
    MvPolynomial.eval (fun z => (fullTaggedPhysicalIntegerPoint J poly c x z : ℝ))
      (fullTaggedSlowProjectionChart J P (fun z => (N z : ℝ)) poly c (Sum.inl a)) =
      (N a : ℝ)⁻¹ * (x a : ℝ) := by
  simp [fullTaggedPhysicalIntegerPoint]

theorem fullTaggedSlowProjectionChart_physical_spatial_abs_le_one [Fintype X]
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X → ℤ) (hx : x ∈ integerBox N) (a : X) :
    |MvPolynomial.eval (fun z => (fullTaggedPhysicalIntegerPoint J poly c x z : ℝ))
      (fullTaggedSlowProjectionChart J P (fun z => (N z : ℝ)) poly c (Sum.inl a))| ≤ 1 := by
  rw [fullTaggedSlowProjectionChart_physical_spatial]
  have ha := (mem_integerBox N x).mp hx a
  have hx0 : (0 : ℝ) ≤ x a := by exact_mod_cast ha.1
  have hxN : (x a : ℝ) < N a := by exact_mod_cast ha.2
  have hN : (0 : ℝ) < N a := lt_of_le_of_lt hx0 hxN
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hN.le) hx0), mul_comm, ← div_eq_mul_inv]
  exact (div_le_one hN).mpr hxN.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

omit [∀ j, Fintype (J j)] in

theorem fullTaggedCenteredCoordinates_eval
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X → ℝ) (j : Fin m) (i : J j) :
    MvPolynomial.eval x (fullTaggedCenteredCoordinates J poly c ⟨j, i⟩) =
      eval x (poly j) i - c j i := by
  have he : eval₂ x (poly j) = eval x (poly j) := by
    simpa using eval₂_algebraMap (S := ℝ) x (poly j)
  rw [fullTaggedCenteredCoordinates, map_sub, eval_C, ← coordinate_eval₂, he]
  rfl

theorem fullTaggedSlowProjectionChart_physical_tag
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ))
    (hP : ∀ j y, y ∈ U j → P j y = y) (N : X → ℝ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j α, coefficients (poly j) α ∈ U j)
    (c : ∀ j, U j) (x : X → ℤ) (j : Fin m) (i : J j) :
    MvPolynomial.eval
      (fun z => (fullTaggedPhysicalIntegerPoint J poly (fun j => (c j).val) x z : ℝ))
      (fullTaggedSlowProjectionChart J P N poly (fun j => (c j).val) (Sum.inr ⟨j, i⟩)) =
      P j (fun a => (round (eval (fun z => (x z : ℝ)) (poly j) a - (c j).val a) : ℝ) -
        (eval (fun z => (x z : ℝ)) (poly j) a - (c j).val a)) i := by
  have hmem : eval (fun z => (x z : ℝ)) (poly j) - (c j).val ∈ U j :=
    (U j).sub_mem ((eval_mem_iff_coefficients (U j) (poly j)).mpr (hm j) _) (c j).property
  rw [fullTaggedSlowProjectionChart_inr, map_sub, fullTaggedLinearMapChart_eval_tag,
    MvPolynomial.eval_rename]
  change P j (fun a => (round (eval (fun z => (x z : ℝ)) (poly j) a - (c j).val a) : ℝ)) i -
    MvPolynomial.eval (fun z => (x z : ℝ))
      (fullTaggedCenteredCoordinates J poly (fun j => (c j).val) ⟨j, i⟩) = _
  rw [fullTaggedCenteredCoordinates_eval]
  change _ = P j ((fun a => (round (eval (fun z => (x z : ℝ)) (poly j) a - (c j).val a) : ℝ)) -
    (eval (fun z => (x z : ℝ)) (poly j) - (c j).val)) i
  rw [map_sub, hP j _ hmem, Pi.sub_apply, Pi.sub_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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

namespace AllocatedExternalLocalChart

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem slowProjection_mass
    (P : ∀ j, Matrix (J j) (J j) ℚ)
    (hP : ∀ j x, x ∈ U j → fullTaggedRealMatrixProjection J P j x = x)
    {d H : ℝ} (hd : 0 ≤ d)
    (hheight : ∀ j i a, rationalLogHeight (P j i a) ≤ H)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d)
    (hτ1 : τ ≤ 1) (hξ1 : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (z : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes
      (fun i : C.Variables => layerSamplerBox B U b S i.val)
      (aeval (integerSampledRealChart C.integerChart)
        (fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J P)
          (fun x => (N x : ℝ)) poly (fun j => (C.centerLift j).val) z))) ≤
      actualCandidateSlowProjectionMassBudget m
        (Fintype.card (LayerSamplerVariables G I n B)) d H := by
  have hv : C.path.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 := by
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using C.path.2.property
  apply C.recovered.integerFullChart_frozen_slowProjection_mass B U b hb o S hR hσ poly hm
    (fullTaggedRealMatrixProjection J P) hP N A.size_pos A.trim_pos hξ1 hp
    C.centerLift C.path.1.val C.path.2.val hv C.sample C.read hσ1 Cgeo hCgeo hchart hsmall
    (actualCandidateSlowProjectionMassBudget m
      (Fintype.card (LayerSamplerVariables G I n B)) d H) ?_ ?_
    C.keep C.fixed C.fixed_abs_le_box z
  · intro x
    exact (A.path_spatial_center_mass_le hτ1 C.path x).trans
      (actualCandidateSlowProjectionMassBudget_two_le _ _ hd)
  · intro j i
    have hrow := fullTaggedRealMatrixProjection_slow_mass_row_le J P hheight hdim
      (Fintype.card (LayerSamplerVariables G I n B)) j i
    unfold actualCandidateSlowProjectionMassBudget
    linarith

theorem slowProjection_mass_sides
    (P : ∀ j, Matrix (J j) (J j) ℚ)
    (hP : ∀ j x, x ∈ U j → fullTaggedRealMatrixProjection J P j x = x)
    {d H : ℝ} (hd : 0 ≤ d)
    (hheight : ∀ j i a, rationalLogHeight (P j i a) ≤ H)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ d)
    (hτ1 : τ ≤ 1) (hξ1 : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (z : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes (fun i : C.Variables => (A.sides i.val : ℝ))
      (aeval (integerSampledRealChart C.integerChart)
        (fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J P)
          (fun x => (N x : ℝ)) poly (fun j => (C.centerLift j).val) z))) ≤
      actualCandidateSlowProjectionMassBudget m
        (Fintype.card (LayerSamplerVariables G I n B)) d H := by
  have hT : (fun i : C.Variables => (A.sides i.val : ℝ)) =
      (fun i : C.Variables => layerSamplerBox B U b S i.val) := by
    funext i
    exact (allocatedParameterBox_side_eq B U b S i.val).symm
  rw [hT]
  exact C.slowProjection_mass P hP hd hheight hdim hτ1 hξ1 hp hσ1 Cgeo hCgeo hchart hsmall z

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCertifiedAffinePhysicalSlowBound
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.CertifiedAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
    (C : P.CertifiedAffineRefinement K pAffine)

local notation "wt" => fullTaggedVariableWeight (X := X) J

noncomputable def globalChart :
    (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ :=
  fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J C.projection) C.translate

noncomputable def slowChart :
    (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ :=
  fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J C.projection)
    (fun i => (N i : ℝ)) poly (fun j => (P.centerLift j).val)

noncomputable def commonDenominator : ℕ := ∏ j, C.denominator j

theorem globalChart_support (i : X ⊕ (Σ j, J j)) :
    C.globalChart i ∈ weightedSupportLE wt (wt i) :=
  fullTaggedAffineMapChart_support J _ _ i

theorem globalChart_top (i : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent wt (wt i) (C.globalChart i) =
      fullTaggedLinearMapChart J (fullTaggedRealMatrixProjection J C.projection) i :=
  fullTaggedAffineMapChart_top J _ _ i

theorem globalChart_top_mem (x : X ⊕ (Σ j, J j) → ℝ) :
    (fun i => MvPolynomial.eval x
      (weightedHomogeneousComponent wt (wt i) (C.globalChart i))) ∈ K := by
  apply fullTaggedAffineMapChart_top_mem_set J _ _
    (fun j => realRationalCoordinateSpan (C.space j)) _ K _ x
  · intro j y
    rw [← C.range_eq j]
    exact LinearMap.mem_range_self _ y
  · intro y hy
    rw [C.constraint]
    exact hy

theorem commonDenominator_pos : 0 < C.commonDenominator :=
  Finset.prod_pos (fun j _ => C.denominator_pos j)

theorem commonDenominator_bound :
    (C.commonDenominator : ℝ) ≤
      Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine) := by
  rw [commonDenominator, Nat.cast_prod]
  calc
    _ ≤ ∏ _j : Fin m, Real.exp (certifiedAffineCenterBudget pAffine) :=
      Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _) (fun j _ => C.denominator_bound j)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]

theorem globalChart_top_grid (v : X ⊕ (Σ j, J j)) :
    realPolynomialCoefficientGrid C.commonDenominator
      (weightedHomogeneousComponent wt (wt v) (C.globalChart v)) := by
  rw [C.globalChart_top]
  apply fullTaggedLinearMapChart_coefficientGrid J
    (fullTaggedRealMatrixProjection J C.projection) C.commonDenominator
  intro j i a
  obtain ⟨z, hz⟩ := C.projection_grid j i a
  have hdiv : C.denominator j ∣ C.commonDenominator :=
    Finset.dvd_prod_of_mem C.denominator (Finset.mem_univ j)
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨(k : ℤ) * z, ?_⟩
  have hentry : fullTaggedRealMatrixProjection J C.projection j (Pi.single a 1) i =
      (C.projection j i a : ℝ) := by
    change (Matrix.mulVecLin (fun (i a : J j) => (C.projection j i a : ℝ)))
      (Pi.single a (1 : ℝ)) i = (C.projection j i a : ℝ)
    exact congrFun (Matrix.mulVec_single_one
      (fun (i a : J j) => (C.projection j i a : ℝ)) a) i
  rw [hentry, hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← hz]
  ring

end AllocatedExternalCandidateProblem.CertifiedAffineRefinement
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.CertifiedAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
    (C : P.CertifiedAffineRefinement K pAffine)

theorem projection_fixes_original
    (hretained : ∀ x, (∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ U j) → x ∈ K)
    (j : Fin m) (x : J j → ℝ) (hx : x ∈ U j) :
    fullTaggedRealMatrixProjection J C.projection j x = x := by
  apply C.fixes_space j x
  exact retained_tag_le_of_product_constraint K
    (fun j => realRationalCoordinateSpan (C.space j)) C.constraint hretained j hx

theorem slowChart_mass_sides
    (hretained : ∀ x, (∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ U j) → x ∈ K)
    {dTag : ℝ} (hdTag : 0 ≤ dTag)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ dTag)
    (hτ1 : τ ≤ 1) (hξ1 : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (z : C.refinement.problem.productive) (i : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes
      (fun a : (C.refinement.problem.chart z).Variables => (A.sides a.val : ℝ))
      (aeval (integerSampledRealChart (C.refinement.problem.chart z).integerChart)
        (C.slowChart i))) ≤
      actualCandidateSlowProjectionMassBudget m
        (Fintype.card (LayerSamplerVariables G I n B)) dTag
        (((pAffine + ((pAffine + 2) ^ 2 + 2) ^ 63) + 2) ^ 8) := by
  have h := (C.refinement.problem.chart z).slowProjection_mass_sides C.projection
    (C.projection_fixes_original hretained) hdTag C.projection_height hdim
    hτ1 hξ1 hp hσ1 Cgeo hCgeo hchart hsmall i
  rw [C.refinement.problem.chart_centerLift z] at h
  exact h

end AllocatedExternalCandidateProblem.CertifiedAffineRefinement
end Erdos3.VectorPolynomial

end

end OAI
end


