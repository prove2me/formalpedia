-- Prove2me | Definitions.Def_OAIErdos3B113
-- name    : OAIErdos3B113
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T04:25:35.75899+00:00
-- url     : https://prove2.me/theorems/222a37e1-ddf8-460d-b71b-2c402e57bfda
-- title:
--   OpenAI Erdős-3 split, definitions bundle 114 of 132
-- statement:
--   Definitions bundle 114 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B112`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 114 available.
--
--   Modules: `OAI.Erdos3.RationalFilteredNilmanifold.MultidegreeStructure.exists_native_dilation_orbit`, `OAI.Erdos3.exists_lattice_normalized_refiltered_factorization`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B119

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_native_dilation_orbit (q : ℤ)
    (E : RationalFilteredNilmanifold (M.filtration.ordinary.dilationPairSubalgebra (q : ℚ)) s r)
    (hEF : E.filtration = M.filtration.ordinary.dilationPairFiltration (q : ℚ))
    (g : M.filtration.realification.PolynomialOrbit) (ε γ : D.RealGroup)
    (hγ : γ ∈ D.realLattice) (hfactor : M.filtration.realification.polynomialOrbitEval 0 g = ε * γ) :
    ∃ h : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
      E.filtration.realification.polynomialOrbitEval _ 0 h = 1 ∧
      ∀ x : σ → ℤ,
        (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection (q : ℚ) 0
          (E.filtration.realification.polynomialOrbitEval _ x h)) : D.Space) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval (fun i => q * x i) g) ∧
        (QuotientGroup.mk (ε * M.filtration.ordinary.realDilationPairProjection (q : ℚ) 1
          (E.filtration.realification.polynomialOrbitEval _ x h)) : D.Space) =
            QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval x g) := by
  let F := M.filtration.ordinary.dilationPairFiltration (q : ℚ)
  obtain ⟨h, hh0, hh⟩ := M.filtration.exists_real_normalized_dilationPair_orbit q g ε γ hfactor
  have hF : F.realification = E.filtration.realification := by rw [hEF]
  let hE := F.realification.orbitEquivOfEq hF (fun _ : σ => 1)
    ((M.filtration.dilationPairMultidegree (q : ℚ)).realification.toOrdinaryOrbit h)
  have hhE (x : σ → ℤ) : E.filtration.realification.polynomialOrbitEval _ x hE =
      (M.filtration.dilationPairMultidegree (q : ℚ)).realification.polynomialOrbitEval x h :=
    F.realification.orbitEquivOfEq_eval hF _ _ x
  refine ⟨hE, (hhE 0).trans hh0, fun x => ?_⟩
  rw [hhE]
  constructor
  · rw [(hh x).1]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)
  · rw [(hh x).2]
    simp only [← mul_assoc, mul_inv_cancel, one_mul]
    exact QuotientGroup.mk_mul_of_mem _ (D.realLattice.inv_mem hγ)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeNormalizedRefiltering
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_lattice_normalized_refiltered_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (eta : J → L →ₗ[ℚ] ℚ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, D.filtration.ControlledSymbolFactorization D.basis w hF (eta j) A
        (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) p) →
      ∃ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (v : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v i) k) ≤
          (p + C) ^ C) ∧
        (∀ j x, x ∈ D.filtration.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨c, _, hnormalize⟩ := exists_native_polynomial_normalization s
  obtain ⟨k, _, hcommon⟩ := exists_common_refiltered_factorization s
  obtain ⟨l, _, hleft⟩ := exists_native_slow_left_constant_bound s
  let N : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let F : Polynomial ℕ := (Polynomial.X + 2) ^ k
  let H : Polynomial ℕ := ((Polynomial.X + 2) ^ 2 + 2) ^ 63 + 1
  let Q : Polynomial ℕ := Polynomial.X + N + F
  let P : Polynomial ℕ := F + H + (Q + Polynomial.C l) ^ l
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ D w hF eta p hp hD hσ hJ A hA g hfactor
  let q := p + (p + c) ^ c + (p + 2) ^ k
  have hn0 : 0 ≤ (p + c) ^ c := by positivity
  have hf0 : 0 ≤ (p + 2) ^ k := by positivity
  have hh0 : 0 ≤ ((p + 2) ^ 2 + 2) ^ 63 + 1 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hnq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hfq : (p + 2) ^ k ≤ q := by dsimp [q]; linarith
  have hb : (p + 2) ^ k + (((p + 2) ^ 2 + 2) ^ 63 + 1) + (q + l) ^ l ≤ (p + C) ^ C := by
    simpa [P, Q, N, F, H, q, Polynomial.eval₂_pow] using hbudget p hp
  have hl0 : 0 ≤ (q + l) ^ l := by positivity
  have hfC : (p + 2) ^ k ≤ (p + C) ^ C := by linarith
  have hhC : ((p + 2) ^ 2 + 2) ^ 63 + 1 ≤ (p + C) ^ C := by linarith
  have hlC : (q + l) ^ l ≤ (p + C) ^ C := by linarith
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  obtain ⟨a, κ, g₀, ha, hκ, hnormalizeEq, hg₀zero, hsymbol⟩ :=
    hnormalize D w hF (fun _ : σ => 1) p hp hD g
  have hfactor₀ : ∀ j, D.filtration.ControlledSymbolFactorization D.basis w hF (eta j) A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g₀) p := by
    intro j
    rw [hsymbol]
    exact hfactor j
  obtain ⟨W, v, m, e₀, b, R, hv, hW, hheight, hfreq, hm, hmp, hebr,
      hmid, he, hR, _, hR0, hb0, hvalues⟩ :=
    hcommon D.filtration D.basis w hF eta p hp
      (by simpa only [Fintype.card_fin] using hD.1) hσ hJ (fun i j k => hD.2.2.1 i j k)
      A (fun i => (Real.exp_le_exp.mpr hfC).trans (hA i)) g₀ hfactor₀
  let E := D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) a * e₀
  have hE : D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A
      (Real.exp ((p + C) ^ C)) E := by
    have hsmall := hleft D w hF q hq (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hD hpq)
      (hσ.trans hpq) A hApos a (fun i => (ha i).trans (Real.exp_le_exp.mpr hnq)) e₀
      (D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hApos (Real.exp_le_exp.mpr hfq) e₀ he)
    exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hApos
      (Real.exp_le_exp.mpr hlC) E hsmall
  have hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g := by
    calc
      _ = D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) a *
          (e₀ * b * R) * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ := by
        simp only [E, mul_assoc]
      _ = g := by rw [hebr]; exact hnormalizeEq
  let e := Fintype.equivFin (Fin d)
  have hrange : Set.range (fun i => v (e i)) = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective i
      exact ⟨j, congrArg v hj⟩
  have hv' : Submodule.span ℚ (Set.range (fun i => v (e i))) = W.toSubmodule := by
    rw [hrange]
    exact hv
  refine ⟨W, (fun i => v (e i)), m, κ, E, b, R, hv', hW,
    (fun i j => (hheight (e i) j).trans hhC), hfreq, hm,
    hmp.trans (Real.exp_le_exp.mpr hfC), hκ, hprod, hE, hR,
    hb0.trans hg₀zero, hR0, ?_, hvalues hg₀zero⟩
  exact (D.filtration.real_symbol_values_iff_refiltration_coefficients D.basis w hF
    (fun _ => 1) W b.coord).mp hmid

end Erdos3

end

end OAI

end


