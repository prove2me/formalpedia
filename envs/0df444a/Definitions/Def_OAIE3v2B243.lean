-- Prove2me | Definitions.Def_OAIE3v2B243
-- name    : OAIE3v2B243
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:16:58.681006+00:00
-- url     : https://prove2.me/theorems/d4b5c47b-78a7-4e34-9c43-135121b92fca
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 248 of 311
-- statement:
--   Definitions bundle 248 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B219`, `OAIE3v2B220`, `OAIE3v2B224`, `OAIE3v2B226`, `OAIE3v2B228`, `OAIE3v2B229`, `OAIE3v2B230`, `OAIE3v2B231` of this split.
--
--   Modules: `Dynamics/CommonRefilteredGlobalMarkedFamilyReset.lean`, `Estimates/AllocatedExternalLocalFiniteFreezing.lean`, `Estimates/ControlledPrescribedMarkedNativeFactorization.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Estimates/ProductiveFrozenLocalMajorFamily.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Geometry/TerminalChartSlowEvaluation.lean`, `Lattices/QuadraticMarkedAffine.lean`, `Linear/ControlledProjectionUniformBudget.lean`, `Polynomial/PreparedPolynomialIdentity.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B219
import Definitions.Def_OAIE3v2B220
import Definitions.Def_OAIE3v2B224
import Definitions.Def_OAIE3v2B226
import Definitions.Def_OAIE3v2B228
import Definitions.Def_OAIE3v2B229
import Definitions.Def_OAIE3v2B230
import Definitions.Def_OAIE3v2B231

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledPrescribedMarkedNativeFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ L M : Type*}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

variable [Fintype σ] [Fintype ι] [Fintype κ]

theorem exists_common_refiltered_marked_symbol_factors
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hentries : ∀ i j, RationalHeightLE (c.repr (φ (b j)) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ p)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (side : σ → ℝ), (∀ i, 0 < side i) →
      ∀ (q : ℝ) (W : LieSubalgebra ℚ F.AssociatedGraded)
        (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
      ∃ El Pl Rl : G.RealPolynomialSymbolGroup (fun _ : σ => 1),
        El * Pl * Rl = G.realPolynomialSymbolHom c ν hG (fun _ => 1)
          (F.realPolynomialGroupMap G φ hφ (fun _ => 1) g) ∧
        Pl.coord ∈ realificationLieSubalgebra
          (G.symbolPointwiseSubalgebra c ν hG (fun _ => 1)
            (W.map (F.associatedGradedMap G φ hφ))) ∧
        G.SymbolSlowBound c ν hG (fun _ => 1) side
          (Real.exp ((p + 2) ^ 3 + q)) El ∧
        G.SymbolRationalGrid c ν hG (fun _ => 1) m Rl := by
  obtain ⟨m, hm, hmp, hlm, hgrid⟩ :=
    F.exists_realFilteredSymbolGroupMap_grid G b ω hF c ν hG φ hφ (fun _ : σ => 1)
      hH hentries hp hsource htarget hHp l hl hlp
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro side hside q W g hfactor
  obtain ⟨E, P, R, hprod, hP, hE, hR⟩ :=
    hfactor.symbolFactors F b ω hF side q l W g
  let π := F.realFilteredSymbolGroupMap G φ hφ (fun _ : σ => 1)
  refine ⟨π E, π P, π R, ?_, ?_, ?_, hgrid R hR⟩
  · rw [← map_mul, ← map_mul, hprod]
    exact F.realFilteredSymbolGroupMap_symbol G b ω hF c ν hG φ hφ (fun _ => 1) g
  · exact F.real_symbolPointwiseSubalgebra_map_mem G b ω hF c ν hG φ hφ
      (fun _ => 1) W P.coord hP
  · have hslow := F.realFilteredSymbolGroupMap_slow_exp G b ω hF c ν hG φ hφ
      (fun _ : σ => 1) hH hentries hp hsource hHp side hside (Real.exp_nonneg q) E hE
    simpa only [Real.exp_add] using hslow

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.QuadraticMarkedAffine
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem projectedLift_phase (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    torusPhaseLinear (phase t m) (projectedLift t a b) = 0 :=
  normalizedMarkedPhase_real_pure filtration generators weights marked t m _
    (projectedLift_pure t a b)

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem parameter_mul (t : ℕ) (v w : Fin t → ℝ) :
    parameter t v * parameter t w = parameter t (v + w) :=
  realMarkedParameterElement_mul filtration generators weights marked weight_pos generator_mem t v w

theorem parameter_inv (t : ℕ) (v : Fin t → ℝ) : (parameter t v)⁻¹ = parameter t (-v) :=
  realMarkedParameterElement_inv filtration generators weights marked weight_pos generator_mem t v

theorem affineElement_phase (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) :
    torusPhaseLinear (phase t m) (affineElement t a b n).coord = 0 := by
  change torusPhaseLinear (phase t m) (n • projectedLift t a b) = 0
  rw [map_smul, projectedLift_phase, smul_zero]

theorem centeredElement_phase {t d : ℕ} (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    torusPhaseLinear (phase t m) (centeredElement t m a b n v).coord = -v := by
  rw [centeredElement, torusPhaseLinear_mul D, affineElement_phase, zero_add]
  exact normalizedMarkedPhase_real_scaled_parameter filtration generators weights marked t m hm (-v)

theorem centeredElement_retraction_coord {t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d)
    (m : ℕ) (hm : 0 < m) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    (normalizedMarkedRetraction filtration generators weights marked weight_pos generator_mem t m D
      (centeredElement t m a b n v)).coord =
        (lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
          (realMarkedAffineShift filtration generators weights marked weight_pos generator_mem t ((m : ℝ) • v)
            (n • sourceLift t a (fun i => (m : ℝ)⁻¹ * b i))) := by
  let f := affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n
  have heq : normalizedMarkedRetraction filtration generators weights marked weight_pos generator_mem t m D
      (centeredElement t m a b n v) = parameter t ((m : ℝ) • v) * f *
        (parameter t ((m : ℝ) • v))⁻¹ := by
    change parameter t ((m : ℝ) • -(torusPhaseLinear (phase t m)
      (centeredElement t m a b n v).coord)) *
        (f * parameter t ((m : ℝ) • -v)) = _
    rw [centeredElement_phase D m hm, neg_neg, smul_neg, ← parameter_inv]
    exact (mul_assoc _ _ _).symm
  rw [heq]
  change conjugationCoord (parameter t ((m : ℝ) • v)) (n • projectedLift t a _) = _
  have hlift : n • projectedLift t a (fun i => (m : ℝ)⁻¹ * b i) =
      (lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
        (n • sourceLift t a (fun i => (m : ℝ)⁻¹ * b i)) := (map_smul _ _ _).symm
  rw [hlift]
  exact realMarkedAffineShift_conjugation filtration generators weights marked weight_pos generator_mem
    t (by decide) ((m : ℝ) • v) _

end Erdos3.QuadraticMarked

end

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped BigOperators

noncomputable def localOrbit {N : ℕ} (t m : ℕ) (a : ℝ) (b u c : Fin t → ℝ) (h₀ : ZMod N) :
    (multidegree t).realification.PolynomialOrbit :=
  Mul.mul (α := (multidegree t).realification.PolynomialOrbit)
    (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i))
    (realMarkedParameterOrbit filtration generators weights marked weight_pos generator_mem t
      (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i))

theorem localOrbit_eval {N : ℕ} (t m : ℕ) (a : ℝ) (b u c : Fin t → ℝ)
    (h₀ h : ZMod N) (n : ℤ) :
    (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (localOrbit t m a b u c h₀) =
        affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n *
          parameter t (fun i => -(m : ℝ) * (((h.val : ℝ) - h₀.val) * u i - c i)) := by
  have he : (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i)) =
        affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n :=
    NilpotentLieBCHGroup.ext (pureOrbit_eval t a _ h.val n)
  let E := (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
  let P : (multidegree t).realification.PolynomialOrbit :=
    realMarkedParameterOrbit filtration generators weights marked weight_pos generator_mem t
      (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i)
  have hmul : E (localOrbit t m a b u c h₀) =
      E (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i)) * E P := E.map_mul _ _
  apply hmul.trans
  change E (pureOrbit t a (fun i => (m : ℝ)⁻¹ * b i)) = _ at he
  rw [he]
  apply congrArg (affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n * ·)
  apply (realMarkedParameterOrbit_eval filtration generators weights marked weight_pos generator_mem t
    (fun i => (m : ℝ) * ((h₀.val : ℝ) * u i + c i)) (fun i => -(m : ℝ) * u i) h.val n).trans
  apply congrArg (parameter t)
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_natCast]
  ring

theorem latticeCorrection_mem {N t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d) (m : ℕ)
    (hlat : ∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
      filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice)
    (u c : Fin t → ℝ) (h₀ h : ZMod N) : latticeCorrection t m u c h₀ h ∈ D.realLattice :=
  realMarkedParameterElement_scaled_integer_mem filtration generators weights marked weight_pos generator_mem
    t m D hlat (fun i => -affineCyclicTorusCarry u c h₀ h i)

theorem localOrbit_right_normalization {N : ℕ} (t m : ℕ) (a : ℝ) (b u c : Fin t → ℝ)
    (h₀ h : ZMod N) (n : ℤ) :
    (multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (localOrbit t m a b u c h₀) * (latticeCorrection t m u c h₀ h)⁻¹ =
        centeredElement t m a b n (affineCyclicTorusLocalLift u c h₀ h) := by
  rw [localOrbit_eval, latticeCorrection, parameter_inv, mul_assoc, parameter_mul]
  apply congrArg (affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n * ·)
  apply congrArg (parameter t)
  funext i
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Int.cast_neg,
    affineCyclicTorusLocalLift_eq_sub_carry]
  ring

theorem localOrbit_quotient {N t d : ℕ}
    (D : RationalFilteredNilmanifold (Algebra t) 2 d) (m : ℕ)
    (hlat : ∀ a : Fin t → ℤ, (⟨(m : ℚ) • markedQuotientDirection
      filtration generators weights marked t (fun i => (a i : ℚ))⟩ : D.filtration.Group) ∈ D.lattice)
    (a : ℝ) (b u c : Fin t → ℝ) (h₀ h : ZMod N) (n : ℤ) :
    (QuotientGroup.mk ((multidegree t).realification.polynomialOrbitEval (correlationInput (h.val : ℤ) n)
      (localOrbit t m a b u c h₀)) : D.Space) =
        QuotientGroup.mk (centeredElement t m a b n (affineCyclicTorusLocalLift u c h₀ h)) := by
  have hc := latticeCorrection_mem D m hlat u c h₀ h
  calc
    _ = QuotientGroup.mk ((multidegree t).realification.polynomialOrbitEval
        (correlationInput (h.val : ℤ) n) (localOrbit t m a b u c h₀) *
          (latticeCorrection t m u c h₀ h)⁻¹) :=
      (quotient_mk_mul_mem D.realLattice _ ⟨_, D.realLattice.inv_mem hc⟩).symm
    _ = _ := congrArg QuotientGroup.mk (localOrbit_right_normalization t m a b u c h₀ h n)

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_character_cross_row_step {s A : ℕ} (hs : 1 ≤ s)
    (hdetect : NativeCrossRowDetection s A) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCharacterCrossRowDetection (s + 1) C := by
  obtain ⟨B, _, hdifference⟩ := RationalFilteredNilmanifold.exists_differenced_rows_degree s hs
  obtain ⟨D, _, hfamily⟩ := exists_gowers_of_native_cross_family hdetect
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d M T p hp hT N _ hN f g χ hf hg hcorr
  let u := (p + B) ^ B
  let v := (u + D) ^ D
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨K, hK, hKcorr⟩ := hdifference M T hp hT
    ((Real.exp_le_exp.mpr huC).trans hN) (characterCrossRow f g χ)
    (characterCrossRow_norm f g χ hf hg) hcorr
  have hclean : Real.exp (-u) ≤ (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simpa only [characterCrossRow_derivative_correlation_norm] using hKcorr
  have hmean := hfamily hu ((Real.exp_le_exp.mpr hvC).trans hN)
    (fun k => multiplicativeDerivative f k) (fun k => multiplicativeDerivative g k) K
    (multiplicativeDerivative_norm_le_one f hf) (multiplicativeDerivative_norm_le_one g hg)
    hK hclean
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans
    (exp_le_gowers_of_mean_derivative s g hv hmean)

theorem exists_native_cross_row_detection (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCrossRowDetection s C := by
  have hall : ∀ n : ℕ, ∃ C : ℕ, 2 ≤ C ∧ NativeCrossRowDetection (n + 1) C := by
    intro n
    induction n with
    | zero => exact exists_native_cross_row_detection_one
    | succ n ih =>
        obtain ⟨A, _, hdetect⟩ := ih
        obtain ⟨C, hC, hstep⟩ := exists_native_character_cross_row_step
          (by omega : 1 ≤ n + 1) hdetect
        refine ⟨C, hC, ?_⟩
        intro L _ _ _ _ _ _ d M T p hp hT N _ hN f g hf hg hcorr
        apply hstep M T hp hT hN f g (fun _ => 1) hf hg
        simpa [characterCrossRow] using hcorr
  cases s with
  | zero => omega
  | succ n => exact hall n

theorem exists_native_character_cross_row_detection (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeCharacterCrossRowDetection s C := by
  cases s with
  | zero => omega
  | succ n =>
      have hn : 1 ≤ n := by omega
      obtain ⟨A, _, hdetect⟩ := exists_native_cross_row_detection n hn
      exact exists_native_character_cross_row_step hn hdetect

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection
  realSymbolGradeQuotientPolynomial CertifiedFullChartFiniteHistory.outer
  FullChartControlledFactors

theorem exists_certified_full_chart_history_control (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {X ι η L : Type} [Fintype X] [Fintype ι] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] {m : ℕ}
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
      (Utag : ∀ j, Submodule ℝ (J j → ℝ))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
      (Bphase B p : ℝ) (H qS : ℕ) (n : ℕ),
      1 ≤ H → 0 ≤ p → 0 ≤ Bphase → 0 < qS → n ≤ s →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) * Bphase) ≤ Real.exp p →
      (Fintype.card η : ℝ) * B * Real.exp Bphase ≤ Real.exp ((p + 2) ^ a) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i) ∈ realDenominatorGrid qS) →
      ∀ history : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift
        Z Kinitial Utag poly N Bphase n,
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((p + C) ^ C) := by
  obtain ⟨C, hC, hprefix⟩ := exists_restricted_chart_prefix_control s a
  refine ⟨C, hC, ?_⟩
  intro X ι η L _ _ _ _ _ m F b ω hF J _ fast basis lift Z Kinitial Utag poly N
    Bphase B p H qS n hH hp hBphase hqS hn hι hσ hHp hstructure hden hcost hentry hgrid history
  obtain ⟨q, hq, hqbound, _, Echart, hE, hEbound, hRgrid⟩ :=
    hprefix F b ω hF (fullTaggedVariableWeight J) (fullTaggedVariableWeight_pos J)
      H p hH hp hι hσ hHp hstructure fast lift basis B Bphase qS hBphase hqS
      hden hcost hentry hgrid
      (normalizedRealPolynomialChart (fun i => (N i : ℝ)) (fullTaggedMajorTopCoordinates J poly))
      (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ)))
      history.slow history.rat history.q n hn history.q_pos history.q_bound
      history.slow_bound history.rat_grid
  unfold FullChartControlledFactors CertifiedFullChartFiniteHistory.outer
  with_reducible exact ⟨q, hq, hqbound, Echart, hE, hEbound, hRgrid⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realChartSubstitute

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L)
    (w : σ → ℕ)

theorem polynomialSlowBound_constantChart_value
    (v : τ → ℕ) (T : τ → ℝ) (bound : ℝ) (x : σ → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hslow : F.PolynomialSlowBound b v T bound
      (F.weightedAdaptedRealChartHom w v
        (fun i => (MvPolynomial.C (x i) : MvPolynomial τ ℝ))
        (fun i => weightedSupportLE_C v (w i) (x i)) g)) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w x g).coord i| ≤ bound := by
  rw [F.weightedAdaptedRealChartHom_constantChart] at hslow
  simpa only [F.realification.adaptedConstantGroupHom_log, coefficients_monomial,
    Finsupp.single_eq_same, monomialScale_zero, div_one] using hslow 0 i

theorem value_bound_of_terminal_chart_control [Fintype σ]
    (δ : σ → MvPolynomial σ ℝ) (p budget : ℝ) (a Ce : ℕ) (hp : 0 ≤ p)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (hcharts : ∀ {τ : Type*} [Fintype τ] (v : τ → ℕ), (∀ i, 0 < v i) →
      (Fintype.card τ : ℝ) ≤ p →
      ∀ (γ : σ → MvPolynomial τ ℝ)
        (hγ : ∀ i, γ i ∈ weightedSupportLE v (w i))
        (T : τ → ℝ), (∀ i, 0 < T i) →
      ∀ mass : ℝ, 1 ≤ mass →
        (∀ i, realPolynomialMass (scaleMvPolynomialAxes T
          (MvPolynomial.aeval γ (δ i))) ≤ mass) →
        (((Fintype.card σ : ℝ) + 1) ^ s * Real.exp budget * mass ^ s ≤
          Real.exp ((p + 2) ^ a)) →
        F.PolynomialSlowBound b v T (Real.exp ((p + Ce) ^ Ce))
          (F.weightedAdaptedRealChartHom w v γ hγ g))
    (x : σ → ℝ) (mass : ℝ) (hmass : 1 ≤ mass)
    (hpoint : ∀ i, |MvPolynomial.eval x (δ i)| ≤ mass)
    (hbudget : ((Fintype.card σ : ℝ) + 1) ^ s * Real.exp budget * mass ^ s ≤
      Real.exp ((p + 2) ^ a)) (i : ι) :
    |(b.baseChange ℝ).repr (F.adaptedPolynomialRealValueHom w x g).coord i| ≤
      Real.exp ((p + Ce) ^ Ce) := by
  apply F.polynomialSlowBound_constantChart_value b w (fun _ : PEmpty => 1)
    (fun _ => 1) _ x g
  apply hcharts (fun _ : PEmpty => 1) (fun i => PEmpty.elim i)
    (by simpa only [Fintype.card_pempty, Nat.cast_zero] using hp)
    (fun i => MvPolynomial.C (x i))
    (fun i => weightedSupportLE_C (fun _ : PEmpty => 1) (w i) (x i))
    (fun _ => 1) (fun i => PEmpty.elim i) mass hmass
    (fun i => ?_) hbudget
  simpa only [realPolynomialMass_constant_specialization] using hpoint i

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CommonRefilteredGlobalMarkedFamilyReset
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct

theorem exists_common_refiltered_terminal_native_reset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
      Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (H l : ℕ) (pMap pNative : ℝ), 1 ≤ H → 0 < l → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → (l : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (Fintype.card ι : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card σ : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) H) →
    ∃ mMap m : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l ∣ mMap ∧ 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ m ∧
    ∀ (side : σ → ℝ), (∀ i, Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ side i) →
    ∀ (q : ℝ), Real.exp q ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ a) →
    ∀ X EF RF : (G.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      G.PolynomialSlowBound c (fun _ : σ => 1) side (Real.exp ((pNative + 2) ^ a)) EF →
      G.PolynomialRationalGrid c (fun _ : σ => 1) mMap RF →
      (G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1) (EF⁻¹ * X * RF⁻¹)).coord ∈
        realificationLieSubalgebra (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))) →
      coefficients ((EF⁻¹ * X * RF⁻¹).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) 0 ∈
        G.realGradedRefiltrationLayer (W.map (F.associatedGradedMap G φ hφ)) 1 →
    ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g = X →
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (native : (F.gradedRefiltration W).realification.PolynomialOrbit (fun _ : σ => 1)),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) e = EF ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) r = RF ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) middle = EF⁻¹ * X * RF⁻¹ ∧
      F.PolynomialSlowBound b (fun _ : σ => 1) side
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative)) e ∧
      F.PolynomialRationalGrid b (fun _ : σ => 1) m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        native.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval (fun _ : σ => 1) t native) =
          F.adaptedPolynomialRealValueHom (fun _ : σ => 1) t middle := by
  obtain ⟨Ccompare, hCcompare, hcompare⟩ := exists_common_refiltered_terminal_discrepancies s a
  obtain ⟨Cf, Cnative, hCf, hCnative, hnative⟩ :=
    exists_controlled_prescribed_marked_native_factorizations s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ χ L M _ _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c ν hG hsurj
    bk W v hW hvspan vg hvgspan _ _ H l pMap pNative hH hl hpMap hpNative
    hsrc htgt hHmap hlmap hmabsorb hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  obtain ⟨mMap, hmMap, hmMapBound, hlmMap, hdiscrepancy⟩ :=
    hcompare (χ := χ) F G b ω hF c ν hG φ hφ H l pMap hH hl hpMap hentries hsrc htgt hHmap hlmap
  obtain ⟨m, hm, hmp, hmMapm, hreset⟩ := hnative F G φ hφ b ω hF c ν hG
    (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) hsurj bk W v hW hvspan H mMap pNative
    hH hmMap hpNative hι hκ hξ hμ hσ hHp (hmMapBound.trans hmabsorb)
    hb hc hkernel hentries hv
  refine ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, ?_⟩
  intro side hside q hq hmapslow X EF RF hEF hRF hterminal hconstant g hg hfactor
  have hsidePos : ∀ i, 0 < side i := fun i => (Real.exp_pos _).trans_le (hside i)
  obtain ⟨E, P, R, hprod, hP, hE, hR, hdiff⟩ :=
    hdiscrepancy H pNative hH hpNative hκ hσ hχ hHp hmabsorb hc
      side hside q hmapslow W vg hvgspan hvg g hfactor
  have hterminal' :
      ((G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1) EF)⁻¹ *
        G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1)
          (F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g) *
        (G.realPolynomialSymbolHom c ν hG (fun _ : σ => 1) RF)⁻¹).coord ∈
        realificationLieSubalgebra (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))) := by
    simpa only [map_mul, map_inv, hg] using hterminal
  obtain ⟨hleft, hright⟩ := hdiff _ _ hterminal'
    (G.polynomialSlowBound_symbol c ν hG (fun _ : σ => 1) side _ EF hEF)
    (G.polynomialRationalGrid_symbol c ν hG (fun _ : σ => 1) mMap RF hRF)
  exact hreset side hsidePos X EF RF hEF hRF hconstant g hg E P R hprod hP
    (F.symbolSlowBound_mono b ω hF (fun _ : σ => 1) side hsidePos hq E hE)
    (F.symbolRationalGrid_mono b ω hF (fun _ : σ => 1) hl hlmMap R hR) hleft hright

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra

theorem exists_common_refiltered_globalMarked_native_reset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
      Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (H l : ℕ) (pMap pNative : ℝ), 1 ≤ H → 0 < l → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → (l : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (Fintype.card ι : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card σ : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) H) →
    ∃ mMap m : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l ∣ mMap ∧ 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ m ∧
    ∀ (side : σ → ℝ), (∀ i, Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ side i) →
    ∀ (q : ℝ), Real.exp q ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ a) →
    ∀ {α : Type*} (w : α → ℕ) (β : α → MvPolynomial α ℝ)
      (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
      (marked : (G.realification.adaptedPolynomialFiltration w).Group)
      (E R : G.RealPolynomialSymbolGroup w)
      (A : GlobalMarkedNativeFactors G c ν hG w
        (W.map (F.associatedGradedMap G φ hφ))
        (G.weightedAdaptedRealChartHom w w β hβ marked) E R)
      (γ : α → MvPolynomial σ ℤ)
      (hγ : ∀ i, MvPolynomial.map (Int.castRingHom ℝ) (γ i) ∈
        weightedSupportLE (fun _ : σ => 1) (w i)),
      (∀ t : σ → ℝ,
        (fun i => MvPolynomial.eval
          (fun j => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ j))) (β i)) =
        (fun i => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ i)))) →
      G.PolynomialSlowBound c (fun _ : σ => 1) side (Real.exp ((pNative + 2) ^ a))
        (G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.left) →
      G.PolynomialRationalGrid c w l A.right →
    ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) g =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ marked →
      F.HasCommonRefilteredOrbitFactors b ω hF side q l W g →
    ∃ (e middle r : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (native : (F.gradedRefiltration W).realification.PolynomialOrbit (fun _ : σ => 1)),
      e * middle * r = g ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) e =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.left ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) r =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.right ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) middle =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)) hγ A.middle ∧
      F.PolynomialSlowBound b (fun _ : σ => 1) side
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative)) e ∧
      F.PolynomialRationalGrid b (fun _ : σ => 1) m r ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        native.log = (middle.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval (fun _ : σ => 1) t native) =
          F.adaptedPolynomialRealValueHom (fun _ : σ => 1) t middle := by
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_common_refiltered_terminal_native_reset s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ χ L M _ _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c ν hG hsurj
    bk W v hW hvspan vg hvgspan _ _ H l pMap pNative hH hl hpMap hpNative
    hsrc htgt hHmap hlmap hmabsorb hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  obtain ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, hrun⟩ :=
    hreset F G φ hφ b ω hF c ν hG hsurj bk W v hW hvspan vg hvgspan
      H l pMap pNative hH hl hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
      hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  refine ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, ?_⟩
  intro side hside q hq hmapslow α w β hβ marked E R A γ hγ hfixed hslow hgrid g hg hcommon
  let γR := fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ i)
  let pull := G.weightedAdaptedRealChartHom w (fun _ : σ => 1) γR hγ
  have hlocalGrid : G.PolynomialRationalGrid c (fun _ : σ => 1) mMap (pull A.right) :=
    G.polynomialRationalGrid_of_dvd c (fun _ : σ => 1) hl hlmMap _
      (G.polynomialRationalGrid_integerChart c w (fun _ : σ => 1) γ hγ l A.right hgrid)
  have hconditions := A.fixed_chart_native_conditions γR hγ hfixed
  have hresidual := A.fixed_chart_residual_eq γR hγ hfixed
  obtain ⟨e, middle, r, native, hprod, he, hr, hmid, heSlow, hrGrid, hlog, hvalues⟩ :=
    hrun side hside q hq hmapslow (pull marked) (pull A.left) (pull A.right)
      hslow hlocalGrid hconditions.1 hconditions.2 g hg hcommon
  exact ⟨e, middle, r, native, hprod, he, hr, hmid.trans hresidual,
    heSlow, hrGrid, hlog, hvalues⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound

theorem exists_common_refiltered_globalMarked_family_reset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {σ ι κ ξ μ χ L M : Type*} [Fintype σ] [Fintype ι] [Fintype κ]
      [Fintype ξ] [Fintype μ] [Fintype χ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
      (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)
      (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis κ ℚ M) (ν : κ → ℕ)
      (hG : ∀ j, G.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y) →
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ F.AssociatedGraded) (v : μ → F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → G.PolynomialSymbol (fun _ : σ => 1)),
      Submodule.span ℚ (Set.range vg) =
        (G.symbolPointwiseSubalgebra c ν hG (fun _ : σ => 1)
          (W.map (F.associatedGradedMap G φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]
      (H l nFinal : ℕ) (pMap pNative : ℝ),
      1 ≤ H → 0 < l → 0 < nFinal → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → ((l * nFinal : ℕ) : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (Fintype.card ι : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card σ : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H) →
      (∀ i j, RationalHeightLE (b.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (c.repr (φ (b i)) k) H) →
      (∀ j i, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((G.polynomialSymbolBasis c ν hG (fun _ : σ => 1)).repr (vg i) z) H) →
    ∃ mMap m : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l * nFinal ∣ mMap ∧ 0 < m ∧
      (m : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ m ∧
    ∀ {Ω α : Type*} (w : α → ℕ) (β : α → MvPolynomial α ℝ)
      (hβ : ∀ i, β i ∈ weightedSupportLE w (w i))
      (marked : (G.realification.adaptedPolynomialFiltration w).Group)
      (E R : G.RealPolynomialSymbolGroup w)
      (A : GlobalMarkedNativeFactors G c ν hG w
        (W.map (F.associatedGradedMap G φ hφ))
        (G.weightedAdaptedRealChartHom w w β hβ marked) E R),
      G.PolynomialRationalGrid c w nFinal A.right →
    ∀ (side : Ω → σ → ℝ) (q : Ω → ℝ)
      (γ : Ω → α → MvPolynomial σ ℤ)
      (hγ : ∀ z i, MvPolynomial.map (Int.castRingHom ℝ) (γ z i) ∈
        weightedSupportLE (fun _ : σ => 1) (w i)),
      (∀ z i, Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ side z i) →
      (∀ z, Real.exp (q z) ≤ Real.exp ((pNative + 2) ^ a)) →
      (∀ z, Real.exp ((pMap + 2) ^ 3 + q z) ≤ Real.exp ((pNative + 2) ^ a)) →
      (∀ z, ∀ t : σ → ℝ,
        (fun i => MvPolynomial.eval
          (fun j => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ z j))) (β i)) =
        (fun i => MvPolynomial.eval t (MvPolynomial.map (Int.castRingHom ℝ) (γ z i)))) →
      (∀ z, G.PolynomialSlowBound c (fun _ : σ => 1) (side z) (Real.exp ((pNative + 2) ^ a))
        (G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.left)) →
    ∀ g : Ω → (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ z, F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (g z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) marked) →
      (∀ z, F.HasCommonRefilteredOrbitFactors b ω hF (side z) (q z) l W (g z)) →
    ∃ (e middle r : Ω → (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
      (native : Ω → (F.gradedRefiltration W).realification.PolynomialOrbit (fun _ : σ => 1)),
      ∀ z,
      e z * middle z * r z = g z ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (e z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.left ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (r z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.right ∧
      F.realPolynomialGroupMap G φ hφ (fun _ : σ => 1) (middle z) =
        G.weightedAdaptedRealChartHom w (fun _ : σ => 1)
          (fun i => MvPolynomial.map (Int.castRingHom ℝ) (γ z i)) (hγ z) A.middle ∧
      F.PolynomialSlowBound b (fun _ : σ => 1) (side z)
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput s a Cf pNative) + Cnative) ^ Cnative)) (e z) ∧
      F.PolynomialRationalGrid b (fun _ : σ => 1) m (r z) ∧
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        (native z).log = ((middle z).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∧
      ∀ t : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := (F.gradedRefiltration W).lowerCentralSeries_eq_bot)
        (hM := F.lowerCentralSeries_eq_bot) (F.gradedRefiltrationSubalgebra W).incl
        ((F.gradedRefiltration W).realification.polynomialOrbitRealEval (fun _ : σ => 1) t (native z)) =
          F.adaptedPolynomialRealValueHom (fun _ : σ => 1) t (middle z) := by
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_common_refiltered_globalMarked_native_reset s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro σ ι κ ξ μ χ L M _ _ _ _ _ _ _ _ _ _ F G φ hφ b ω hF c ν hG hsurj
    bk W v hW hvspan vg hvgspan _ _ H l nFinal pMap pNative hH hl hnFinal hpMap hpNative
    hsrc htgt hHmap hlmap hmabsorb hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  have hwide : 0 < l * nFinal := Nat.mul_pos hl hnFinal
  obtain ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, hrun⟩ :=
    hreset F G φ hφ b ω hF c ν hG hsurj bk W v hW hvspan vg hvgspan
      H (l * nFinal) pMap pNative hH hwide hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
      hι hκ hξ hμ hχ hσ hHp hb hc hkernel hentries hv hvg
  refine ⟨mMap, m, hmMap, hmMapBound, hlmMap, hm, hmp, hmMapm, ?_⟩
  intro Ω α w β hβ marked E R A hgrid side q γ hγ hside hq hmapslow hfixed hslow g hg hcommon
  have hglobalGrid : G.PolynomialRationalGrid c w (l * nFinal) A.right :=
    G.polynomialRationalGrid_of_dvd c w hnFinal (dvd_mul_left nFinal l) A.right hgrid
  have hfamily (z : Ω) := hrun (side z) (hside z) (q z) (hq z) (hmapslow z)
    w β hβ marked E R A (γ z) (hγ z) (hfixed z) (hslow z) hglobalGrid (g z) (hg z)
    (HasCommonRefilteredOrbitFactors.of_dvd F b ω hF (side z) (q z) hl
      (dvd_mul_right l nFinal) W (g z) (hcommon z))
  classical
  choose e middle r native hproperties using hfamily
  exact ⟨e, middle, r, native, hproperties⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct
open VectorPolynomial

namespace RankPreparationFamily

theorem polynomial_degree {I J : Type} [DecidableEq J] {s : ℕ}
    (L : RankPreparationFamily I J s)
    (hL : ∀ u, DegreeLE (fun _ => 1) (u.val + 1) (L u).poly) :
    DegreeLE (fun _ => 1) s L.polynomial := by
  apply degreeLE_finset_sum
  intro u _
  apply DegreeLE.map
  intro α hα
  exact hL u α (lt_of_le_of_lt (Nat.succ_le_of_lt u.isLt) hα)

end RankPreparationFamily

end Erdos3

end

end OAI
end

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

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductiveFrozenLocalMajorFamily
namespace OAI

section

namespace Erdos3
open scoped TensorProduct BigOperators
variable {I L : Type*} [Fintype I] [DecidableEq I]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_productive_localMajorSlice_coordinate_family
    {Ω X η : Type*} [Fintype Ω]
    (D : RationalFilteredNilmanifold L s d)
    (law : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (N : I → ℕ) (hN : ∀ i, 0 < N i) (cost budget δ : ℝ)
    (fallback : LocalMajorSliceTest D N cost budget)
    (physical : Ω → (I → ℤ) → X) (signal : η → X → ℂ)
    (hlocal : ∀ j z, z ∈ good j → ∃ A : LocalMajorSliceTest D N cost budget,
      δ ≤ ‖𝔼 x ∈ A.slice.integerPoints, signal j (physical z x) * A.weight x‖) :
    ∃ chosen : Ω → Option η → LocalMajorSliceTest D N cost budget,
      (∀ j z, z ∈ good j → δ ≤ ‖𝔼 x ∈ (chosen z (some j)).slice.integerPoints,
        signal j (physical z x) * (chosen z (some j)).weight x‖) ∧
      ∀ j, δ * law.mass (good j) ≤ sampledSliceSeminorm law
        (fun z (x : integerBox N) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox N) => (chosen z a).weight x.val) (signal j) := by
  classical
  let chosen (z : Ω) : Option η → LocalMajorSliceTest D N cost budget
    | none => fallback
    | some j => if hz : z ∈ good j then Classical.choose (hlocal j z hz) else fallback
  have hchosen (j : η) (z : Ω) (hz : z ∈ good j) :
      δ ≤ ‖𝔼 x ∈ (chosen z (some j)).slice.integerPoints,
        signal j (physical z x) * (chosen z (some j)).weight x‖ := by
    have he : chosen z (some j) = Classical.choose (hlocal j z hz) := by
      simp only [chosen, dif_pos hz]
    rw [he]
    exact Classical.choose_spec (hlocal j z hz)
  refine ⟨chosen, hchosen, ?_⟩
  intro j
  let : Nonempty (integerBox N) := ⟨⟨fun _ => 0,
    (mem_integerBox _ _).mpr (fun i => ⟨le_rfl, by exact_mod_cast hN i⟩)⟩⟩
  apply productive_mass_mul_le_sampledSliceSeminorm law (good j)
    (fun z (x : integerBox N) => physical z x.val)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a (x : integerBox N) => (chosen z a).weight x.val)
    (fun z a => (chosen z a).slice.subtypeSites_nonempty_of_integerPoints
      (chosen z a).dense.nonempty)
    (fun z a x => (chosen z a).weight_norm x.val) (signal j) δ
  intro z hz
  refine ⟨some j, ?_⟩
  rw [(chosen z (some j)).slice.expect_subtypeSites
    (fun x => signal j (physical z x) * (chosen z (some j)).weight x)]
  exact hchosen j z hz
namespace OrdinaryPolynomialPhase

variable {n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra weight n)]

noncomputable def zeroLocalMajorSlice (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (cost : ℝ) (hcost : 0 ≤ cost) :
    LocalMajorSliceTest (nilmanifold n) N cost (budget n) := by
  let T := RationalFilteredNilmanifold.Niltest.const (nilmanifold n)
    (fun _ : I => 1) (0 : ℂ)
  apply LocalMajorSliceTest.full N hN cost (budget n) hcost T
  · change ‖(0 : ℂ)‖ ≤ 1
    simp
  · refine ⟨nilmanifold_geometry n, ?_⟩
    change Real.log (2 + ‖(0 : ℂ)‖ + 0) ≤ budget n
    simp only [norm_zero, add_zero]
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith [two_le_budget n]

end OrdinaryPolynomialPhase

end Erdos3

end

section

namespace Erdos3
open scoped TensorProduct BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

namespace UniversalLocalMajorSliceTest

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {N : I → ℕ} {degree : ℕ} {cost budget : ℝ}

noncomputable def default (N : I → ℕ) (hN : ∀ i, 0 < N i)
    (degree : ℕ) (cost budget : ℝ) (hcost : 0 ≤ cost) (hbudget : 2 ≤ budget) :
    UniversalLocalMajorSliceTest N degree cost budget := by
  let model : NativeSampleModel (fun _ : I => 1) degree budget id (fun _ => 1) :=
    NativeSampleModel.constOne hbudget
  exact ofLocalMajorSliceTest (LocalMajorSliceTest.full N hN cost budget hcost
    model.test (by exact_mod_cast model.norm) model.complexity)

end UniversalLocalMajorSliceTest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
namespace OAI

universe u

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

variable {κ M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (G : NilpotentLieFiltration M s)
    (f : Basis κ ℚ M) (ν : κ → ℕ)
    (hG : ∀ j, G.layer j = Submodule.span ℚ (f '' {i | j ≤ ν i}))
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : ∀ j, ∀ x ∈ F.layer j, φ x ∈ G.layer j)

theorem controlledSymbolFactorizationAtFast_projection_of_dimensions
    [Fintype σ] [Fintype ι] [Fintype κ]
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ F.layer j, φ x = y)
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (η : M →ₗ[ℚ] ℚ) (U : LieSubalgebra ℚ G.AssociatedGraded)
    (hfactor : G.ControlledSymbolFactorizationAtFast f ν hG η T
      (F.realSymbolProjection G φ hφ (fun _ => 1) X) p U) :
    F.ControlledSymbolFactorizationAtFast e ω hF (η.comp φ.toLinearMap) T X
      (controlledProjectionBudget (controlledProjectionDimensionInput s p))
      (U.comap (F.associatedGradedMap G φ hφ)) := by
  let :=  symbolBasisIndexFintype (fun _ : σ => 1) ω s (fun _ => Nat.zero_lt_one)
    (F.adaptedBasis_weight_le_step e ω hF)
  let :=  symbolBasisIndexFintype (fun _ : σ => 1) ν s (fun _ => Nat.zero_lt_one)
    (G.adaptedBasis_weight_le_step f ν hG)
  let q : ℝ := (p + (s + 2)) ^ (s + 2)
  let r : ℝ := controlledProjectionDimensionInput s p
  have hpR : p ≤ r := by
    change p ≤ 2 * q ^ 2 + p + 1
    nlinarith [sq_nonneg q]
  have hR : 0 ≤ r := hp.trans hpR
  have hq : 1 ≤ q := by
    apply one_le_pow₀
    have := Nat.cast_nonneg (α := ℝ) s
    linarith
  have hsource : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le _ _ s (fun _ => Nat.zero_lt_one)
      (F.adaptedBasis_weight_le_step e ω hF))).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have htarget : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ q :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le _ _ s (fun _ => Nat.zero_lt_one)
      (G.adaptedBasis_weight_le_step f ν hG))).trans
      (symbol_dimension_bound_le_power s (Fintype.card κ) (Fintype.card σ) hp hκ hσ)
  have hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ r := by
    simp only [Fintype.card_sum, Nat.cast_add]
    change _ ≤ 2 * q ^ 2 + p + 1
    nlinarith
  have hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ r := by
    rw [Nat.cast_mul]
    have hnonneg := Nat.cast_nonneg (α := ℝ)
      (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω))
    have hsquare := mul_self_le_mul_self hnonneg hsource
    change _ ≤ 2 * q ^ 2 + p + 1
    nlinarith
  exact F.controlledSymbolFactorizationAtFast_projection_pullback G e ω hF f ν hG φ hφ
    hsurj hH hentries hR (hι.trans hpR) (hκ.trans hpR) hrows hcols
    (hHp.trans (Real.exp_le_exp.mpr hpR)) T hT X η U
    (hfactor.mono G f ν hG hpR hT)

end Erdos3.NilpotentLieFiltration

end

end OAI
end


