-- Prove2me | Definitions.Def_OAIErdos3B192
-- name    : OAIErdos3B192
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T09:20:16.171231+00:00
-- url     : https://prove2.me/theorems/d29345f9-aa9e-45c1-9ccb-8bf394e7112f
-- title:
--   OpenAI Erdős-3 split, definitions bundle 193 of 206
-- statement:
--   Definitions bundle 193 of 206 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B191`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 193 available.
--
--   Modules: `OAI.Erdos3.exists_markedShiftQuotient_bounded_evaluation_data`, `OAI.Erdos3.exists_markedShift_bounded_basis`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B188

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MarkedProjectionBounds
namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hw hv hH hc hgen in
theorem exists_markedShift_bounded_basis (hω : ∀ i, ω i ≤ s) (t : ℕ) :
    ∃ e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
        (markedShiftSubalgebra F v w marked t),
      ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
        (e i).val j) (lieTreeHeight (Fintype.card ι) H s) := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (Set.range (markedShiftGenerator F v w marked hw hv t 0 0))
  rw [markedShiftGenerator_span, markedShiftBiLayer_zero, finrank_top] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  let e := Basis.mk hzli (le_of_eq hzspan.symm)
  refine ⟨e, ?_⟩
  intro i j
  simp only [e, Basis.mk_apply]
  obtain ⟨k, hk⟩ := hz i
  rw [← hk]
  exact markedShiftGenerator_coordinate_height F b ω hF v w marked hw hv hH hc hgen t 0 0 k j

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r d q : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (e : Basis (Fin d) ℚ (markedShiftSubalgebra F v w marked t))
  {H : ℕ} (he : ∀ i j, RationalHeightLE
    ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr (e i).val j) H)

include he

variable (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
  {Q : ℕ} (hQ : 1 ≤ Q)
  (hf : ∀ i j, RationalHeightLE
    (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)

include hQ hf

variable {ν : Type*} (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
  (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
  (hc : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K)

include hc

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedEvaluationJointBounds
namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι ν L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hw hv hH hc hgen in
theorem exists_markedShiftQuotient_bounded_evaluation_data (t : ℕ)
    (J : LieIdeal ℚ L) (hJ : markedLieSpan v w marked 0 2 0 ≤ J.toSubmodule)
    (c : Basis ν ℚ (L ⧸ J)) {K : ℕ}
    (hcoef : ∀ i j, RationalHeightLE (c.repr (lieQuotientMap J (b j)) i) K) :
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∃ m : ℕ, m ≤ finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ∧
      ∃ q : ℕ, q ≤ d ∧ ∃ f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t),
        let R := markedEvaluationHeight s (Fintype.card ι) a d m q H K
        (∀ i j k, RationalHeightLE (lieStructureConstants f i j k) R) ∧
        (∀ α : Fin 2 → ℕ,
          ∃ e : Basis (Fin (finrank ℚ (markedShiftQuotientLayer F v w marked t α))) ℚ
              (markedShiftQuotientLayer F v w marked t α),
            ∀ i j, RationalHeightLE (f.repr (e i).val j) R) ∧
        (∀ i j, RationalHeightLE
          (f.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) R) ∧
        (∀ i j, RationalHeightLE (markedQuotientPhase F v w marked t (f j) i) R) ∧
        ∀ i j, RationalHeightLE (c.repr (markedBaseEvaluation F v w marked t J hJ 0 (f j)) i) R := by
  classical
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  let T := lieTreeHeight (Fintype.card ι) H s
  let U := max T (s + 1)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  let C := rationalLieStructureHeight a (max U (rationalSolveHeight d U))
  obtain ⟨e, he⟩ := exists_markedShift_bounded_basis F b ω hF v w marked hw hv hH hc hgen hω t
  obtain ⟨m, hm, q, hq, f, hf⟩ := exists_markedShiftQuotient_bounded_coordinates
    F b ω hF v w marked hw hv hH hc hgen hω t e he
  let Q := rationalKernelHeight m B
  let V := max 1 (max C Q)
  let A := max T ((Fintype.card ι + 1) * (T * K) ^ Fintype.card ι)
  let G := markedQuotientHeight s (Fintype.card ι) a d m q H
  let R := markedEvaluationHeight s (Fintype.card ι) a d m q H K
  have hGR : G ≤ R := Nat.le_max_left _ _
  have hT : 1 ≤ T := hH.trans (lieTreeHeight_ge_input _ _ _)
  have hsolve := rationalSolveHeight_pos d hT
  have hB : 1 ≤ B := by
    dsimp [B]
    have := Nat.zero_lt_of_lt hT
    exact Nat.succ_le_iff.mpr (by positivity)
  have hQ : 1 ≤ Q := rationalKernelHeight_pos m hB
  have hC : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) C :=
    markedShiftBasis_structure_height F b ω hF hω v w marked hH hc t e he
  have hproj : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q := hf
  have hmatrix (i j) : RationalHeightLE
      (LinearMap.toMatrix e f (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap i j) V := by
    rw [LinearMap.toMatrix_apply]
    exact (hproj i j).mono ((Nat.le_max_right C Q).trans (Nat.le_max_right 1 _))
  obtain ⟨_, _, _, hstructure⟩ := exists_bounded_lie_quotient_section e f
    (lieQuotientMap (markedShiftSecondIdeal F v w marked t)) (lieQuotientMap_surjective _)
    (Nat.le_max_left 1 (max C Q))
    (fun i j k => (hC i j k).mono ((Nat.le_max_left C Q).trans (Nat.le_max_right 1 _))) hmatrix
  have hphaseR : (d + 1) * (rationalSolveHeight q Q * T) ^ d ≤ R := by
    apply le_trans _ (Nat.le_max_right G _)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_max_left _ _)) _)
  have hevalR : (d + 1) *
      (rationalSolveHeight q Q * ((Fintype.card ι + 1) * (T * K) ^ Fintype.card ι)) ^ d ≤ R := by
    apply le_trans _ (Nat.le_max_right G _)
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (Nat.le_max_right _ _)) _)
  refine ⟨m, hm, q, hq, f, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j k
    apply RationalHeightLE.mono _ hGR
    change RationalHeightLE _ (max (rationalLieStructureHeight d (max V (rationalSolveHeight q V)))
      ((d + 1) * (B * Q) ^ d))
    apply RationalHeightLE.mono _ (Nat.le_max_left _ _)
    simpa only [Fintype.card_fin] using hstructure i j k
  · intro α
    obtain ⟨e', he'⟩ := exists_markedShiftQuotientLayer_bounded_basis
      F b ω hF v w marked hw hv hH hc hgen hω t e he f hproj α
    refine ⟨e', ?_⟩
    intro i j
    exact (he' i j).mono ((Nat.le_max_right _ _).trans hGR)
  · intro i j
    exact (markedQuotientDirection_coordinate_height F v w marked t b ω hF hω hT
      e he f hproj i j).mono ((Nat.le_max_right _ _).trans hGR)
  · intro i j
    exact (markedQuotientPhase_coordinate_height F v w marked t b ω hF e he f hQ hproj i j).mono hphaseR
  · intro i j
    exact (markedBaseEvaluation_zero_coordinate_height F v w marked t b ω hF e he f hQ hproj
      J hJ c hcoef i j).mono hevalR

end Erdos3

end

end OAI

end


