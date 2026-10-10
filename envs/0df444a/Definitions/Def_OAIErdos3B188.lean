-- Prove2me | Definitions.Def_OAIErdos3B188
-- name    : OAIErdos3B188
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T08:52:31.663315+00:00
-- url     : https://prove2.me/theorems/0ca4c965-c188-4272-8a5c-38bd34e85048
-- title:
--   OpenAI Erdős-3 split, definitions bundle 189 of 205
-- statement:
--   Definitions bundle 189 of 205 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B187`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 189 available.
--
--   Modules: `OAI.Erdos3.exists_markedShiftLayer_bounded_basis`, `OAI.Erdos3.exists_markedShiftLayer_coordinate_basis`, `OAI.Erdos3.exists_markedShiftQuotientLayer_bounded_basis`, `OAI.Erdos3.exists_markedShiftQuotient_bounded_coordinates`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B190

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedShiftGeneratorBounds
namespace OAI

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (t : ℕ)

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {I L : Type*} [Fintype I] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial NilpotentLieBCHGroup

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

end Erdos3

end

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

variable {I σ ι L : Type*} [Fintype I] [Fintype σ] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L]

variable {s r : ℕ} (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (v : I → L) (w : I → ℕ) (marked : I → Bool) (hw : ∀ i, 0 < w i)
  (hv : ∀ i, v i ∈ F.layer (w i) 1) {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

omit [Fintype σ] in
include hw hv hH hc hgen in
theorem exists_markedShiftLayer_bounded_basis (hω : ∀ i, ω i ≤ s) (t h n : ℕ) :
    ∃ e : Basis (Fin (finrank ℚ (markedShiftBiLayer F v w marked t h n))) ℚ
        (markedShiftBiLayer F v w marked t h n),
      ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
        (e i).val.val j) (lieTreeHeight (Fintype.card ι) H s) := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ
    (Set.range (markedShiftGenerator F v w marked hw hv t h n))
  rw [markedShiftGenerator_span] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro i j
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz i
  rw [← hk]
  exact markedShiftGenerator_coordinate_height F b ω hF v w marked hw hv hH hc hgen t h n k j

end Erdos3

end

end OAI

end

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
theorem exists_markedShiftLayer_coordinate_basis (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s)) (h n : ℕ) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∃ c : Basis (Fin (finrank ℚ (markedShiftBiLayer F v w marked t h n))) ℚ
        (markedShiftBiLayer F v w marked t h n),
      ∀ i j, RationalHeightLE (e.repr (c i).val j)
        ((a + 1) * (rationalSolveHeight d T * T) ^ a) := by
  classical
  dsimp only
  let _ : Fintype (NilpotentLieFiltration.AdaptedBasisIndex (fun _ : Fin t => 1) ω) :=
    NilpotentLieFiltration.adaptedBasisIndexFintype (fun _ : Fin t => 1) ω s (by simp) hω
  obtain ⟨c, hc'⟩ := exists_markedShiftLayer_bounded_basis F b ω hF v w marked hw hv hH hc hgen hω t h n
  refine ⟨c, ?_⟩
  intro i j
  have hb := embedding_basis_coordinate_height e (F.associatedDegree.polynomialShiftBasis b ω hF t)
    (markedShiftSubalgebra F v w marked t).incl.toLinearMap
    (fun _ _ h => Subtype.ext h) (hH.trans (lieTreeHeight_ge_input _ _ _))
    (fun j i => he i j) (c i).val (hc' i) j
  simpa only [Fintype.card_fin,
    ← finrank_eq_card_basis (F.associatedDegree.polynomialShiftBasis b ω hF t)] using hb

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

include hw hv hH hc hgen in
theorem exists_markedShiftQuotient_bounded_coordinates (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s)) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
    ∃ m : ℕ, m ≤ finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ∧
      ∃ q : ℕ, q ≤ d ∧ ∃ f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t),
        ∀ i j, RationalHeightLE
          (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i)
          (rationalKernelHeight m B) := by
  let T := lieTreeHeight (Fintype.card ι) H s
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
  have hT : 1 ≤ T := hH.trans (lieTreeHeight_ge_input _ _ _)
  have hsolve : 0 < rationalSolveHeight d T := rationalSolveHeight_pos d hT
  have hB : 1 ≤ B := by
    have hTpos : 0 < T := Nat.zero_lt_of_lt hT
    exact Nat.one_le_iff_ne_zero.mpr (by dsimp [B]; positivity)
  have hex := exists_markedShiftLayer_coordinate_basis F b ω hF v w marked hw hv hH hc hgen hω t e he 2 0
  dsimp only at hex
  rw [markedShiftBiLayer_second] at hex
  obtain ⟨c, hc'⟩ := hex
  have hcoords : ∀ i j, RationalHeightLE (e.repr (c i).val j) B := hc'
  obtain ⟨m, hm, q, hq, f, hf⟩ := exists_bounded_submodule_quotient_basis e
    (markedShiftSecondIdeal F v w marked t).toSubmodule (fun i => (c i).val)
    (span_submodule_basis _ c) hB hcoords
  refine ⟨m, ?_, q, ?_, f, hf⟩
  · simpa only [Fintype.card_fin] using hm
  · simpa only [Fintype.card_fin] using hq

include hw hv hH hc hgen in
theorem exists_markedShiftQuotientLayer_bounded_basis (hω : ∀ i, ω i ≤ s) (t : ℕ)
    (e : Basis (Fin (finrank ℚ (markedShiftSubalgebra F v w marked t))) ℚ
      (markedShiftSubalgebra F v w marked t))
    (he : ∀ i j, RationalHeightLE ((F.associatedDegree.polynomialShiftBasis b ω hF t).repr
      (e i).val j) (lieTreeHeight (Fintype.card ι) H s))
    {q Q : ℕ} (f : Basis (Fin q) ℚ (MarkedShiftQuotient F v w marked t))
    (hf : ∀ i j, RationalHeightLE
      (f.repr (lieQuotientMap (markedShiftSecondIdeal F v w marked t) (e j)) i) Q)
    (α : Fin 2 → ℕ) :
    let T := lieTreeHeight (Fintype.card ι) H s
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    let B := (a + 1) * (rationalSolveHeight d T * T) ^ a
    ∃ c : Basis (Fin (finrank ℚ (markedShiftQuotientLayer F v w marked t α))) ℚ
        (markedShiftQuotientLayer F v w marked t α),
      ∀ i j, RationalHeightLE (f.repr (c i).val j) ((d + 1) * (B * Q) ^ d) := by
  dsimp only
  obtain ⟨c, hc'⟩ := exists_markedShiftLayer_coordinate_basis F b ω hF v w marked hw hv hH hc hgen
    hω t e he (α 0) (α 1)
  let π := (lieQuotientMap (markedShiftSecondIdeal F v w marked t)).toLinearMap
  have hspan : Submodule.span ℚ (Set.range (fun i => π (c i).val)) =
      markedShiftQuotientLayer F v w marked t α := by
    change Submodule.span ℚ (Set.range (π ∘ (fun i => (c i).val))) = _
    rw [Set.range_comp, ← Submodule.map_span, span_submodule_basis]
    rfl
  apply exists_bounded_submodule_basis_from_spanning f _ (fun i => π (c i).val) hspan
  intro i j
  have h := linearMap_coordinate_height e f π (fun i j => hf j i) (c i).val (hc' i) j
  simpa only [Fintype.card_fin] using h

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


