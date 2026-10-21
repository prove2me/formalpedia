-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P15
-- name    : QAlgorithms_Papers_Independent_Support21_P15
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T04:33:45.216694+00:00
-- url     : https://prove2.me/theorems/33c4c38d-d958-4487-a57a-d25565fa226d
-- title:
--   Definitions for On subspaces of non-commutative L_p-spaces
-- statement:
--   The objects the formalized statements of *On subspaces of non-commutative L_p-spaces* (arXiv:math/0307169) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ComplexQuasiNorm`: Complex quasi-norm axioms for the abstract spaces on PDF pp.14--15. Only the defining vector-space axioms are fields, with no embedding conclusions.
--   - `normQuasiNorm`: Ordinary norms are particular quasi-norms; used to pin the Banach regime.
--   - `GaugeComplete`: Completeness in the quasi-norm topology, PDF p.15: every gauge-Cauchy sequence has a gauge limit. This is the usual completeness of a quasi-normed space.
--   - `IsSourcePBanach`: The abstract category in Lemma 3.2, PDF p.15: Banach for p≥1, and p-Banach for 0<p<1, using the specified quasi-norm.
--   - `finiteLpSize`: The finite p-direct-sum quasi-norm, PDF p.14. Used only at p>0.
--   - `coefficientLpSize`: The norm of finite scalar coefficients in the ell_p basis, PDF p.7.
--   - `coefficientVector`: A finite linear combination of the given sequence, PDF p.7.
--   - `EquivalentLp`: Basis equivalence with distortion K, PDF p.7: two positive scale constants with ratio at most K, bounding every finitely supported complex combination. In a complete quasi-normed space these inequalities say that b is a basic sequence in its closed span, including in the nonlocally convex regime.
--   - `GaugeSpanning`: Density of the finite linear span, in the quasi-norm topology of PDF p.15. Together with EquivalentLp this specifies a basis of the whole space.
--   - `FiniteLpEmbedding`: K-isomorphic finite p-sum embedding, PDF pp.14--15. Continuity and continuity of the inverse on the image are exactly the two gauge bounds.
--   - `ComplementedRange`: C-complementation in the ambient space, PDF pp.14--15. The actual idempotent, its exact range and its bound are tied to the same embedding.
--   - `coordinateVector`: Coordinate vector e_i tensor x in the finite sum, PDF p.14.
--   - `RefinedFiniteEmbedding`: A single embedding has the simultaneous normalized-column property in Lemma 3.2, PDF p.15. Each column is divided by its own norm.
--   - `SuccessiveBlocks`: Successive nonempty finite coefficient blocks of the original basis, PDF p.15. This requires strict ordering of all supports of consecutive blocks.
--   - `schattenBlockInclusion`: Block-diagonal complex-linear inclusion, PDF p.14. Product indices label n blocks of size m, hence the target is the nm-dimensional Schatten matrix space.
--   - `schattenBlockProjection`: Pinching onto the block-diagonal range, PDF p.14. Off-diagonal blocks are set to zero; the norm-one claim below is restricted to p≥1.
-- source:
--   On subspaces of non-commutative L_p-spaces, arXiv:math/0307169v1, https://arxiv.org/abs/math/0307169v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

/-!
Statements from Raynaud--Xu, arXiv:math/0307169v1, PDF pp.14--15.
The other planned nodes are explicitly deferred in the assigned unit artifacts.
The finite-matrix Schatten formula is reused from the pinned accepted library.
Local quasi-norms below one are not installed as ordinary normed-space instances.
The gauges determine convergence, Cauchy sequences and bounded operators directly.
No Haagerup space or Raynaud identification is replaced by abstract assumed data.
Compilation is pending the batch mechanical check.
-/

noncomputable section

open scoped BigOperators
open Filter

namespace QAlgorithms.Papers.Independent.Support21.P15

/-- Complex quasi-norm axioms for the abstract spaces on PDF pp.14--15.
Only the defining vector-space axioms are fields, with no embedding conclusions. -/
structure ComplexQuasiNorm (E : Type*) [AddCommGroup E] [Module ℂ E] where
  size : E → ℝ
  nonneg : ∀ x, 0 ≤ size x
  eq_zero : ∀ x, size x = 0 ↔ x = 0
  smul_size : ∀ (c : ℂ) x, size (c • x) = ‖c‖ * size x
  quasi_triangle : ∃ C : ℝ, 1 ≤ C ∧ ∀ x y, size (x + y) ≤ C * (size x + size y)

/-- Ordinary norms are particular quasi-norms; used to pin the Banach regime. -/
def normQuasiNorm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ComplexQuasiNorm E where
  size x := ‖x‖
  nonneg := norm_nonneg
  eq_zero := fun _ => norm_eq_zero
  smul_size := norm_smul
  quasi_triangle := ⟨1, le_refl 1, fun x y => by simpa using norm_add_le x y⟩

/-- Completeness in the quasi-norm topology, PDF p.15: every gauge-Cauchy
sequence has a gauge limit. This is the usual completeness of a quasi-normed space. -/
def GaugeComplete {E : Type*} [AddCommGroup E] [Module ℂ E]
    (g : ComplexQuasiNorm E) : Prop :=
  ∀ u : ℕ → E,
    (∀ eps : ℝ, 0 < eps → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, g.size (u m - u n) < eps) →
    ∃ x : E, Tendsto (fun n => g.size (u n - x)) atTop (nhds 0)

/-- The abstract category in Lemma 3.2, PDF p.15: Banach for p≥1,
and p-Banach for 0<p<1, using the specified quasi-norm. -/
def IsSourcePBanach {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p : ℝ) (g : ComplexQuasiNorm E) : Prop :=
  GaugeComplete g ∧
    (if 1 ≤ p then ∀ x y, g.size (x + y) ≤ g.size x + g.size y
     else ∀ x y, g.size (x + y) ^ p ≤ g.size x ^ p + g.size y ^ p)

/-- The finite p-direct-sum quasi-norm, PDF p.14. Used only at p>0. -/
def finiteLpSize {E : Type*} {n : ℕ} (p : ℝ) (size : E → ℝ)
    (x : Fin n → E) : ℝ := (∑ i, size (x i) ^ p) ^ (1 / p)

/-- The norm of finite scalar coefficients in the ell_p basis, PDF p.7. -/
def coefficientLpSize {J : Type*} (p : ℝ) (c : J →₀ ℂ) : ℝ :=
  (c.sum fun _ a => ‖a‖ ^ p) ^ (1 / p)

/-- A finite linear combination of the given sequence, PDF p.7. -/
def coefficientVector {J E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : J → E) (c : J →₀ ℂ) : E := c.sum fun i a => a • b i

/-- Basis equivalence with distortion K, PDF p.7: two positive scale constants
with ratio at most K, bounding every finitely supported complex combination.
In a complete quasi-normed space these inequalities say that b is a basic
sequence in its closed span, including in the nonlocally convex regime. -/
def EquivalentLp {J E : Type*} [AddCommGroup E] [Module ℂ E]
    (p K : ℝ) (g : ComplexQuasiNorm E) (b : J → E) : Prop :=
  ∃ lo : ℝ, 0 < lo ∧ ∃ hi : ℝ, 0 < hi ∧ hi ≤ K * lo ∧
    ∀ c : J →₀ ℂ,
      lo * coefficientLpSize p c ≤ g.size (coefficientVector b c) ∧
      g.size (coefficientVector b c) ≤ hi * coefficientLpSize p c

/-- Density of the finite linear span, in the quasi-norm topology of PDF p.15.
Together with EquivalentLp this specifies a basis of the whole space. -/
def GaugeSpanning {E : Type*} [AddCommGroup E] [Module ℂ E]
    (g : ComplexQuasiNorm E) (b : ℕ → E) : Prop :=
  ∀ x : E, ∀ eps : ℝ, 0 < eps → ∃ c : ℕ →₀ ℂ,
    g.size (x - coefficientVector b c) < eps

/-- K-isomorphic finite p-sum embedding, PDF pp.14--15. Continuity and
continuity of the inverse on the image are exactly the two gauge bounds. -/
def FiniteLpEmbedding {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {n : ℕ}
    (p K : ℝ) (gF : ComplexQuasiNorm F) (gE : ComplexQuasiNorm E)
    (T : (Fin n → F) →ₗ[ℂ] E) : Prop :=
  Function.Injective T ∧ ∃ lo : ℝ, 0 < lo ∧ ∃ hi : ℝ, 0 < hi ∧ hi ≤ K * lo ∧
    ∀ x, lo * finiteLpSize p gF.size x ≤ gE.size (T x) ∧
      gE.size (T x) ≤ hi * finiteLpSize p gF.size x

/-- C-complementation in the ambient space, PDF pp.14--15. The actual
idempotent, its exact range and its bound are tied to the same embedding. -/
def ComplementedRange {D E : Type*} [AddCommGroup D] [Module ℂ D]
    [AddCommGroup E] [Module ℂ E] (g : ComplexQuasiNorm E)
    (C : ℝ) (T : D →ₗ[ℂ] E) : Prop :=
  ∃ P : E →ₗ[ℂ] E, P.comp P = P ∧ LinearMap.range P = LinearMap.range T ∧
    ∀ x, g.size (P x) ≤ C * g.size x

/-- Coordinate vector e_i tensor x in the finite sum, PDF p.14. -/
def coordinateVector {F : Type*} [Zero F] {n : ℕ} (i : Fin n) (x : F) : Fin n → F :=
  fun j => if j = i then x else 0

/-- A single embedding has the simultaneous normalized-column property in
Lemma 3.2, PDF p.15. Each column is divided by its own norm. -/
def RefinedFiniteEmbedding {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F] {n : ℕ}
    (p K eps : ℝ) (gF : ComplexQuasiNorm F) (gE : ComplexQuasiNorm E)
    (T : (Fin n → F) →ₗ[ℂ] E) : Prop :=
  FiniteLpEmbedding p K gF gE T ∧ ∀ x : F, x ≠ 0 →
    EquivalentLp p (1 + eps) gE (fun i : Fin n =>
      ((gE.size (T (coordinateVector i x)))⁻¹ : ℂ) • T (coordinateVector i x))

/-- Successive nonempty finite coefficient blocks of the original basis,
PDF p.15. This requires strict ordering of all supports of consecutive blocks. -/
def SuccessiveBlocks (c : ℕ → (ℕ →₀ ℂ)) : Prop :=
  (∀ n, (c n).support.Nonempty) ∧
    ∀ n, ∀ i ∈ (c n).support, ∀ j ∈ (c (n + 1)).support, i < j

/-- Block-diagonal complex-linear inclusion, PDF p.14. Product indices label
n blocks of size m, hence the target is the nm-dimensional Schatten matrix space. -/
def schattenBlockInclusion (n m : ℕ) :
    (Fin n → Matrix (Fin m) (Fin m) ℂ) →ₗ[ℂ]
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ where
  toFun x i j := if i.1 = j.1 then x i.1 i.2 j.2 else 0
  map_add' x y := by
    ext i j
    change (if i.1 = j.1 then x i.1 i.2 j.2 + y i.1 i.2 j.2 else 0) =
      (if i.1 = j.1 then x i.1 i.2 j.2 else 0) +
        (if i.1 = j.1 then y i.1 i.2 j.2 else 0)
    by_cases h : i.1 = j.1 <;> simp [h]
  map_smul' c x := by
    ext i j
    change (if i.1 = j.1 then c * x i.1 i.2 j.2 else 0) =
      c * (if i.1 = j.1 then x i.1 i.2 j.2 else 0)
    by_cases h : i.1 = j.1 <;> simp [h]

/-- Pinching onto the block-diagonal range, PDF p.14. Off-diagonal blocks
are set to zero; the norm-one claim below is restricted to p≥1. -/
def schattenBlockProjection (n m : ℕ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ →ₗ[ℂ]
      Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ where
  toFun x i j := if i.1 = j.1 then x i j else 0
  map_add' x y := by
    ext i j
    change (if i.1 = j.1 then x i j + y i j else 0) =
      (if i.1 = j.1 then x i j else 0) + (if i.1 = j.1 then y i j else 0)
    by_cases h : i.1 = j.1 <;> simp [h]
  map_smul' c x := by
    ext i j
    change (if i.1 = j.1 then c * x i j else 0) =
      c * (if i.1 = j.1 then x i j else 0)
    by_cases h : i.1 = j.1 <;> simp [h]

example (z : ℂ) : (normQuasiNorm ℂ).size z = ‖z‖ := rfl

example (z : ℂ) : finiteLpSize 1 (fun w : ℂ => ‖w‖) (fun _ : Fin 1 => z) = ‖z‖ := by
  simp [finiteLpSize]

example {F : Type*} [Zero F] {n : ℕ} (i : Fin n) (x : F) :
    coordinateVector i x i = x := by simp [coordinateVector]

example (x : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ) :
    schattenBlockInclusion 2 1 x (0, 0) (1, 0) = 0 := by
  change (if (0 : Fin 2) = 1 then x 0 0 0 else 0) = 0
  simp

example (x : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) :
    schattenBlockProjection 1 1 x = x := by
  ext i j
  change (if i.1 = j.1 then x i j else 0) = x i j
  exact if_pos (Subsingleton.elim i.1 j.1)

end QAlgorithms.Papers.Independent.Support21.P15


