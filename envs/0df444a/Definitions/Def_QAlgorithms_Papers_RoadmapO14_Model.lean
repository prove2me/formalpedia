-- Prove2me | Definitions.Def_QAlgorithms_Papers_RoadmapO14_Model
-- name    : QAlgorithms_Papers_RoadmapO14_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:27:21.620538+00:00
-- url     : https://prove2.me/theorems/717790c7-f2a6-4727-929a-d6be1f238db7
-- title:
--   Convex optimization using quantum oracles: supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Convex optimization using quantum oracles, arXiv:1809.00643v4, https://arxiv.org/abs/1809.00643v4. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_GridSubgradientPrograms
noncomputable section

namespace QAlgorithms.Papers.RoadmapO14

open QAlgorithms.ValueAccess

/-! Chunk-local geometric access objects submitted in DEFINITION_REVIEW.md.
They assert no oracle success, local linearity, or curvature event. -/

/-- Finite regular query grid with compatible finite-difference radii.
Source: arXiv:1809.00643v4, pp.8-10, Lemma 18 and footnote 8, p.12. -/
structure SubgradientGrid (n : ℕ) where
  axisSize : ℕ
  axisSize_pos : 0 < axisSize
  mesh : ℝ
  origin : ℝ
  centerSpacing : ℝ
  centerTicks : ℕ
  differenceTicks : ℕ
  localBits : ℕ

/-- The query register stores the exact grid index, separately from its affine coordinates. -/
abbrev GridIndex {n : ℕ} (H : SubgradientGrid n) := Fin n → Fin H.axisSize

instance {n : ℕ} (H : SubgradientGrid n) : Nonempty (GridIndex H) :=
  ⟨fun _ => ⟨0, H.axisSize_pos⟩⟩

/-- Known affine coordinates of a finite binary-encoded grid index. -/
def queryPoint {n : ℕ} (H : SubgradientGrid n) (z : GridIndex H) : Fin n → ℝ :=
  fun i => H.origin + H.mesh * (z i : ℕ)

/-- Uniform center grid, at cell midpoints of the rounded inner cube. -/
def centerPoint {n : ℕ} (H : SubgradientGrid n)
    (z : Fin n → Fin (2 * H.centerTicks)) : Fin n → ℝ :=
  fun i => H.centerSpacing * ((z i : ℕ) + (1 / 2 : ℝ) - H.centerTicks)

/-- Geometric resolution and rounding conditions. The arithmetic guards preserve the
printed coefficient and near-linearity tolerance after rounding; they contain no f or U.
The precision threshold in the theorem is existential, not an attributed numeric bound. -/
def HasSubgradientGeometry {n : ℕ} (H : SubgradientGrid n)
    (r1 L delta rho precision : ℝ) : Prop :=
  let a : ℝ := H.centerSpacing * H.centerTicks
  let b : ℝ := H.centerSpacing * H.differenceTicks
  let r2 : ℝ := Real.sqrt (delta * r1 * rho / ((n : ℝ) * L))
  0 < H.mesh ∧ H.mesh ≤ precision ∧
  0 < H.centerSpacing ∧ H.centerSpacing ≤ precision ∧
  1 ≤ H.differenceTicks ∧ H.differenceTicks ≤ H.centerTicks ∧
  a ≤ r1 ∧ r1 - a ≤ precision ∧ b ≤ r2 ∧ r2 - b ≤ precision ∧
  (2 * b / n) * ((2 : ℝ) ^ H.localBits)⁻¹ ≤ precision ∧
  L * (2 * b / n) ≤ 28 * Real.pi * delta * (2 : ℝ) ^ H.localBits ∧
  (n : ℝ) * L * b ^ 2 / (rho * a) ≤ delta ∧
  (n : ℝ) * L * b / (rho * a) + 168 * Real.pi * delta * n / b ≤
    529 * Real.sqrt (delta * (n : ℝ) ^ 3 * L / (rho * r1)) ∧
  (∀ z : GridIndex H, ∀ i, |queryPoint H z i| ≤ 2 * r1) ∧
  (∃ index : (Fin n → Fin (2 * H.centerTicks)) → GridIndex H,
    ∀ z, queryPoint H (index z) = centerPoint H z) ∧
  (∃ index : (Fin n → Fin (2 * H.centerTicks)) →
      (Fin n → Qubits H.localBits) → GridIndex H,
    ∀ z u i, queryPoint H (index z u) i =
      centerPoint H z i + (2 * b / n) * gridPoint H.localBits (u i)) ∧
  (∃ index : (Fin n → Fin (2 * H.centerTicks)) → Fin n → Bool → GridIndex H,
    ∀ z j sign i, queryPoint H (index z j sign) i =
      centerPoint H z i + (if i = j then (if sign then b else -b) else 0))

/-- Standing assumptions of section 3: convex domain and objective, and Euclidean
Lipschitzness only on the closed outer cube. Its inclusion implies 0 is interior to C. -/
def IsLemma18Function {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (r1 L : ℝ) : Prop :=
  Convex ℝ C ∧ ConvexOn ℝ C f ∧
  {x : Fin n → ℝ | ∀ i, |x i| ≤ 2 * r1} ⊆ C ∧
  ∀ x y : Fin n → ℝ, (∀ i, |x i| ≤ 2 * r1) → (∀ i, |y i| ≤ 2 * r1) →
    |f x - f y| ≤ L * euclidNorm (x - y)

/-- Both printed inequalities, simultaneously for every y in C.
Lemma 18, arXiv:1809.00643v4, p.12. The omitted norm is Euclidean. -/
def SubgradientEvent {n : ℕ} (C : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (r1 L delta rho : ℝ) (g : Fin n → ℝ) : Prop :=
  ∀ y ∈ C,
    f 0 + g ⬝ᵥ y - 23 ^ 2 * Real.sqrt (delta * (n : ℝ) ^ 3 * L / (rho * r1)) *
      (∑ i, |y i|) - 2 * L * Real.sqrt n * r1 ≤ f y ∧
    f 0 + g ⬝ᵥ y - (23 * (n : ℝ)) ^ 2 * Real.sqrt (delta * L / (rho * r1)) *
      euclidNorm y - 2 * L * Real.sqrt n * r1 ≤ f y


end QAlgorithms.Papers.RoadmapO14


