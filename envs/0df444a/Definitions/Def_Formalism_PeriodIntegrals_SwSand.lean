-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_SwSand
-- name    : Formalism_PeriodIntegrals_SwSand
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:01:54.79448+00:00
-- url     : https://prove2.me/theorems/1a920608-8ad0-4244-a509-f0f097c741d7
-- title:
--   Sw Sand
-- statement:
--   Definitions and structural lemmas for Sw Sand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/SwSand.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology Classical
open scoped ENNReal NNReal
namespace PI.SwSand
open PI.SwBig
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ
def realifyFun {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) : Fin m × Fin m × Bool → ℝ :=
  fun p => if p.2.2 then (X p.1 p.2.1).im else (X p.1 p.2.1).re
def unrealify {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => ⟨x (i, j, false), x (i, j, true)⟩
def lieOf {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Set (Matrix (Fin m) (Fin m) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ S}
def lieE {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) : Submodule ℝ (EuclideanSpace ℝ (Fin m × Fin m × Bool)) :=
  Submodule.span ℝ ((fun X => (WithLp.equiv 2 _).symm (realifyFun X)) '' lieOf S)
variable {k r : ℕ}
def dg (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k
def Fil (p : ℕ) (X : Mat k r) : Prop := ∀ i j, dg k r j < dg k r i + p → X i j = 0
theorem Fil.add {p : ℕ} {X Y : Mat k r} (hX : Fil p X) (hY : Fil p Y) : Fil p (X + Y) := by
  unfold PI.SwSand.Fil at hX hY ⊢
  intro i j h
  rw [Matrix.add_apply, hX i j h, hY i j h, add_zero]
theorem Fil.smul {p : ℕ} {X : Mat k r} (c : ℂ) (hX : Fil p X) : Fil p (c • X) := by
  unfold PI.SwSand.Fil at hX ⊢
  intro i j h
  rw [Matrix.smul_apply, hX i j h, smul_zero]
theorem Fil.zero (p : ℕ) : Fil p (0 : Mat k r) := by
  unfold PI.SwSand.Fil
  intro i j _
  exact Matrix.zero_apply i j
def adjH (X : Mat k r) : Mat k r := Hpk k r * Xᴴ * Hpk k r
theorem adjH_add (X Y : Mat k r) : adjH (X + Y) = adjH X + adjH Y := by
  simp only [adjH, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
theorem adjH_smul (c : ℂ) (X : Mat k r) : adjH (c • X) = star c • adjH X := by
  simp only [adjH, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
def lieN (k r : ℕ) : Set (Mat k r) := {X | Fil 1 X ∧ adjH X + X = 0}
theorem lieN_smul {X : Mat k r} (hX : X ∈ lieN k r) (t : ℝ) : ((t : ℂ) • X) ∈ lieN k r := by
  obtain ⟨h1, h2⟩ := hX
  show Fil 1 ((t : ℂ) • X) ∧ adjH ((t : ℂ) • X) + (t : ℂ) • X = 0
  refine ⟨h1.smul _, ?_⟩
  rw [adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, h2, smul_zero]
theorem lieN_add {X Y : Mat k r} (hX : X ∈ lieN k r) (hY : Y ∈ lieN k r) : X + Y ∈ lieN k r := by
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  show Fil 1 (X + Y) ∧ adjH (X + Y) + (X + Y) = 0
  refine ⟨hX1.add hY1, ?_⟩
  rw [adjH_add, add_add_add_comm, hX2, hY2, add_zero]
theorem zero_mem_lieN : (0 : Mat k r) ∈ lieN k r := by
  show Fil 1 (0 : PI.SwBig.Mat k r) ∧ adjH (0 : PI.SwBig.Mat k r) + 0 = 0
  exact ⟨PI.SwSand.Fil.zero 1, by simp [adjH]⟩
def lieNS (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := lieN k r
  add_mem' := lieN_add
  zero_mem' := zero_mem_lieN
  smul_mem' := fun c X hX => by
    show c • X ∈ lieN k r
    rw [← Complex.coe_smul]; exact lieN_smul hX c
def RL : Mat k r →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]
  map_smul' c X := by
    ext p
    rcases p with ⟨i, j, b⟩
    cases b <;> simp [realifyFun]
def expBall (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (ρ : ℝ) : Set (Mt k r) :=
  (fun x : lieE S =>
      fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) '' Metric.ball 0 ρ
def gBall (k r : ℕ) (ρ : ℝ) : Set (Mt k r) := expBall (k := k) (r := r) (UH (Hpk k r)) ρ
def rhoS (k r : ℕ) (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (x : Mt k r) : ℝ≥0∞ :=
  ⨅ (Y : lieE S)
    (_ : (fun i j => NormedSpace.exp (unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x),
    (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
def Qf (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : ℝ≥0∞ :=
  rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) + rhoS k r (UWb k r) m ^ 2 +
    rhoS k r (Nset k r) n' ^ 2
def Psi (k r : ℕ) (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) : Mt k r :=
  fun i j => (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) i j
def Sandwich : Prop :=
  ∀ (k r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < δ →
    ∀ (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r), Matrix.of n ∈ Nset k r → Matrix.of m ∈ UWb k r →
      Matrix.of n' ∈ Nset k r →
      (Psi k r n c m n' ∈ gBall k r ρ → Qf k r n c m n' < ENNReal.ofReal (((1 + ε) * ρ) ^ 2)) ∧
      (Qf k r n c m n' < ENNReal.ofReal (((1 - ε) * ρ) ^ 2) → Psi k r n c m n' ∈ gBall k r ρ)
def Mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k
def uH (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_ofPred_eq] at *
    rw [adjH_add, show adjH X + adjH Y + (X + Y) = (adjH X + X) + (adjH Y + Y) by abel, hX, hY, add_zero]
  zero_mem' := by simp [adjH]
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_ofPred_eq] at *
    rw [← Complex.coe_smul, adjH_smul, Complex.star_def, Complex.conj_ofReal, ← smul_add, hX, smul_zero]
def uWb (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | adjH X + X = 0 ∧ ∀ i j, ¬ (Mid k r i ∧ Mid k r j) → X i j = 0}
  add_mem' := by
    intro X Y hX hY
    refine ⟨(uH k r).add_mem hX.1 hY.1, fun i j h => ?_⟩
    simp [hX.2 i j h, hY.2 i j h]
  zero_mem' := ⟨(uH k r).zero_mem, fun i j _ => rfl⟩
  smul_mem' := by
    intro c X hX
    refine ⟨(uH k r).smul_mem c hX.1, fun i j h => ?_⟩
    simp [hX.2 i j h]
def Vs (k r : ℕ) : Submodule ℝ (Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) :=
  (lieNS k r).prod ((⊤ : Submodule ℝ (Fin r → ℂ)).prod ((uWb k r).prod (lieNS k r)))
def LieG : Prop := ∀ k r : ℕ, lieE (UH (Hpk k r)) = (uH k r).map RL
def LieWb : Prop := ∀ k r : ℕ, (∀ Z ∈ uWb k r, NormedSpace.exp Z ∈ UWb k r) ∧
  lieE (UWb k r) = (uWb k r).map RL
def LIso : Prop := ∀ k r : ℕ, (∀ v ∈ Vs k r, Lm k r v ∈ uH k r) ∧ (∀ Y ∈ uH k r, ∃ v ∈ Vs k r, Lm k r v = Y) ∧
  ∀ v ∈ Vs k r, ‖RL (Lm k r v)‖ ^ 2 = ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2
def LieEN : Prop := ∀ k r : ℕ, lieE (Nset k r) = (lieNS k r).map RL
def ExpN : Prop := ∀ (k r : ℕ) (X : Mat k r), X ∈ lieN k r → NormedSpace.exp X ∈ Nset k r
def SandwichOf : Prop :=
  LieG → LieWb → GaussUniq → PhiForm → BigCellG → PhiDeriv → LIso → LongWeylElementSquare → LieEN → ExpN → Sandwich
end PI.SwSand


