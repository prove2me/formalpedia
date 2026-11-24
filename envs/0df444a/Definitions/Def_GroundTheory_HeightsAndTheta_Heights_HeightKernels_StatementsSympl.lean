-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:36.222546+00:00
-- url     : https://prove2.me/theorems/61c9d6cc-34f0-4903-ad5c-e3e2f3d9c4c1
-- title:
--   Statements Sympl
-- statement:
--   Definitions and structural lemmas for Statements Sympl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsSympl.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open Matrix
noncomputable section
def symplOmega {R : Type*} [CommRing R] {l : Type*} [Fintype l] [DecidableEq l]
    (u v : l ⊕ l → R) : R :=
  u ⬝ᵥ (J l R *ᵥ v)
def symplCons {R : Type*} {n : ℕ} (p q : R) (w : Fin n ⊕ Fin n → R) :
    Fin (n + 1) ⊕ Fin (n + 1) → R :=
  Sum.elim (vecCons p fun j => w (Sum.inl j)) (vecCons q fun j => w (Sum.inr j))
def symplTail {R : Type*} {n : ℕ} (u : Fin (n + 1) ⊕ Fin (n + 1) → R) : Fin n ⊕ Fin n → R :=
  fun x => u (Sum.map Fin.succ Fin.succ x)
def symplExt {R : Type*} [Zero R] {n : ℕ} (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) R :=
  Matrix.of (Sum.elim (vecCons (symplCons α β 0) fun i => symplCons 0 0 (Q (Sum.inl i)))
    (vecCons (symplCons γ δ 0) fun i => symplCons 0 0 (Q (Sum.inr i))))
def symplReduce {n : ℕ} (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  fun a b => H (Sum.map Fin.succ Fin.succ a) (Sum.map Fin.succ Fin.succ b) -
    H (Sum.map Fin.succ Fin.succ a) (Sum.inl 0) * H (Sum.inl 0) (Sum.map Fin.succ Fin.succ b) /
      H (Sum.inl 0) (Sum.inl 0)
def symplGram {l : Type*} [Fintype l] (P : Matrix l l ℤ) (G : Matrix l l ℝ) : Matrix l l ℝ :=
  P.map (Int.cast : ℤ → ℝ) * G * (P.map (Int.cast : ℤ → ℝ))ᵀ
def SymplOmegaMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (l : Type) [Fintype l] [DecidableEq l]
    (M : Matrix (l ⊕ l) (l ⊕ l) R),
    M ∈ symplecticGroup l R ↔ ∀ x y, symplOmega (M x) (M y) = J l R x y
def SymplCons.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ),
    (∀ u : Fin (n + 1) ⊕ Fin (n + 1) → R,
      symplCons (u (Sum.inl 0)) (u (Sum.inr 0)) (symplTail u) = u) ∧
    ∀ (p q p' q' : R) (w w' : Fin n ⊕ Fin n → R),
      symplOmega (symplCons p q w) (symplCons p' q' w') = q * p' - p * q' + symplOmega w w'
def SymplExtMem.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ : R) (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R),
    α * δ - β * γ = 1 → Q ∈ symplecticGroup (Fin n) R →
    symplExt α β γ δ Q ∈ symplecticGroup (Fin (n + 1)) R
def SymplExtVecMul.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (α β γ δ p q : R)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (w : Fin n ⊕ Fin n → R),
    symplCons p q w ᵥ* symplExt α β γ δ Q = symplCons (p * α + q * γ) (p * β + q * δ) (w ᵥ* Q)
def SymplTwoRow.Statement : Prop :=
  ∀ (n : ℕ) (c d x y : ℤ), x * c + y * d = 1 →
    ∃ P ∈ symplecticGroup (Fin (n + 1 + 1)) ℤ, P (Sum.inl 0) = symplCons c 0 (symplCons d 0 0)
def SymplGcd.Statement : Prop :=
  ∀ a b : ℤ, ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1
def SymplOrbit.Statement : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ),
    ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, ∃ m : ℤ, v = m • P (Sum.inl 0)
def SymplQuadDiag.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ (O : Matrix ι ι ℝ) (lam : ι → ℝ), (∀ i, 0 < lam i) ∧ |O.det| = 1 ∧ ∏ i, lam i = G.det ∧
      ∀ x : ι → ℝ, qf G x = ∑ i, lam i * (O *ᵥ x) i ^ 2
def SymplBoxVolume.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), A.det ≠ 0 →
    (∀ i, 0 < a i) →
    MeasureTheory.volume {x : ι → ℝ | ∀ i, |(A *ᵥ x) i| < a i} =
      ENNReal.ofReal ((∏ i, 2 * a i) / |A.det|)
def SymplMinkowskiBox.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (a : ι → ℝ), |A.det| = 1 →
    (∀ i, 0 < a i) → 1 < ∏ i, a i →
    ∃ v : ι → ℤ, v ≠ 0 ∧ ∀ i, |(A *ᵥ intVec v) i| < a i
def SymplMinExists.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∃ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m
def SymplMinBound.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef → G.det = 1 →
    ∀ m : ℝ, IsLeast {t | ∃ v : ι → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} m → m ≤ Fintype.card ι
def SymplShortPrim.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ), G.PosDef →
    ∀ (v w : ι → ℤ) (m : ℤ), v = m • w → v ≠ 0 →
    (∀ u : ι → ℤ, u ≠ 0 → qf G (intVec v) ≤ qf G (intVec u)) → m = 1 ∨ m = -1
def SymplGramMem.Statement : Prop :=
  ∀ (n : ℕ) (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ)
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    P ∈ symplecticGroup (Fin n) ℤ → G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    symplGram P G ∈ symplecticGroup (Fin n) ℝ ∧ (symplGram P G).PosDef ∧
      (∀ Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ,
        symplGram (Q * P) G = symplGram Q (symplGram P G)) ∧
      ∀ x, symplGram P G x x = qf G (intVec (P x))
def SymplFirstRow.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq
def SymplReduceMem.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H ∈ symplecticGroup (Fin (n + 1)) ℝ → H (Sum.inl 0) (Sum.inl 0) ≠ 0 →
    symplReduce H ∈ symplecticGroup (Fin n) ℝ
def SymplReducePosDef.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    H.PosDef → (symplReduce H).PosDef
def SymplReduceConj.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) (Sum.inl 0) (Sum.inl 0) =
        H (Sum.inl 0) (Sum.inl 0) ∧
      symplReduce (symplExt 1 0 0 1 Q * H * (symplExt 1 0 0 1 Q)ᵀ) = Q * symplReduce H * Qᵀ
def SymplDetSchur.Statement : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ), A 0 0 ≠ 0 →
    A.det = A 0 0 * (Matrix.of fun i j : Fin n => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0).det
def SymplReduceStep.Statement : Prop :=
  ∀ (n : ℕ) (H : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ),
    H (Sum.inl 0) (Sum.inl 0) ≠ 0 → Q ∈ symplecticGroup (Fin n) ℤ →
    ∃ Q' ∈ symplecticGroup (Fin (n + 1)) ℤ,
      symplGram Q' H (Sum.inl 0) (Sum.inl 0) = H (Sum.inl 0) (Sum.inl 0) ∧
      (symplGram Q' H).toBlocks₁₁.det =
        H (Sum.inl 0) (Sum.inl 0) * (symplGram Q (symplReduce H)).toBlocks₁₁.det
def SymplStep.Statement : Prop :=
  ∀ (n : ℕ) (B : ℝ) (G : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ),
    G ∈ symplecticGroup (Fin (n + 1)) ℝ → G.PosDef →
    (∀ H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ, H ∈ symplecticGroup (Fin n) ℝ → H.PosDef →
      ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P H).toBlocks₁₁.det ≤ B) →
    ∃ ρsq : ℝ, IsLeast {t | ∃ v : Fin (n + 1) ⊕ Fin (n + 1) → ℤ, v ≠ 0 ∧ t = qf G (intVec v)} ρsq ∧
      0 < ρsq ∧ ρsq ≤ 2 * ((n : ℝ) + 1) ∧
      ∃ P ∈ symplecticGroup (Fin (n + 1)) ℤ, symplGram P G (Sum.inl 0) (Sum.inl 0) = ρsq ∧
        (symplGram P G).toBlocks₁₁.det ≤ ρsq * B
def SymplDetBound.Statement : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
    G ∈ symplecticGroup (Fin n) ℝ → G.PosDef →
    ∃ P ∈ symplecticGroup (Fin n) ℤ, (symplGram P G).toBlocks₁₁.det ≤ (2 * (n : ℝ)) ^ n
example (n : ℕ) :
    (1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) ∈
        symplecticGroup (Fin (n + 1)) ℝ ∧
      (1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ).PosDef ∧
      (1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) (Sum.inl 0) (Sum.inl 0) ≠ 0 ∧
      (1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℤ) ∈
        symplecticGroup (Fin (n + 1)) ℤ :=
  ⟨Submonoid.one_mem _, Matrix.PosDef.one, by simp, Submonoid.one_mem _⟩
example : siegelGram (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 ≠ 1 ∧
    siegelGram (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (Sum.inl 0) (Sum.inl 0) ≠ 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun (congrFun h (Sum.inr 0)) (Sum.inr 0)
    simp [siegelGram] at this
  · simp [siegelGram]
example (n : ℕ) : (1 : ℤ) * 1 - 0 * 0 = 1 ∧ (2 : ℤ) * 1 - 1 * 1 = 1 ∧
    (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) ∈ symplecticGroup (Fin n) ℤ :=
  ⟨by norm_num, by norm_num, Submonoid.one_mem _⟩
example : (-1 : ℤ) * 2 + 1 * 3 = 1 := by norm_num
example : (1 : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 ∧ |(1 : Matrix (Fin 2) (Fin 2) ℝ).det| = 1 ∧
    (∀ i : Fin 2, (0 : ℝ) < (fun _ => 2) i) ∧ (1 : ℝ) < ∏ _i : Fin 2, (2 : ℝ) ∧
    (1 : Matrix (Fin 2) (Fin 2) ℝ).PosDef ∧ (1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  refine ⟨by simp, by simp, fun _ => by norm_num, by norm_num, Matrix.PosDef.one, by simp⟩
example : (fun _ : Fin 1 => (1 : ℤ)) = (1 : ℤ) • (fun _ : Fin 1 => (1 : ℤ)) ∧
    (fun _ : Fin 1 => (1 : ℤ)) ≠ 0 ∧
    ∀ u : Fin 1 → ℤ, u ≠ 0 →
      qf (1 : Matrix (Fin 1) (Fin 1) ℝ) (intVec fun _ => (1 : ℤ)) ≤ qf 1 (intVec u) := by
  refine ⟨by simp, fun h => by simpa using congrFun h 0, ?_⟩
  intro u hu
  have h0 : u 0 ≠ 0 := by
    intro h; apply hu; funext i; fin_cases i; exact h
  have h1 : (1 : ℝ) ≤ |(u 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h0
  have h2 : (1 : ℝ) ≤ (u 0 : ℝ) * (u 0 : ℝ) := by
    nlinarith [abs_mul_abs_self (u 0 : ℝ), abs_nonneg (u 0 : ℝ)]
  simpa [qf, intVec, dotProduct] using h2
end
end GroundTheory.Heights₂.Heights


