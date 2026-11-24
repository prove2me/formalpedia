-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementU
-- name    : Formalism_HermitianCurvature_StatementU
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:09:56.137224+00:00
-- url     : https://prove2.me/theorems/54af3a5d-3cfc-41c9-9cef-67928f94d702
-- title:
--   Statement U
-- statement:
--   Definitions and structural lemmas for Statement U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementU.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.U
open Formalism.REAL Formalism.QuantumDeterminants
def mx {α β : Type*} [Fintype α] [Fintype β] (M : Matrix α β ℂ) : ℝ := ‖Matrix.of.symm M‖
abbrev Ix (k j ρ : ℕ) : Type := (Fin j ⊕ Fin (2 * ρ + k + 1)) ⊕ Fin j
def eB (k j ρ : ℕ) : Ix k j ρ ≃ Fin (2 * (j + ρ) + k + 1) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin j))).trans (finSumFinEquiv.trans (finCongr (by omega)))
def blk3 {k j ρ : ℕ}
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ) :
    B.Mat k (j + ρ) :=
  Matrix.reindex (eB k j ρ) (eB k j ρ)
    (Matrix.fromBlocks (Matrix.fromBlocks A11 A12 A21 A22) (Matrix.fromRows A13 A23) (Matrix.fromCols A31 A32) A33)
def mMap (k j ρ : ℕ) (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ) : B.Mat k (j + ρ) :=
  blk3 0 0 (Zᴴ⁻¹ * G.wMat j) 0 γ 0 (G.wMat j * Z) 0 0
def muP (k j ρ : ℕ) (q : Matrix (Fin j) (Fin j) ℂ) : B.Mat k (j + ρ) :=
  blk3 q 0 0 0 1 0 0 0 (G.wMat j * qᴴ⁻¹ * G.wMat j)
def embG (k j ρ : ℕ) (y : B.Mat k ρ) : B.Mat k (j + ρ) := blk3 1 0 0 0 y 0 0 0 1
abbrev RC (k j ρ : ℕ) : Type := (Fin (2 * ρ + k + 1) → Fin j → ℂ) × ((G.UT j → ℂ) × (Fin j → ℝ))
def skewOf {j : ℕ} (q : (G.UT j → ℂ) × (Fin j → ℝ)) : Matrix (Fin j) (Fin j) ℂ :=
  G.strictUpper q.1 - (G.strictUpper q.1)ᴴ + Matrix.diagonal fun i => Complex.I * (q.2 i : ℂ)
def Rn (k j ρ : ℕ) (x : RC k j ρ) : B.Mat k (j + ρ) :=
  blk3 1 (-(G.wMat j * (Matrix.of x.1)ᴴ * Hpk k ρ))
    (G.wMat j * ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2))
    0 1 (Matrix.of x.1) 0 0 1
def Rset (k j ρ : ℕ) : Set (B.Mat k (j + ρ)) :=
  {g | g ∈ B.GV k (j + ρ) ∧
    (∀ i b : Fin (2 * (j + ρ) + k + 1), b.val < j → g i b = if i = b then 1 else 0) ∧
    (∀ i b : Fin (2 * (j + ρ) + k + 1), j ≤ b.val → b.val < j + (2 * ρ + k + 1) → j ≤ i.val →
      g i b = if i = b then 1 else 0)}
def Zh (k j ρ : ℕ) (g : B.Mat k (j + ρ)) : Matrix (Fin j) (Fin j) ℂ :=
  fun a b => g ⟨2 * (j + ρ) + k - a.val, by omega⟩ ⟨b.val, by omega⟩
def DjU (k j ρ : ℕ) (g : B.Mat k (j + ρ)) : ℂ := (Zh k j ρ g).det
def lowV (k j ρ : ℕ) (z : Fin (2 * (j + ρ) + k + 1) → ℂ) : Fin (2 * ρ + k + 1) → ℂ :=
  fun i => z ⟨j + i.val, by omega⟩
def inLieP (k j ρ : ℕ) (X : B.Mat k (j + ρ)) : Prop :=
  B.inLie k (j + ρ) X ∧ ∀ i b : Fin (2 * (j + ρ) + k + 1), b.val < j → j ≤ i.val → X i b = 0
def wP {p : ℕ} (σ : Equiv.Perm (Fin p)) : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun a b => if σ a = b then 1 else 0
def hMat {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ := wP σ * Matrix.diagonal d
abbrev LW {p : ℕ} (σ : Equiv.Perm (Fin p)) : Type :=
  {q : Fin p × Fin p // q.2 < q.1 ∧ σ.symm q.2 < σ.symm q.1}
def lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  1 + Matrix.of fun a b => if h : b < a ∧ σ.symm b < σ.symm a then v ⟨(a, b), h⟩ else 0
def headH {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (v : LW σ → ℂ) (u : G.UT p → ℂ) :
    Matrix (Fin p) (Fin p) ℂ := wP σ * lowW σ v * Matrix.diagonal d * G.upper u
def blk2 {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
    (D : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin (p + s)) (Fin (p + s)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B' C D)
def Zj {p s : ℕ} (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (Z : Matrix (Fin s) (Fin s) ℂ) : Matrix (Fin (p + s)) (Fin (p + s)) ℂ :=
  blk2 1 0 (Matrix.of a) 1 * blk2 H 0 0 Z * blk2 1 (Matrix.of b) 0 1
abbrev XiH (p s : ℕ) (σ : Equiv.Perm (Fin p)) : Type :=
  ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) × ((LW σ → ℂ) × (G.UT p → ℂ))
abbrev Xi (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) : Type := (RC k (p + s) ρ × RC k (p + s) ρ) × XiH p s σ
def muRC (k j ρ : ℕ) : Measure (RC k j ρ) := volume
def muXiH (p s : ℕ) (σ : Equiv.Perm (Fin p)) : Measure (XiH p s σ) := volume
def muXi (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) : Measure (Xi k p s ρ σ) :=
  ((muRC k (p + s) ρ).prod (muRC k (p + s) ρ)).prod (muXiH p s σ)
def ZjH {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : XiH p s σ) (Z : G.Mat s) :
    Matrix (Fin (p + s)) (Fin (p + s)) ℂ := Zj η.1.1 η.1.2 (headH σ d η.2.1 η.2.2) (Matrix.of Z)
def gaXi (k : ℕ) {p s : ℕ} (ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : Xi k p s ρ σ) (Z : G.Mat s)
    (γ : B.Mat k ρ) : B.Mat k (p + s + ρ) :=
  (Rn k (p + s) ρ ξ.1.1)⁻¹ * mMap k (p + s) ρ (ZjH σ d ξ.2 Z) γ * Rn k (p + s) ρ ξ.1.2
def subS {p : ℕ} (l : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  ∑ i : Fin p, if h : i.val + 1 < p then l ⟨i.val + 1, h⟩ i else 0
def supS {p : ℕ} (u : Matrix (Fin p) (Fin p) ℂ) : ℂ :=
  ∑ i : Fin p, if h : i.val + 1 < p then u i ⟨i.val + 1, h⟩ else 0
def cornerA {p s : ℕ} (a : Fin s → Fin p → ℂ) : ℂ :=
  if h : 0 < s ∧ 0 < p then a ⟨0, h.1⟩ ⟨p - 1, by omega⟩ else 0
def cornerB {p s : ℕ} (b : Fin p → Fin s → ℂ) : ℂ :=
  if h : 0 < s ∧ 0 < p then b ⟨p - 1, by omega⟩ ⟨0, h.1⟩ else 0
def betaU : ℂ := -cStd
def psiH {p s : ℕ} (β : ℂ) (σ : Equiv.Perm (Fin p)) (η : XiH p s σ) : ℂ :=
  G.psi β (subS (wP σ * lowW σ η.2.1 * (wP σ)⁻¹) + supS (G.upper η.2.2) + cornerA η.1.1 + cornerB η.1.2)
def psiStar (k : ℕ) {p s : ℕ} (ρ : ℕ) (σ : Equiv.Perm (Fin p)) (z z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ)
    (ξ : Xi k p s ρ σ) : ℂ :=
  Formalism.QuantumDeterminants.psi k (p + s + ρ) z cStd (Rn k (p + s) ρ ξ.1.1) *
    star (Formalism.QuantumDeterminants.psi k (p + s + ρ) z' cStd (Rn k (p + s) ρ ξ.1.2)) * psiH betaU σ ξ.2
def PhiFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k : ℕ) {p s : ℕ} (ρ : ℕ) (σ : Equiv.Perm (Fin p))
    (d : Fin p → ℂ) (z z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ) (F₁ : B.Mat k (p + s + ρ) → E) (Z : G.Mat s)
    (γ : B.Mat k ρ) : E :=
  ∫ ξ : Xi k p s ρ σ, psiStar k ρ σ z z' ξ • F₁ (gaXi k ρ σ d ξ Z γ) ∂(muXi k p s ρ σ)
def wtH {p s : ℕ} {σ : Equiv.Perm (Fin p)} (η : XiH p s σ) : ℝ :=
  (1 + ‖η.1.1‖) * (1 + ‖η.1.2‖) * (1 + ‖η.2.1‖) * (1 + ‖η.2.2‖)
def wt {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} (ξ : Xi k p s ρ σ) : ℝ :=
  (1 + ‖ξ.1.1‖) * (1 + ‖ξ.1.2‖) * wtH ξ.2
def HpkBlocks : Prop :=
  ∀ k j ρ : ℕ, Hpk k (j + ρ) = blk3 0 0 (G.wMat j) 0 (Hpk k ρ) 0 (G.wMat j) 0 0
def SliceMem : Prop :=
  ∀ k j ρ : ℕ,
    (∀ (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ), Z.det ≠ 0 → γ ∈ B.GV k ρ →
      mMap k j ρ Z γ ∈ B.GV k (j + ρ)) ∧
    (∀ q : Matrix (Fin j) (Fin j) ℂ, q.det ≠ 0 → muP k j ρ q ∈ B.GV k (j + ρ)) ∧
    (∀ y ∈ B.GV k ρ, embG k j ρ y ∈ B.GV k (j + ρ))
def RadicalParam : Prop :=
  ∀ k j ρ : ℕ, Function.Injective (Rn k j ρ) ∧ Set.range (Rn k j ρ) = Rset k j ρ ∧ Rset k j ρ ⊆ Nset k (j + ρ)
def LowWSpec : Prop :=
  ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (l : Matrix (Fin p) (Fin p) ℂ),
    (G.IsLowerUni l ∧ G.IsLowerUni (wP σ * l * (wP σ)⁻¹)) ↔ ∃ v : LW σ → ℂ, l = lowW σ v
def HeadOrbit : Prop :=
  ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
    (∀ l u : Matrix (Fin p) (Fin p) ℂ, G.IsLowerUni l → G.IsUpperUni u →
      ∃! q : (LW σ → ℂ) × (G.UT p → ℂ), l * hMat σ d * u = headH σ d q.1 q.2) ∧
    ∀ q : (LW σ → ℂ) × (G.UT p → ℂ), ∃ l u : Matrix (Fin p) (Fin p) ℂ, G.IsLowerUni l ∧ G.IsUpperUni u ∧
      l * hMat σ d * u = headH σ d q.1 q.2
def CharBlock : Prop :=
  ∀ (p s : ℕ) (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (lh uh : Matrix (Fin p) (Fin p) ℂ)
    (l u : Matrix (Fin s) (Fin s) ℂ), G.IsLowerUni lh → G.IsLowerUni l → G.IsUpperUni uh → G.IsUpperUni u →
    subS (blk2 1 0 (Matrix.of a) 1 * blk2 lh 0 0 l) = subS lh + cornerA a + subS l ∧
    supS (blk2 uh 0 0 u * blk2 1 (Matrix.of b) 0 1) = supS uh + cornerB b + supS u
def CornerInv : Prop :=
  ∀ (p s : ℕ) (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (lh uh : Matrix (Fin p) (Fin p) ℂ)
    (l u : Matrix (Fin s) (Fin s) ℂ), G.IsLowerUni lh → G.IsLowerUni l → G.IsUpperUni uh → G.IsUpperUni u →
    cornerA (l * Matrix.of a * lh⁻¹) = cornerA a ∧ cornerB (uh⁻¹ * Matrix.of b * u) = cornerB b
def ZhSlice : Prop :=
  ∀ (k j ρ : ℕ) (x x' : RC k j ρ) (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ),
    Zh k j ρ ((Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x') = Z
def DetZj : Prop :=
  ∀ (p s : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : XiH p s σ) (Z : G.Mat s),
    (ZjH σ d η Z).det = (hMat σ d).det * G.detM Z
def ZhDmin : Prop :=
  ∀ (k j ρ : ℕ) (z z' : Fin (2 * (j + ρ) + k + 1) → ℂ) (g : B.Mat k (j + ρ)),
    Dmin k (j + ρ) z z' g ⟨j, by omega⟩ = DjU k j ρ g
def GfSlice : Prop :=
  ∀ (k j ρ : ℕ) (z z' : Fin (2 * (j + ρ) + k + 1) → ℂ), inWb k (j + ρ) z → inWb k (j + ρ) z' →
    ∀ (x x' : RC k j ρ) (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ),
      Gf k (j + ρ) z z' ((Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x') =
        Complex.normSq Z.det * Gf k ρ (lowV k j ρ z) (lowV k j ρ z') γ
def BigCellBij : Prop :=
  ∀ (k j ρ : ℕ), ∀ g ∈ B.GV k (j + ρ), DjU k j ρ g ≠ 0 →
    ∃! q : (RC k j ρ × RC k j ρ) × (Matrix (Fin j) (Fin j) ℂ × B.Mat k ρ),
      q.2.1.det ≠ 0 ∧ q.2.2 ∈ B.GV k ρ ∧ g = (Rn k j ρ q.1.1)⁻¹ * mMap k j ρ q.2.1 q.2.2 * Rn k j ρ q.1.2
def SliceRight : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ y : B.Mat k ρ),
    gaXi k ρ σ d ξ Z (γ * y) =
      gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ * embG k (p + s) ρ y * Rn k (p + s) ρ ξ.1.2)
def SliceLeft : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ y : B.Mat k ρ),
    gaXi k ρ σ d ξ Z (y * γ) =
      ((Rn k (p + s) ρ ξ.1.1)⁻¹ * embG k (p + s) ρ y * Rn k (p + s) ρ ξ.1.1) * gaXi k ρ σ d ξ Z γ
def SliceZ : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : Xi k p s ρ σ) (Z : G.Mat s)
    (q : Matrix (Fin s) (Fin s) ℂ) (γ : B.Mat k ρ),
    gaXi k ρ σ d ξ (Matrix.of Z * q) γ =
      gaXi k ρ σ d ξ Z γ * ((Rn k (p + s) ρ ξ.1.2)⁻¹ *
        muP k (p + s) ρ ((blk2 1 (Matrix.of ξ.2.1.2) 0 1)⁻¹ * blk2 1 0 0 q * blk2 1 (Matrix.of ξ.2.1.2) 0 1) *
        Rn k (p + s) ρ ξ.1.2)
def DirectionsInP : Prop :=
  ∀ (k j ρ : ℕ) (x : RC k j ρ),
    (∀ Y : B.Mat k ρ, B.inLie k ρ Y →
      inLieP k j ρ ((Rn k j ρ x)⁻¹ * blk3 0 0 0 0 Y 0 0 0 0 * Rn k j ρ x)) ∧
    (∀ Q : Matrix (Fin j) (Fin j) ℂ,
      inLieP k j ρ ((Rn k j ρ x)⁻¹ * blk3 Q 0 0 0 0 0 0 0 (-(G.wMat j * Qᴴ * G.wMat j)) * Rn k j ρ x))
def BigCellCoordinateSizes : Prop :=
  ∀ k j ρ : ℕ, 1 ≤ j → ∃ C : ℝ, ∀ (x x' : RC k j ρ) (Z : Matrix (Fin j) (Fin j) ℂ) (γ : B.Mat k ρ),
    Z.det ≠ 0 → γ ∈ B.GV k ρ →
    B.gN (Rn k j ρ x) ≤ C * B.gN ((Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x') ^ j / min 1 ‖Z.det‖ ∧
    B.gN (Rn k j ρ x') ≤ C * B.gN ((Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x') ^ j / min 1 ‖Z.det‖ ∧
    mx Z ≤ C * B.gN ((Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x') ∧
    mx Z⁻¹ ≤ C * B.gN ((Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x') ^ (j - 1) / ‖Z.det‖ ∧
    B.gN γ ≤ C * B.gN ((Rn k j ρ x)⁻¹ * mMap k j ρ Z γ * Rn k j ρ x') ^ (2 * j + 1) / min 1 ‖Z.det‖ ^ 2
def BlockHeadSizes : Prop :=
  ∀ (p s : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) → ∃ C : ℝ,
    ∀ (η : XiH p s σ) (Z : G.Mat s),
      ‖η.1.1‖ ≤ C * mx (ZjH σ d η Z) ^ p ∧ ‖η.1.2‖ ≤ C * mx (ZjH σ d η Z) ^ p ∧
      ‖η.2.1‖ ≤ C * mx (ZjH σ d η Z) ^ p ∧ ‖η.2.2‖ ≤ C * mx (ZjH σ d η Z) ^ p ∧
      ‖Z‖ ≤ C * mx (ZjH σ d η Z) ^ (p + 1) ∧
      (G.detM Z ≠ 0 → mx (Matrix.of Z)⁻¹ ≤ mx (ZjH σ d η Z)⁻¹)
def SliceCoordinateSizes : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) → 1 ≤ s →
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 → ∃ C : ℝ,
    ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ), γ ∈ B.GV k ρ →
      ‖DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ)‖ ∈ K →
      1 ≤ B.gN (gaXi k ρ σ d ξ Z γ) ∧
      B.gN (Rn k (p + s) ρ ξ.1.1) ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ (p + s) ∧
      B.gN (Rn k (p + s) ρ ξ.1.2) ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ (p + s) ∧
      1 + ‖ξ.1.1‖ ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ (p + s) ∧
      1 + ‖ξ.1.2‖ ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ (p + s) ∧
      1 + ‖ξ.2.1.1‖ ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ p ∧
      1 + ‖ξ.2.1.2‖ ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ p ∧
      1 + ‖ξ.2.2.1‖ ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ p ∧
      1 + ‖ξ.2.2.2‖ ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ p ∧
      1 + ‖Z‖ ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ (p + 1) ∧
      B.gN γ ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ (2 * (p + s) + 1) ∧
      mx (Matrix.of Z)⁻¹ ≤ C * B.gN (gaXi k ρ σ d ξ Z γ) ^ (p + s - 1)
def CoordinateSizesFromComponents : Prop := SliceMem → BigCellCoordinateSizes → BlockHeadSizes → ZhSlice → DetZj → SliceCoordinateSizes
def CoordinateDecay : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) → 1 ≤ s →
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 → ∀ A' : ℝ, 0 ≤ A' → ∃ C : ℝ,
    ∀ (ξ : Xi k p s ρ σ) (Z : G.Mat s) (γ : B.Mat k ρ), γ ∈ B.GV k ρ →
      ‖DjU k (p + s) ρ (gaXi k ρ σ d ξ Z γ)‖ ∈ K →
      B.gN (gaXi k ρ σ d ξ Z γ) ^ (-A') ≤
        C * (wt ξ * (1 + ‖Z‖) * B.gN γ) ^ (-(A' / (8 * (2 * ((p + s + ρ : ℕ) : ℝ) + 1))))
def CoordinateDecayOfSizes : Prop := SliceCoordinateSizes → CoordinateDecay
def WeightIntegrable : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (a : ℝ), 1 ≤ s →
    2 * ((p + s + ρ : ℕ) : ℝ) * ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) < a →
    Integrable (fun ξ : Xi k p s ρ σ => wt ξ ^ (-a)) (muXi k p s ρ σ)
def unitP (k j ρ : ℕ) (u : List (B.Mat k (j + ρ))) : Prop :=
  ∀ X ∈ u, inLieP k j ρ X ∧ ∀ a b, ‖X a b‖ ≤ 1
def unitW (k ρ : ℕ) (u : List (B.Mat k ρ)) : Prop := ∀ X ∈ u, B.unitLie k ρ X
def Star {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (k j ρ : ℕ) (F₁ : B.Mat k (j + ρ) → E)
    (A₁ : ℝ) (Q : ℕ) (B₁ : ℝ) (K : Set ℝ) : Prop :=
  B.CkOn (Q : ℕ∞) (B.GV k (j + ρ)) F₁ ∧
  (∀ g ∈ B.GV k (j + ρ), F₁ g ≠ 0 → ‖DjU k j ρ g‖ ∈ K) ∧
  ∀ u v : List (B.Mat k (j + ρ)), unitP k j ρ u → unitP k j ρ v → u.length + v.length ≤ Q →
    ∀ g ∈ B.GV k (j + ρ), B.gN g ^ A₁ * ‖B.dLR u v F₁ g‖ ≤ B₁
def a1 (r : ℕ) (A₁ : ℝ) (m mm : ℕ) : ℝ :=
  (A₁ - 5 * (r : ℝ) * ((m : ℝ) + 1) - 2 * (r : ℝ) * (mm : ℝ)) / (8 * (2 * (r : ℝ) + 1))
def DerivativeCost : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) → 1 ≤ s →
    ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 → ∀ Q : ℕ, ∃ C : ℝ,
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F₁ : B.Mat k (p + s + ρ) → E) (A₁ B₁ : ℝ),
      Star k (p + s) ρ F₁ A₁ Q B₁ K →
      ∀ (ξ : Xi k p s ρ σ) (u v : List (B.Mat k ρ)) (q : ℕ), unitW k ρ u → unitW k ρ v →
        q + u.length + v.length ≤ Q → ∀ (Z : G.Mat s) (γ : B.Mat k ρ), G.detM Z ≠ 0 → γ ∈ B.GV k ρ →
        ContDiffAt ℝ q (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) Z ∧
        ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s => B.dLR u v (fun γ' => F₁ (gaXi k ρ σ d ξ Z' γ')) γ) Z‖ ≤
          C * B₁ * B.gN (gaXi k ρ σ d ξ Z γ) ^
            (-A₁ + 5 * ((p + s + ρ : ℕ) : ℝ) * (q : ℝ) + 2 * ((p + s + ρ : ℕ) : ℝ) * ((u.length + v.length : ℕ) : ℝ))
def DerivativeCostFromComponents : Prop :=
  SliceMem → RadicalParam → SliceRight → SliceLeft → SliceZ → DirectionsInP → SliceCoordinateSizes → DerivativeCost
def PointwiseIntegralBound : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ),
    (∀ i, d i ≠ 0) → 1 ≤ s → ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 → ∀ (m mm Q : ℕ) (A₁ : ℝ),
    m + 1 + mm ≤ Q →
    2 * ((p + s + ρ : ℕ) : ℝ) * ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) < a1 (p + s + ρ) A₁ m mm → ∃ C : ℝ,
    ∀ (z z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ)
      (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F₁ : B.Mat k (p + s + ρ) → E) (B₁ : ℝ),
      Star k (p + s) ρ F₁ A₁ Q B₁ K →
      (∀ (Z : G.Mat s) (γ : B.Mat k ρ), G.detM Z ≠ 0 → γ ∈ B.GV k ρ →
        Integrable (fun ξ : Xi k p s ρ σ => psiStar k ρ σ z z' ξ • F₁ (gaXi k ρ σ d ξ Z γ)) (muXi k p s ρ σ)) ∧
      (∀ Z : G.Mat s, G.detM Z ≠ 0 →
        B.CCle (a1 (p + s + ρ) A₁ m mm) mm (PhiFun k ρ σ d z z' F₁ Z)
          (C * B₁ * (1 + ‖Z‖) ^ (-(a1 (p + s + ρ) A₁ m mm)))) ∧
      ∀ u v : List (B.Mat k ρ), unitW k ρ u → unitW k ρ v → u.length + v.length ≤ mm → ∀ γ ∈ B.GV k ρ,
        ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun Z' : G.Mat s => B.dLR u v (PhiFun k ρ σ d z z' F₁ Z') γ)
          {Z | G.detM Z ≠ 0} ∧
        ∀ q ≤ m + 1, ∀ Z : G.Mat s, G.detM Z ≠ 0 →
          B.gN γ ^ (a1 (p + s + ρ) A₁ m mm) *
              ‖iteratedFDeriv ℝ q (fun Z' : G.Mat s => B.dLR u v (PhiFun k ρ σ d z z' F₁ Z') γ) Z‖ ≤
            C * B₁ * (1 + ‖Z‖) ^ (-(a1 (p + s + ρ) A₁ m mm))
def PointwiseIntegralBoundFromComponents : Prop := SliceMem → DerivativeCost → CoordinateDecay → WeightIntegrable → PointwiseIntegralBound
def PhiSupport : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (z z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (F₁ : B.Mat k (p + s + ρ) → E) (A₁ B₁ : ℝ) (Q : ℕ)
    (K : Set ℝ), (∀ i, d i ≠ 0) → Star k (p + s) ρ F₁ A₁ Q B₁ K →
    ∀ (Z : G.Mat s), G.detM Z ≠ 0 → ‖(hMat σ d).det * G.detM Z‖ ∉ K → ∀ γ ∈ B.GV k ρ,
      PhiFun k ρ σ d z z' F₁ Z γ = 0
structure CCModel (k ρ : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ)
    (S : Set (B.Mat k ρ)) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] where
  ev : V →ₗ[ℂ] (B.Mat k ρ → E)
  mem : ∀ v, B.CCle a mm (ev v) ‖v‖
  least : ∀ v c, B.CCle a mm (ev v) c → ‖v‖ ≤ c
  off : ∀ v, ∀ g ∈ B.GV k ρ, g ∉ S → ev v g = 0
  surj : ∀ F : B.Mat k ρ → E, B.InCC a mm F → (∀ g ∈ B.GV k ρ, g ∉ S → F g = 0) →
    ∃ v, ∀ g ∈ B.GV k ρ, ev v g = F g
def CCModelExists : Prop :=
  ∀ (k ρ : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (a : ℝ) (mm : ℕ)
    (S : Set (B.Mat k ρ)),
    ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : NormedSpace ℂ V), CompleteSpace V ∧ Nonempty (CCModel k ρ E a mm S V)
def WeakToStrong : Prop :=
  ∀ (X V E I : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] [NormedAddCommGroup E] [NormedSpace ℂ E] (lam : I → V →L[ℂ] E),
    (∀ (v : V) (c : ℝ), (∀ i, ‖lam i v‖ ≤ c) → ‖v‖ ≤ c) →
    ∀ (Ω : Set X) (Φ : X → V) (m : ℕ) (bd : X → ℝ), IsOpen Ω → ContinuousOn bd Ω →
      (∀ i, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun x => lam i (Φ x)) Ω) →
      (∀ i, ∀ q ≤ m + 1, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ q (fun x => lam i (Φ x)) x‖ ≤ bd x) →
      ContDiffOn ℝ (m : WithTop ℕ∞) Φ Ω ∧ ∀ q ≤ m, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ q Φ x‖ ≤ bd x
def TheoremU : Prop :=
  ∀ (k p s ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ),
    (∀ i, d i ≠ 0) → 1 ≤ s → ∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 → ∀ (m mm Q : ℕ) (A₁ : ℝ),
    m + 1 + mm ≤ Q →
    2 * ((p + s + ρ : ℕ) : ℝ) * ((2 * (p + s + ρ) + k + 1 : ℕ) : ℝ) < a1 (p + s + ρ) A₁ m mm → ∃ C : ℝ,
    ∀ (z z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ)
      (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (F₁ : B.Mat k (p + s + ρ) → E) (B₁ : ℝ),
      Star k (p + s) ρ F₁ A₁ Q B₁ K →
      (∀ (Z : G.Mat s) (γ : B.Mat k ρ), G.detM Z ≠ 0 → γ ∈ B.GV k ρ →
        Integrable (fun ξ : Xi k p s ρ σ => psiStar k ρ σ z z' ξ • F₁ (gaXi k ρ σ d ξ Z γ)) (muXi k p s ρ σ)) ∧
      (∀ Z : G.Mat s, G.detM Z ≠ 0 → ‖(hMat σ d).det * G.detM Z‖ ∉ K → ∀ γ ∈ B.GV k ρ,
        PhiFun k ρ σ d z z' F₁ Z γ = 0) ∧
      ∀ (S : Set (B.Mat k ρ)) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (M : CCModel k ρ E (a1 (p + s + ρ) A₁ m mm) mm S V),
        (∀ Z : G.Mat s, G.detM Z ≠ 0 → ∀ γ ∈ B.GV k ρ, γ ∉ S → PhiFun k ρ σ d z z' F₁ Z γ = 0) →
        ∃ Φ : G.Mat s → V,
          (∀ Z : G.Mat s, G.detM Z ≠ 0 → ∀ γ ∈ B.GV k ρ, M.ev (Φ Z) γ = PhiFun k ρ σ d z z' F₁ Z γ) ∧
          ∀ Z : G.Mat s, G.detM Z ≠ 0 → ContDiffAt ℝ m Φ Z ∧
            ∀ q ≤ m, ‖iteratedFDeriv ℝ q Φ Z‖ ≤ C * B₁ * (1 + ‖Z‖) ^ (-(a1 (p + s + ρ) A₁ m mm))
def TheoremUOfParts : Prop := PointwiseIntegralBound → PhiSupport → WeakToStrong → TheoremU
def IsPolyDeg {N : ℕ} (κ : ℕ) (P : Matrix (Fin N) (Fin N) ℂ → ℂ) : Prop :=
  ∃ q : MvPolynomial ((Fin N × Fin N) ⊕ (Fin N × Fin N)) ℂ, q.totalDegree ≤ κ ∧
    ∀ g, P g = MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q
def IsCutC (χ : ℂ → ℂ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧ (0 : ℂ) ∉ tsupport χ
def IsCutG (ε : ℝ) (χε : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χε ∧ (∀ q : ℕ, ∃ c : ℝ, ∀ x, ‖iteratedDeriv q χε x‖ ≤ c) ∧ ∀ x < ε, χε x = 0
section ops
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def InDD (k j ρ o κ : ℕ) (Θ : B.DiffOp k (j + ρ) Wp Wq) : Prop :=
  ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ (P : B.Mat k (j + ρ) → ℂ) (a b : ℕ), IsPolyDeg κ P ∧
    ∀ g, T.coef g = (P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b) •
      ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)
def cutD (k j ρ : ℕ) (χ : ℂ → ℂ) (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp) :=
  fun g => χ (DjU k j ρ g) • f g
def cutDG (k j ρ : ℕ) (z z' : Fin (2 * (j + ρ) + k + 1) → ℂ) (χ : ℂ → ℂ) (χε : ℝ → ℝ)
    (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp) :=
  fun g => (χ (DjU k j ρ g) * ((χε (Gf k (j + ρ) z z' g) : ℝ) : ℂ)) • f g
end ops
def ComposeDD : Prop :=
  ∀ (k j ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o₁ κ₁ o₂ κ₂ : ℕ) (Θ₁ Θ₂ : B.DiffOp k (j + ρ) Wp Wq),
    InDD k j ρ o₁ κ₁ Θ₁ → InDD k j ρ o₂ κ₂ Θ₂ →
    ∃ Θ : B.DiffOp k (j + ρ) Wp Wq, InDD k j ρ (o₁ + o₂) (κ₁ + κ₂ + j * o₁) Θ ∧
      ∀ F : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp), B.CkOn ((o₁ + o₂ : ℕ) : ℕ∞) (B.GV k (j + ρ)) F →
        ∀ g ∈ B.GV k (j + ρ), DjU k j ρ g ≠ 0 → B.opApply Θ F g = B.opApply Θ₁ (B.opApply Θ₂ F) g
def StarBoundOfCutoffOperator : Prop :=
  ∀ (k j ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (Θ : B.DiffOp k (j + ρ) Wp Wq) (χ : ℂ → ℂ),
    InDD k j ρ o κ Θ → IsCutC χ → ∀ (Q mm₀ : ℕ) (A₀ : ℝ), Q + o ≤ mm₀ → ∃ C : ℝ,
    ∀ (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm₀ f c →
      Star k j ρ (B.opApply Θ (cutD k j ρ χ f)) (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ)) Q (C * c)
        ((fun w : ℂ => ‖w‖) '' tsupport χ)
def StarBoundOfTwoCutoffOperator : Prop :=
  ∀ (k j ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (z z' : Fin (2 * (j + ρ) + k + 1) → ℂ) (o κ : ℕ)
    (Θ : B.DiffOp k (j + ρ) Wp Wq) (χ : ℂ → ℂ) (χε : ℝ → ℝ) (ε : ℝ),
    InDD k j ρ o κ Θ → IsCutC χ → IsCutG ε χε → ∀ (Q mm₀ : ℕ) (A₀ : ℝ), Q + o ≤ mm₀ → ∃ C : ℝ,
    ∀ (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm₀ f c →
      Star k j ρ (B.opApply Θ (cutDG k j ρ z z' χ χε f))
        (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - 2 * (((j + ρ : ℕ) : ℝ) + 1) * ((Q + o : ℕ) : ℝ)) Q (C * c)
        ((fun w : ℂ => ‖w‖) '' tsupport χ)
def StarPi : Prop :=
  ∀ (k j ρ : ℕ) (ι E : Type) [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E] (F₁ : B.Mat k (j + ρ) → ι → E)
    (A₁ B₁ : ℝ) (Q : ℕ) (K : Set ℝ), 0 ≤ B₁ → (∀ i, Star k j ρ (fun g => F₁ g i) A₁ Q B₁ K) → Star k j ρ F₁ A₁ Q B₁ K
def BudgetWord : Prop :=
  ∀ N j r : ℕ, 1 ≤ j → j ≤ r →
    N * j ≤ N * r ∧ (N * j + N * j ^ 2) + j * (N * j) ≤ 3 * N * r ^ 2
def BudgetWordStar : Prop :=
  ∀ N r n : ℕ, 2 * r + 2 ≤ n → 3 * N * r ^ 2 ≤ N * n ^ 2 + n ^ 3
def DerivativeBudgetCount : Prop :=
  ∀ (r m mmB o κjo As : ℕ) (Cc A₀ : ℝ), 1 ≤ r → m + 1 ≤ As → mmB ≤ As → o ≤ As → κjo ≤ As → 20 ≤ Cc →
    Cc * ((r : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ →
    (m + 1 + mmB) + o ≤ 3 * As ∧
    A₀ - (As : ℝ) - 6 * ((r : ℝ) + 1) * (As : ℝ) ≤
      A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * (((m + 1 + mmB) + o : ℕ) : ℝ) ∧
    A₀ - (13 * (r : ℝ) + 7) * (As : ℝ) ≤
      8 * (2 * (r : ℝ) + 1) * a1 r (A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * (((m + 1 + mmB) + o : ℕ) : ℝ)) m mmB ∧
    A₀ - 20 * (r : ℝ) * (As : ℝ) ≤ A₀ - (13 * (r : ℝ) + 7) * (As : ℝ) ∧
    (Cc - 20) / 16 * ((r : ℝ) + 1) ^ 3 * (As : ℝ) ≤
      a1 r (A₀ - (κjo : ℝ) - 2 * ((r : ℝ) + 1) * (((m + 1 + mmB) + o : ℕ) : ℝ)) m mmB
def GermThresholds : Prop :=
  ∀ (r n s As C₁ : ℕ) (c AB : ℝ), 1 ≤ n → s ≤ r → n ^ 3 ≤ As → AB ≤ (As : ℝ) → 1 ≤ c → (C₁ : ℝ) ≤ c →
    2 * (r : ℝ) * (n : ℝ) < c * ((r : ℝ) + 1) ^ 3 * (As : ℝ) ∧ AB ≤ c * ((r : ℝ) + 1) ^ 3 * (As : ℝ) ∧
    (C₁ : ℝ) * (s : ℝ) ^ 2 ≤ c * ((r : ℝ) + 1) ^ 3 * (As : ℝ)
structure UData (k p s ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ι : Type) where
  σ : Equiv.Perm (Fin p)
  d : Fin p → ℂ
  z : Fin (2 * (p + s + ρ) + k + 1) → ℂ
  z' : Fin (2 * (p + s + ρ) + k + 1) → ℂ
  Θ : ι → B.DiffOp k (p + s + ρ) Wp Wq
  χ : ℂ → ℂ
  χε : ℝ → ℝ
  ε : ℝ
  ε' : ℝ
  o : ℕ
  κ : ℕ
  AB : ℝ
  mmB : ℕ
  As : ℕ
section udata
variable {k p s ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {ι : Type}
def UData.Ok (U : UData k p s ρ Wp Wq ι) (C₂ : ℕ) : Prop :=
  (∀ i, U.d i ≠ 0) ∧ 1 ≤ s ∧ inWb k (p + s + ρ) U.z ∧ inWb k (p + s + ρ) U.z' ∧
  (∀ i, InDD k (p + s) ρ U.o U.κ (U.Θ i)) ∧ IsCutC U.χ ∧ IsCutG U.ε U.χε ∧ 0 < U.ε' ∧
  (∀ w ∈ tsupport U.χ, U.ε' * ‖w‖ ^ 2 ≤ U.ε) ∧
  U.o ≤ U.As ∧ U.κ + (p + s) * U.o ≤ U.As ∧ U.AB ≤ (U.As : ℝ) ∧ U.mmB ≤ U.As ∧
  (2 * (p + s + ρ) + k + 1) ^ 3 ≤ U.As ∧ C₂ * (p + s + ρ + 1) ^ 2 + 1 ≤ U.As
def UData.F1 (U : UData k p s ρ Wp Wq ι) (f : B.Mat k (p + s + ρ) → (Wq →L[ℂ] Wp)) :
    B.Mat k (p + s + ρ) → ι → (Wq →L[ℂ] Wp) :=
  fun g i => B.opApply (U.Θ i) (cutDG k (p + s) ρ U.z U.z' U.χ U.χε f) g
def UData.Phi (U : UData k p s ρ Wp Wq ι) [Fintype ι] (f : B.Mat k (p + s + ρ) → (Wq →L[ℂ] Wp)) (Z : G.Mat s)
    (γ : B.Mat k ρ) : ι → (Wq →L[ℂ] Wp) :=
  PhiFun k ρ U.σ U.d U.z U.z' (U.F1 f) Z γ
def UData.a (U : UData k p s ρ Wp Wq ι) (C₂ : ℕ) (A₀ : ℝ) : ℝ :=
  a1 (p + s + ρ)
    (A₀ - (U.κ : ℝ) - ((p + s : ℕ) : ℝ) * (U.o : ℝ) -
      2 * (((p + s + ρ : ℕ) : ℝ) + 1) * (((C₂ * s ^ 2 + 1 + U.mmB) + U.o : ℕ) : ℝ))
    (C₂ * s ^ 2) U.mmB
def UData.S (U : UData k p s ρ Wp Wq ι) : Set (B.Mat k ρ) :=
  {γ | U.ε' ≤ Gf k ρ (lowV k (p + s) ρ U.z) (lowV k (p + s) ρ U.z') γ}
end udata
def PhiSuppG : Prop :=
  ∀ (k p s ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ι : Type) [Fintype ι] (U : UData k p s ρ Wp Wq ι) (C₂ : ℕ),
    U.Ok C₂ → ∀ (f : B.Mat k (p + s + ρ) → (Wq →L[ℂ] Wp)) (Z : G.Mat s), G.detM Z ≠ 0 →
      ∀ γ ∈ B.GV k ρ, γ ∉ U.S → U.Phi f Z γ = 0
def GermExpansionHypothesis : Prop :=
  ∀ C₁ C₂ : ℕ, ∃ Cc : ℝ,
  ∀ (k p s ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ι : Type) [Fintype ι]
    (U : UData k p s ρ Wp Wq ι), U.Ok C₂ → ∀ A₀ : ℝ, Cc * (((p + s + ρ : ℕ) : ℝ) + 1) ^ 4 * (U.As : ℝ) ≤ A₀ →
    ((C₁ : ℝ) + 1) * (((p + s + ρ : ℕ) : ℝ) + 1) ^ 3 * (U.As : ℝ) ≤ U.a C₂ A₀ ∧
    (C₁ : ℝ) * (s : ℝ) ^ 2 ≤ U.a C₂ A₀ ∧ U.AB ≤ U.a C₂ A₀ ∧
    ∃ C : ℝ, ∀ (f : B.Mat k (p + s + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * U.As) f c →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (M : CCModel k ρ (ι → (Wq →L[ℂ] Wp)) (U.a C₂ A₀) U.mmB U.S V),
        ∃ Φ : G.Mat s → V,
          (∀ Z : G.Mat s, G.detM Z ≠ 0 → ∀ γ ∈ B.GV k ρ, M.ev (Φ Z) γ = U.Phi f Z γ) ∧
          ∀ Z : G.Mat s, G.detM Z ≠ 0 → ContDiffAt ℝ ((C₂ * s ^ 2 : ℕ) : WithTop ℕ∞) Φ Z ∧
            ∀ q ≤ C₂ * s ^ 2, ‖iteratedFDeriv ℝ q Φ Z‖ ≤ C * c * (1 + ‖Z‖) ^ (-(U.a C₂ A₀))
def GermExpansionHypothesisFromComponents : Prop :=
  TheoremU → StarBoundOfTwoCutoffOperator → StarPi → DerivativeBudgetCount → GermThresholds → PhiSuppG → GermExpansionHypothesis
def PhiSuppGOfParts : Prop := GfSlice → DetZj → ZhSlice → PhiSuppG
def DecayMin : Prop :=
  ∀ x A : ℝ, 0 < x → 0 ≤ A → (1 + x) ^ (-A) ≤ min 1 (x ^ (-A))
def DerivBoundOfDecay : Prop :=
  ∀ (s k : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : G.Mat s → V) (A K : ℝ) (Kd : Set ℂ),
    1 ≤ s → 0 ≤ A → 0 ≤ K → (0 : ℂ) ∉ Kd →
    (∀ Z : G.Mat s, G.detM Z ≠ 0 → ContDiffAt ℝ k Φ Z ∧ ∀ q ≤ k, ‖iteratedFDeriv ℝ q Φ Z‖ ≤ K * (1 + ‖Z‖) ^ (-A)) →
    G.DerivBound k Kd (fun Z => K * min 1 (‖Z‖ ^ (-A))) Φ
def DerivBoundComp : Prop :=
  ∀ (s k : ℕ) (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V'] [NormedSpace ℂ V']
    (T : V →L[ℂ] V') (Φ : G.Mat s → V) (Kd : Set ℂ) (bd : G.Mat s → ℝ),
    G.DerivBound k Kd bd Φ → G.DerivBound k Kd (fun Z => ‖T‖ * bd Z) (fun Z => T (Φ Z))
def SeminormCompletion : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (p : Seminorm ℂ V) (Cp : ℝ), (∀ v, p v ≤ Cp * ‖v‖) →
    ∃ (V' : Type) (_ : NormedAddCommGroup V') (_ : NormedSpace ℂ V'), CompleteSpace V' ∧
      ∃ T : V →L[ℂ] V', (∀ v, ‖T v‖ = p v) ∧ DenseRange T
def CCS {k ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (a : ℝ) (mm : ℕ) (S : Set (B.Mat k ρ))
    (F : B.Mat k ρ → E) : Prop :=
  B.InCC a mm F ∧ ∀ g ∈ B.GV k ρ, g ∉ S → F g = 0
def PosP {k ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (bet : (B.Mat k ρ → E) → (B.Mat k ρ → E) → ℂ) (a : ℝ) (mm : ℕ) (S : Set (B.Mat k ρ)) : Prop :=
  B.SesqOn (CCS a mm S) bet ∧ ∀ x, CCS a mm S x → (bet x x).im = 0 ∧ 0 ≤ (bet x x).re
def LBound {k ρ : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (bet : (B.Mat k ρ → E) → (B.Mat k ρ → E) → ℂ) (AB : ℝ) (mmB : ℕ) (S : Set (B.Mat k ρ)) (Cp : ℝ) : Prop :=
  ∀ (x : B.Mat k ρ → E) (c : ℝ), B.CCle AB mmB x c → (∀ g ∈ B.GV k ρ, g ∉ S → x g = 0) → ‖bet x x‖ ≤ (Cp * c) ^ 2
def CCMono : Prop :=
  ∀ (k ρ : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (a AB c : ℝ) (mm : ℕ) (F : B.Mat k ρ → E),
    AB ≤ a → B.CCle a mm F c → B.CCle AB mm F c
def SeminormOfForm : Prop :=
  ∀ (k ρ : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (bet : (B.Mat k ρ → E) → (B.Mat k ρ → E) → ℂ) (a AB Cp : ℝ) (mmB : ℕ) (S : Set (B.Mat k ρ)),
    AB ≤ a → 0 ≤ Cp → PosP bet a mmB S → LBound bet AB mmB S Cp →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (M : CCModel k ρ E a mmB S V),
      ∃ p : Seminorm ℂ V, (∀ v, p v ^ 2 = (bet (M.ev v) (M.ev v)).re) ∧ ∀ v, p v ≤ Cp * ‖v‖
def UseDerivBound : Prop :=
  ∀ C₁ C₂ : ℕ, ∃ Cc : ℝ,
  ∀ (k p s ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ι : Type) [Fintype ι]
    (U : UData k p s ρ Wp Wq ι), U.Ok C₂ → ∀ A₀ : ℝ, Cc * (((p + s + ρ : ℕ) : ℝ) + 1) ^ 4 * (U.As : ℝ) ≤ A₀ →
    ((C₁ : ℝ) + 1) * (((p + s + ρ : ℕ) : ℝ) + 1) ^ 3 * (U.As : ℝ) ≤ U.a C₂ A₀ ∧
    (C₁ : ℝ) * (s : ℝ) ^ 2 ≤ U.a C₂ A₀ ∧ U.AB ≤ U.a C₂ A₀ ∧
    ∃ C : ℝ, ∀ (bet : (B.Mat k ρ → ι → (Wq →L[ℂ] Wp)) → (B.Mat k ρ → ι → (Wq →L[ℂ] Wp)) → ℂ) (Cp : ℝ), 0 ≤ Cp →
      PosP bet (U.a C₂ A₀) U.mmB U.S → LBound bet U.AB U.mmB U.S Cp →
      (∀ x y x' y' : B.Mat k ρ → ι → (Wq →L[ℂ] Wp), (∀ g ∈ B.GV k ρ, x g = x' g) → (∀ g ∈ B.GV k ρ, y g = y' g) →
        bet x y = bet x' y') →
      ∀ (f : B.Mat k (p + s + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * U.As) f c →
      ∃ (V' : Type) (_ : NormedAddCommGroup V') (_ : NormedSpace ℂ V'), CompleteSpace V' ∧ ∃ Φ' : G.Mat s → V',
        (∀ (J : Finset (G.Mat s)) (w : G.Mat s → ℂ), (∀ Z ∈ J, G.detM Z ≠ 0) →
          ‖∑ Z ∈ J, w Z • Φ' Z‖ ^ 2 = (bet (∑ Z ∈ J, w Z • U.Phi f Z) (∑ Z ∈ J, w Z • U.Phi f Z)).re) ∧
        ∀ Kd : Set ℂ, (0 : ℂ) ∉ Kd →
          G.DerivBound (C₂ * s ^ 2) Kd (fun Z => C * Cp * c * min 1 (‖Z‖ ^ (-(U.a C₂ A₀)))) Φ'
def UseDerivBoundOfParts : Prop :=
  GermExpansionHypothesis → CCModelExists → CCMono → SeminormOfForm → SeminormCompletion → DerivBoundOfDecay → DerivBoundComp →
    UseDerivBound
def Mlev (k ρ : ℕ) : ℕ := k + 2 * ρ + 3
section germ
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def uD (β : ℂ) (m M : ℕ) (Φ : G.Mat (m + 1 + 1) → V) (t D : ℂ) : V :=
  (((‖t‖ ^ (m + 1))⁻¹ * ‖t‖ ^ ((m + 1) * (M + m)) * ‖D / t ^ (m + 1)‖ ^ (M - 2) : ℝ) : ℂ) •
    G.OmBlock β (m + 1) Φ t (D / t ^ (m + 1))
def aD (β : ℂ) (m M : ℕ) (Φ : G.Mat (m + 1 + 1) → V) (t D : ℂ) : V :=
  ((‖D‖ ^ (M - 2) : ℝ) : ℂ) • G.mainTerm β m (fun _ => 1) Φ t D
end germ
def PowerMatch : Prop :=
  ∀ (m M : ℕ) (β t D : ℂ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : G.Mat (m + 1 + 1) → V),
    2 ≤ M → t ≠ 0 →
    uD β m M Φ t D - aD β m M Φ t D =
      ((‖D‖ ^ (M - 2) : ℝ) : ℂ) • G.remainder β m (fun _ => 1) Φ t (D / t ^ (m + 1))
def ScaleMatch : Prop :=
  (starRingEnd ℂ) cStd = betaU ∧ betaU ≠ 0 ∧
    ∀ x : ℂ, Complex.exp (Complex.I * (((cStd * (starRingEnd ℂ) x).re : ℝ) : ℂ)) = G.psi betaU x ∧
      star (Complex.exp (Complex.I * (((cStd * x).re : ℝ) : ℂ))) = G.psi betaU x
def UseGerm : Prop :=
  ∃ (C₂ : ℕ) (Cc : ℝ),
  ∀ (k p m ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ι : Type) [Fintype ι]
    (U : UData k p (m + 1 + 1) ρ Wp Wq ι), U.Ok C₂ →
    ∀ A₀ : ℝ, Cc * (((p + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (U.As : ℝ) ≤ A₀ →
    U.AB ≤ U.a C₂ A₀ ∧
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc → ∃ Cst : ℝ,
    ∀ (f : B.Mat k (p + (m + 1 + 1) + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * U.As) f c →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (M : CCModel k ρ (ι → (Wq →L[ℂ] Wp)) (U.a C₂ A₀) U.mmB U.S V),
        ∃ Φ : G.Mat (m + 1 + 1) → V,
          (∀ Z : G.Mat (m + 1 + 1), G.detM Z ≠ 0 → ∀ γ ∈ B.GV k ρ, M.ev (Φ Z) γ = U.Phi f Z γ) ∧
          ∀ t D : ℂ, t ≠ 0 → D ∈ Kc →
            ‖uD betaU m (Mlev k ρ) Φ t D - aD betaU m (Mlev k ρ) Φ t D‖ ≤ Cst * c * ‖t‖
def UseGermOfParts : Prop :=
  G.GermRate → G.DetMatch → GermExpansionHypothesis → DerivBoundOfDecay → PowerMatch → ScaleMatch → UseGerm
def GermInForm : Prop :=
  ∃ (C₂ : ℕ) (Cc : ℝ),
  ∀ (k p m ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ι : Type) [Fintype ι]
    (U : UData k p (m + 1 + 1) ρ Wp Wq ι), U.Ok C₂ →
    ∀ A₀ : ℝ, Cc * (((p + (m + 1 + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 * (U.As : ℝ) ≤ A₀ →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc → ∃ Cst : ℝ,
    ∀ (bet : (B.Mat k ρ → ι → (Wq →L[ℂ] Wp)) → (B.Mat k ρ → ι → (Wq →L[ℂ] Wp)) → ℂ) (Cp : ℝ), 0 ≤ Cp →
      PosP bet (U.a C₂ A₀) U.mmB U.S → LBound bet U.AB U.mmB U.S Cp →
      (∀ x y x' y' : B.Mat k ρ → ι → (Wq →L[ℂ] Wp), (∀ g ∈ B.GV k ρ, x g = x' g) → (∀ g ∈ B.GV k ρ, y g = y' g) →
        bet x y = bet x' y') →
      ∀ (f : B.Mat k (p + (m + 1 + 1) + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ (3 * U.As) f c →
      ∃ (V' : Type) (_ : NormedAddCommGroup V') (_ : NormedSpace ℂ V'), CompleteSpace V' ∧
        ∃ Φ' : G.Mat (m + 1 + 1) → V',
        (∀ (J : Finset (G.Mat (m + 1 + 1))) (w : G.Mat (m + 1 + 1) → ℂ), (∀ Z ∈ J, G.detM Z ≠ 0) →
          ‖∑ Z ∈ J, w Z • Φ' Z‖ ^ 2 = (bet (∑ Z ∈ J, w Z • U.Phi f Z) (∑ Z ∈ J, w Z • U.Phi f Z)).re) ∧
        ∀ t c' : ℂ, t ≠ 0 → c' * t ^ (m + 1) ∈ Kc →
          ‖G.remainder betaU m (fun _ => 1) Φ' t c'‖ ≤ Cst * Cp * c * ‖t‖
def GermInFormOfParts : Prop := G.GermRate → G.DetMatch → UseDerivBound → ScaleMatch → GermInForm
section top
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def DecayAll {N : ℕ} (q : ℕ) (e : ℕ → ℝ) (K : ℝ) (Φ0 : G.Mat N → V) : Prop :=
  ContDiff ℝ q Φ0 ∧ ∀ i ≤ q, ∀ Z, ‖iteratedFDeriv ℝ i Φ0 Z‖ ≤ K * (1 + ‖Z‖) ^ (-(e i))
def PhiTop {p s : ℕ} (β : ℂ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (Φ0 : G.Mat (p + s) → V) (CC : G.Mat s) : V :=
  ∫ η : XiH p s σ, psiH β σ η • Φ0 (ZjH σ d η CC) ∂(muXiH p s σ)
end top
def ZjAffine : Prop :=
  ∀ (p s : ℕ) (a : Fin s → Fin p → ℂ) (b : Fin p → Fin s → ℂ) (H : Matrix (Fin p) (Fin p) ℂ)
    (CC : Matrix (Fin s) (Fin s) ℂ),
    Zj a b H CC = blk2 H (H * Matrix.of b) (Matrix.of a * H) (Matrix.of a * H * Matrix.of b + CC)
def SizesTop : Prop :=
  ∀ (p s : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) → 1 ≤ s → ∀ A' : ℝ, 0 ≤ A' → ∃ C : ℝ,
    ∀ (η : XiH p s σ) (CC : G.Mat s),
      (1 + mx (ZjH σ d η CC)) ^ (-A') ≤ C * (wtH η * (1 + ‖CC‖)) ^ (-(A' / (5 * ((p + s : ℕ) : ℝ))))
def IntTop : Prop :=
  ∀ (p s : ℕ) (σ : Equiv.Perm (Fin p)) (a : ℝ), 2 * ((p + s : ℕ) : ℝ) ^ 2 < a →
    Integrable (fun η : XiH p s σ => wtH η ^ (-a)) (muXiH p s σ)
def TopCells : Prop :=
  ∀ (p s : ℕ) (β : ℂ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) → 1 ≤ s → ∀ (q : ℕ) (e : ℕ → ℝ),
    (∀ i ≤ q, 2 * ((p + s : ℕ) : ℝ) ^ 2 < e i / (5 * ((p + s : ℕ) : ℝ))) → ∃ Cst : ℝ,
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ0 : G.Mat (p + s) → V) (K : ℝ),
      DecayAll q e K Φ0 →
      (∀ CC : G.Mat s, Integrable (fun η : XiH p s σ => psiH β σ η • Φ0 (ZjH σ d η CC)) (muXiH p s σ)) ∧
      DecayAll q (fun i => e i / (5 * ((p + s : ℕ) : ℝ))) (Cst * K) (PhiTop β σ d Φ0)
def TopCellsOfParts : Prop := ZjAffine → BlockHeadSizes → SizesTop → IntTop → TopCells
def BudgetTop : Prop :=
  ∀ C₁ C₂ Ca : ℕ, ∃ Cc : ℝ, ∀ (r n s As al : ℕ) (A A₀ : ℝ), 2 * r + 2 ≤ n → s ≤ r + 1 → n ^ 3 ≤ As →
    al ≤ C₂ * s ^ 2 + 1 → Cc * ((r : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ → A₀ - (Ca : ℝ) * (r : ℝ) * (As : ℝ) ≤ A →
    (C₁ : ℝ) * (s : ℝ) ^ 3 ≤
      (A - (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ))) / (5 * ((r : ℝ) + 1)) - (Ca : ℝ) * (r : ℝ) ^ 2
def BudgetTopConv : Prop :=
  ∀ C₁ C₂ Ca : ℕ, ∃ Cc : ℝ, ∀ (r n s As al : ℕ) (A A₀ : ℝ), 2 * r + 2 ≤ n → 1 ≤ s → s ≤ r + 1 → n ^ 3 ≤ As →
    al ≤ C₂ * s ^ 2 + 1 → Cc * ((r : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ → A₀ - (Ca : ℝ) * (r : ℝ) * (As : ℝ) ≤ A →
    (C₁ : ℝ) * (s : ℝ) ^ 2 + 2 * ((r : ℝ) + 1) ^ 2 <
      (A - (Ca : ℝ) * ((n : ℝ) ^ 2 + (r : ℝ) ^ 3 + (r : ℝ) * (al : ℝ))) / (5 * ((r : ℝ) + 1)) - (Ca : ℝ) * (r : ℝ) ^ 2
def UseGermTop : Prop :=
  ∃ C₁ C₂ : ℕ, ∀ (p m : ℕ) (β : ℂ), β ≠ 0 → ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ), (∀ i, d i ≠ 0) →
    ∀ (e : ℕ → ℝ) (A : ℝ), (C₁ : ℝ) * ((m : ℝ) + 2) ^ 2 ≤ A →
    (∀ i ≤ C₂ * (m + 2) ^ 2, A ≤ e i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ)) ∧
      2 * ((p + (m + 1 + 1) : ℕ) : ℝ) ^ 2 < e i / (5 * ((p + (m + 1 + 1) : ℕ) : ℝ))) →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc → ∃ Cst : ℝ,
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ0 : G.Mat (p + (m + 1 + 1)) → V)
      (K : ℝ), DecayAll (C₂ * (m + 2) ^ 2) e K Φ0 →
      ∀ t c : ℂ, t ≠ 0 → c * t ^ (m + 1) ∈ Kc →
        ‖G.remainder β m (fun _ => 1) (PhiTop β σ d Φ0) t c‖ ≤ Cst * K * ‖t‖
def UseGermTopOfParts : Prop := G.GermRate → G.DetMatch → TopCells → DerivBoundOfDecay → UseGermTop
def UseGermTopCount : Prop :=
  ∃ C₂ : ℕ, ∀ Ca : ℕ, ∃ Cc : ℝ, ∀ (p m : ℕ) (β : ℂ), β ≠ 0 → ∀ (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ),
    (∀ i, d i ≠ 0) → ∀ (n As : ℕ) (A A₀ : ℝ), 2 * (p + m + 1) + 2 ≤ n → n ^ 3 ≤ As →
    Cc * (((p + m + 1 : ℕ) : ℝ) + 1) ^ 4 * (As : ℝ) ≤ A₀ → A₀ - (Ca : ℝ) * ((p + m + 1 : ℕ) : ℝ) * (As : ℝ) ≤ A →
    ∀ Kc : Set ℂ, IsCompact Kc → (0 : ℂ) ∉ Kc → ∃ Cst : ℝ,
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (Φ0 : G.Mat (p + (m + 1 + 1)) → V)
      (K : ℝ), DecayAll (C₂ * (m + 2) ^ 2)
        (fun i => A - (Ca : ℝ) * ((n : ℝ) ^ 2 + ((p + m + 1 : ℕ) : ℝ) ^ 3 + ((p + m + 1 : ℕ) : ℝ) * (i : ℝ))) K Φ0 →
      ∀ t c : ℂ, t ≠ 0 → c * t ^ (m + 1) ∈ Kc →
        ‖G.remainder β m (fun _ => 1) (PhiTop β σ d Φ0) t c‖ ≤ Cst * K * ‖t‖
def UseGermTopCountOfParts : Prop := UseGermTop → BudgetTopConv → UseGermTopCount
end Formalism.FourierDecayAlt.U


