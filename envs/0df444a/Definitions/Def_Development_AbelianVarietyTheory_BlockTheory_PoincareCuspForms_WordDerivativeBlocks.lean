-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks
-- name    : Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_WordDerivativeBlocks
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:05:31.4488+00:00
-- url     : https://prove2.me/theorems/72cc59e6-893f-4441-98b4-9f500378b3de
-- title:
--   Word Derivative Blocks
-- statement:
--   Definitions and structural lemmas for Word Derivative Blocks, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/PoincareCuspForms/WordDerivativeBlocks.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials
abbrev Letter {ι : Type} (dim : ι → ℕ) (n : ℕ) : Type := Fin n × (Σ s : ι, Fin (dim s))
structure Block {ι : Type} (dim : ι → ℕ) (n : ℕ) where
  emb : ι
  size : ℕ
  expo : ℕ
  one_le_size : 1 ≤ size
  size_le : size ≤ dim emb
  one_le_expo : 1 ≤ expo
  col : Fin size ↪ Fin n
  vec : Fin size → EuclideanSpace ℂ (Fin (dim emb))
  orthonormal_vec : Orthonormal ℂ vec
variable {ι : Type} {dim : ι → ℕ} {n : ℕ}
def Block.entry (B : Block dim n) (a b : Fin B.size) : MvPolynomial (Letter dim n) ℂ :=
  ∑ k : Fin (dim B.emb),
    MvPolynomial.C (B.vec a k) * MvPolynomial.X (B.col b, ⟨B.emb, k⟩)
def Block.poly (B : Block dim n) : MvPolynomial (Letter dim n) ℂ :=
  (Matrix.of fun a b => B.entry a b).det ^ B.expo
structure BlockSystem {ι : Type} (dim : ι → ℕ) (n : ℕ) where
  card : ℕ
  block : Fin card → Block dim n
  disjoint : Pairwise fun j j' =>
    Disjoint (Set.range (block j).col) (Set.range (block j').col)
def BlockSystem.poly (S : BlockSystem dim n) : MvPolynomial (Letter dim n) ℂ :=
  ∏ j, (S.block j).poly
def BlockSystem.degree (S : BlockSystem dim n) : ℕ :=
  ∑ j, (S.block j).size * (S.block j).expo
def IsBlockPolynomial (P : MvPolynomial (Letter dim n) ℂ) (D : ℕ) : Prop :=
  ∃ S : BlockSystem dim n, S.poly = P ∧ S.degree = D
def exampleBlock : Block (fun _ : Fin 2 => 2) 3 where
  emb := 0
  size := 2
  expo := 3
  one_le_size := by norm_num
  size_le := le_rfl
  one_le_expo := by norm_num
  col := Fin.castLEEmb (by norm_num)
  vec := EuclideanSpace.basisFun (Fin 2) ℂ
  orthonormal_vec := (EuclideanSpace.basisFun (Fin 2) ℂ).orthonormal
def exampleSystem : BlockSystem (fun _ : Fin 2 => 2) 3 where
  card := 1
  block := fun _ => exampleBlock
  disjoint := Subsingleton.pairwise
example : exampleSystem.degree = 6 := by
  decide
section Operator
variable {Λ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
def wordDeriv (dir : Λ → W) (l : List Λ) (F : W → ℂ) (p : W) : ℂ :=
  iteratedFDeriv ℂ l.length F p fun j => dir (l.get j)
def applyAt (dir : Λ → W) (P : MvPolynomial Λ ℂ) (F : W → ℂ) (p : W) : ℂ :=
  ∑ μ ∈ P.support, P.coeff μ * wordDeriv dir (Finsupp.toMultiset μ).toList F p
example (dir : Λ → W) (F : W → ℂ) (p : W) : applyAt dir 1 F p = F p := by
  classical
  have h : (Finsupp.toMultiset (0 : Λ →₀ ℕ)).toList = [] := by simp
  simp only [applyAt, MvPolynomial.support_one, Finset.sum_singleton, h]
  simp [wordDeriv]
end Operator
section Columns
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def letterDir (e : (s : ι) → Fin (dim s) → V) (x : Letter dim n) : Fin n → V :=
  Pi.single x.1 (e x.2.1 x.2.2)
def opAt (e : (s : ι) → Fin (dim s) → V) (P : MvPolynomial (Letter dim n) ℂ)
    (F : (Fin n → V) → ℂ) (p : Fin n → V) : ℂ :=
  applyAt (letterDir e) P F p
end Columns
def gDim (f r : ℕ) : ℕ := f * r
def bigR (rd : ℝ) : ℝ := rd ^ 7
def dStar (f m : ℕ) : ℕ := 2 * f * m
def omStar (f : ℕ) (rd : ℝ) : ℝ := 2 * (f : ℝ) ^ ((3 : ℝ) / 2) * rd
def thSq (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := f * R₀ ^ 2 * bigR rd ^ 3 / q
def th (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := Real.sqrt (thSq f rd q R₀)
def bZero (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := q / (R₀ ^ 2 * bigR rd ^ 4)
def tZero (rd : ℝ) (q : ℕ) (R₀ : ℝ) : ℝ := q * bZero rd q R₀
def mOne (f m : ℕ) (rd : ℝ) : ℝ := 90 * (m : ℝ) ^ 2 * (dStar f m : ℝ) ^ 2 * rd
def cChi (f m : ℕ) (rd : ℝ) : ℝ := 8100 * (m : ℝ) ^ 4 * (dStar f m : ℝ) ^ 4 * bigR rd
def ph (f : ℕ) (rd : ℝ) (q : ℕ) (R₀ : ℝ) (la : Set.Ioi (0 : ℝ)) : ℝ :=
  if (la : ℝ) < th f rd q R₀ then 2 * f / (rd ^ 2 * (la : ℝ) ^ 2) else 0
structure Params {ι : Type} (dim : ι → ℕ) (f r : ℕ) (rd : ℝ) (D n : ℕ) where
  q : ℕ
  R₀ : ℝ
  m : ℕ
  one_le_m : 1 ≤ m
  min_dim_le : ∃ s, dim s ≤ m
  m_pow_le : m ^ 4 ≤ f
  f_sq_le : (f : ℝ) ^ 2 ≤ rd
  sixteen_le : 16 ≤ rd
  two_le_fr : 2 ≤ f * r
  three_le_q : 3 ≤ q
  one_le_D : 1 ≤ D
  one_le_n : 1 ≤ n
  R₀_pos : 0 < R₀
  R₀_sq : max (270 : ℝ) (90 * ((gDim f r : ℝ) + D)) ≤ R₀ ^ 2
  threshold_lt : (dStar f m : ℝ) ^ 2 * omStar f rd * thSq f rd q R₀ < 1
  one_le_bZero : 1 ≤ bZero rd q R₀
  mOne_le : mOne f m rd ≤ (q : ℝ) / 2
  D_le_q : D ≤ q
  tZero_ge_log : 4 * (D : ℝ) * (7 + Real.log ((q : ℝ) * D)) + (dStar f m : ℝ) + 1 ≤ tZero rd q R₀
  tZero_ge_rank : (gDim f r : ℝ) * Real.log 2 + 2 * (dStar f m : ℝ) + 3 +
    ((D : ℝ) + 1) * ((r : ℝ) * Real.log r + 3 * r + 3) ≤ tZero rd q R₀
structure ParamsWithLevel {ι : Type} (dim : ι → ℕ) (f r : ℕ) (rd : ℝ) (D n : ℕ)
    extends Params dim f r rd D n where
  r₁ : ℕ
  two_le_r₁ : 2 ≤ r₁
def exampleParams : ParamsWithLevel (fun _ : Fin 2 => 1) 1 2 16 1 1 where
  q := 2 ^ 130
  R₀ := 17
  m := 1
  r₁ := 2
  two_le_r₁ := le_rfl
  one_le_m := le_rfl
  min_dim_le := ⟨0, le_rfl⟩
  m_pow_le := by norm_num
  f_sq_le := by norm_num
  sixteen_le := le_rfl
  two_le_fr := by norm_num
  three_le_q := by norm_num
  one_le_D := le_rfl
  one_le_n := le_rfl
  R₀_pos := by norm_num
  R₀_sq := by norm_num [gDim]
  threshold_lt := by norm_num [dStar, omStar, thSq, bigR]
  one_le_bZero := by norm_num [bZero, bigR]
  mOne_le := by norm_num [mOne, dStar]
  D_le_q := by norm_num
  tZero_ge_log := by
    have h : Real.log (((2 ^ 130 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) ≤ ((2 ^ 130 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) :=
      Real.log_le_self (by positivity)
    have h2 : 4 * ((1 : ℕ) : ℝ) * (7 + ((2 ^ 130 : ℕ) : ℝ) * ((1 : ℕ) : ℝ)) + (dStar 1 1 : ℝ) + 1
        ≤ tZero 16 (2 ^ 130) 17 := by
      norm_num [dStar, tZero, bZero, bigR]
    refine le_trans ?_ h2
    gcongr
  tZero_ge_rank := by
    have h : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
    have h2 : (100 : ℝ) ≤ tZero 16 (2 ^ 130) 17 := by
      norm_num [tZero, bZero, bigR]
    refine le_trans ?_ h2
    simp only [gDim, dStar]
    push_cast
    linarith
def kaZero (f m : ℕ) (rd : ℝ) : ℝ := 4 * bigR rd * (dStar f m : ℝ) ^ 2
def pOne (f r q : ℕ) : ℝ :=
  1 + (gDim f r : ℝ) * Real.log (1 + 6 * Real.sqrt ((gDim f r : ℝ) * q))
def pTwo (f m : ℕ) : ℝ := Real.log (2 * (3 * (dStar f m : ℝ)) ^ dStar f m)
def pThree (f r q m : ℕ) : ℝ := r * (pOne f r q + pTwo f m + (dStar f m : ℝ))
def pFour (f r r₁ : ℕ) (Nc : Set.Ici (1 : ℝ)) : ℝ :=
  Real.log Nc + 2 * f * (r : ℝ) ^ 2 * Real.log r₁
def bigA (f r m r₁ : ℕ) : ℝ := (r₁ : ℝ) ^ 4 * r * (dStar f m : ℝ) / 2
def bigA' (f r m : ℕ) : ℝ := max 1 (r * (dStar f m : ℝ) / 4)
def pSixteen (f r : ℕ) (rd : ℝ) (q m r₁ : ℕ) (Nc : Set.Ici (1 : ℝ)) : ℝ :=
  2 * (r₁ : ℝ) ^ 4 * (pThree f r q m + pFour f r r₁ Nc) +
    bigA f r m r₁ * Real.log (bigA f r m r₁ * kaZero f m rd)
def pFourteen (f r n q m : ℕ) : ℝ :=
  1 / 2 * ((f : ℝ) * r * n * Real.log q +
    n * (Real.log 24 + (f : ℝ) * m * Real.log (4 * f * m)) + ((r : ℝ) + 2) * Real.log 2)
def pThirteenMin (f n m : ℕ) : ℝ := 16200 * Real.pi * n * (m : ℝ) ^ 4 * (dStar f m : ℝ) ^ 4
def cCoeff (rd PP : ℝ) (D q : ℕ) : ℝ := bigR rd * PP * (D : ℝ) ^ 2 / q
def jetBound (f r : ℕ) (rd : ℝ) (D n q : ℕ) (R₀ : ℝ) (m : ℕ) (la : Set.Ioi (0 : ℝ)) : ℝ :=
  ((4 : ℝ) ^ n)⁻¹ * ((6 * (2 * (dStar f m : ℝ)) ^ ((dStar f m : ℝ) / 2)) ^ n)⁻¹ *
    ((2 : ℝ) ^ ((r + 2) * D))⁻¹ *
    Real.exp (-(2 * Real.pi * n * cChi f m rd * ph f rd q R₀ la / q))
namespace Params
variable {f r : ℕ} {rd : ℝ} {D : ℕ} (P : Params dim f r rd D n)
def ph (la : Set.Ioi (0 : ℝ)) : ℝ := WordBlockPolynomials.ph f rd P.q P.R₀ la
def jetBound (la : Set.Ioi (0 : ℝ)) : ℝ := WordBlockPolynomials.jetBound f r rd D n P.q P.R₀ P.m la
def kaZero : ℝ := WordBlockPolynomials.kaZero f P.m rd
def pOne : ℝ := WordBlockPolynomials.pOne f r P.q
def pTwo : ℝ := WordBlockPolynomials.pTwo f P.m
def pThree : ℝ := WordBlockPolynomials.pThree f r P.q P.m
end Params
end GlobalTheory.IndefiniteRowSideFullHecke.WordBlockPolynomials


