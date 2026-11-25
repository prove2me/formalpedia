-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:54:21.04384+00:00
-- url     : https://prove2.me/theorems/0cf7ef1d-60bf-41e5-aec2-d6425f29c328
-- title:
--   PFlag Dim
-- statement:
--   Definitions and structural lemmas for PFlag Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
namespace FlagDim
abbrev UIdx (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2} ⊕ Fin (n - 1)
def uMat (F : Type) [Field F] (n : ℕ) : Matrix (Fin n) (Fin n) (MvPolynomial (UIdx n) F) :=
  Matrix.of fun r c =>
    if h : r < c then X (Sum.inl ⟨(r, c), h⟩)
    else if h' : r = c ∧ r.val + 1 < n then X (Sum.inr ⟨r.val, by omega⟩) else 0
def toUpper (F : Type) [Field F] (n : ℕ) :
    MvPolynomial (Fin n × Fin n) F →ₐ[F] MvPolynomial (UIdx n) F :=
  aeval fun p => uMat F n p.1 p.2
def flagMinorMap (F : Type) [Field F] (n : ℕ) :
    MRingOver F (PluckerBlocks n n) →ₐ[F] MvPolynomial (Fin n × Fin n) F :=
  aeval fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2
def rowCols {n : ℕ} (r : ℕ) (c : Fin n) : Fin (r + 1) → Fin n :=
  fun i => if h : i.val < r ∧ i.val < c.val then ⟨i.val, by omega⟩ else c
theorem rowCols_strictMono {n : ℕ} (r : ℕ) (c : Fin n) (hc : r ≤ c.val) :
    StrictMono (rowCols r c) := by
  intro a b hab
  simp only [rowCols]
  split_ifs with h1 h2 h2 <;> simp only [Fin.lt_def] at * <;> omega
def colSet {n : ℕ} (r : ℕ) (c : Fin n) : Finset (Fin n) := Finset.univ.image (rowCols r c)
theorem colSet_card {n : ℕ} (r : ℕ) (c : Fin n) (hc : r ≤ c.val) : (colSet r c).card = r + 1 := by
  rw [colSet, Finset.card_image_of_injective _ (rowCols_strictMono r c hc).injective]
  simp
section RowReduce
variable {K : Type} [Field K] {n : ℕ}
def leadBlock (T : Matrix (Fin n) (Fin n) K) (i : Fin n) : Matrix (Fin i.val) (Fin i.val) K :=
  T.submatrix (Fin.castLE i.2.le) (Fin.castLE i.2.le)
def redCoeff (T : Matrix (Fin n) (Fin n) K) (i : Fin n) : Fin i.val → K :=
  Matrix.vecMul (fun c : Fin i.val => T i (Fin.castLE i.2.le c)) (leadBlock T i)⁻¹
def redMat (T : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i k => if h : k.val < i.val then redCoeff T i ⟨k.val, h⟩ else 0
end RowReduce
section Generic
variable (F : Type) [Field F] (n : ℕ)
abbrev GenField : Type := FractionRing (MvPolynomial (Fin n × Fin n) F)
def genMatK : Matrix (Fin n) (Fin n) (GenField F n) := (genMat F n).map (algebraMap _ _)
def genRed : Matrix (Fin n) (Fin n) (GenField F n) := (1 - redMat (genMatK F n)) * genMatK F n
def fromUpper : MvPolynomial (UIdx n) F →ₐ[F] GenField F n :=
  aeval fun u => match u with
    | Sum.inl p => genRed F n p.1.1 p.1.2
    | Sum.inr r => genRed F n ⟨r.val, by omega⟩ ⟨r.val, by omega⟩
end Generic
def ltPairsEquiv (n : ℕ) : {p : Fin n × Fin n // p.1 < p.2} ≃ Σ c : Fin n, Fin c.val where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun q := ⟨(⟨q.2.val, q.2.2.trans q.1.2⟩, q.1), q.2.2⟩
  left_inv := by rintro ⟨⟨a, b⟩, h⟩; rfl
  right_inv := by rintro ⟨c, k⟩; rfl
section Trdeg
variable (F : Type) [Field F] (n : ℕ)
def diagProd (r : ℕ) (hr : r < n) : MvPolynomial (UIdx n) F :=
  ∏ k : Fin r, uMat F n ⟨k.val, by omega⟩ ⟨k.val, by omega⟩
abbrev upperKer : Ideal (MRingOver F (PluckerBlocks n n)) := RingHom.ker ((toUpper F n).comp (flagMinorMap F n))
instance upperKer_isPrime : (upperKer F n).IsPrime := RingHom.ker_isPrime _
abbrev UpperQuot : Type := MRingOver F (PluckerBlocks n n) ⧸ upperKer F n
end Trdeg
section Grading
variable (F : Type) [Field F] (n : ℕ)
def plWeight : (Σ j, PluckerBlocks n n j) → (Fin (n - 1) → ℕ) := fun q => Pi.single q.1 1
def rowWeight : UIdx n → (Fin n → ℕ)
  | Sum.inl p => Pi.single p.1.1 1
  | Sum.inr r => Pi.single ⟨r.val, by omega⟩ 1
def rowsUpTo (j : Fin (n - 1)) : Fin n → ℕ := fun r => if r.val ≤ j.val then 1 else 0
def rowDeg : (Fin (n - 1) → ℕ) →+ (Fin n → ℕ) where
  toFun a := ∑ j, a j • rowsUpTo n j
  map_zero' := by simp
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
abbrev upperMap : MRingOver F (PluckerBlocks n n) →ₐ[F] MvPolynomial (UIdx n) F := (toUpper F n).comp (flagMinorMap F n)
end Grading
end FlagDim
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter


