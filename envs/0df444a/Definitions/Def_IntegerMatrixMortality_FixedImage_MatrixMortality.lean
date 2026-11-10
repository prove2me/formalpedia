-- Prove2me | Definitions.Def_IntegerMatrixMortality_FixedImage_MatrixMortality
-- name    : IntegerMatrixMortality_FixedImage_MatrixMortality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:28:20.911128+00:00
-- url     : https://prove2.me/theorems/e0ab4023-c757-4adb-a3c5-62c6d7eff082
-- title:
--   Matrix mortality, rational rank and effective input promises
-- statement:
--   For a coefficient ring K, a word in a family G of two-by-two matrices is any finite chronological list A₁,…,Aℓ, acting by Aℓ⋯A₁. The empty word acts by the identity. Define mortality by
--
--   $$\operatorname{Mortal}(G)\iff\exists\ell\ge1,\ A_1,\ldots,A_\ell\in G,\quad A_\ell\cdots A_1=0.$$
--
--   Integer matrices are included entrywise in rational matrices. Rank, image and kernel are taken over the rationals. A rational line L is a one-dimensional rational linear subspace of the rational plane. The promise on R is R≠0, rank R=1 and im R=L. A promised decider is a total computable Boolean function of the four signed entries, correct on every matrix satisfying that promise. The second decision interface accepts injective lists of four-entry matrix encodings of a fixed length; different orders represent the same finite set and all orders must receive the correct answer.
--
--   These definitions give reusable matrix decision problems, without any restriction on word lengths or entries.
-- source:
--   Thanin Quartz, Ivan O. Shevchenko, Hans De Sterck, Jun Liu, STOC 2027 submission #1062 (October 2026), §§1 and 3, PDF p. 3 / printed p. 1

import Mathlib

set_option autoImplicit false

namespace IntegerMatrixMortality.FixedImage


/-- Actual matrices; row-major codes provide an effective input interface. -/
abbrev ZMat := Matrix (Fin 2) (Fin 2) ℤ
abbrev QMat := Matrix (Fin 2) (Fin 2) ℚ
abbrev MatCode := ℤ × ℤ × ℤ × ℤ
abbrev QVec := Fin 2 → ℚ

def matrixOfCode (c : MatCode) : ZMat := !![c.1, c.2.1; c.2.2.1, c.2.2.2]
def rationalMatrix (A : ZMat) : QMat := A.map (Int.castRingHom ℚ)
def matrixLinear (A : QMat) : QVec →ₗ[ℚ] QVec := Matrix.toLin' A
/-- Chronological words: the last letter acts last. The empty word is the identity. -/
def wordMatrix {K : Type} [Semiring K] (w : List (Matrix (Fin 2) (Fin 2) K)) := w.reverse.prod

def Mortal {K : Type} [Semiring K] (G : Set (Matrix (Fin 2) (Fin 2) K)) : Prop :=
  ∃ w : List (Matrix (Fin 2) (Fin 2) K), w ≠ [] ∧ (∀ A ∈ w, A ∈ G) ∧ wordMatrix w = 0

def IsRationalLine (L : Submodule ℚ QVec) : Prop := Module.finrank ℚ L = 1

def RankOnePromise (L : Submodule ℚ QVec) (R : ZMat) : Prop :=
  R ≠ 0 ∧ Module.finrank ℚ (LinearMap.range (matrixLinear (rationalMatrix R))) = 1 ∧
    LinearMap.range (matrixLinear (rationalMatrix R)) = L

/-- The Boolean algorithm is total on all four-entry encodings, correct on every promised input. -/
def NoPromisedDecider (G : Finset ZMat) (L : Submodule ℚ QVec) : Prop :=
  ¬ ∃ f : MatCode → Bool, Computable f ∧ ∀ c : MatCode,
    RankOnePromise L (matrixOfCode c) →
      (f c = true ↔ Mortal ((G : Set ZMat) ∪ {matrixOfCode c}))

/-- Injective lists encode finite sets of exactly k distinct matrices. -/
def NoExactSizeDecider (k : ℕ) : Prop :=
  ¬ ∃ f : List MatCode → Bool, Computable f ∧ ∀ cs : List MatCode,
    cs.Nodup → cs.length = k →
      (f cs = true ↔ Mortal (matrixOfCode '' {c | c ∈ cs}))

def DeterminantsAtPrime (G : Finset ZMat) (p : ℕ) : Prop :=
  ∀ A ∈ G, A.det ≠ 0 ∧ (A.det = (p : ℤ) ∨ A.det = -(p : ℤ))


end IntegerMatrixMortality.FixedImage


