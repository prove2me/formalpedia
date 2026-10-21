-- Prove2me | Definitions.Def_ConvexNotSOS_Octonion_Symmetry
-- name    : ConvexNotSOS_Octonion_Symmetry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:47.301951+00:00
-- url     : https://prove2.me/theorems/d9ea6981-2626-446a-a63c-f7da4ab58852
-- title:
--   Clifford and symmetry objects for the octonionic quartic
-- statement:
--   This file defines the nine $16\times16$ **Clifford matrices** $S_0,\ldots,S_8$ from the octonion right-multiplication table, their ordered products $S_J$, and the concrete matrix group $G$ preserving their span under conjugation. Saunderson identifies $G$ with $\operatorname{Spin}(9)$. It also defines the eight index pairs
--
--   $$\Lambda=\{(0,0),(1,0),(4,0),(0,1),(1,1),(4,1),(2,-1),(3,-1)\}$$
--
--   and the invariant quartics $s_{ij}$ used in the SOS characterization. Finally, $X_1,X_2,X_3$ are the three test matrices of the proof of Theorem 4.11. These objects allow the paper's symmetry-reduced feasibility calculation to be stated directly.
--
--   **Formalization Note.** Each $s_{ij}$ is encoded by projection onto the scalar, traceless symmetric, or skew-symmetric matrix subspace and a sum over normalized Clifford products $S_J/4$. This is the basis-independent form of the page's double sum over orthonormal bases. Matrix indices start at zero.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, pp. 9–14, (10)–(13), §4.4, proof of Theorem 4.11

import Definitions.Def_ConvexNotSOS_Octonion_Forms

noncomputable section

namespace ConvexNotSOS.Octonion

/-- The Clifford matrices on p. 9, in 0-based block coordinates. -/
def S : Fin 9 → Matrix (Fin 16) (Fin 16) ℝ := fun i r c =>
  if hi : i.val = 8 then
    if r = c then (if r.val < 8 then 1 else -1) else 0
  else
    if hr : r.val < 8 then
      if hc : c.val < 8 then 0
      else Rmat (fun a : Fin 8 => if a.val = i.val then 1 else 0)
        ⟨r.val, by omega⟩ ⟨c.val - 8, by omega⟩
    else
      if hc : c.val < 8 then
        (Rmat (fun a : Fin 8 => if a.val = i.val then 1 else 0)).transpose
          ⟨r.val - 8, by omega⟩ ⟨c.val, by omega⟩
      else 0

/-- Ordered product of the Clifford matrices indexed by `J`. -/
def SJ (J : Finset (Fin 9)) : Matrix (Fin 16) (Fin 16) ℝ :=
  (J.sort (· ≤ ·)).foldl (fun A i => A * S i) 1

def V1 : Submodule ℝ (Matrix (Fin 16) (Fin 16) ℝ) :=
  Submodule.span ℝ (Set.range S)
/-- The concrete matrix group G from p. 9, identified there with Spin(9). -/
def spin9 : Set (Matrix (Fin 16) (Fin 16) ℝ) :=
  {g | g ∈ Matrix.orthogonalGroup (Fin 16) ℝ ∧ g.det = 1 ∧
    (fun Z => g * Z * g.transpose) '' (V1 : Set (Matrix (Fin 16) (Fin 16) ℝ)) = V1}

inductive UIdx where
  | minusOne | zero | one
  deriving DecidableEq

/-- The eight pairs in equation (13), in its printed order. -/
inductive Lam where
  | l00 | l10 | l40 | l01 | l11 | l41 | l2m | l3m
  deriving DecidableEq

instance : Fintype UIdx := ⟨{.minusOne, .zero, .one}, by intro x; cases x <;> simp⟩
instance : Fintype Lam := ⟨{.l00, .l10, .l40, .l01, .l11, .l41, .l2m, .l3m}, by intro x; cases x <;> simp⟩

def Lam.i : Lam → ℕ
  | .l00 | .l01 => 0
  | .l10 | .l11 => 1
  | .l2m => 2
  | .l3m => 3
  | .l40 | .l41 => 4

def Lam.j : Lam → UIdx
  | .l00 | .l10 | .l40 => .zero
  | .l01 | .l11 | .l41 => .one
  | .l2m | .l3m => .minusOne

variable {R : Type*} [CommRing R] [Algebra ℝ R]

def tracePart {k : ℕ} (A : Matrix (Fin k) (Fin k) R) : Matrix (Fin k) (Fin k) R :=
  Matrix.diagonal (fun _ => algebraMap ℝ R (1 / (k : ℝ)) * Matrix.trace A)

def projU {k : ℕ} (j : UIdx) (A : Matrix (Fin k) (Fin k) R) :
    Matrix (Fin k) (Fin k) R :=
  match j with
  | .zero => tracePart A
  | .one => algebraMap ℝ R (1 / 2) • (A + A.transpose) - tracePart A
  | .minusOne => algebraMap ℝ R (1 / 2) • (A - A.transpose)

def frobSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) : R :=
  ∑ i : Fin m, ∑ j : Fin n, A i j ^ 2

/-- The basis-independent projection formula for the paper's `s_ij`, p. 13. -/
def sForm {k : ℕ} (l : Lam) (X : Matrix (Fin 16) (Fin k) R) : R :=
  ∑ J ∈ (Finset.univ : Finset (Finset (Fin 9))).filter (fun J => J.card = l.i),
    algebraMap ℝ R (1 / 16) * frobSq (projU l.j (X.transpose *
      (SJ J).map (algebraMap ℝ R) * X))

def sPoly (k : ℕ) (l : Lam) : MvPolynomial (Var k) ℝ := sForm l (Xvar k)

/-- The three evaluation matrices from the proof of Theorem 4.11, p. 14. -/
def X1 (k : ℕ) : Matrix (Fin 16) (Fin k) ℝ :=
  fun r c => if r.val = 0 ∧ c.val = 0 then 1 else 0
def X2 (k : ℕ) : Matrix (Fin 16) (Fin k) ℝ :=
  fun r c => if c.val < 8 ∧ r.val % 8 = c.val then 1 else 0
def X3 (k : ℕ) : Matrix (Fin 16) (Fin k) ℝ :=
  fun r c => if r.val = c.val then 1 else 0

end ConvexNotSOS.Octonion


