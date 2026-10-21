-- Prove2me | Definitions.Def_ConvexNotSOS_Octonion_Forms
-- name    : ConvexNotSOS_Octonion_Forms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:13.811131+00:00
-- url     : https://prove2.me/theorems/b58ce72d-6ebd-448d-8157-609fa78e5878
-- title:
--   Octonionic Cauchy–Schwarz and sphere-optimization forms
-- statement:
--   The coordinate model fixes the octonion multiplication used throughout this mission. For $k$ octonion pairs $x_j,y_j$, write $\|x\|^2=\sum_j|x_j|^2$ and $\langle x,y\rangle=\sum_j\bar x_jy_j$. The two quartics are
--
--   $$\operatorname{cs}^{\mathbb O}_k=\|x\|^2\|y\|^2-|\langle x,y\rangle|^2,\qquad q^{\mathbb O}_k=\operatorname{cs}^{\mathbb O}_k+\tfrac14(\|x\|^2+\|y\|^2)^2.$$
--
--   For any real polynomial $p$ in finitely many variables, the definitions also give its minimum and maximum on the Euclidean unit sphere, the best lower bound obtained from an SOS decomposition of $p-\gamma\|z\|^{2d}$, and the resulting gap quotient. These shared objects fix the meaning of every subsequent theorem.
--
--   **Formalization Note.** Octonions use the right-multiplication table printed on p. 9; $x$ and $y$ occupy the first and last eight rows of a $16\times k$ matrix. The extrema and best SOS bound use real `sInf` and `sSup`, which have Lean default values for empty or unbounded sets. The main theorem uses $k\ge17$, where the sphere is nonempty and the extrema are genuine.
-- source:
--   Saunderson, A convex form that is not a sum of squares, arXiv:2105.08432v2, pp. 2–4 and 9, (1), (8), right-multiplication matrix [Tia00]

import Mathlib

noncomputable section

namespace ConvexNotSOS.Octonion
open MvPolynomial

variable {R : Type*} [CommRing R] [Algebra ℝ R]

/-- Right multiplication by the octonion with coordinates `a`, in the table of p. 9. -/
def Rmat (a : Fin 8 → R) : Matrix (Fin 8) (Fin 8) R :=
  !![a 0, -a 1, -a 2, -a 3, -a 4, -a 5, -a 6, -a 7;
     a 1, a 0, a 3, -a 2, a 5, -a 4, -a 7, a 6;
     a 2, -a 3, a 0, a 1, a 6, a 7, -a 4, -a 5;
     a 3, a 2, -a 1, a 0, a 7, -a 6, a 5, -a 4;
     a 4, -a 5, -a 6, -a 7, a 0, a 1, a 2, a 3;
     a 5, a 4, -a 7, a 6, -a 1, a 0, -a 3, a 2;
     a 6, a 7, a 4, -a 5, -a 2, a 3, a 0, -a 1;
     a 7, -a 6, a 5, a 4, -a 3, -a 2, a 1, a 0]

def omul (v u : Fin 8 → R) : Fin 8 → R := (Rmat u).mulVec v
def oconj (u : Fin 8 → R) : Fin 8 → R := fun i => if i = 0 then u 0 else -u i

def xc {k : ℕ} (X : Matrix (Fin 16) (Fin k) R) (j : Fin k) : Fin 8 → R :=
  fun a => X ⟨a.val, by omega⟩ j
def yc {k : ℕ} (X : Matrix (Fin 16) (Fin k) R) (j : Fin k) : Fin 8 → R :=
  fun a => X ⟨a.val + 8, by omega⟩ j

def nx {k : ℕ} (X : Matrix (Fin 16) (Fin k) R) : R :=
  ∑ j : Fin k, ∑ a : Fin 8, xc X j a ^ 2
def ny {k : ℕ} (X : Matrix (Fin 16) (Fin k) R) : R :=
  ∑ j : Fin k, ∑ a : Fin 8, yc X j a ^ 2
def ip {k : ℕ} (X : Matrix (Fin 16) (Fin k) R) : Fin 8 → R :=
  ∑ j : Fin k, omul (oconj (xc X j)) (yc X j)
def csForm {k : ℕ} (X : Matrix (Fin 16) (Fin k) R) : R :=
  nx X * ny X - ∑ a : Fin 8, ip X a ^ 2
def qForm {k : ℕ} (X : Matrix (Fin 16) (Fin k) R) : R :=
  csForm X + algebraMap ℝ R (1 / 4) * (nx X + ny X) ^ 2

abbrev Var (k : ℕ) := Fin 16 × Fin k
def Xvar (k : ℕ) : Matrix (Fin 16) (Fin k) (MvPolynomial (Var k) ℝ) :=
  fun i j => MvPolynomial.X (i, j)
def csPoly (k : ℕ) : MvPolynomial (Var k) ℝ := csForm (Xvar k)
def qPoly (k : ℕ) : MvPolynomial (Var k) ℝ := qForm (Xvar k)
def evalM {k : ℕ} (X : Matrix (Fin 16) (Fin k) ℝ)
    (f : MvPolynomial (Var k) ℝ) : ℝ :=
  MvPolynomial.eval (fun ij => X ij.1 ij.2) f

def normSqPoly (σ : Type*) [Fintype σ] : MvPolynomial σ ℝ :=
  ∑ i : σ, MvPolynomial.X i ^ 2
def unitSphere (σ : Type*) [Fintype σ] : Set (σ → ℝ) :=
  {x | ∑ i : σ, x i ^ 2 = 1}
def pmax {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) : ℝ :=
  sSup ((fun x => MvPolynomial.eval x p) '' unitSphere σ)
def pmin {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) : ℝ :=
  sInf ((fun x => MvPolynomial.eval x p) '' unitSphere σ)
def psosMin {σ : Type*} [Fintype σ] (d : ℕ) (p : MvPolynomial σ ℝ) : ℝ :=
  sSup {γ : ℝ | IsSumSq (p - MvPolynomial.C γ * normSqPoly σ ^ d)}
def gap {σ : Type*} [Fintype σ] (d : ℕ) (p : MvPolynomial σ ℝ) : ℝ :=
  (pmax p - psosMin d p) / (pmax p - pmin p)

end ConvexNotSOS.Octonion


