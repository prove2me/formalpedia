-- Prove2me | Definitions.Def_opg37364_lps13
-- name    : opg37364_lps13
-- status  : Definition
-- author  : @arexychen
-- created : 2026-09-09T14:07:55.17271+00:00
-- url     : https://prove2.me/theorems/5913399a-8c29-444e-8f1f-7e7ec09704f1
-- title:
--   Fixed-p=13 integral generators and PGL₂ Cayley graph
-- statement:
--   Structural definitions for the fixed-$p=13$ PGL Cayley construction. The fourteen integral Hamilton quaternions have coordinates $(1,\pm2,\pm2,\pm2)$ or $(3,\pm2,0,0)$ with the nonzero imaginary entry in one of three positions. The explicit finite index is `Fin 14`, with an involution reversing the three imaginary signs.
--
--   For a prime $q>13$ and a chosen root $i^2=-1$ in $\mathbb F_q$, reduce the coordinates and use the matrix $M_i(a)$ from DSV Proposition 2.5.2 with $x=i,y=0$. The norm and determinant certificates prove $\det M_i(a)=13\ne0$, permitting the GL representative and its image in PGL modulo all nonzero scalars. The graph is Mathlib's multiplicative Cayley graph with right-multiplication edges $v\sim vs$.
--
--   The bundle contains the coordinate table, integral quaternions, conjugation index, root subtype, finite vertex instance, matrix and GL/PGL images, generator finset and graph. Its two elementary norm/determinant certificates are needed for the GL constructor. Projective distinctness, nonidentity, inverse closure and the substantive regularity proof are kept in the separate proved theorem. The definitions include no assumed connectedness, bipartiteness, girth, expansion or spectral bound.
-- source:
--   Lubotzky, Phillips and Sarnak, Ramanujan graphs, Combinatorica 8 (1988), p. 262, https://doi.org/10.1007/BF02126799 (positive odd real coordinate and even imaginary coordinates). Davidoff, Sarnak and Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs, Proposition 2.5.2 (matrix formula with x=i, y=0), Definition 4.1.1 (right Cayley convention), and Section 4.2, especially Lemma 4.2.1 and Remark 4.2.3(c), https://math.bme.hu/~gabor/oktatas/SztoM/DavidoffSarnakValette.pdf . Fixed-p=13 structural formalization of classical mathematics.

import Definitions.Def_opg37364_matching_cuts
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace OPG37364

/-- The fourteen Hamilton quaternion coordinate vectors, with positive odd real part. -/
def lps13Coords : Fin 14 → Fin 4 → ℤ :=
  ![![1, 2, 2, 2], ![1, 2, 2, -2], ![1, 2, -2, 2], ![1, 2, -2, -2],
    ![1, -2, 2, 2], ![1, -2, 2, -2], ![1, -2, -2, 2], ![1, -2, -2, -2],
    ![3, 2, 0, 0], ![3, -2, 0, 0], ![3, 0, 2, 0], ![3, 0, -2, 0],
    ![3, 0, 0, 2], ![3, 0, 0, -2]]

/-- The norm-13 integral Hamilton quaternion at an index. -/
def lps13Quaternion (a : Fin 14) : Quaternion ℤ :=
  ⟨lps13Coords a 0, lps13Coords a 1, lps13Coords a 2, lps13Coords a 3⟩

/-- Conjugation preserves the real part and reverses all three imaginary signs. -/
def lps13ConjIndex : Fin 14 → Fin 14 :=
  ![7, 6, 5, 4, 3, 2, 1, 0, 9, 8, 11, 10, 13, 12]

/-- A chosen square root of -1; its existence is not built into the definition. -/
abbrev LPS13Root (q : ℕ) := {i : ZMod q // i ^ 2 = -1}

/-- The projective vertex group is finite, as a quotient of the finite matrix unit group. -/
instance lps13PGL_finite {q : ℕ} [Fact q.Prime] :
    Finite (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- DSV's quaternion matrix formula with x=i and y=0, reducing integer coordinates. -/
def lps13QuaternionMatrix {q : ℕ} (i : ZMod q) (a : Quaternion ℤ) :
    Matrix (Fin 2) (Fin 2) (ZMod q) :=
  !![(a.re : ZMod q) + i * a.imI, (a.imJ : ZMod q) + i * a.imK;
     -(a.imJ : ZMod q) + i * a.imK, (a.re : ZMod q) - i * a.imI]

/-- The matrix representative of an indexed generator. -/
def lps13Matrix {q : ℕ} (i : LPS13Root q) (a : Fin 14) :=
  lps13QuaternionMatrix i.val (lps13Quaternion a)

-- These two structural certificates are needed to form GL elements in the definitions.
theorem lps13Quaternion_norm (a : Fin 14) :
    Quaternion.normSq (lps13Quaternion a) = 13 := by
  revert a
  decide

theorem lps13QuaternionMatrix_det {q : ℕ} (i : LPS13Root q) (a : Quaternion ℤ) :
    (lps13QuaternionMatrix i.val a).det = ((Quaternion.normSq a : ℤ) : ZMod q) := by
  simp only [lps13QuaternionMatrix, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Quaternion.normSq_def',
    Int.cast_add, Int.cast_pow]
  linear_combination -(a.imI : ZMod q)^2 * i.property - (a.imK : ZMod q)^2 * i.property

/-- The indexed GL representative. Its determinant is explicitly proved to be 13≠0. -/
noncomputable def lps13GL {q : ℕ} [Fact q.Prime] (hq : 13 < q)
    (i : LPS13Root q) (a : Fin 14) : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (lps13Matrix i a) (by
    rw [lps13Matrix, lps13QuaternionMatrix_det, lps13Quaternion_norm]
    simpa using (ZMod.natCast_eq_zero_iff 13 q).not.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) hq))

/-- Projectivization by all nonzero scalar matrices. -/
noncomputable def lps13Generator {q : ℕ} [Fact q.Prime] (hq : 13 < q)
    (i : LPS13Root q) (a : Fin 14) : Matrix.ProjGenLinGroup (Fin 2) (ZMod q) :=
  Matrix.ProjGenLinGroup.mk (lps13GL hq i a)

/-- The finite set of projective generator images. -/
noncomputable def lps13Generators {q : ℕ} [Fact q.Prime] (hq : 13 < q)
    (i : LPS13Root q) : Finset (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :=
  open scoped Classical in Finset.univ.image (lps13Generator hq i)

/-- The fixed-p=13 PGL Cayley graph, with edges v -> v*s. -/
noncomputable def lps13Graph {q : ℕ} [Fact q.Prime] (hq : 13 < q)
    (i : LPS13Root q) : SimpleGraph (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) :=
  SimpleGraph.mulCayley (lps13Generators hq i : Set _)

end OPG37364


