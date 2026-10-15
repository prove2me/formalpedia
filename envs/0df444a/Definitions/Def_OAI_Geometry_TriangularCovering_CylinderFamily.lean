-- Prove2me | Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
-- name    : OAI_Geometry_TriangularCovering_CylinderFamily
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:37:54.831723+00:00
-- url     : https://prove2.me/theorems/fe99c3ca-356c-4127-a0f8-24b68984d317
-- title:
--   The explicit family of $2n(\varepsilon)$ tilted triangular cylinders
-- statement:
--   Let $H=\sqrt2$, so that the tetrahedron is $K=\{(x,y,Ht):0\le t\le1,\ |x|\le1-t,\ |y|\le t\}$. Use the coordinate-cover notation $\alpha(a,b)=\frac{1+ab}4$, $\beta(a,b)=\frac{a+b}4$, the cutoff height $T_\varepsilon(a,b)=\frac12+\varepsilon^2M(a,b)$ with $M(a,b)=\frac1{1000}+\max\{d(a),d(b)\}$, $d(q)=\frac{q^2(1+q^2)}{16}$, the mesh $m_{N,j}=-1+2j/N$, and $n(\varepsilon)=\lceil2/\varepsilon^2\rceil$. For a vector $v\neq0$ write $\hat v=v/\|v\|$, and let $\mathcal C_u(p_0,p_1,p_2)$ be the triangular cylinder with axis $u$ whose base is the orthogonal projection of $\triangle(p_0,p_1,p_2)$ onto $u^\perp$.
--
--   1. **Tilted directions.** For $\varepsilon,A,B\in\mathbb{R}$,
--   $$
--   v_\varepsilon(A,B)=(1,\ \varepsilon A,\ H\varepsilon B),\qquad w_\varepsilon(A,B)=(-\varepsilon A,\ 1,\ H\varepsilon B),
--   $$
--   both nonzero.
--   2. **Base triangles.** For $a,b,T\in\mathbb{R}$, the lower triangle has vertices $(0,0,0)$, $(0,aT,HT)$, $(0,bT,HT)$ in the plane $x=0$, and the upper triangle has vertices $(0,0,H)$, $(aT,0,H(1-T))$, $(bT,0,H(1-T))$ in the plane $y=0$. For both, with $p_0,p_1,p_2$ the listed vertices and $u$ the normalized direction $\hat v_\varepsilon(A,B)$, respectively $\hat w_\varepsilon(A,B)$,
--   $$
--   \langle u,(p_1-p_0)\times(p_2-p_0)\rangle=\frac{H(a-b)T^2}{\|v_\varepsilon(A,B)\|}\ \text{ resp. }\ \frac{H(a-b)T^2}{\|w_\varepsilon(A,B)\|},
--   $$
--   which is nonzero when $a<b$ and $T>0$.
--   3. **Lower and upper cylinders.** For $a<b$ and $T>0$, the lower cylinder $L(a,b,T,\varepsilon,A,B)$ is $\mathcal C_u$ of the lower triangle with $u=\hat v_\varepsilon(A,B)$, and the upper cylinder $U(a,b,T,\varepsilon,A,B)$ is $\mathcal C_u$ of the upper triangle with $u=\hat w_\varepsilon(A,B)$.
--   4. **The family.** For $\varepsilon>0$ let $n=n(\varepsilon)$ and, for $j=0,\dots,n-1$, $a=m_{n,j}$, $b=m_{n,j+1}$. Then $L_j=L(a,b,T_\varepsilon(a,b),\varepsilon,\alpha(a,b),\beta(a,b))$ and $U_j=U(a,b,T_\varepsilon(a,b),\varepsilon,\alpha(a,b),\beta(a,b))$, and
--   $$
--   \mathcal F_\varepsilon=(L_0,\dots,L_{n-1},U_0,\dots,U_{n-1})
--   $$
--   is a family of exactly $2n(\varepsilon)$ triangular cylinders.
--
--   Also included: $H>0$, $T_\varepsilon(a,b)>0$ for all real $\varepsilon,a,b$, and $m_{N,j}<m_{N,j+1}$ for $N\ge1$, which are the side conditions needed to form the cylinders. The family $\mathcal F_\varepsilon$ is the explicit covering of $K$ used for both the asymptotic covering bound and the normalized counterexample: the lower cylinders cover the points of $K$ near the bottom edge, sector by sector, and the upper cylinders those near the top edge.
--
--   **Formalization Note** The Lean names are `tiltV`, `tiltW`, `lowerVertices`, `upperVertices`, `lowerCylinder`, `upperCylinder`, `lowerFamily`, `upperFamily` and `finiteFamily`; the cylinders are built with `projectedCylinder` and `unit`. The family is indexed by `Fin (2 * n ε)` via `Fin.append` and a cast along $2n=n+n$, lower cylinders first. The definitions take the proofs of $a<b$, $T>0$ and $\varepsilon>0$ as arguments; the helper facts are `H_pos`, `H_ne_zero`, `cutoff_pos_all`, `mesh_strict` and the cross-product computations `lower_triple`, `upper_triple` with their nonvanishing versions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CylinderFamily.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CylinderFamily.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma H_pos : 0 < H := by norm_num [H]
lemma H_ne_zero : H ≠ 0 := ne_of_gt H_pos
def tiltV (ε A B : ℝ) : Space := !₂[1, ε*A, H*ε*B]
def tiltW (ε A B : ℝ) : Space := !₂[-ε*A, 1, H*ε*B]

def lowerVertices (a b T : ℝ) : Fin 3 → Space :=
  ![point 0 0 0, point 0 (a*T) T, point 0 (b*T) T]
def upperVertices (a b T : ℝ) : Fin 3 → Space :=
  ![point 0 0 1, point (a*T) 0 (1-T), point (b*T) 0 (1-T)]

lemma tiltV_ne_zero (ε A B : ℝ) : tiltV ε A B ≠ 0 := by
  intro h
  have := congrArg (fun z : Space => z 0) h
  norm_num [tiltV] at this

lemma tiltW_ne_zero (ε A B : ℝ) : tiltW ε A B ≠ 0 := by
  intro h
  have := congrArg (fun z : Space => z 1) h
  norm_num [tiltW] at this

lemma lower_triple (a b T ε A B : ℝ) :
    inner ℝ (unit (tiltV ε A B))
      (cross3 (lowerVertices a b T 1-lowerVertices a b T 0)
        (lowerVertices a b T 2-lowerVertices a b T 0)) =
      H*(a-b)*T^2 / ‖tiltV ε A B‖ := by
  simp only [unit, inner_smul_left, conj_trivial, inner_coord, cross3_coord]
  dsimp [lowerVertices, point, tiltV]
  ring

lemma upper_triple (a b T ε A B : ℝ) :
    inner ℝ (unit (tiltW ε A B))
      (cross3 (upperVertices a b T 1-upperVertices a b T 0)
        (upperVertices a b T 2-upperVertices a b T 0)) =
      H*(a-b)*T^2 / ‖tiltW ε A B‖ := by
  simp only [unit, inner_smul_left, conj_trivial, inner_coord, cross3_coord]
  dsimp [upperVertices, point, tiltW]
  ring

lemma lower_triple_ne_zero {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    inner ℝ (unit (tiltV ε A B))
      (cross3 (lowerVertices a b T 1-lowerVertices a b T 0)
        (lowerVertices a b T 2-lowerVertices a b T 0)) ≠ 0 := by
  rw [lower_triple]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero H_ne_zero (sub_ne_zero.mpr (ne_of_lt hab)))
    (pow_ne_zero _ (ne_of_gt hT))) (norm_ne_zero_iff.mpr (tiltV_ne_zero ε A B))

lemma upper_triple_ne_zero {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) :
    inner ℝ (unit (tiltW ε A B))
      (cross3 (upperVertices a b T 1-upperVertices a b T 0)
        (upperVertices a b T 2-upperVertices a b T 0)) ≠ 0 := by
  rw [upper_triple]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero H_ne_zero (sub_ne_zero.mpr (ne_of_lt hab)))
    (pow_ne_zero _ (ne_of_gt hT))) (norm_ne_zero_iff.mpr (tiltW_ne_zero ε A B))

def lowerCylinder {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) : TriCylinder :=
  projectedCylinder (unit (tiltV ε A B)) (unit_norm (tiltV_ne_zero ε A B))
    (lowerVertices a b T 0) (lowerVertices a b T 1) (lowerVertices a b T 2)
    (lower_triple_ne_zero hab hT ε A B)

def upperCylinder {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B : ℝ) : TriCylinder :=
  projectedCylinder (unit (tiltW ε A B)) (unit_norm (tiltW_ne_zero ε A B))
    (upperVertices a b T 0) (upperVertices a b T 1) (upperVertices a b T 2)
    (upper_triple_ne_zero hab hT ε A B)

end TriangularCovering

namespace TriangularCovering

lemma cutoff_pos_all (ε a b : ℝ) : 0 < cutoff ε a b := by
  have hd : 0 ≤ d a := by unfold d; positivity
  have hm : 0 ≤ cutoffCoeff a b := by
    unfold cutoffCoeff η
    have := le_max_left (d a) (d b)
    linarith
  dsimp [cutoff]
  positivity

lemma mesh_strict {N : ℕ} (hN : 0 < N) (j : ℕ) : mesh N j < mesh N (j+1) := by
  have := mesh_succ N j
  have := step_pos hN
  linarith

def lowerFamily (ε : ℝ) (he : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  lowerCylinder (mesh_strict (ceil_count_pos he) j) (cutoff_pos_all ε (mesh (n ε) j) (mesh (n ε) (j+1))) ε
    (alpha (mesh (n ε) j) (mesh (n ε) (j+1)))
    (beta (mesh (n ε) j) (mesh (n ε) (j+1)))

def upperFamily (ε : ℝ) (he : 0 < ε) (j : Fin (n ε)) : TriCylinder :=
  upperCylinder (mesh_strict (ceil_count_pos he) j) (cutoff_pos_all ε (mesh (n ε) j) (mesh (n ε) (j+1))) ε
    (alpha (mesh (n ε) j) (mesh (n ε) (j+1)))
    (beta (mesh (n ε) j) (mesh (n ε) (j+1)))

def finiteFamily (ε : ℝ) (he : 0 < ε) : Fin (2*n ε) → TriCylinder :=
  (Fin.append (lowerFamily ε he) (upperFamily ε he)) ∘ Fin.cast (two_mul (n ε))

end TriangularCovering

end

end OAI


