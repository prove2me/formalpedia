-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
-- name    : OAI_Geometry_DoublingHilbert_Construction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:07:07.591431+00:00
-- url     : https://prove2.me/theorems/84fe190e-5cc5-464c-a14d-8d3166fa2bfc
-- title:
--   Colored strips, scales $1000^{-(j+1)}$, and orthogonal displacement sheets: a subset of $\ell^2$
-- statement:
--   This module constructs, once and for all, the subset $S$ of real $\ell^2$ that serves as a doubling subset of Hilbert space with no bi-Lipschitz embedding into any $\mathbb{R}^k$. Throughout, $\ell^2=\ell^2(\mathbb{N};\mathbb{R})$ has standard unit vectors $e_0,e_1,e_2,\dots$, points of the base plane $\mathbb{R}^2$ are written $p=(p_1,p_2)$, and $\pi:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ denotes Mathlib's pairing bijection.
--
--   1. **Scales and level parameters.** Level $j\in\mathbb{N}$ has scale $r_j=1000^{-(j+1)}$. Its number of colors $N_j$ and width factor $W_j$ are read off from $j$ by unpairing twice: if $\pi^{-1}(j)=(m,m')$ and $\pi^{-1}(m)=(a,b)$, then $N_j=a+1$ and $W_j=b+1$. Hence $r_j>0$, $N_j\ge1$, $W_j\ge1$, and every pair $(N,W)$ of positive integers equals $(N_j,W_j)$ for infinitely many levels $j$.
--
--   2. **Colored strips and allowed colors.** A real number $t$ lies in a strip of width $h$ and color $i$ modulo $N$ if $qh<t<(q+1)h$ for some integer $q$ with $q\bmod N=i$. Color $i$ is allowed at level $j$ at the point $p$ if $p_2$ lies in a horizontal strip of width $r_j$ of color $i$, or $p_1$ lies in a vertical strip of width $W_jr_j$ of color $i$ (both modulo $N_j$):
--   $$
--   U_{j,i}=\Bigl\{p:\ p_2\in\bigcup_{q\equiv i\ (N_j)}\bigl(qr_j,(q+1)r_j\bigr)\Bigr\}\ \cup\ \Bigl\{p:\ p_1\in\bigcup_{q\equiv i\ (N_j)}\bigl(qW_jr_j,(q+1)W_jr_j\bigr)\Bigr\}.
--   $$
--
--   3. **Admissible tuples and sheet domains.** A tuple is a finitely supported function $w:\mathbb{N}\to\mathbb{N}$; the entry $w_j=0$ means no displacement at level $j$, and $w_j=i+1$ means a displacement of color $i$. The pair $(p,w)$ is admissible if $w_j\le N_j$ and $p\in U_{j,w_j-1}$ for every $j$ with $w_j\neq0$. The sheet domain of $w$ is $\Omega_w=\{p\in\mathbb{R}^2:(p,w)\text{ admissible}\}$; in particular the zero tuple is admissible at every $p$.
--
--   4. **Points and the set $S$.** The displacement of level $j$ and color $i$ is $\ell_{j,i}=r_j\,e_{2+\pi(j,i)}$, so distinct pairs $(j,i)$ use distinct coordinates, all different from $0$ and $1$. With $b(p)=p_1e_0+p_2e_1$ and $\tau(w)=\sum_{j:\,w_j\neq0}\ell_{j,w_j-1}$, the point attached to $(p,w)$ and the constructed set are
--   $$
--   z(p,w)=b(p)+\tau(w),\qquad S=\{z(p,w):\ (p,w)\text{ admissible}\}\subseteq\ell^2 .
--   $$
--   The full level-$j$ component of $z(p,w)$ is $\epsilon_j(w)=0$ if $w_j=0$ and $\epsilon_j(w)=\ell_{j,w_j-1}$ otherwise.
--
--   5. **Elementary metric facts** recorded with the definitions: $\|\ell_{j,i}\|=r_j$; $\langle\ell_{j,i},\ell_{m,h}\rangle$ equals $r_jr_m$ if $(j,i)=(m,h)$ and $0$ otherwise; $b(p)-b(q)=b(p-q)$ and $\|b(p)\|^2=p_1^2+p_2^2$; for a common tuple, $\|z(p,w)-z(q,w)\|^2=(p_1-q_1)^2+(p_2-q_2)^2$ and hence $\|z(p,w)-z(q,w)\|\le 2\,d(p,q)$; finally $z(p,0)=b(p)$ and $z(p,w)\in S$ whenever $(p,w)$ is admissible.
--
--   The rapid decay of the scales $r_j$ is what yields a uniform doubling constant for $S$, while the recurrence of every pair $(N_j,W_j)$ and the mutual orthogonality of all displacements let the sheets $p\mapsto f(z(p,w))$ of a hypothetical embedding $f$ be compared across colors at arbitrarily fine levels.
--
--   **Formalization Note** The plane is the type `Base` of pairs of reals with Lean's product metric $d(p,q)=\max(|p_1-q_1|,|p_2-q_2|)$, tuples are `Tuple` (finitely supported functions on the naturals), and $\ell^2$ is `RealL2`. The objects above are `scale`, `colors`, `widthFactor`, `inColoredStrip`, `allowed`, `admissible`, `sheetDomain`, `coordinate` (the index $2+\pi(j,i)$), `levelVector`, `tupleVector`, `baseVector`, `point`, `constructedSet` and `entryVector`. The residue $q\bmod N$ is the integer remainder `Int.emod`, so a color $i\ge N$ is never allowed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Construction.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Construction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DoublingHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DoublingHilbert

namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

abbrev Base := ℝ × ℝ
abbrev Tuple := ℕ →₀ ℕ

/-- The scale at index `j` has exponent `j + 1`. -/
def scale (j : ℕ) : ℝ := (1000 : ℝ)⁻¹ ^ (j + 1)

def colors (j : ℕ) : ℕ := (Nat.unpair (Nat.unpair j).1).1 + 1

def widthFactor (j : ℕ) : ℕ := (Nat.unpair (Nat.unpair j).1).2 + 1

theorem colors_pos (j : ℕ) : 0 < colors j := Nat.succ_pos _

theorem widthFactor_pos (j : ℕ) : 0 < widthFactor j := Nat.succ_pos _

theorem scale_pos (j : ℕ) : 0 < scale j := by unfold scale; positivity

def inColoredStrip (width : ℝ) (N i : ℕ) (t : ℝ) : Prop :=
  ∃ q : ℤ, q % (N : ℤ) = (i : ℤ) ∧ (q : ℝ) * width < t ∧
    t < ((q : ℝ) + 1) * width

def allowed (j i : ℕ) (p : Base) : Prop :=
  inColoredStrip (scale j) (colors j) i p.2 ∨
    inColoredStrip ((widthFactor j : ℝ) * scale j) (colors j) i p.1

/-- Value zero means no displacement; a nonzero tuple entry `i+1` means color `i`. -/
def admissible (p : Base) (w : Tuple) : Prop :=
  ∀ j ∈ w.support, w j ≤ colors j ∧ allowed j (w j - 1) p

def sheetDomain (w : Tuple) : Set Base := {p | admissible p w}

def coordinate (j i : ℕ) : ℕ := 2 + Nat.pair j i

noncomputable def levelVector (j i : ℕ) : RealL2 :=
  lp.single 2 (coordinate j i) (scale j)

noncomputable def tupleVector (w : Tuple) : RealL2 :=
  ∑ j ∈ w.support, levelVector j (w j - 1)

noncomputable def baseVector (p : Base) : RealL2 :=
  lp.single 2 0 p.1 + lp.single 2 1 p.2

noncomputable def point (p : Base) (w : Tuple) : RealL2 :=
  baseVector p + tupleVector w

/-- The fixed subset defined by finite-support displacements and open-strip conditions. -/
def constructedSet : Set RealL2 := {z | ∃ p w, admissible p w ∧ z = point p w}

@[simp] theorem admissible_zero (p : Base) : admissible p 0 := by simp [admissible]

@[simp] theorem tupleVector_zero : tupleVector 0 = 0 := by simp [tupleVector]

@[simp] theorem point_zero (p : Base) : point p 0 = baseVector p := by simp [point]

theorem point_mem (p : Base) (w : Tuple) (h : admissible p w) :
    point p w ∈ constructedSet := ⟨p, w, h, rfl⟩

theorem coordinate_injective : Function.Injective (fun ji : ℕ × ℕ => coordinate ji.1 ji.2) := by
  intro a b h
  apply Nat.pairEquiv.injective
  exact Nat.add_left_cancel h

@[simp] theorem coordinate_ne_zero (j i : ℕ) : coordinate j i ≠ 0 := by
  unfold coordinate; omega

@[simp] theorem coordinate_ne_one (j i : ℕ) : coordinate j i ≠ 1 := by
  unfold coordinate; omega

@[simp] theorem norm_levelVector (j i : ℕ) : ‖levelVector j i‖ = scale j := by
  rw [levelVector, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  exact Real.norm_of_nonneg (scale_pos j).le

@[simp] theorem inner_levelVector (j i m h : ℕ) :
    inner ℝ (levelVector j i) (levelVector m h) =
      if j = m ∧ i = h then scale j * scale m else 0 := by
  classical
  rw [levelVector, lp.inner_single_left]
  simp only [levelVector, lp.single_apply, RCLike.inner_apply, conj_trivial]
  by_cases heq : coordinate j i = coordinate m h
  · have heq' : (j, i) = (m, h) := coordinate_injective heq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq'
    simp
  · have hneq : ¬ (j = m ∧ i = h) := by
      rintro ⟨rfl, rfl⟩
      exact heq rfl
    simp [heq, hneq]

theorem baseVector_sub (p q : Base) :
    baseVector p - baseVector q = baseVector (p - q) := by
  simp only [baseVector, Prod.fst_sub, Prod.snd_sub, lp.single_sub]
  abel

theorem baseVector_norm_sq (p : Base) : ‖baseVector p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [baseVector, norm_add_sq_real]
  simp [lp.inner_single_left, lp.single_apply, lp.norm_single, Real.norm_eq_abs, sq_abs]

theorem point_dist_sameTuple_sq (p q : Base) (w : Tuple) :
    dist (point p w) (point q w) ^ 2 = (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
  rw [dist_eq_norm]
  simp only [point, add_sub_add_right_eq_sub, baseVector_sub, baseVector_norm_sq,
    Prod.fst_sub, Prod.snd_sub]

/-- The complete level coordinate, including zero. -/
def entryVector (w : Tuple) (j : ℕ) : RealL2 :=
  if w j = 0 then 0 else levelVector j (w j - 1)

@[simp] theorem entryVector_eq_zero {w : Tuple} {j : ℕ} (hj : w j = 0) :
    entryVector w j = 0 := by simp [entryVector, hj]

@[simp] theorem entryVector_of_ne_zero {w : Tuple} {j : ℕ} (hj : w j ≠ 0) :
    entryVector w j = levelVector j (w j - 1) := by simp [entryVector, hj]

theorem point_dist_sameTuple_le (p q : Base) (w : Tuple) :
    dist (point p w) (point q w) ≤ 2 * dist p q := by
  have hd := point_dist_sameTuple_sq p q w
  have hx : |p.1 - q.1| ≤ dist p q := by simp [Real.dist_eq, Prod.dist_eq]
  have hy : |p.2 - q.2| ≤ dist p q := by simp [Real.dist_eq, Prod.dist_eq]
  have hxs : (p.1 - q.1)^2 ≤ (dist p q)^2 := by nlinarith [sq_abs (p.1 - q.1), abs_nonneg (p.1 - q.1)]
  have hys : (p.2 - q.2)^2 ≤ (dist p q)^2 := by nlinarith [sq_abs (p.2 - q.2), abs_nonneg (p.2 - q.2)]
  nlinarith [dist_nonneg (x := p) (y := q), dist_nonneg (x := point p w) (y := point q w)]

end DoublingHilbert

end

end OAI


