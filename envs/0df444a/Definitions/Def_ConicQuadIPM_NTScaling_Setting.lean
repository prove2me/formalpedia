-- Prove2me | Definitions.Def_ConicQuadIPM_NTScaling_Setting
-- name    : ConicQuadIPM_NTScaling_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:08:37.721934+00:00
-- url     : https://prove2.me/theorems/396a7498-4f87-4d71-ac2f-102ade2ac5ba
-- title:
--   Definitions 3.1–3.2 and p. 9 — R₊ (13), the quadratic cone (14), the rotated quadratic cone (15), their interiors, Tⁱ, Qⁱ, the arrow-head matrix mat(v)
-- statement:
--   This module fixes the three cone types used from §3 on, for a single cone block of dimension $d$.
--
--   1. **Cone kinds.** `ConeKind` has three values: the positive half-line $\mathbb R_+$ (13), the **quadratic cone** (14)
--   $$K^q = \{x\in\mathbb R^d : x_1 \ge \|x_{2:d}\|\},$$
--   and the **rotated quadratic cone** (15)
--   $$K^r = \{x\in\mathbb R^d : 2x_1x_2 \ge \|x_{3:d}\|^2,\ x_1,x_2\ge 0\}.$$
--   Here $\|\cdot\|$ is the Euclidean norm and $x_{k:d}$ the subvector of coordinates $k,\dots,d$.
--   2. **Interiors.** $\operatorname{int}(\mathbb R_+) = \{x_1>0\}$, $\operatorname{int}(K^q) = \{x_1 > \|x_{2:d}\|\}$, $\operatorname{int}(K^r) = \{2x_1x_2 > \|x_{3:d}\|^2,\ x_1,x_2>0\}$.
--   3. **The matrices of Definition 3.2.** For $\mathbb R_+$, $T = Q = 1$ (16). For $K^q$, $T = I$ and $Q = \operatorname{diag}(1,-1,\dots,-1)$ (17). For $K^r$, $T$ is the identity except for its leading $2\times2$ block $\begin{bmatrix} 1/\sqrt2 & 1/\sqrt2\\ 1/\sqrt2 & -1/\sqrt2\end{bmatrix}$ (18), and $Q$ has $Q_{12}=Q_{21}=1$, $Q_{jj}=-1$ for $j\ge3$ and zeros elsewhere (19).
--   4. **The arrow-head matrix** $\operatorname{mat}(v)$ of p. 9: first row $v^T$, first column $v$, diagonal entries $v_1$, zeros elsewhere.
--   5. The dimension conventions $d=1$ for $\mathbb R_+$, $d\ge1$ for $K^q$ and $d\ge2$ for $K^r$ (`WellFormedBlock`).
--
--   These objects are the setting of the Nesterov–Todd scaling formulas of Lemma 4.2.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with 0-based indices (the paper's $x_1$ is `coord x 0`); $\|x_{2:n}\|^2$ is `tailSq x 1`, a sum of squares (Euclidean, never Mathlib's sup norm); $x^Ts$ is `x ⬝ᵥ s`. `coord v r` is the $(r+1)$-st coordinate and `tailSq v r` is $\sum_{j\ge r} v_j^2$ (0-based), so $\|v_{2:d}\|^2$ is `tailSq v 1`. The cones are stated through squared norms ($\|x_{2:d}\|^2 \le x_1^2$, $x_1\ge0$), which is equivalent to (14). The interiors use strict inequalities; the paper never defines $\operatorname{int}(K)$ concretely, and these coincide with the topological interiors. The dimension conventions are not stated in the paper; they are the minimal ones under which (13)–(19) make sense. `ConeKind`, `coord`, `tailSq`, `e1` and the cone predicates `inCone` (13)–(15) are imported from the shared module `ConicQuadIPM.Complementarity.Setting` (`e1` takes its dimension implicitly); this module adds the interiors, `WellFormedBlock`, `Tmat`, `Qmat` and `arrow`.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003), DOI 10.1007/s10107-002-0349-3; authors' preprint of 18 Dec 2000, pp. 7–9, (13)–(19), Definitions 3.1–3.2, mat(v) on p. 9

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

namespace ConicQuadIPM.NTScaling

open Matrix

/-- Dimension conventions the paper leaves implicit: `R₊` is one-dimensional, the quadratic cone
has `d ≥ 1` (so `x₁` exists), the rotated quadratic cone has `d ≥ 2` (so `x₁, x₂` exist). -/
def WellFormedBlock (kind : ConicQuadIPM.Complementarity.ConeKind) (d : ℕ) : Prop :=
  (kind = .nonneg → d = 1) ∧ (kind = .quad → 1 ≤ d) ∧ (kind = .rot → 2 ≤ d)

/-- Interior of `R₊`: `x₁ > 0`. -/
def inNonnegInt {d : ℕ} (v : Fin d → ℝ) : Prop := 0 < ConicQuadIPM.Complementarity.coord v 0

/-- Interior of `K^q`: `x₁ > ‖x_{2:n}‖`, written as `‖x_{2:n}‖² < x₁²`, `x₁ > 0`. -/
def inQuadInt {d : ℕ} (v : Fin d → ℝ) : Prop :=
  ConicQuadIPM.Complementarity.tailSq v 1 < ConicQuadIPM.Complementarity.coord v 0 ^ 2 ∧ 0 < ConicQuadIPM.Complementarity.coord v 0

/-- Interior of `K^r`: `2x₁x₂ > ‖x_{3:n}‖²`, `x₁, x₂ > 0`. -/
def inRotInt {d : ℕ} (v : Fin d → ℝ) : Prop :=
  ConicQuadIPM.Complementarity.tailSq v 2 < 2 * ConicQuadIPM.Complementarity.coord v 0 * ConicQuadIPM.Complementarity.coord v 1 ∧ 0 < ConicQuadIPM.Complementarity.coord v 0 ∧ 0 < ConicQuadIPM.Complementarity.coord v 1

/-- Membership in the interior of the cone of the given kind (strict inequalities). -/
def inConeInt {d : ℕ} : ConicQuadIPM.Complementarity.ConeKind → (Fin d → ℝ) → Prop
  | .nonneg, v => inNonnegInt v
  | .quad, v => inQuadInt v
  | .rot, v => inRotInt v

/-- The matrix `T` of Definition 3.2, p. 8: `T = 1` for `R₊` (16), `T = I` for `K^q` (17), and
for `K^r` (18) the matrix whose leading `2 × 2` block is `[1/√2, 1/√2; 1/√2, −1/√2]` and which is
the identity elsewhere. -/
noncomputable def Tmat : ConicQuadIPM.Complementarity.ConeKind → (d : ℕ) → Matrix (Fin d) (Fin d) ℝ
  | .nonneg, _ => 1
  | .quad, _ => 1
  | .rot, _ => Matrix.of fun i j =>
      if i.val < 2 ∧ j.val < 2 then
        (if i.val = 1 ∧ j.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2)
      else if i = j then 1 else 0

/-- The matrix `Q` of Definition 3.2, p. 8: `Q = 1` for `R₊` (16), `Q = diag(1, −1, …, −1)` for
`K^q` (17), and for `K^r` (19) the matrix with `Q₁₂ = Q₂₁ = 1`, `Q_jj = −1` for `j ≥ 3`, and zeros
elsewhere. -/
def Qmat : ConicQuadIPM.Complementarity.ConeKind → (d : ℕ) → Matrix (Fin d) (Fin d) ℝ
  | .nonneg, _ => 1
  | .quad, _ => Matrix.of fun i j => if i = j then (if i.val = 0 then 1 else -1) else 0
  | .rot, _ => Matrix.of fun i j =>
      if (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 0) then 1
      else if i = j ∧ 2 ≤ i.val then -1 else 0

/-- The arrow-head matrix `mat(v)` of p. 9: first row `vᵀ`, first column `v`, diagonal entries
`v₁`, zeros elsewhere. -/
def arrow {d : ℕ} (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j =>
    if i.val = 0 then v j else if j.val = 0 then v i else if i = j then ConicQuadIPM.Complementarity.coord v 0 else 0

end ConicQuadIPM.NTScaling


