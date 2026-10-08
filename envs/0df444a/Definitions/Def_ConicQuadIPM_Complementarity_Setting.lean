-- Prove2me | Definitions.Def_ConicQuadIPM_Complementarity_Setting
-- name    : ConicQuadIPM_Complementarity_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:11:51.347639+00:00
-- url     : https://prove2.me/theorems/1cfd97db-716c-4a48-b472-8a877624569b
-- title:
--   Definitions 3.1–3.2, pp. 7–9 and p. 11 — R₊, the quadratic cone (14), the rotated quadratic cone (15), Tⁱ, Qⁱ, the arrow-head matrix mat(v), the product cone K, µ and N(β)
-- statement:
--   This module fixes the objects of §3 of Andersen, Roos & Terlaky.
--
--   **Cones (Definition 3.1, p. 7).** For a vector $v=(v_1,\dots,v_n)\in\mathbb R^n$ write $v_{2:n}=(v_2,\dots,v_n)$ and let $\|\cdot\|$ be the Euclidean norm. The three cones are
--   $$
--   \mathbb R_+=\{x\in\mathbb R: x\ge 0\},\qquad
--   K^q=\{x\in\mathbb R^n: x_1^2\ge\|x_{2:n}\|^2,\ x_1\ge 0\},\qquad
--   K^r=\{x\in\mathbb R^n: 2x_1x_2\ge\|x_{3:n}\|^2,\ x_1,x_2\ge 0\}.
--   $$
--
--   **The matrices $T$ and $Q$ (Definition 3.2, p. 8).** For $\mathbb R_+$, $T=Q=1$. For the quadratic cone $T=I_n$ and $Q=\operatorname{diag}(1,-1,\dots,-1)$. For the rotated quadratic cone $T$ is the identity except for its leading $2\times 2$ block $\begin{pmatrix}1/\sqrt2&1/\sqrt2\\1/\sqrt2&-1/\sqrt2\end{pmatrix}$, and $Q$ is $-I$ except for its leading $2\times2$ block $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   **The arrow-head matrix (p. 9).** For $v\in\mathbb R^n$,
--   $$
--   \operatorname{mat}(v)=\begin{pmatrix}v_1 & v_{2:n}^T\\ v_{2:n} & v_1 I\end{pmatrix},
--   $$
--   and $e_1$ is the first unit vector.
--
--   **The product cone (p. 8).** $K=K^1\times\cdots\times K^k$, each $K^i$ one of the three cones above, of dimension $n^i$, and $x=(x^1;\dots;x^k)$ with $x^i\in\mathbb R^{n^i}$; $x^Ts=\sum_i (x^i)^Ts^i$.
--
--   **The neighbourhood (p. 11).** With $\mu=(x^Ts+\tau\kappa)/(k+1)$,
--   $$
--   \mathcal N(\beta)=\Bigl\{(x,\tau,s,\kappa): (x;\tau),(s;\kappa)\in K\times\mathbb R_+,\ \min\Bigl(\sqrt{(x^1)^TQ^1x^1(s^1)^TQ^1s^1},\dots,\sqrt{(x^k)^TQ^kx^k(s^k)^TQ^ks^k},\ \tau\kappa\Bigr)\ge\beta\mu\Bigr\}.
--   $$
--
--   These are the shared objects of the complementarity lemma (Lemma 3.1) and of the central-path neighbourhood used by the algorithm.
--
--   **Formalization Note.** Vectors are `Fin d → ℝ` with the paper's $x_1$ at index `0` (`coord v 0`), $x_2$ at index `1`. Norms are Euclidean and written out: `tailSq v 1` $=\|v_{2:n}\|^2$, `tailSq v 2` $=\|v_{3:n}\|^2$ (never Mathlib's sup norm). A point of $K$ is stored block by block, `x : (i : Fin k) → Fin (n i) → ℝ`, and $x^Ts$ is written $\sum_i x^i\cdot s^i$. The paper leaves the block dimensions implicit; `BlockWF`/`WellFormed` record them ($n^i=1$ for $\mathbb R_+$, $n^i\ge1$ for $K^q$, $n^i\ge2$ for $K^r$) and are added as a hypothesis wherever needed. `Nbhd` encodes the minimum as one inequality per entry.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, pp. 7–11, Definitions 3.1–3.2, (13)–(19), mat(v) (p. 9), N(β) and µ (p. 11)

import Mathlib

namespace ConicQuadIPM.Complementarity

open Matrix

/-- The three kinds of cone of Definition 3.1: `R₊` (13), the quadratic cone `K^q` (14),
the rotated quadratic cone `K^r` (15). -/
inductive ConeKind
  | nonneg
  | quad
  | rot
  deriving DecidableEq

/-- The `r`-th coordinate of `v`, 0-based (`coord v 0` is the paper's `v₁`). It is `0` when
`r ≥ d`. -/
def coord {d : ℕ} (v : Fin d → ℝ) (r : ℕ) : ℝ :=
  ∑ j : Fin d, if j.val = r then v j else 0

/-- `tailSq v r = ∑_{j ≥ r} v_j²` (0-based), the squared Euclidean norm of the paper's
`v_{r+1:n}`. So `tailSq v 1 = ‖v_{2:n}‖²` and `tailSq v 2 = ‖v_{3:n}‖²`. -/
def tailSq {d : ℕ} (v : Fin d → ℝ) (r : ℕ) : ℝ :=
  ∑ j : Fin d, if r ≤ j.val then v j ^ 2 else 0

/-- `R₊` (13): `v₁ ≥ 0`. -/
def inNonneg {d : ℕ} (v : Fin d → ℝ) : Prop :=
  0 ≤ coord v 0

/-- The quadratic cone (14): `v₁² ≥ ‖v_{2:n}‖²`, `v₁ ≥ 0`. -/
def inQuad {d : ℕ} (v : Fin d → ℝ) : Prop :=
  tailSq v 1 ≤ coord v 0 ^ 2 ∧ 0 ≤ coord v 0

/-- The rotated quadratic cone (15): `2 v₁ v₂ ≥ ‖v_{3:n}‖²`, `v₁, v₂ ≥ 0`. -/
def inRot {d : ℕ} (v : Fin d → ℝ) : Prop :=
  tailSq v 2 ≤ 2 * coord v 0 * coord v 1 ∧ 0 ≤ coord v 0 ∧ 0 ≤ coord v 1

/-- Membership in the cone of the given kind. -/
def inCone {d : ℕ} : ConeKind → (Fin d → ℝ) → Prop
  | .nonneg, v => inNonneg v
  | .quad, v => inQuad v
  | .rot, v => inRot v

/-- The matrix `Tⁱ` of Definition 3.2, (16)–(18). For `rot` the leading `2 × 2` block is
`[1/√2, 1/√2; 1/√2, −1/√2]` and the rest is the identity. -/
noncomputable def Tmat : ConeKind → (d : ℕ) → Matrix (Fin d) (Fin d) ℝ
  | .nonneg, _ => 1
  | .quad, _ => 1
  | .rot, _ => fun a b =>
      if a.val < 2 ∧ b.val < 2 then
        (if a.val = 1 ∧ b.val = 1 then -(1 / Real.sqrt 2) else 1 / Real.sqrt 2)
      else if a = b then 1 else 0

/-- The matrix `Qⁱ` of Definition 3.2, (16), (17), (19): `1` for `R₊`,
`diag(1, −1, …, −1)` for `K^q`, and for `K^r` the leading block `[0, 1; 1, 0]` followed by
`−1` on the rest of the diagonal. -/
def Qmat : ConeKind → (d : ℕ) → Matrix (Fin d) (Fin d) ℝ
  | .nonneg, _ => 1
  | .quad, _ => Matrix.diagonal (fun a => if a.val = 0 then 1 else -1)
  | .rot, _ => fun a b =>
      if a.val < 2 ∧ b.val < 2 then (if a.val ≠ b.val then 1 else 0)
      else if a = b then -1 else 0

/-- The arrow-head matrix `mat(v) = [v₁, v_{2:n}ᵀ; v_{2:n}, v₁ I]` (p. 9). -/
def arrow {d : ℕ} (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ := fun a b =>
  if a.val = 0 then v b
  else if b.val = 0 then v a
  else if a = b then coord v 0
  else 0

/-- The first unit vector `e₁` (index `0`). -/
def e1 {d : ℕ} : Fin d → ℝ := fun a => if a.val = 0 then 1 else 0

/-- Dimension conventions of a single block, left implicit by the paper:
`R₊` has dimension `1`, `K^q` dimension `≥ 1`, `K^r` dimension `≥ 2`. -/
def BlockWF (c : ConeKind) (d : ℕ) : Prop :=
  (c = .nonneg → d = 1) ∧ (c = .quad → 1 ≤ d) ∧ (c = .rot → 2 ≤ d)

/-- Every block of the product `K = K¹ × ⋯ × Kᵏ` satisfies `BlockWF`. -/
def WellFormed {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ) : Prop :=
  ∀ i, BlockWF (kind i) (n i)

/-- `x ∈ K = K¹ × ⋯ × Kᵏ`, with `x = (x¹; …; xᵏ)` stored block by block. -/
def inK {k : ℕ} (kind : Fin k → ConeKind) {n : Fin k → ℕ}
    (x : (i : Fin k) → Fin (n i) → ℝ) : Prop :=
  ∀ i, inCone (kind i) (x i)

/-- `µ = (xᵀs + τκ)/(k + 1)` (p. 11), with `xᵀs = ∑ᵢ (xⁱ)ᵀsⁱ`. -/
noncomputable def mu {k : ℕ} {n : Fin k → ℕ} (x s : (i : Fin k) → Fin (n i) → ℝ)
    (τ κ : ℝ) : ℝ :=
  ((∑ i, x i ⬝ᵥ s i) + τ * κ) / ((k : ℝ) + 1)

/-- The neighbourhood `N(β)` of p. 11: `(x; τ), (s; κ) ∈ K̄ = K × R₊` and
`min(√((x¹)ᵀQ¹x¹ (s¹)ᵀQ¹s¹), …, √((xᵏ)ᵀQᵏxᵏ (sᵏ)ᵀQᵏsᵏ), τκ) ≥ βµ`. -/
def Nbhd {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ) (β : ℝ)
    (x : (i : Fin k) → Fin (n i) → ℝ) (τ : ℝ)
    (s : (i : Fin k) → Fin (n i) → ℝ) (κ : ℝ) : Prop :=
  inK kind x ∧ 0 ≤ τ ∧ inK kind s ∧ 0 ≤ κ ∧
  (∀ i, β * mu x s τ κ ≤
      Real.sqrt ((x i ⬝ᵥ (Qmat (kind i) (n i) *ᵥ x i)) *
        (s i ⬝ᵥ (Qmat (kind i) (n i) *ᵥ s i)))) ∧
  β * mu x s τ κ ≤ τ * κ

end ConicQuadIPM.Complementarity


