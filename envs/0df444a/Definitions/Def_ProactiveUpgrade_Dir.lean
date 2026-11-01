-- Prove2me | Definitions.Def_ProactiveUpgrade_Dir
-- name    : ProactiveUpgrade_Dir
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:11.304101+00:00
-- url     : https://prove2.me/theorems/00d8b59d-41e2-4e53-bb6d-0a0068431ef0
-- title:
--   First-difference operators $\Delta_{e_i}$, $\Delta_{-e_i}$, $\Delta_{d_i}$ on $\mathbb Z^n$
-- statement:
--   For a function $g$ on $\mathbb Z^n$ the Online Supplement defines
--
--   $$
--   \Delta_{e_i}g(x)=g(x+e_i)-g(x),\qquad \Delta_{-e_i}g(x)=g(x-e_i)-g(x),
--   $$
--
--   $$
--   \Delta_{d_i}g(x)=\Delta_{-e_i}g(x)-\Delta_{-e_{i-1}}g(x)=g(x-e_{i-1}+d_i)-g(x-e_{i-1}),\qquad i\ge2,
--   $$
--
--   with $d_i=e_{i-1}-e_i$. Each operator is encoded as a **direction**: a shift $s$ and a vector $v$, with $\Delta g(x)=g(x+s+v)-g(x+s)$; for $\Delta_{d_i}$ the shift is $-e_{i-1}$. A second difference $\Delta_u\Delta_w g(x)$ evaluates $g$ at the four points $x+s_u+s_w+c$, $c\in\{0,v_u,v_w,v_u+v_w\}$.
--
--   The file also fixes the unit vectors $e_i$, the quadrant $\mathbb N^n\subseteq\mathbb Z^n$, and the reading of a function on $\mathbb N^n$ as a function on $\mathbb Z^n$.
--
--   **Formalization Note** Functions of the paper live on inventories $x\ge0$; they are read on $\mathbb Z^n$ through `Int.toNat` (`liftZ`), whose values off the quadrant are junk. Every statement evaluates them only at points of the quadrant (`EvalInQuad`, `InQuad`).
-- source:
--   Chen, Tang, Wang, Wang & Yu, Offering Free Upgrades Even before Stocks Run out, SSRN 3777846, Appendix A, p.31

import Mathlib

namespace ProactiveUpgrade

/-- The unit vector `eᵢ ∈ ℤⁿ`. -/
def unitVec {n : ℕ} (i : Fin n) : Fin n → ℤ :=
  Pi.single i 1

/-- `y` lies in the quadrant `ℕⁿ ⊆ ℤⁿ`. -/
def InQuad {n : ℕ} (y : Fin n → ℤ) : Prop :=
  ∀ k, 0 ≤ y k

/-- A nonnegative integer vector seen in `ℤⁿ`. -/
def toZ {n : ℕ} (x : Fin n → ℕ) : Fin n → ℤ :=
  fun k => (x k : ℤ)

/-- A function on `ℕⁿ` read on `ℤⁿ` through `Int.toNat`. **Formalization Note** Its values off the
quadrant are junk; every statement evaluates it only at points that satisfy `InQuad`. -/
def liftZ {n : ℕ} (f : (Fin n → ℕ) → ℝ) : (Fin n → ℤ) → ℝ :=
  fun y => f (fun k => (y k).toNat)

/-- The index `k − 1` of a nonzero index `k`. -/
def predIdx {n : ℕ} (k : Fin n) (hk : 0 < k.val) : Fin n :=
  ⟨k.val - 1, by omega⟩

/-- **First-difference operators of the Online Supplement** (Chen et al., SSRN 3777846, Appendix A,
p.31). A direction is a shift `s` and a vector `v`; its difference operator is
`∆g(x) = g(x + s + v) − g(x + s)`. The paper's operators are
* `∆_{eᵢ} g(x) = g(x + eᵢ) − g(x)` (`Dir.posE`, `s = 0`, `v = eᵢ`);
* `∆_{−eᵢ} g(x) = g(x − eᵢ) − g(x)` (`Dir.negE`, `s = 0`, `v = −eᵢ`);
* `∆_{dᵢ} g(x) = ∆_{−eᵢ} g(x) − ∆_{−e_{i−1}} g(x) = g(x − e_{i−1} + dᵢ) − g(x − e_{i−1})` for
  `i ≥ 2` (`Dir.dd`, `s = −e_{i−1}`, `v = dᵢ = e_{i−1} − eᵢ`).

**Formalization Note** The shift makes `∆_{dᵢ}` exactly the printed operator, which is not the plain
difference `g(x + dᵢ) − g(x)`. -/
structure Dir (n : ℕ) where
  /-- base-point shift `s` -/
  shift : Fin n → ℤ
  /-- step vector `v` -/
  vec : Fin n → ℤ

/-- The difference operator of a direction: `∆g(x) = g(x + s + v) − g(x + s)`. -/
def Dir.delta {n : ℕ} (u : Dir n) (g : (Fin n → ℤ) → ℝ) (x : Fin n → ℤ) : ℝ :=
  g (x + u.shift + u.vec) - g (x + u.shift)

/-- `∆_{eᵢ}`. -/
def Dir.posE {n : ℕ} (i : Fin n) : Dir n :=
  ⟨0, unitVec i⟩

/-- `∆_{−eᵢ}`. -/
def Dir.negE {n : ℕ} (i : Fin n) : Dir n :=
  ⟨0, -unitVec i⟩

/-- `∆_{d_k}` for `k ≥ 2` in the paper's 1-based numbering (`0 < k.val` here): shift `−e_{k−1}`,
vector `d_k = e_{k−1} − e_k`. -/
def Dir.dd {n : ℕ} (k : Fin n) (hk : 0 < k.val) : Dir n :=
  ⟨-unitVec (predIdx k hk), unitVec (predIdx k hk) - unitVec k⟩

/-- The four points at which the second difference `∆_u ∆_w g(x)` evaluates `g` all lie in `ℕⁿ`:
`x + s_u + s_w + c` for `c ∈ {0, v_u, v_w, v_u + v_w}`. -/
def EvalInQuad {n : ℕ} (u w : Dir n) (x : Fin n → ℤ) : Prop :=
  InQuad (x + u.shift + w.shift) ∧ InQuad (x + u.shift + w.shift + u.vec) ∧
    InQuad (x + u.shift + w.shift + w.vec) ∧ InQuad (x + u.shift + w.shift + u.vec + w.vec)

end ProactiveUpgrade


