-- Prove2me | Definitions.Def_ChenWhitt93_Reflection_ReflectionMap
-- name    : ChenWhitt93_Reflection_ReflectionMap
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:13:56.900209+00:00
-- url     : https://prove2.me/theorems/42fbd774-5071-4a4c-9e1c-2177651c7aee
-- title:
--   Section 2, (2.1)–(2.4) — the oblique reflection map associated with $Q$ and the operator $\pi_x$
-- statement:
--   Let $Q$ be an $n\times n$ matrix, $T \ge 0$ and $x \in D([0,T],\mathbb R^n)$. Following Harrison and Reiman, a pair $(y,z)$ of paths is the **reflection** of $x$ associated with $Q$, written $(y,z) = (\psi(x),\phi(x))$, when $y \in D([0,T],\mathbb R^n)$ and
--
--   $$
--   z = x + (I - Q)\,y \ge 0, \tag{2.1}
--   $$
--
--   $$
--   y_j \text{ is nondecreasing with } y_j(0) = 0, \qquad 1 \le j \le n, \tag{2.2}
--   $$
--
--   $$
--   \int_0^T z_j(t)\,dy_j(t) = 0, \qquad 1 \le j \le n. \tag{2.3}
--   $$
--
--   Condition (2.3) means that $y_j$ increases only at times $t$ when $z_j(t) = 0$.
--
--   The file also defines the operator of (2.4),
--   $$
--   \pi_x(y) = (Qy - x)^{\uparrow} \vee 0, \qquad f^{\uparrow}(t) = \sup_{0 \le s \le t} f(s),
--   $$
--   applied coordinatewise, and its iterates $\pi_x^k$.
--
--   The reflection map turns a netput process into the pair (cumulative idleness, queue content) of an open queueing network; every result of the mission is a statement about it.
--
--   **Formalization Note** Condition (2.3) is encoded in the paper's own gloss: for each $j$ there is a Stieltjes function $F$ that agrees with $y_j$ on $[0,T]$ and vanishes on $(-\infty,0)$, and the Lebesgue–Stieltjes measure $dF$ gives zero mass to $\{t \in [0,T] : z_j(t) > 0\}$. Since $z \ge 0$, this is equivalent to $\int_{[0,T]} z_j\,dy_j = 0$ for measurable $z$, and it allows $y_j$ to jump at a time where $z_j = 0$. The page prints the index range of (2.2)–(2.3) as $1 \le j \le J$; the dimension is $n$. Values of the paths outside $[0,T]$ play no role.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 337, Section 2, 'The reflection map', Eqs. (2.1)–(2.4)

import Mathlib
import Definitions.Def_ChenWhitt93_Reflection_Basic

open Filter Topology Matrix

namespace ChenWhitt93.Reflection

/-- Condition (2.1) on `[0,T]`: `z = x + (I − Q) y ≥ 0`. -/
def Cond21 {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (T : ℝ)
    (x y z : ℝ → Fin n → ℝ) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) T, z t = x t + (1 - Q) *ᵥ y t ∧ 0 ≤ z t

/-- Condition (2.2) on `[0,T]`: each `yⱼ` is nondecreasing with `yⱼ(0) = 0`. -/
def Cond22 {n : ℕ} (T : ℝ) (y : ℝ → Fin n → ℝ) : Prop :=
  (∀ j, MonotoneOn (fun t => y t j) (Set.Icc (0 : ℝ) T)) ∧ y 0 = 0

/-- Condition (2.3), `∫₀ᵀ zⱼ(t) dyⱼ(t) = 0`, in the paper's gloss "`yⱼ` increases only
at times `t` when `zⱼ(t) = 0`": for each `j` there is a Stieltjes function `F` agreeing
with `yⱼ` on `[0,T]` and vanishing on `(-∞,0)` (so `dyⱼ` has no atom at `0`), and the
Lebesgue–Stieltjes measure `dF` of `{t ∈ [0,T] : zⱼ(t) > 0}` is zero. For `z ≥ 0` and
measurable `z` this is equivalent to `∫_{[0,T]} zⱼ dyⱼ = 0`. -/
def Cond23 {n : ℕ} (T : ℝ) (y z : ℝ → Fin n → ℝ) : Prop :=
  ∀ j, ∃ F : StieltjesFunction ℝ,
    (∀ t ∈ Set.Icc (0 : ℝ) T, F t = y t j) ∧ (∀ t < 0, F t = 0) ∧
    F.measure {t | t ∈ Set.Icc (0 : ℝ) T ∧ 0 < z t j} = 0

/-- `(y, z)` is the reflection of `x` associated with `Q` on `[0,T]`, i.e.
`y = ψ(x)`, `z = φ(x)`: `y ∈ D([0,T], ℝⁿ)` and (2.1)–(2.3) hold. -/
def IsReflection {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (T : ℝ)
    (x y z : ℝ → Fin n → ℝ) : Prop :=
  IsCadlagOn T y ∧ Cond21 Q T x y z ∧ Cond22 T y ∧ Cond23 T y z

/-- Running supremum from time `0`: `f↑(t) = sup_{0 ≤ s ≤ t} f(s)`. -/
noncomputable def runSup (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ) t, f s

/-- The operator (2.4): `πₓ(y) = (Qy − x)↑ ∨ 0`, coordinatewise. -/
noncomputable def piMap {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (x y : ℝ → Fin n → ℝ) : ℝ → Fin n → ℝ :=
  fun t j => max (runSup (fun s => (Q *ᵥ y s) j - x s j) t) 0

end ChenWhitt93.Reflection


