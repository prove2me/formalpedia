-- Prove2me | Definitions.Def_LogGammaPolymer_Variance_Paths
-- name    : LogGammaPolymer_Variance_Paths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:29.676013+00:00
-- url     : https://prove2.me/theorems/2968b8e0-c18a-43c5-8904-25a00593341a
-- title:
--   Sec. 2–3, (2.1), (2.8), (3.1)–(3.2), (3.15)–(3.16), (5.1) — up-right paths, partition functions, exit points, quenched measure, recursion (3.2), down-right paths
-- statement:
--   This file fixes the deterministic objects of the directed polymer on the nonnegative quadrant $\mathbb Z_+^2$, for an arbitrary real weight configuration $Y=(Y_{i,j})_{(i,j)\in\mathbb Z_+^2}$. Following the paper, $\mathbb N=\{1,2,\dots\}$; the weights $U_{i,0}=Y_{i,0}$ and $V_{0,j}=Y_{0,j}$ ($i,j\in\mathbb N$) sit on the two axes (2.2).
--
--   1. **Up-right paths.** An up-right path from $(k,\ell)$ to $(m,n)$ is a sequence $x_0=(k,\ell),x_1,\dots,x_{m-k+n-\ell}=(m,n)$ whose steps $x_r-x_{r-1}$ are $e_1=(1,0)$ or $e_2=(0,1)$; it is encoded by its sequence of steps, with exactly $m-k$ east steps.
--   2. **Partition functions.** For $k\le m$, $\ell\le n$,
--   $$Z_{(k,\ell),(m,n)}=\sum_{x}\prod_{r=1}^{m-k+n-\ell}Y_{x_r},$$
--   the sum over up-right paths from $(k,\ell)$ to $(m,n)$; the weight of the starting point is excluded and $Z_{(k,\ell),(k,\ell)}=1$ (2.13). $Z_{m,n}=Z_{(0,0),(m,n)}$ is (2.1). The restricted partition function $Z_{m,n}(A)$ is the same sum over the paths of an event $A\subseteq\Pi_{m,n}$ (5.1), and $Z^{\square}_{(i,j),(k,\ell)}=Y_{i,j}Z_{(i,j),(k,\ell)}$ includes the starting weight (3.1).
--   3. **Quenched measure.** $Q_{m,n}(x)=Z_{m,n}^{-1}\prod_{k=1}^{m+n}Y_{x_k}$ (2.8), and $Q_{m,n}(A)=Z_{m,n}(A)/Z_{m,n}$.
--   4. **Exit points.** For a path from the origin, $\xi_x=\max\{k\ge0: x_i=(i,0)\text{ for }0\le i\le k\}$ and $\xi_y=\max\{k\ge0: x_j=(0,j)\text{ for }0\le j\le k\}$ (3.15)–(3.16).
--   5. **Recursion (3.2).** Starting from $U_{i,0}=Y_{i,0}$, $V_{0,j}=Y_{0,j}$, for $i,j\in\mathbb N$
--   $$U_{i,j}=Y_{i,j}\Bigl(1+\frac{U_{i,j-1}}{V_{i-1,j}}\Bigr),\qquad V_{i,j}=Y_{i,j}\Bigl(1+\frac{V_{i-1,j}}{U_{i,j-1}}\Bigr),\qquad X_{i-1,j-1}=\Bigl(\frac1{U_{i,j-1}}+\frac1{V_{i-1,j}}\Bigr)^{-1}.$$
--   6. **Down-right paths (Sec. 3.1).** A down-right path from $(0,a)$ to $(b,0)$ has steps $e_1$ or $-e_2$, positions $z_0,\dots,z_{a+b}$ and edges $f_k=\{z_{k-1},z_k\}$. The edge variable is $T_{f_k}=U_{z_k}$ for a horizontal and $V_{z_{k-1}}$ for a vertical edge, and the interior is $\mathcal I=\{(i,j):\exists m\in\mathbb N,\ (i+m,j+m)\in\{z_k\}\}$. Extended up the $y$-axis above $(0,a)$ and along the $x$-axis beyond $(b,0)$, this is a bi-infinite down-right path; the family $\{T_{f_k},X_z\}$ of Theorem 3.3 is collected over its edges and interior.
--
--   These are the objects in which every statement of the mission is written; they hold for every weight configuration, random or not.
--
--   **Formalization Note** Sites are `ℕ × ℕ`. `Steps a b` is the type of step sequences of length $a+b$ with exactly $a$ `true` steps (east for up-right paths, east for down-right paths, `false` = north resp. south). The unused values $U_{0,j}$, $V_{i,0}$ and the value at $(0,0)$ of the recursion are set to $0$; $X_{i,j}$ is indexed as in $X_{i-1,j-1}$ of (3.2) shifted by one, i.e. $X_{i,j}=(U_{i+1,j}^{-1}+V_{i,j+1}^{-1})^{-1}$. `Zgen Y k ℓ m n` is meaningful only for $k\le m$, $\ell\le n$.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Sec. 2, (2.1), (2.2), (2.8), (2.13), pp. 5, 7, 8; Sec. 3, (3.1), (3.2), p. 11, down-right paths p. 12, (3.15)–(3.16), p. 15; (5.1), p. 26

import Mathlib

namespace LogGammaPolymer.Variance

/-! Deterministic objects of Seppäläinen, arXiv:0911.2446v4, Sec. 2–3 and 5: up-right lattice paths,
the partition functions (2.1), (2.13), (3.1), (5.1), the exit points (3.15)–(3.16), the quenched
polymer measure (2.8), the recursion (3.2), and the down-right paths of Sec. 3.1 (p. 12).

Sites are `ℕ × ℕ` (the paper's `ℤ²₊`); the paper's `ℕ = {1, 2, …}`. A weight configuration is any
function `Y : ℕ × ℕ → ℝ`; `Y (i, 0)` is the paper's `U_{i,0}`, `Y (0, j)` its `V_{0,j}` (2.2). -/

/-- Step sequences of length `a + b` with exactly `a` steps equal to `true`. For an up-right path,
`true` is an east step `e₁ = (1, 0)` and `false` a north step `e₂ = (0, 1)`, so `Steps a b` is the set of
up-right paths with displacement `(a, b)`. -/
def Steps (a b : ℕ) : Type :=
  {s : Fin (a + b) → Bool // (Finset.univ.filter (fun i => s i = true)).card = a}

instance (a b : ℕ) : Fintype (Steps a b) := by
  unfold Steps; infer_instance

/-- Number of `true` steps among the first `r` steps of `s`. -/
def trueCount {L : ℕ} (s : Fin L → Bool) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin L => i.val < r ∧ s i = true)).card

/-- Number of `false` steps among the first `r` steps of `s`. -/
def falseCount {L : ℕ} (s : Fin L → Bool) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin L => i.val < r ∧ s i = false)).card

/-- Position `x_r` after `r` steps of the up-right path with steps `s` started at `start`
(`true` = east, `false` = north). -/
def upPos {L : ℕ} (start : ℕ × ℕ) (s : Fin L → Bool) (r : ℕ) : ℕ × ℕ :=
  (start.1 + trueCount s r, start.2 + falseCount s r)

/-- The weight `∏_{r=1}^{L} Y_{x_r}` of an up-right path started at `start`: the weight of the
starting point `x_0` is excluded (2.1), (2.13). -/
noncomputable def pathWeight (Y : ℕ × ℕ → ℝ) {L : ℕ} (start : ℕ × ℕ) (s : Fin L → Bool) : ℝ :=
  ∏ r ∈ Finset.Icc 1 L, Y (upPos start s r)

/-- The partition function `Z_{(k,ℓ),(m,n)}` of (2.13): the sum over up-right paths from `(k, ℓ)` to
`(m, n)` of the product of the weights of all sites except the starting point. Meaningful for
`k ≤ m`, `ℓ ≤ n`; `Z_{(k,ℓ),(k,ℓ)} = 1`. -/
noncomputable def Zgen (Y : ℕ × ℕ → ℝ) (k ℓ m n : ℕ) : ℝ :=
  ∑ s : Steps (m - k) (n - ℓ), pathWeight Y (k, ℓ) s.1

/-- The point-to-point partition function `Z_{m,n}` of (2.1): paths from `(0, 0)` to `(m, n)`,
origin excluded, `Z_{0,0} = 1`. -/
noncomputable def Z (Y : ℕ × ℕ → ℝ) (m n : ℕ) : ℝ :=
  ∑ s : Steps m n, pathWeight Y (0, 0) s.1

/-- The restricted partition function `Z_{m,n}(A)` of (5.1): the sum (2.1) over the paths of the
event `A ⊆ Π_{m,n}` only. -/
noncomputable def Zr (Y : ℕ × ℕ → ℝ) (m n : ℕ) (A : Steps m n → Prop) : ℝ := by
  classical
  exact ∑ s ∈ Finset.univ.filter A, pathWeight Y (0, 0) s.1

/-- `Z^□_{(i,j),(k,ℓ)} = Y_{i,j} Z_{(i,j),(k,ℓ)}` of (3.1): the partition function including the weight
of the starting point. -/
noncomputable def Zbox (Y : ℕ × ℕ → ℝ) (i j k ℓ : ℕ) : ℝ :=
  Y (i, j) * Zgen Y i j k ℓ

/-- The quenched polymer probability `Q^ω_{m,n}(x) = Z_{m,n}^{-1} ∏_{k=1}^{m+n} Y_{x_k}` of a single
path (2.8). -/
noncomputable def Qpt (Y : ℕ × ℕ → ℝ) (m n : ℕ) (s : Steps m n) : ℝ :=
  pathWeight Y (0, 0) s.1 / Z Y m n

/-- The quenched probability `Q^ω_{m,n}(A) = Z_{m,n}(A) / Z_{m,n}` of an event `A ⊆ Π_{m,n}`
(p. 26, after (5.1)). -/
noncomputable def Q (Y : ℕ × ℕ → ℝ) (m n : ℕ) (A : Steps m n → Prop) : ℝ :=
  Zr Y m n A / Z Y m n

/-- The exit point `ξ_x = max{k ≥ 0 : x_i = (i, 0) for 0 ≤ i ≤ k}` of (3.15) of an up-right path from
the origin: the number of initial east steps. -/
def ξx {L : ℕ} (s : Fin L → Bool) : ℕ :=
  Nat.findGreatest (fun k => ∀ i : Fin L, i.val < k → s i = true) L

/-- The exit point `ξ_y = max{k ≥ 0 : x_j = (0, j) for 0 ≤ j ≤ k}` of (3.16) of an up-right path from
the origin: the number of initial north steps. -/
def ξy {L : ℕ} (s : Fin L → Bool) : ℕ :=
  Nat.findGreatest (fun k => ∀ i : Fin L, i.val < k → s i = false) L

/-- The pair `(U_{i,j}, V_{i,j})` of the recursion (3.2), built from the weights `Y`:
`U_{i,0} = Y_{i,0}` and `V_{0,j} = Y_{0,j}` for `i, j ≥ 1`, and for `i, j ≥ 1`
`U_{i,j} = Y_{i,j}(1 + U_{i,j-1}/V_{i-1,j})`, `V_{i,j} = Y_{i,j}(1 + V_{i-1,j}/U_{i,j-1})`.
The components `U_{0,j}`, `V_{i,0}` and both components at `(0, 0)` are never used by (3.2) and are set
to `0`. -/
noncomputable def UV (Y : ℕ × ℕ → ℝ) : ℕ → ℕ → ℝ × ℝ
  | 0, 0 => (0, 0)
  | i + 1, 0 => (Y (i + 1, 0), 0)
  | 0, j + 1 => (0, Y (0, j + 1))
  | i + 1, j + 1 =>
      ((Y (i + 1, j + 1)) * (1 + (UV Y (i + 1) j).1 / (UV Y i (j + 1)).2),
       (Y (i + 1, j + 1)) * (1 + (UV Y i (j + 1)).2 / (UV Y (i + 1) j).1))
  termination_by i j => i + j

/-- `U_{i,j}` of (3.2) (used for `i ≥ 1`); by (3.4) it equals `Z_{i,j}/Z_{i-1,j}`. -/
noncomputable def U (Y : ℕ × ℕ → ℝ) (i j : ℕ) : ℝ := (UV Y i j).1

/-- `V_{i,j}` of (3.2) (used for `j ≥ 1`); by (3.4) it equals `Z_{i,j}/Z_{i,j-1}`. -/
noncomputable def V (Y : ℕ × ℕ → ℝ) (i j : ℕ) : ℝ := (UV Y i j).2

/-- `X_{i,j} = (1/U_{i+1,j} + 1/V_{i,j+1})^{-1}` of (3.2) (written there as `X_{i-1,j-1}`), for
`i, j ≥ 0`. -/
noncomputable def X (Y : ℕ × ℕ → ℝ) (i j : ℕ) : ℝ :=
  ((U Y (i + 1) j)⁻¹ + (V Y i (j + 1))⁻¹)⁻¹

/-- Position `z_r` of the down-right path from `(0, a)` with steps `s` (`true` = east `e₁`,
`false` = south `-e₂`); with exactly `a` south steps it ends at `(b, 0)` (Sec. 3.1, p. 12). -/
def downPos {L : ℕ} (a : ℕ) (s : Fin L → Bool) (r : ℕ) : ℕ × ℕ :=
  (trueCount s r, a - falseCount s r)

/-- The (lower left) interior `I = {(i, j) : ∃ m ∈ ℕ, (i + m, j + m) ∈ {z_k}}` of the down-right path
from `(0, a)` with steps `s` (p. 12; `m ≥ 1`). -/
def drInterior {L : ℕ} (a : ℕ) (s : Fin L → Bool) : Set (ℕ × ℕ) :=
  {p | ∃ t : ℕ, 1 ≤ t ∧ ∃ r : ℕ, r ≤ L ∧ (p.1 + t, p.2 + t) = downPos a s r}

/-- The edge variable `T_{f_k}` of the `k`-th edge `f_k = {z_{k-1}, z_k}` (`k = r + 1`) of the down-right
path: `U_{z_k}` if the edge is horizontal, `V_{z_{k-1}}` if it is vertical (p. 12). -/
noncomputable def edgeVar (Y : ℕ × ℕ → ℝ) {L : ℕ} (a : ℕ) (s : Fin L → Bool) (r : Fin L) : ℝ :=
  if s r = true then U Y (downPos a s (r.val + 1)).1 (downPos a s (r.val + 1)).2
  else V Y (downPos a s r.val).1 (downPos a s r.val).2

/-- Index set of Theorem 3.3 for the bi-infinite down-right path that runs down the `y`-axis to
`(0, a)`, follows the steps `s` (exactly `b` east and `a` south steps) to `(b, 0)`, and then runs along
the `x`-axis: the `b + a` edges of the finite portion, the interior points, the horizontal axis edges
`{(i-1,0),(i,0)}` with `i > b`, and the vertical axis edges `{(0,j-1),(0,j)}` with `j > a`. -/
abbrev BurkeIndex (a b : ℕ) (s : Steps b a) : Type :=
  Fin (b + a) ⊕ (drInterior a s.1) ⊕ {i : ℕ // b < i} ⊕ {j : ℕ // a < j}

/-- The variables `{T_{f_k}, X_z : k ∈ ℤ, z ∈ I}` of Theorem 3.3 for the path of `BurkeIndex`. -/
noncomputable def burkeFamily (Y : ℕ × ℕ → ℝ) (a b : ℕ) (s : Steps b a) : BurkeIndex a b s → ℝ
  | Sum.inl r => edgeVar Y a s.1 r
  | Sum.inr (Sum.inl p) => X Y p.1.1 p.1.2
  | Sum.inr (Sum.inr (Sum.inl i)) => U Y i.1 0
  | Sum.inr (Sum.inr (Sum.inr j)) => V Y 0 j.1

end LogGammaPolymer.Variance


