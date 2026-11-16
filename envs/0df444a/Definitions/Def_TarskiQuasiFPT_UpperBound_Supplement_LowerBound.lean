-- Prove2me | Definitions.Def_TarskiQuasiFPT_UpperBound_Supplement_LowerBound
-- name    : TarskiQuasiFPT_UpperBound_Supplement_LowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:28:56.503184+00:00
-- url     : https://prove2.me/theorems/b2211530-5edc-45e1-af9f-737857152b8c
-- title:
--   Hard distributions for the Tarski lower bound: success probability, $G_H$, the sign function, boxes and $\mathrm{Amp}_m(\mathcal H)$
-- statement:
--   This file fixes the objects of §3 of the paper. Points of $[n]^k=\{1,\dots,n\}^k$ are ordered coordinatewise. A deterministic query algorithm is a decision tree: each query at $x$ returns the whole vector $F(x)$.
--
--   1. **Unique fixed point.** $F$ has a unique fixed point if there is exactly one $x$ with $F(x)=x$.
--   2. **Depth and success probability.** A tree has depth at most $q$ (a real number) if on every oracle it makes at most $q$ queries. For a distribution $\mathcal D$ over maps $F$ and a deterministic tree $T$, the success probability is
--   $$\Pr_{F\sim\mathcal D}\big[F(T(F))=T(F)\big],$$
--   the probability that the tree's output is a fixed point of $F$ ("the tree finds the fixed point").
--   3. **Complement and $G_H$.** For $z\in[n]^k$ let $\bar z=(n+1)\mathbf 1-z$. For $H:[n]^k\to[n]^k$ define $G_H:[n]^{2k}\to[n]^{2k}$ by
--   $$G_H(x,u)=\big(H(x),\ \overline{H(\bar u)}\big)\qquad\text{(eq. (5))}.$$
--   4. **Anti-chain and sign function.** $C=\{(z,\bar z):z\in[n]^k\}$, $D_C=\{w:\exists w'\in C,\ w\preceq w'\}$, $U_C=[n]^{2k}\setminus D_C$. For $c\in\{0,1\}$, $S_{H,c}(X)=c$ if $X=(P_H,\overline{P_H})$, $0$ if $X\in D_C\setminus\{(P_H,\overline{P_H})\}$, and $1$ if $X\in U_C$ (eq. (6)), where $P_H$ is the unique fixed point of $H$.
--   5. **Boxes.** For $t\in[m]$ the box $B_t\subseteq[mn]^{2k}$ has all coordinates in $((t-1)n,tn]$. The projection is $[P_t(X)]_i=\min\{tn,\max\{(t-1)n+1,X_i\}\}$, and $X\mapsto P_t(X)-(t-1)n\mathbf 1$ maps into $[n]^{2k}$ (eq. (7)).
--   6. **Amplified function.** Given $H_1,\dots,H_m$ and a hidden $t^*\in[m]$, put $c_t=\mathbf 1(t\le t^*)$ for $t\in[m]$ and $c_{m+1}=0$. For $W=(a,b,X,Y)\in[m]^2\times[mn]^{4k}$:
--   $$\begin{aligned}F_X(W)&=(a-1)n\mathbf 1+G_{H_a}(P_a(X)-(a-1)n\mathbf 1),\\ F_Y(W)&=(b-1)n\mathbf 1+G_{H_b}(P_b(Y)-(b-1)n\mathbf 1),\\ F_b(W)&=\min\{m,\ a+S_{H_a,c_{a+1}}(P_a(X)-(a-1)n\mathbf 1)\},\\ F_a(W)&=\max\{1,\ b-1+S_{H_b,c_b}(P_b(Y)-(b-1)n\mathbf 1)\},\end{aligned}$$
--   and $F(W)=(F_a(W),F_b(W),F_X(W),F_Y(W))$.
--   7. **$\mathrm{Amp}_m(\mathcal H)$.** Draw $H_1,\dots,H_m$ i.i.d. from $\mathcal H$ and, independently, $t^*$ uniformly from $[m]$. $\mathrm{Amp}_m(\mathcal H)$ is the law of the resulting $F$ (eq. (4)).
--
--   These objects carry the paper's inductive lower-bound construction: Lemmas 14–17 are statements about them, and Theorem 6 asserts the existence of the resulting hard distributions.
--
--   **Formalization Note** `[n]^k` reuses the published `Point n k = Fin k → Fin n`, so a value $a$ stands for $a+1$. The space $[N]^{2k}$ is a pair `Point N k × Point N k` with the product order. $[m]^2\times[mn]^{4k}$ is `Fin m × Fin m × Pair (m*n) k × Pair (m*n) k`, also with the product order. The complement is `Fin.rev` in each coordinate. Distributions are `PMF`s, and the i.i.d. sample is built by recursion on $m$. $\mathrm{Amp}_m$ requires $m\ge1$ (`NeZero m`), because $t^*$ is uniform on $[m]$.
--
--   In 0-based form, $F_b=\min(m-1,a_0+S)$ and $F_a=b_0+S-1$. The truncated natural-number subtraction is exactly the clamp $\max\{1,\cdot\}$, and $S\le1$ keeps $F_a$ in range. The translated projection is, coordinatewise, $v\mapsto\min(v-t_0n,\,n-1)$; truncated subtraction implements the lower clamp.
--
--   The special point $(P_H,\overline{P_H})$ of $S_{H,c}$ is written as "$X_1$ is a fixed point of $H$ and $X_2=\overline{X_1}$". This is the same point whenever $H$ has a unique fixed point, which is the §3.2 setting. The tree "finds" the fixed point when its output is a fixed point.
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, §3 (Theorem 6 setting, eqs. (4)–(7), §3.2.4 steps 1–6, §3.4 Lemma 17 setting), PDF pp. 15–23 (printed pp. 14–22)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid

set_option autoImplicit false

namespace TarskiQuasiFPT.UpperBound.Supplement

/-! # Hard distributions for the Tarski lower bound (§3)

Chen, Gao, Li, Rubinstein, Yannakakis, *Tarski Fixed Points in Quasi-FPT Queries*,
STOC 2027 submission #403, §3 (PDF pp. 14–25).

Grid conventions are those of the published base layer: `Point n k = Fin k → Fin n` with the
pointwise order; the value `a : Fin n` stands for `a + 1 ∈ [n] = {1,…,n}`. A query returns the
whole vector `F(x)`; a deterministic algorithm is a `QAlgorithms.DecisionTree`. -/

open QAlgorithms

/-! ## Unique fixed points, depth, success probability -/

/-- `F` has a unique fixed point. -/
def HasUniqueFixedPoint {α : Type*} (F : α → α) : Prop :=
  ∃! x, F x = x

/-- A decision tree has **depth at most `q`** (a real number): on every oracle `g` the path
followed makes at most `q` queries. -/
def DepthLE {α : Type*} (T : DecisionTree α α α) (q : ℝ) : Prop :=
  ∀ g : α → α, (T.queries g : ℝ) ≤ q

/-- The probability, over `F ∼ D`, that the deterministic decision tree `T` **finds the fixed
point** of `F`, i.e. that its output `T.eval F` is a fixed point of `F`. -/
noncomputable def succProb {α : Type*} (D : PMF (α → α)) (T : DecisionTree α α α) : ℝ :=
  (D.toOuterMeasure {F | F (T.eval F) = T.eval F}).toReal

/-! ## The inner construction on `[n]^{2k}` (§3.2.1–3.2.2)

`[n]^{2k}` is encoded as `Point n k × Point n k` with the product (coordinatewise) order:
the pair `(x, u)` lists the first `k` and the last `k` coordinates. -/

/-- A point of `[N]^{2k}`, as a pair of points of `[N]^k`, ordered coordinatewise. -/
abbrev Pair (N k : ℕ) := Point N k × Point N k

variable {n k : ℕ}

/-- The complement `z̄ = (n+1)·1 − z` of `z ∈ [n]^k`; on the 0-based encoding it is `Fin.rev`
in every coordinate. -/
def complement (z : Point n k) : Point n k := fun i => Fin.rev (z i)

/-- Equation (5): `G_H(x, u) = (H(x), \overline{H(\overline{u})})`. -/
def G (H : Point n k → Point n k) (X : Pair n k) : Pair n k :=
  (H X.1, complement (H (complement X.2)))

/-- The anti-chain `C = {(z, z̄) : z ∈ [n]^k}`. -/
def antichainC : Set (Pair n k) := {X | X.2 = complement X.1}

/-- `D_C = {w ∈ [n]^{2k} : ∃ w′ ∈ C, w ⪯ w′}`; its complement is `U_C`. -/
def downC : Set (Pair n k) := {X | ∃ Y ∈ (antichainC : Set (Pair n k)), X ≤ Y}

open Classical in
/-- Equation (6), the sign function `S_{H,c} : [n]^{2k} → {0,1}` with hidden bit `c`:
`S_{H,c}(X) = c` if `X = (P_H, \overline{P_H})`, `0` if `X ∈ D_C \ {(P_H, \overline{P_H})}`,
`1` if `X ∈ U_C`. The point `(P_H, \overline{P_H})` is written as "`X.1` is a fixed point of `H`
and `X.2 = \overline{X.1}`", which is exactly `X = (P_H, \overline{P_H})` when `P_H` is the unique
fixed point of `H` (the §3.2 setting). -/
noncomputable def signFn (H : Point n k → Point n k) (c : Bool) (X : Pair n k) : ℕ :=
  if H X.1 = X.1 ∧ X.2 = complement X.1 then c.toNat
  else if X ∈ (downC : Set (Pair n k)) then 0 else 1

theorem signFn_le_one (H : Point n k → Point n k) (c : Bool) (X : Pair n k) :
    signFn H c X ≤ 1 := by
  unfold signFn
  split_ifs <;> simp [Bool.toNat_le]

/-! ## Boxes and projections (eq. (7) and §3.2.4)

For `t ∈ [m]` (0-based `t₀ = t − 1 : Fin m`) the box `B_t ⊆ [mn]^{2k}` consists of the points
whose 1-based coordinates lie in `((t−1)n, tn]`. The map `X ↦ P_t(X) − (t−1)n·1` (project onto
`B_t`, then translate to `[n]^{2k}`) is, coordinatewise and 0-based,
`v ↦ min (v − t₀ n) (n − 1)` (truncated subtraction is the `max{(t−1)n+1, ·}` clamp). -/

/-- One coordinate of `P_t(X) − (t−1)n·1`, 0-based: clamp `v − t₀ n` to `{0,…,n−1}`. -/
def localCoord {m : ℕ} (t : Fin m) (v : Fin (m * n)) : Fin n :=
  ⟨min (v.val - t.val * n) (n - 1), by
    have hv := v.isLt
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hv
    omega⟩

/-- One coordinate of `(t−1)n·1 + w`, 0-based: `w ↦ t₀ n + w`, landing in the box `B_t`. -/
def globalCoord {m : ℕ} (t : Fin m) (w : Fin n) : Fin (m * n) :=
  ⟨t.val * n + w.val, by
    have ht := t.isLt
    have hw := w.isLt
    calc t.val * n + w.val < t.val * n + n := by omega
      _ = (t.val + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right n ht⟩

/-- `X ↦ P_t(X) − (t−1)n·1 : [mn]^{2k} → [n]^{2k}`. -/
def toLocal {m : ℕ} (t : Fin m) (X : Pair (m * n) k) : Pair n k :=
  (fun i => localCoord t (X.1 i), fun i => localCoord t (X.2 i))

/-- `Z ↦ (t−1)n·1 + Z : [n]^{2k} → B_t ⊆ [mn]^{2k}`. -/
def toGlobal {m : ℕ} (t : Fin m) (Z : Pair n k) : Pair (m * n) k :=
  (fun i => globalCoord t (Z.1 i), fun i => globalCoord t (Z.2 i))

/-! ## The amplified function and `Amp_m(H)` (§3.2.4) -/

/-- The domain `[m]^2 × [mn]^{4k}` of the amplified functions, as `(a, b, X, Y)` with
`a, b ∈ [m]` (0-based `Fin m`) and `X, Y ∈ [mn]^{2k}`, ordered coordinatewise
(the product order). -/
abbrev AmpPoint (m n k : ℕ) := Fin m × Fin m × Pair (m * n) k × Pair (m * n) k

/-- The signs `c_t = 1(t ≤ t*)` for 1-based `t ∈ [m+1]` (so `c_{m+1} = 0`), where the hidden
number is the 1-based `t* = tstar + 1`. -/
def cSign {m : ℕ} (tstar : Fin m) (t : ℕ) : Bool :=
  decide (t ≤ tstar.val + 1)

/-- The amplified function `F` built from the sampled `H_1, …, H_m` (`Hs : Fin m → …`, 0-based)
and the hidden number `t*` (`tstar`, 0-based), §3.2.4 steps 3–6: for `W = (a, b, X, Y)`,
* `F_X(W) = (a−1)n·1 + G_{H_a}(P_a(X) − (a−1)n·1)`,
* `F_Y(W) = (b−1)n·1 + G_{H_b}(P_b(Y) − (b−1)n·1)`,
* `F_b(W) = min{m, a + S_{H_a, c_{a+1}}(P_a(X) − (a−1)n·1)}`,
* `F_a(W) = max{1, b − 1 + S_{H_b, c_b}(P_b(Y) − (b−1)n·1)}`,
and `F(W) = (F_a(W), F_b(W), F_X(W), F_Y(W))`. In the 0-based encoding `a₀ = a − 1`:
`F_b = min (m−1) (a₀ + S)` and `F_a = b₀ + S − 1` with truncated subtraction (the clamp
`max{1, ·}`); the 1-based index of `c_{a+1}` is `a₀ + 2`, that of `c_b` is `b₀ + 1`. -/
noncomputable def ampFun {m : ℕ} (Hs : Fin m → Point n k → Point n k) (tstar : Fin m)
    (W : AmpPoint m n k) : AmpPoint m n k :=
  let a := W.1
  let b := W.2.1
  let X := W.2.2.1
  let Y := W.2.2.2
  let sX := signFn (Hs a) (cSign tstar (a.val + 2)) (toLocal a X)
  let sY := signFn (Hs b) (cSign tstar (b.val + 1)) (toLocal b Y)
  (⟨b.val + sY - 1, by
      have := signFn_le_one (Hs b) (cSign tstar (b.val + 1)) (toLocal b Y)
      have := b.isLt
      omega⟩,
   ⟨min (m - 1) (a.val + sX), by
      have := a.isLt
      omega⟩,
   toGlobal a (G (Hs a) (toLocal a X)),
   toGlobal b (G (Hs b) (toLocal b Y)))

/-- `m` i.i.d. samples from `D`, as a distribution on `Fin m → β`. -/
noncomputable def iid {β : Type*} (D : PMF β) : (m : ℕ) → PMF (Fin m → β)
  | 0 => PMF.pure Fin.elim0
  | m + 1 => D.bind fun b => (iid D m).map fun v => Fin.cons b v

/-- `Amp_m(H)` (eq. (4)): sample `H_1, …, H_m` i.i.d. from `D` and, independently, `t*` uniform
on `[m]`; output the amplified function `ampFun (H_1, …, H_m) t*`. -/
noncomputable def ampDist (m : ℕ) [NeZero m] (D : PMF (Point n k → Point n k)) :
    PMF (AmpPoint m n k → AmpPoint m n k) :=
  (iid D m).bind fun Hs => (PMF.uniformOfFintype (Fin m)).map fun tstar => ampFun Hs tstar

end TarskiQuasiFPT.UpperBound.Supplement


