-- Prove2me | Definitions.Def_FasterWCTFPTAS_Main_Geometry
-- name    : FasterWCTFPTAS_Main_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:05:55.744196+00:00
-- url     : https://prove2.me/theorems/2e5008d0-7986-4b23-952b-c8536d6d6680
-- title:
--   Relaxed representative sets, directional width and ε-kernels
-- statement:
--   Fix a dimension $m\ge 2$. A point of $\mathbb R^m$ is written as a pair $(a,b)$ with $a\in\mathbb R^{m-1}$ and $b\in\mathbb R$; the inner product is $\langle (a,b),(x,c)\rangle=\langle a,x\rangle+bc$ and $\|v\|=\sqrt{\langle v,v\rangle}$.
--
--   **Definition 3.1 (Relaxed representative set).** Let $\delta\in(0,1)$, $A,B,X\ge 0$ and $D\subseteq[0,A]^{m-1}\times[0,B]$. A relaxed $\delta$-representative set of $D$ for $(A,B,X)$ is a subset $\widetilde D\subseteq D$ such that for every $x\in[-X,X]^{m-1}$ and every $(a,b)\in D$ there exists $(\tilde a,\tilde b)\in\widetilde D$ such that
--
--   $$
--   \langle\tilde a,x\rangle+\tilde b\le\langle a,x\rangle+b+\delta(A\cdot X+B).
--   $$
--
--   **Directional width and $\varepsilon$-kernel (§3.2).** For a nonzero $v\in\mathbb R^m$ and a set $S$ of points,
--
--   $$
--   \mathrm{width}_v(S)=\max_{s\in S}\Big\langle s,\frac{v}{\|v\|}\Big\rangle-\min_{s\in S}\Big\langle s,\frac{v}{\|v\|}\Big\rangle ,
--   $$
--
--   and a subset $Q\subseteq S$ is an $\varepsilon$-kernel of $S$ if $\mathrm{width}_v(Q)\ge(1-\varepsilon)\,\mathrm{width}_v(S)$ for every $v\in\mathbb R^m\setminus\{0\}$.
--
--   These are the geometric notions of §3. Relaxed representative sets are the lower-envelope relaxation of the scheduling notion of Definition 4.2, and $\varepsilon$-kernels are the computational-geometry objects through which they are computed.
--
--   **Formalization Note** The parameter ranges of Definition 3.1 ($\delta\in(0,1)$, $A,B,X\ge0$, the box condition on $D$) are hypotheses of the theorems that use it, not part of the predicate. The width is computed with `sSup`/`sInf`, which equal the maximum and minimum on nonempty finite sets; the kernel predicate additionally requires $Q$ to be nonempty whenever $S$ is, since the width of the empty set is undefined in the source (and `sSup ∅ = sInf ∅ = 0` in Lean would otherwise make $\emptyset$ an $\varepsilon$-kernel of any singleton).
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 7 (PDF p. 8), Definition 3.1; p. 10 (PDF p. 11), §3.2 ε-kernel

import Mathlib

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-!
# Relaxed representative sets and ε-kernels (§3, pp. 7 and 10, PDF 8 and 11)

Throughout §3 a dimension `m ≥ 2` is fixed. A point of `ℝ^m` is written as a pair `(a, b)` with
`a ∈ ℝ^{m−1}` and `b ∈ ℝ`, exactly as the paper interprets a pair `(a, b) ∈ D` as a point of `ℝ^m`
(p. 10). The same representation is used in §4 for the DP pairs `(π, θ)`.
-/

/-- A point of `ℝ^m`, written `(a, b)` with `a ∈ ℝ^{m−1}`, `b ∈ ℝ`. -/
abbrev Pt (m : ℕ) := (Fin (m - 1) → ℝ) × ℝ

/-- The standard inner product on `ℝ^{m−1}`: `⟨a, x⟩ = Σ_k a_k x_k`. -/
def dotm {m : ℕ} (a x : Fin (m - 1) → ℝ) : ℝ := ∑ k, a k * x k

/-- The standard inner product on `ℝ^m = ℝ^{m−1} × ℝ`: `⟨(a, b), (x, c)⟩ = ⟨a, x⟩ + b c`. -/
def ip {m : ℕ} (s v : Pt m) : ℝ := dotm s.1 v.1 + s.2 * v.2

/-- The Euclidean length `‖v‖ = √⟨v, v⟩`. -/
noncomputable def norm2 {m : ℕ} (v : Pt m) : ℝ := Real.sqrt (ip v v)

/-- The box `[0, A]^{m−1} × [0, B]`. -/
def InBox {m : ℕ} (A B : ℝ) (s : Pt m) : Prop :=
  (∀ k, 0 ≤ s.1 k ∧ s.1 k ≤ A) ∧ 0 ≤ s.2 ∧ s.2 ≤ B

/-- **Definition 3.1** (relaxed representative set), p. 7 (PDF 8). `Dt` is a relaxed
`δ`-representative set of `D` for `(A, B, X)`: `Dt ⊆ D`, and for every `x ∈ [−X, X]^{m−1}` and every
`(a, b) ∈ D` there is `(ã, b̃) ∈ Dt` with `⟨ã, x⟩ + b̃ ≤ ⟨a, x⟩ + b + δ(A·X + B)`.
The parameter ranges `δ ∈ (0,1)`, `A, B, X ≥ 0` and `D ⊆ [0, A]^{m−1} × [0, B]` of the paper are
hypotheses of the theorems that use the notion. -/
def IsRelaxedRep {m : ℕ} (δ A B X : ℝ) (Dt D : Set (Pt m)) : Prop :=
  Dt ⊆ D ∧
    ∀ x : Fin (m - 1) → ℝ, (∀ k, |x k| ≤ X) →
      ∀ a ∈ D, ∃ e ∈ Dt, dotm e.1 x + e.2 ≤ dotm a.1 x + a.2 + δ * (A * X + B)

/-- The directional width `width_v(S) = max_{s∈S} ⟨s, v/‖v‖⟩ − min_{s∈S} ⟨s, v/‖v‖⟩` (§3.2,
p. 10, PDF 11). For a nonempty finite `S` the supremum and infimum are the maximum and minimum.
(On the empty set the value is `0`; `IsKernel` excludes that case explicitly.) -/
noncomputable def width {m : ℕ} (v : Pt m) (S : Set (Pt m)) : ℝ :=
  sSup ((fun s => ip s v / norm2 v) '' S) - sInf ((fun s => ip s v / norm2 v) '' S)

/-- **ε-kernel** (§3.2, p. 10, PDF 11). `Q ⊆ S` is an `ε`-kernel of `S` if
`width_v(Q) ≥ (1 − ε) width_v(S)` for every nonzero `v ∈ ℝ^m`. The width is defined through a
maximum and a minimum, so `Q` is required to be nonempty whenever `S` is (otherwise the empty set
would be an ε-kernel of every singleton). -/
def IsKernel {m : ℕ} (ε : ℝ) (Q S : Set (Pt m)) : Prop :=
  Q ⊆ S ∧ (S.Nonempty → Q.Nonempty) ∧
    ∀ v : Pt m, v ≠ 0 → (1 - ε) * width v S ≤ width v Q

end FasterWCTFPTAS.Main


