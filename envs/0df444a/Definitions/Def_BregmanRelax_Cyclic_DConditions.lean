-- Prove2me | Definitions.Def_BregmanRelax_Cyclic_DConditions
-- name    : BregmanRelax_Cyclic_DConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T20:19:56.60573+00:00
-- url     : https://prove2.me/theorems/023e5cd5-04f5-4e0b-85f9-ef42e160190b
-- title:
--   §1 — conditions I–VI on $D$, the $D$-projection, the relaxation sequence and the cyclic control
-- statement:
--   This definition file sets up the abstract framework of §1 of Bregman (1967).
--
--   Let $X$ be a real linear topological space, let $\{A_i\}_{i\in I}$ be a family of subsets of $X$ indexed by a set $I$, let $S\subset X$, and let $D(x,y)$ be a real function, meaningful for $x,y\in S$. For each $i\in I$ let $P_i : X\to X$ be a map; $P_i y$ is called the **$D$-projection** of $y$ onto $A_i$. The structure $\mathrm{DConditions}(A,S,D,P)$ collects the following requirements.
--
--   1. Every $A_i$ is closed and convex, and $S$ is convex.
--   2. **Condition I.** $D(x,y)\ge 0$ for $x,y\in S$, and $D(x,y)=0$ if and only if $x=y$.
--   3. **Condition II.** For every $i\in I$ and $y\in S$, the point $P_i y$ lies in $A_i\cap S$ and minimizes $D(\cdot,y)$ there:
--   $$D(P_i y, y)=\min_{z\in A_i\cap S} D(z,y).$$
--   4. **Condition III.** For every $i\in I$ and $y\in S$, the function $G(z)=D(z,y)-D(z,P_iy)$ is convex on $A_i\cap S$.
--   5. **Condition IV.** For all $y,w\in S$,
--   $$\lim_{t\to 0^+}\frac{D\bigl(y+t(w-y),\,y\bigr)}{t}=0 .$$
--   6. **Condition VI.** If $x^n, y^n\in S$, $D(x^n,y^n)\to 0$, $y^n\to y^*$ with $y^*\in\bar S$, and the set of elements of $\{x^n\}$ is contained in a (sequentially) compact set, then $x^n\to y^*$.
--
--   The file also defines:
--
--   - **Condition V** for a set $Z$ of points (in §1, $Z=R\cap S$ with $R=\bigcap_{i\in I}A_i$): for every $z\in Z$ and every real $L$, the set $\{x\in S \mid D(z,x)\le L\}$ is sequentially compact.
--   - **Relaxation sequence** with control $(i_n)_{n\ge 0}$: a sequence with $x^0\in S$ and $x^{n+1}=P_{i_n}x^n$ for all $n$.
--   - **Cyclic control** for $I=\{0,\dots,m-1\}$, $m\ge 1$: $i_n = n \bmod m$.
--
--   These are the hypotheses and the iterative process of every result of §1: Lemmas 1–2, Theorems 1–2 and Note 1.
--
--   **Formalization Note** The following choices make the paper's hypotheses explicit.
--   (a) The paper writes $P_iy$ for "a point" given by condition II; here $P$ is a fixed map, and condition III is stated for that map.
--   (b) Condition II as printed reads "$D(x,y)=\min_{z\in A_i\cap S}D(z,x)$" and "$i\in T$"; the intended reading, used in the proof of Lemma 1, is $\min_{z\in A_i\cap S} D(z,y)$ and $i\in I$.
--   (c) The paper's condition IV asks for a two-sided limit $\lim_{t\to 0} D(y+tz,y)/t=0$ for every $z\in X$. Only the right-hand limit in directions $w-y$ with $w\in S$ is assumed here, which is what the proofs use. The paper's IV implies this form, so statements made under it are at least as strong as the paper's.
--   (d) "Compact" in V and VI is sequential compactness, since the proofs extract convergent subsequences. "The set of elements of $\{x^n\}$ is compact" is read as "$\{x^n\}$ lies in a sequentially compact set".
--   (e) In VI the limit $y^*$ may lie in $\bar S$, as printed.
--   (f) The index set is a type $\iota$, and the control is an arbitrary sequence $\mathbb N\to\iota$ ("we select in some way the index"). The paper's 1-based cyclic index $i_n=(n \bmod m)+1$ becomes the 0-based $n\bmod m$.
--   (g) $D$ is a total function $X\times X\to\mathbb R$; every condition constrains it on $S\times S$ only.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), pp. 200–201, §1, conditions I–VI and the iterative process (1)–(2); p. 203, Theorem 1 (cyclic control)

import Mathlib

namespace BregmanRelax.Cyclic

/-- Conditions I–IV and VI of §1 (Bregman 1967, pp. 200–201) on the family of sets `A`, the convex
set `S`, the function `D` (meaningful on `S × S`) and the D-projection map `P` of condition II.
`P i y` is the D-projection of `y` onto `A i`. Condition IV is stated in the form the proofs use
(the right derivative at `y` in the direction of a point `w ∈ S` vanishes); "compact" in VI is
sequential compactness. -/
structure DConditions {X : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] {ι : Type*}
    (A : ι → Set X) (S : Set X) (D : X → X → ℝ) (P : ι → X → X) : Prop where
  /-- every `A i` is closed -/
  isClosed : ∀ i, IsClosed (A i)
  /-- every `A i` is convex -/
  convex : ∀ i, Convex ℝ (A i)
  /-- `S` is convex -/
  convex_S : Convex ℝ S
  /-- condition I: `D ≥ 0` on `S × S` -/
  nonneg : ∀ x ∈ S, ∀ y ∈ S, 0 ≤ D x y
  /-- condition I: `D x y = 0 ↔ x = y` on `S × S` -/
  eq_zero_iff : ∀ x ∈ S, ∀ y ∈ S, D x y = 0 ↔ x = y
  /-- condition II: `P i y ∈ A i ∩ S` minimizes `D (·) y` over `A i ∩ S` -/
  proj : ∀ i, ∀ y ∈ S, P i y ∈ A i ∩ S ∧ ∀ z ∈ A i ∩ S, D (P i y) y ≤ D z y
  /-- condition III: `z ↦ D z y - D z (P i y)` is convex on `A i ∩ S` -/
  convexOn : ∀ i, ∀ y ∈ S, ConvexOn ℝ (A i ∩ S) (fun z => D z y - D z (P i y))
  /-- condition IV: `D (y + t (w - y)) y / t → 0` as `t → 0⁺`, for `y, w ∈ S` -/
  deriv_zero : ∀ y ∈ S, ∀ w ∈ S,
    Filter.Tendsto (fun t : ℝ => D (y + t • (w - y)) y / t) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  /-- condition VI -/
  conv : ∀ (x y : ℕ → X) (y' : X), (∀ n, x n ∈ S) → (∀ n, y n ∈ S) →
    Filter.Tendsto (fun n => D (x n) (y n)) Filter.atTop (nhds 0) →
    Filter.Tendsto y Filter.atTop (nhds y') → y' ∈ closure S →
    (∃ K : Set X, IsSeqCompact K ∧ ∀ n, x n ∈ K) → Filter.Tendsto x Filter.atTop (nhds y')

/-- Condition V (p. 201), for the points `z ∈ Zv` (in §1, `Zv = R ∩ S`): every sublevel set
`{x ∈ S | D z x ≤ L}` is sequentially compact. -/
def CondV {X : Type*} [TopologicalSpace X] (S : Set X) (D : X → X → ℝ) (Zv : Set X) : Prop :=
  ∀ z ∈ Zv, ∀ L : ℝ, IsSeqCompact {x | x ∈ S ∧ D z x ≤ L}

/-- A relaxation sequence with control `i` (p. 201, steps (1)–(2)):
`x 0 ∈ S` and `x (n+1) = P (i n) (x n)`. -/
def IsRelaxSeq {X : Type*} {ι : Type*} (S : Set X) (P : ι → X → X) (i : ℕ → ι) (x : ℕ → X) :
    Prop :=
  x 0 ∈ S ∧ ∀ n, x (n + 1) = P (i n) (x n)

/-- The cyclic control of Theorem 1 (p. 203), 0-based: `n ↦ n mod m`, i.e. the paper's
`i_n = (n mod m) + 1` shifted by one. -/
def cyclicControl {m : ℕ} (hm : 0 < m) : ℕ → Fin m := fun n => ⟨n % m, Nat.mod_lt n hm⟩

end BregmanRelax.Cyclic


