-- Prove2me | Definitions.Def_RamseyLST_Main_FiniteMetric
-- name    : RamseyLST_Main_FiniteMetric
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:07:25.412619+00:00
-- url     : https://prove2.me/theorems/9310f723-e662-44a5-b564-7dc04c82db3a
-- title:
--   Finite metric spaces, diameter, aspect ratio, embeddings with distortion, the class $\mathcal X(\theta)$ and strong Ramsey embeddings
-- statement:
--   A **metric** on a set $P$ is a function $d : P\times P\to\mathbb R$ with $d(x,x)=0$, $d(x,y)>0$ for $x\neq y$, $d(x,y)=d(y,x)$ and $d(x,z)\le d(x,y)+d(y,z)$.
--
--   For a finite set $Y\subseteq P$ the **diameter** is $\operatorname{diam}_d(Y)=\max_{u,v\in Y}d(u,v)$ (and $0$ for $Y=\emptyset$), and the **aspect ratio** is
--
--   $$\Phi_d(Y)=\frac{\operatorname{diam}_d(Y)}{\min_{u\neq v\in Y}d(u,v)},$$
--
--   with the convention $\Phi_d(Y)=1$ when $|Y|\le 1$.
--
--   Following Definition 1, a map $f:(P,d_P)\to(Q,d_Q)$ **embeds with distortion at most $\theta$** if it is injective, **non-contractive** ($d_P(x,y)\le d_Q(f(x),f(y))$ for all $x,y$) and $d_Q(f(x),f(y))\le\theta\,d_P(x,y)$ for all $x,y$; this is the multiplicative form of $\operatorname{dist}_f(x,y)=d_Q(f(x),f(y))/d_P(x,y)\le\theta$.
--
--   A **class of metric spaces** $\mathcal X$ is a predicate on pairs (carrier, distance). For $\theta\ge1$, $\mathcal X(\theta)$ is the class of finite metric spaces which embed with distortion at most $\theta$ into a space of $\mathcal X$.
--
--   Following Definition 2, a map $f:(P,d)\to(Q,d')$ from a finite space with a **core** $Z\subseteq P$ is a **strong $(\alpha,\psi)$-Ramsey embedding** if $f$ is injective and non-contractive, $|Z|\ge|P|^{\psi}$, and $d'(f(x),f(y))\le\alpha\,d(x,y)$ for every $x\in Z$ and every $y\in P$.
--
--   These are the metric notions of §2 used by Theorem 5, Lemmas 6–8 and Corollary 10.
--
--   **Formalization Note** Points form a Lean type; finiteness is a `Fintype` instance where needed. The aspect ratio and the diameter are real numbers computed from `Finset` maxima and minima. A class of metric spaces is any predicate on a type with a real-valued distance; closure under isometry is not required.
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), pp. 8–10 (PDF 12–14), §2, Definitions 1 and 2

import Mathlib

namespace RamseyLST.Main

/-- `d` is a metric on the points of `P` (Bartal–Hovav, §2, p. 8): zero on the diagonal,
positive between distinct points, symmetric, and satisfying the triangle inequality. -/
structure IsMetric {P : Type} (d : P → P → ℝ) : Prop where
  dist_self : ∀ x, d x x = 0
  pos : ∀ x y, x ≠ y → 0 < d x y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- The diameter `diam_d(Y) = max_{u,v ∈ Y} d(u, v)` of a finite set `Y` (§2, p. 8); it is `0`
for the empty set. -/
noncomputable def diamOn {P : Type} (d : P → P → ℝ) (Y : Finset P) : ℝ :=
  if h : Y.Nonempty then (Y ×ˢ Y).sup' (h.product h) (fun p => d p.1 p.2) else 0

/-- The aspect ratio `Φ_d(Y) = diam_d(Y) / min_{u ≠ v ∈ Y} d(u, v)` of a finite set `Y`
(§2, p. 8), with the convention `Φ_d(Y) = 1` when `|Y| ≤ 1`. -/
noncomputable def aspectRatio {P : Type} (d : P → P → ℝ) (Y : Finset P) : ℝ := by
  classical
  exact if h : Y.offDiag.Nonempty then
      diamOn d Y / Y.offDiag.inf' h (fun p => d p.1 p.2)
    else 1

/-- Definition 1 (p. 9): `f : (X, d_X) → (Y, d_Y)` is a metric embedding (injective) which is
non-contractive (`d_X(x, y) ≤ d_Y(f x, f y)`) and has distortion at most `θ`
(`d_Y(f x, f y) ≤ θ · d_X(x, y)` for all `x, y`, the multiplicative form of
`dist_f(x, y) ≤ θ`). -/
def IsEmbeddingWithDistortion {P Q : Type} (dP : P → P → ℝ) (dQ : Q → Q → ℝ) (f : P → Q)
    (θ : ℝ) : Prop :=
  Function.Injective f ∧ (∀ x y, dP x y ≤ dQ (f x) (f y)) ∧
    ∀ x y, dQ (f x) (f y) ≤ θ * dP x y

/-- A class of metric spaces, as a predicate on (carrier type, distance function). No closure
under isometry is required. -/
abbrev MetricClass : Type 1 := (P : Type) → (P → P → ℝ) → Prop

/-- `𝒳(θ)` (§2.1, p. 9): the class of finite metric spaces which embed with distortion at most
`θ` (Definition 1) into a space of `𝒳`. -/
def MetricClass.within (𝒳 : MetricClass) (θ : ℝ) : MetricClass :=
  fun P d => Finite P ∧ IsMetric d ∧
    ∃ (Q : Type) (dQ : Q → Q → ℝ) (f : P → Q), 𝒳 Q dQ ∧ IsEmbeddingWithDistortion d dQ f θ

/-- Definition 2 (pp. 9–10), strong form, core size measured against the whole space: the
embedding `f : (P, d) → (Q, d')` is injective and non-contractive, the core `Z ⊆ P` has
`|Z| ≥ |P|^ψ`, and `d'(f x, f y) ≤ α · d(x, y)` for every `x ∈ Z` and **every** `y ∈ P`. -/
def IsStrongRamseyEmbedding {P Q : Type} [Fintype P] (d : P → P → ℝ) (d' : Q → Q → ℝ)
    (f : P → Q) (Z : Finset P) (α ψ : ℝ) : Prop :=
  Function.Injective f ∧ (∀ x y, d x y ≤ d' (f x) (f y)) ∧
    ((Fintype.card P : ℝ) ^ ψ ≤ (Z.card : ℝ)) ∧
    ∀ x ∈ Z, ∀ y : P, d' (f x) (f y) ≤ α * d x y

end RamseyLST.Main


