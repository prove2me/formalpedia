-- Prove2me | Definitions.Def_InducedExpanderTest989_Structural_Supplement_NoisyLabels
-- name    : InducedExpanderTest989_Structural_Supplement_NoisyLabels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:30:14.453184+00:00
-- url     : https://prove2.me/theorems/535dee7d-5d03-4f4d-be47-6007644a3797
-- title:
--   Isotropic noise, spanning forests and the planted likelihood ratio on a finite multigraph
-- statement:
--   Let $r\ge1$, let $K=\mathbb F_2^r$ be the group of $r$-bit vectors under coordinatewise addition and $q=2^r$. **Isotropic noise** of rate $p$ is the law on $K$ with
--   $$\Pr(Z=0)=1-p,\qquad \Pr(Z=z)=\frac{p}{q-1}\ (z\neq0),\qquad \rho=1-\frac{qp}{q-1}.$$
--
--   A finite multigraph $H$ has a finite vertex set $V$, a finite set $E$ of edge occurrences and an endpoint map; loops and parallel edges are allowed. A set $F\subseteq E$ is a **spanning forest** if it contains no cycle (a loop, or two parallel edges, is a cycle) and has the same connected components as $H$. The forest distance $\mathrm{dist}_F(x,y)$ is the least number of edges of $F$ on a walk from $x$ to $y$, and $\infty$ when $x,y$ lie in different trees.
--
--   For labels $y\in K^{E}$, the planted law draws independent uniform potentials $X_v\in K$ and independent isotropic noises $Z_e$, and sets $Y_e=X_u+X_v+Z_e$ for $e=uv$:
--   $$\Pr\nolimits^H_{\mathcal P}(y)=\sum_{X\in K^V} q^{-|V|}\prod_{e=uv\in E}\Pr(Z=y_e+X_u+X_v).$$
--   The uniform law gives each $y$ probability $q^{-|E|}$, and the **likelihood ratio** is
--   $$D_H(y)=\frac{\Pr^H_{\mathcal P}(y)}{\Pr^H_{\mathcal U}(y)}=q^{|E|}\Pr\nolimits^H_{\mathcal P}(y).$$
--
--   These objects state Lemma 6.8, the analytic core of the indistinguishability argument behind Theorem 6.1.
--
--   **Formalization Note** $K$ is `Fin r → ZMod 2`. A multigraph is a pair of finite types with `ends : E → V × V`; orientation is irrelevant since $-a=a$ in $K$, and a loop contributes $X_v+X_v=0$. Acyclicity of $F$ is stated as: no edge of $F$ has its endpoints joined by the other edges of $F$. `nonforestEndpoint` lists the $2R$ endpoint occurrences of the nonforest edges.
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.35 (PDF p.37), §6.1 labels; p.36 (PDF p.38), eq. (23); p.37 (PDF p.39), Pr^H_U, Pr^H_P; p.40 (PDF p.42), §6.4.1 and eq. (34)

import Mathlib

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

/-- The label group `K = F₂^r` (§6.1); its order is `q = 2^r`. -/
abbrev LabelGroup (r : ℕ) := Fin r → ZMod 2

/-- Isotropic noise (23): mass `1 − p` at `0` and `p/(q − 1)` at each nonzero element. -/
def isoNoise (r : ℕ) (p : ℝ) (z : LabelGroup r) : ℝ :=
  if z = 0 then 1 - p else p / ((2 : ℝ) ^ r - 1)

/-- The character bias `ρ = 1 − q p/(q − 1)` of (23). -/
def noiseBias (r : ℕ) (p : ℝ) : ℝ := 1 - (2 : ℝ) ^ r * p / ((2 : ℝ) ^ r - 1)

section Multigraph

variable {V E : Type}

/-- A finite multigraph is a finite vertex type `V`, a finite type `E` of edge occurrences and
an endpoint map `ends : E → V × V`; loops and parallel edges are allowed. `x` and `y` are
joined by an edge of the set `F`. -/
def edgeAdj (ends : E → V × V) (F : Finset E) (x y : V) : Prop :=
  ∃ e ∈ F, ends e = (x, y) ∨ ends e = (y, x)

/-- `F` is acyclic: no edge of `F` has its endpoints joined by the other edges of `F`. A loop,
or two parallel edges, in `F` is a cycle. -/
def IsAcyclicEdgeSet [DecidableEq E] (ends : E → V × V) (F : Finset E) : Prop :=
  ∀ e ∈ F, ¬ Relation.ReflTransGen (edgeAdj ends (F.erase e)) (ends e).1 (ends e).2

/-- `F ⊆ E` is a spanning forest: acyclic, with the same connected components as the whole
multigraph. -/
def IsSpanningForest [DecidableEq E] [Fintype E] (ends : E → V × V) (F : Finset E) : Prop :=
  IsAcyclicEdgeSet ends F ∧
    ∀ x y : V, Relation.ReflTransGen (edgeAdj ends Finset.univ) x y →
      Relation.ReflTransGen (edgeAdj ends F) x y

/-- There is a walk of exactly `k` edges of `F` from `x` to `y`. -/
def WalkIn (ends : E → V × V) (F : Finset E) : ℕ → V → V → Prop
  | 0, x, y => x = y
  | k + 1, x, y => ∃ z, WalkIn ends F k x z ∧ edgeAdj ends F z y

/-- `dist_F(x, y)`: the least number of edges of `F` on a walk from `x` to `y`, `⊤` (= ∞) for
vertices in different trees. -/
def forestDist (ends : E → V × V) (F : Finset E) (x y : V) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : WalkIn ends F k x y), (k : ℕ∞)

/-- The `2R` endpoint occurrences of the nonforest edges: `(e, 0)` is the first endpoint of
`e ∉ F`, `(e, 1)` the second. -/
def nonforestEndpoint (ends : E → V × V) (F : Finset E) (a : {e // e ∉ F} × Fin 2) : V :=
  if a.2 = 0 then (ends a.1.1).1 else (ends a.1.1).2

/-- `Pr^H_P(y)` of §6.1: potentials `X_v` i.i.d. uniform on `K`, noises `Z_e` i.i.d. isotropic,
and `y_e = X_u + X_v + Z_e` for every edge occurrence `e = uv`. -/
def plantedProb [Fintype V] [Fintype E] (r : ℕ) (p : ℝ) (ends : E → V × V)
    (y : E → LabelGroup r) : ℝ := by
  classical
  exact ∑ X : V → LabelGroup r, (((2 : ℝ) ^ r) ^ Fintype.card V)⁻¹ *
    ∏ e, isoNoise r p (y e + X (ends e).1 + X (ends e).2)

/-- The likelihood ratio (34): `D_H(y) = Pr^H_P(y) / Pr^H_U(y) = q^{|E(H)|} Pr^H_P(y)`. -/
def likelihoodRatio [Fintype V] [Fintype E] (r : ℕ) (p : ℝ) (ends : E → V × V)
    (y : E → LabelGroup r) : ℝ :=
  ((2 : ℝ) ^ r) ^ Fintype.card E * plantedProb r p ends y

end Multigraph

end InducedExpanderTest989.Structural.Supplement


