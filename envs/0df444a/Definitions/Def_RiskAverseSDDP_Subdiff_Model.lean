-- Prove2me | Definitions.Def_RiskAverseSDDP_Subdiff_Model
-- name    : RiskAverseSDDP_Subdiff_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T04:31:10.640432+00:00
-- url     : https://prove2.me/theorems/38fa304f-5757-4f5e-80ea-3d4aed84f850
-- title:
--   (2.1)–(2.3), (H), Lemma 2.1, pp. 3–4 — the convex program, its value function 𝒬, dual function θ_x, subdifferentials and normal cones
-- statement:
--   This file fixes the objects of §2 of Guigues (2016): the value function of a convex program whose parameter $x$ enters both the objective and the constraints, its Lagrangian dual, and the convex-analysis notions in which Lemma 2.1 is stated.
--
--   Write $\mathbb R^k$ for Euclidean space with the scalar product $\langle x,y\rangle=x^\top y$, and $\overline{\mathbb R}=\mathbb R\cup\{\pm\infty\}$. On $\mathbb R^m\times\mathbb R^n$ the pairing is $\langle (s,t),(x,y)\rangle=\langle s,x\rangle+\langle t,y\rangle$.
--
--   **Extended-real notions.** A function $h$ with values in $\overline{\mathbb R}$ is *proper* if it never equals $-\infty$ and is not identically $+\infty$; it is *convex* if its epigraph $\{(z,r): h(z)\le r\}$ is convex; its domain is $\operatorname{dom}(h)=\{z: h(z)<+\infty\}$. The indicator $\mathbb I_C$ of a set $C$ is $0$ on $C$ and $+\infty$ off $C$. The *subdifferential* of $h$ at $z_0$ is
--   $$\partial h(z_0)=\{\,s:\ h(z_0)\in\mathbb R\ \text{ and }\ h(z)\ge h(z_0)+\langle s,z-z_0\rangle\ \text{ for all } z\,\},$$
--   which is empty when $h(z_0)$ is infinite. The *normal cone* of $C$ at $z_0$ is $\mathcal N_C(z_0)=\{v:\ \langle v,z-z_0\rangle\le 0\ \text{for all } z\in C\}$.
--
--   **The program (2.1).** The data are matrices $A\in\mathbb R^{q\times m}$, $B\in\mathbb R^{q\times n}$, a vector $b\in\mathbb R^q$, an objective $f:\mathbb R^m\times\mathbb R^n\to\overline{\mathbb R}$, constraint functions $g_1,\dots,g_p:\mathbb R^m\times\mathbb R^n\to\overline{\mathbb R}$ and a set $Y\subseteq\mathbb R^n$. For every $x\in\mathbb R^m$,
--   $$S(x)=\{y\in Y:\ Ax+By=b,\ g(x,y)\le 0\},\qquad \mathcal Q(x)=\inf_{y\in S(x)} f(x,y),\qquad \operatorname{Sol}(x)=\{y\in S(x): f(x,y)=\mathcal Q(x)\},$$
--   with $\mathcal Q(x)=+\infty$ when $S(x)=\emptyset$. The proof of Lemma 2.1 uses $C_1=\{(x,y): Ax+By=b\}$, $C_2=\{(x,y): g(x,y)\le 0\}$, $\operatorname{Gr}(S)=C_1\cap C_2\cap(\mathbb R^m\times Y)$ and the active set $I(x,y)=\{i: g_i(x,y)=0\}$.
--
--   **The dual (2.3).** For $\lambda\in\mathbb R^q$ and $\mu\in\mathbb R^p$,
--   $$\theta_x(\lambda,\mu)=\inf_{y\in Y}\ f(x,y)+\lambda^\top(Ax+By-b)+\mu^\top g(x,y),$$
--   and $\Lambda(x)$ is the set of $(\lambda,\mu)$ with $\mu\ge 0$ that maximize $\theta_x$ over $\mathbb R^q\times\mathbb R^p_+$.
--
--   **Assumption (H)** for a set $X\subseteq\mathbb R^m$: (1) $f$ is lower semicontinuous, proper and convex; (2) each $g_i$ is convex and lower semicontinuous with values in $\mathbb R\cup\{+\infty\}$; (3) there is $\varepsilon>0$ with $X^\varepsilon\times Y\subseteq\operatorname{dom}(f)$, where $X^\varepsilon=X+\varepsilon B_m$ (2.2).
--
--   **Slater conditions.** The *printed* condition of Lemma 2.1 asks for $(\bar x,\bar y)\in X\times\operatorname{ri}(Y)$ with $(\bar x,\bar y)\in C_1\cap\operatorname{ri}(C_2)$. The *repaired* condition used by this mission asks for $(\bar x,\bar y)\in X\times\operatorname{ri}(Y)$ with $A\bar x+B\bar y=b$, $g_i(\bar x,\bar y)<0$ for every $i$, and $(\bar x,\bar y)\in\operatorname{ri}(\operatorname{dom} f)$.
--
--   These definitions are shared by every statement of the mission: Lemma 2.1, its differentiable case, and the steps of its proof.
--
--   **Formalization Note** $\mathbb R^k$ is `EuclideanSpace ℝ (Fin k)`; pairs are the product type with the pairing written out (`pair`), so no norm of the product is used. Values in $\overline{\mathbb R}$ are `EReal`; the dual function is an `EReal` infimum with the convention $0\cdot(+\infty)=0$. $X^\varepsilon$ is `Metric.cthickening ε X`, which equals $X+\varepsilon B_m$ for compact $X$. $\operatorname{ri}$ is `intrinsicInterior ℝ`. Indices $i=1,\dots,p$ are `Fin p` (0-based). The normal cone on $\mathbb R^n$ is the published `FirstOrderOpt.ConvexTheory.normalCone`; like it, `normalConeProd` does not require $z_0\in C$, and every statement uses it only at points of $C$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, pp. 2–4, notation list, (2.1)–(2.3), Assumption (H), Lemma 2.1 and its proof

import Mathlib
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone
import Definitions.Def_RiskAverseSDDP_Convergence_Basic

namespace RiskAverseSDDP.Subdiff

open scoped RealInnerProductSpace

/-- Euclidean space `ℝ^k` with its usual inner product `⟨x, y⟩ = xᵀy` and norm `‖x‖₂` (p. 3). -/
abbrev E (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

/-- The effective domain `dom(h) = {z | h z < +∞}`. -/
def edom {Z : Type*} (h : Z → EReal) : Set Z := {z | h z ≠ ⊤}

/-- The indicator function `𝕀_C` (p. 3): `0` on `C`, `+∞` off `C`. -/
noncomputable def indicatorE {Z : Type*} (C : Set Z) (z : Z) : EReal := by
  classical
  exact if z ∈ C then 0 else ⊤

/-- The pairing on `ℝ^m × ℝ^n`: `⟨(s, t), (x, y)⟩ = ⟨s, x⟩ + ⟨t, y⟩`, i.e. the usual scalar
product of the concatenated vectors `[s; t]` and `[x; y]`. -/
noncomputable def pair {m n : ℕ} (u z : E m × E n) : ℝ := ⟪u.1, z.1⟫ + ⟪u.2, z.2⟫

/-- The subdifferential of an extended-real function `h : ℝ^k → ℝ ∪ {±∞}` at `x₀`:
the vectors `s` such that `h(x₀)` is finite and `h(x) ≥ h(x₀) + ⟨s, x - x₀⟩` for every
`x ∈ ℝ^k`. It is empty at a point where `h` is infinite. -/
def subdiff {k : ℕ} (h : E k → EReal) (x₀ : E k) : Set (E k) :=
  {s | h x₀ ≠ ⊤ ∧ h x₀ ≠ ⊥ ∧ ∀ x, h x₀ + ((⟪s, x - x₀⟫ : ℝ) : EReal) ≤ h x}

/-- The subdifferential of an extended-real function `F` on `ℝ^m × ℝ^n` at `z₀`, for the pairing
`pair`: the `u` such that `F(z₀)` is finite and `F(z) ≥ F(z₀) + ⟨u, z - z₀⟩` for every `z`. -/
def subdiffProd {m n : ℕ} (F : E m × E n → EReal) (z₀ : E m × E n) : Set (E m × E n) :=
  {u | F z₀ ≠ ⊤ ∧ F z₀ ≠ ⊥ ∧ ∀ z, F z₀ + ((pair u (z - z₀) : ℝ) : EReal) ≤ F z}

/-- The normal cone `𝒩_C(z₀) = {v | ⟨v, z - z₀⟫ ≤ 0 ∀ z ∈ C}` of a set `C ⊆ ℝ^m × ℝ^n`, for the
pairing `pair` (the same convention as `FirstOrderOpt.ConvexTheory.normalCone` on `ℝ^n`; it is
only used at points `z₀ ∈ C`). -/
def normalConeProd {m n : ℕ} (C : Set (E m × E n)) (z₀ : E m × E n) : Set (E m × E n) :=
  {v | ∀ z ∈ C, pair v (z - z₀) ≤ 0}

/-- The data of the convex program (2.1), p. 3: matrices `A ∈ ℝ^{q×m}`, `B ∈ ℝ^{q×n}`, a vector
`b ∈ ℝ^q`, an objective `f : ℝ^m × ℝ^n → ℝ ∪ {±∞}`, constraint functions
`g_1, …, g_p : ℝ^m × ℝ^n → ℝ ∪ {±∞}` and the set `Y ⊆ ℝ^n`. -/
structure ConvexProgram (m n q p : ℕ) where
  A : Matrix (Fin q) (Fin m) ℝ
  B : Matrix (Fin q) (Fin n) ℝ
  b : E q
  f : E m × E n → EReal
  g : Fin p → E m × E n → EReal
  Y : Set (E n)

namespace ConvexProgram

variable {m n q p : ℕ} (P : ConvexProgram m n q p)

/-- `Ax + By ∈ ℝ^q`. -/
noncomputable def lin (x : E m) (y : E n) : E q :=
  Matrix.toEuclideanLin P.A x + Matrix.toEuclideanLin P.B y

/-- The feasible set `S(x) = {y ∈ Y : Ax + By = b, g(x, y) ≤ 0}` of (2.1). -/
def S (x : E m) : Set (E n) :=
  {y | y ∈ P.Y ∧ P.lin x y = P.b ∧ ∀ i, P.g i (x, y) ≤ 0}

/-- The value function (2.1), `𝒬(x) = inf_{y ∈ S(x)} f(x, y)`, defined for every `x ∈ ℝ^m`
(`+∞` when `S(x) = ∅`). -/
noncomputable def Q (x : E m) : EReal :=
  ⨅ y ∈ P.S x, P.f (x, y)

/-- The solution set `Sol(x) = {y ∈ S(x) : f(x, y) = 𝒬(x)}` of (2.1). -/
def Sol (x : E m) : Set (E n) :=
  {y | y ∈ P.S x ∧ P.f (x, y) = P.Q x}

/-- `C₁ = {(x, y) : Ax + By = b}` (Lemma 2.1). -/
def C1 : Set (E m × E n) := {z | P.lin z.1 z.2 = P.b}

/-- `C₂ = {(x, y) : g(x, y) ≤ 0}` (Lemma 2.1). -/
def C2 : Set (E m × E n) := {z | ∀ i, P.g i z ≤ 0}

/-- `Gr(S) = {(x, y) : Ax + By = b, g(x, y) ≤ 0, y ∈ Y} = C₁ ∩ C₂ ∩ ℝ^m × Y` (proof of Lemma 2.1). -/
def GrS : Set (E m × E n) := {z | P.lin z.1 z.2 = P.b ∧ (∀ i, P.g i z ≤ 0) ∧ z.2 ∈ P.Y}

/-- The active set `I(x, y) = {i ∈ {1, …, p} : g_i(x, y) = 0}`. -/
noncomputable def active (x : E m) (y : E n) : Finset (Fin p) := by
  classical
  exact Finset.univ.filter fun i => P.g i (x, y) = 0

/-- The dual function of (2.3):
`θ_x(λ, μ) = inf_{y ∈ Y} f(x, y) + λᵀ(Ax + By - b) + μᵀ g(x, y)`, computed in `EReal`
(the product `μ_i g_i` uses `0 · (+∞) = 0`). -/
noncomputable def theta (x : E m) (lam : E q) (μ : Fin p → ℝ) : EReal :=
  ⨅ y ∈ P.Y, (P.f (x, y) + ((⟪lam, P.lin x y - P.b⟫ : ℝ) : EReal)
    + ∑ i, ((μ i : ℝ) : EReal) * P.g i (x, y))

/-- `Λ(x)`: the set of optimal solutions `(λ, μ) ∈ ℝ^q × ℝ^p_+` of the dual problem (2.3). -/
def Lambda (x : E m) : Set (E q × (Fin p → ℝ)) :=
  {d | 0 ≤ d.2 ∧ ∀ (lam' : E q) (μ' : Fin p → ℝ), 0 ≤ μ' → P.theta x lam' μ' ≤ P.theta x d.1 d.2}

/-- Assumption (H), p. 3, for the sets `X ⊆ ℝ^m` and `Y`:
1) `f` is lower semicontinuous, proper and convex, with values in `ℝ ∪ {+∞}`;
2) every `g_i` is convex and lower semicontinuous with values in `ℝ ∪ {+∞}`;
3) there is `ε > 0` with `X^ε × Y ⊆ dom(f)`, where `X^ε = X + εB_m` is the closed
   `ε`-thickening of `X`. -/
def AssumptionH (X : Set (E m)) : Prop :=
  (LowerSemicontinuous P.f ∧ RiskAverseSDDP.Convergence.EProper P.f ∧ RiskAverseSDDP.Convergence.EConvex P.f) ∧
  (∀ i, LowerSemicontinuous (P.g i) ∧ RiskAverseSDDP.Convergence.EConvex (P.g i) ∧ ∀ z, P.g i z ≠ ⊥) ∧
  ∃ ε : ℝ, 0 < ε ∧ Metric.cthickening ε X ×ˢ P.Y ⊆ edom P.f

/-- The printed Slater-type condition of Lemma 2.1, p. 3: there is `(x̄, ȳ) ∈ X × ri(Y)` with
`(x̄, ȳ) ∈ C₁` and `(x̄, ȳ) ∈ ri(C₂)`. -/
def PrintedSlater (X : Set (E m)) : Prop :=
  ∃ xb ∈ X, ∃ yb ∈ intrinsicInterior ℝ P.Y,
    (xb, yb) ∈ P.C1 ∧ (xb, yb) ∈ intrinsicInterior ℝ P.C2

/-- The repaired Slater condition (R2)–(R3): there is `(x̄, ȳ) ∈ X × ri(Y)` with
`Ax̄ + Bȳ = b`, `g_i(x̄, ȳ) < 0` for every `i`, and `(x̄, ȳ) ∈ ri(dom f)`. -/
def RepairedSlater (X : Set (E m)) : Prop :=
  ∃ xb ∈ X, ∃ yb ∈ intrinsicInterior ℝ P.Y,
    P.lin xb yb = P.b ∧ (∀ i, P.g i (xb, yb) < 0) ∧ (xb, yb) ∈ intrinsicInterior ℝ (edom P.f)

end ConvexProgram

end RiskAverseSDDP.Subdiff


