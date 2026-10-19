-- Prove2me | Definitions.Def_CvxComposite_Conj_Setting
-- name    : CvxComposite_Conj_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:13:56.838196+00:00
-- url     : https://prove2.me/theorems/3779a60b-44a6-4536-aeb4-257464a914dc
-- title:
--   §2–§4 — effective domains, conjugacy setting, cone epigraphs, scalarizations, and dual functions
-- statement:
--   Let $E$, $E_1$, and $E_2$ be finite-dimensional real inner-product spaces. An extended-real function takes values in $\overline{\mathbb R}=\mathbb R\cup\{-\infty,+\infty\}$. Its **effective domain** is $\operatorname{dom}f=\{x:f(x)<+\infty\}$, and $f\in\Gamma(E)$ means that $f$ never equals $-\infty$, is finite somewhere, and has a convex epigraph. The **lower semicontinuous hull** $\operatorname{cl}f$ is the infimum of limits $f(x_k)\to\alpha$ over sequences $x_k\to x$. **Infimal convolution** and the indicator and support functions are
--   $$
--   (f\mathbin{\square}g)(x)=\inf_y\{f(y)+g(x-y)\},\qquad
--   \delta_S(x)=\begin{cases}0&x\in S,\\+\infty&x\notin S,\end{cases}\qquad
--   \sigma_S(y)=\sup_{x\in S}\langle x,y\rangle.
--   $$
--
--   A map $F:E_1\to E_2^\bullet$ is represented by its domain $D\subseteq E_1$ and its values $F(x)\in E_2$ for $x\in D$. For a cone $K\subseteq E_2$, its **$K$-epigraph** is $\{(x,y):x\in D,\ y-F(x)\in K\}$; $F$ is **$K$-convex** when this set is convex. The composite $g\circ F$ and the scalarization $\langle v,F\rangle$ take the value $+\infty$ off $D$. Their values on $D$ are $g(F(x))$ and $\langle v,F(x)\rangle$.
--
--   Condition (7) says $g(F(x))\le g(y)$ whenever $x\in D$ and $y-F(x)\in K$. Condition (8) says $g(u)\le g(v)$ whenever $v-u\in K$. The dual functions used by Theorem 12 and Lemma 10 are
--   $$
--   \eta(p)=\inf_{v\in-K^\circ}\bigl(g^*(v)+\langle v,F\rangle^*(p)\bigr),\qquad
--   \psi(p,v)=g^*(v)+\sigma_{K\text{-epi}F}(p,-v).
--   $$
--
--   These definitions provide a common interface for the theorem statements; in particular, the support functions of the graph and epigraph use the product pairing $\langle(x,y),(p,v)\rangle=\langle x,p\rangle+\langle y,v\rangle$.
--
--   **Formalization Note** The published definitions supply the Fenchel conjugate, epigraph convexity, $\Gamma_0$, closed convex cones, and the polar cone. The partial map is encoded by $(D,F)$, so values of its total representative outside $D$ have no effect. All suprema and infima take values in `EReal`.
-- source:
--   Burke, Hoheisel & Nguyen, A Study of Convex Convex-Composite Functions via Infimal Convolution with Applications, arXiv:1907.08318v2, pp. 3–10, §2–§4, Definition 3, (2), (6)–(9)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_MoreauProx_Decomposition_Cones
open scoped InnerProductSpace Pointwise
open Filter Topology

namespace CvxComposite.Conj

open MoreauProx.Characterization MoreauProx.Decomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
variable {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/-- The effective domain of an extended-real-valued function. -/
def effDom (f : E → EReal) : Set E := {x | f x ≠ ⊤}

/-- The class Γ(E): proper convex functions taking values in ℝ ∪ {+∞}. -/
def IsProperConvex (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (∃ x, f x ≠ ⊤) ∧ EConvex f

/-- The lower semicontinuous hull, as the infimum of sequential limiting values on p. 4. -/
noncomputable def lscHull (f : E → EReal) (x : E) : EReal :=
  ⨅ α ∈ {α : EReal | ∃ u : ℕ → E,
    Tendsto u atTop (𝓝 x) ∧ Tendsto (fun k => f (u k)) atTop (𝓝 α)}, α

/-- Infimal convolution (p. 4). -/
noncomputable def infConv (f g : E → EReal) (x : E) : EReal :=
  ⨅ y : E, f y + g (x - y)

/-- Indicator δ_S: zero on S and +∞ outside S. -/
noncomputable def indicatorFn (S : Set E) (x : E) : EReal :=
  ⨅ (_ : x ∈ S), (0 : EReal)

/-- Support function σ_S, with the extended-real supremum. -/
noncomputable def supportFn (S : Set E) (y : E) : EReal :=
  ⨆ x ∈ S, ((⟪x, y⟫_ℝ : ℝ) : EReal)

/-- A convex cone as in p. 5, without an extra closedness condition. -/
def IsConvexConeSet (K : Set E) : Prop :=
  Convex ℝ K ∧ ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K

/-- The K-epigraph of the partial map encoded by its domain D and a total representative F. -/
def KEpi (K : Set E₂) (D : Set E₁) (F : E₁ → E₂) : Set (E₁ × E₂) :=
  {q | q.1 ∈ D ∧ q.2 - F q.1 ∈ K}

/-- Definition 3: K-convexity is convexity of the K-epigraph. -/
def IsKConvex (K : Set E₂) (D : Set E₁) (F : E₁ → E₂) : Prop :=
  Convex ℝ (KEpi K D F)

/-- Composition (6), with value +∞ off the partial map's domain. -/
noncomputable def comp (g : E₂ → EReal) (D : Set E₁) (F : E₁ → E₂) (x : E₁) : EReal :=
  ⨅ (_ : x ∈ D), g (F x)

/-- The scalarization ⟨v,F⟩, +∞ off D. -/
noncomputable def scal (v : E₂) (D : Set E₁) (F : E₁ → E₂) : E₁ → EReal :=
  comp (fun y => ((⟪v, y⟫_ℝ : ℝ) : EReal)) D F

/-- Support function of the graph of a partial map. -/
noncomputable def suppGph (D : Set E₁) (F : E₁ → E₂) (u : E₁) (v : E₂) : EReal :=
  ⨆ x ∈ D, ((⟪x, u⟫_ℝ + ⟪F x, v⟫_ℝ : ℝ) : EReal)

/-- Support function of the K-epigraph, using the product pairing. -/
noncomputable def suppKEpi (K : Set E₂) (D : Set E₁) (F : E₁ → E₂)
    (u : E₁) (v : E₂) : EReal :=
  ⨆ q ∈ KEpi K D F, ((⟪q.1, u⟫_ℝ + ⟪q.2, v⟫_ℝ : ℝ) : EReal)

/-- Condition (7): monotonicity only along the K-epigraph. -/
def Cond7 (K : Set E₂) (D : Set E₁) (F : E₁ → E₂) (g : E₂ → EReal) : Prop :=
  ∀ x ∈ D, ∀ y, y - F x ∈ K → g (F x) ≤ g y

/-- Condition (8): K-increasingness. -/
def KIncreasing (K : Set E) (g : E → EReal) : Prop :=
  ∀ u v, v - u ∈ K → g u ≤ g v

/-- The dual infimum η of Theorem 12(a). -/
noncomputable def eta (K : Set E₂) (D : Set E₁) (F : E₁ → E₂)
    (g : E₂ → EReal) (p : E₁) : EReal :=
  ⨅ v ∈ {v | -v ∈ polarCone K}, conj g v + conj (scal v D F) p

/-- The function ψ of (9). -/
noncomputable def psi (K : Set E₂) (D : Set E₁) (F : E₁ → E₂)
    (g : E₂ → EReal) (p : E₁) (v : E₂) : EReal :=
  conj g v + suppKEpi K D F p (-v)

/-- The conjugate of ψ under the explicit product pairing. -/
noncomputable def psiConj (K : Set E₂) (D : Set E₁) (F : E₁ → E₂)
    (g : E₂ → EReal) (x : E₁) (u : E₂) : EReal :=
  ⨆ p : E₁, ⨆ v : E₂,
    ((⟪x, p⟫_ℝ + ⟪u, v⟫_ℝ : ℝ) : EReal) - psi K D F g p v

end CvxComposite.Conj


