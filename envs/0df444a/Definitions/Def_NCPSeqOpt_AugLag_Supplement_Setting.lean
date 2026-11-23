-- Prove2me | Definitions.Def_NCPSeqOpt_AugLag_Supplement_Setting
-- name    : NCPSeqOpt_AugLag_Supplement_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:45:33.676902+00:00
-- url     : https://prove2.me/theorems/5feeffe5-f1ac-451f-a540-0d956e0f9bc8
-- title:
--   §2.1–§7, pp. 3–22 — KKT, TAKKT (Def. 3.1), AKKT (Def. 5.1), local minimizer, AGP (4), the sets 𝕂_A, 𝕂_T, 𝕂_AGP, 𝕂_C and their regularity (Def. 7.1), L_Ω, Abadie's CQ
-- statement:
--   This file adds, on top of the published setting `NCPSeqOpt.AugLag.Setting` (projection $\Pi_C$, adjoint $DG(x)^*$, AGP of Definition 3.2 and CAKKT of Definition 3.3), the remaining objects used by Theorems 3.1, 3.2, 7.2, 7.5, Remark 4 and Lemmas 7.3–7.4 of the paper. Throughout, $f:\mathbb R^n\to\mathbb R$ and $G:\mathbb R^n\to\mathbb E$ are the data of
--   $$\min_{x\in\mathbb R^n} f(x)\quad\text{subject to}\quad G(x)\in\mathcal K,\qquad \text{(NCP)}$$
--   with $\mathbb E$ a finite-dimensional real inner product space, $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone, $\mathcal K^\circ=\{w:\langle w,k\rangle\le0\ \forall k\in\mathcal K\}$ its polar, and $\Omega=\{x:G(x)\in\mathcal K\}$ the feasible set.
--
--   1. **KKT (7)–(8).** A feasible $\bar x$ is a KKT point if some $\bar\Lambda\in\mathcal K^\circ$ satisfies $\nabla f(\bar x)+DG(\bar x)^*\bar\Lambda=0$ and $\langle\bar\Lambda,G(\bar x)\rangle=0$.
--   2. **TAKKT (Definition 3.1).** A feasible $\bar x$ satisfies TAKKT if there are $x^k\to\bar x$ and $\Lambda^k\in\mathcal K^\circ$ with $\nabla f(x^k)+DG(x^k)^*\Lambda^k\to0$ (9) and $\langle\Lambda^k,G(x^k)\rangle\to0$ (10).
--   3. **AKKT (Definition 5.1).** A feasible $\bar x$ satisfies AKKT if there are $y^k\to0$ in $\mathbb E$, $x^k\to\bar x$ and $\Lambda^k\in\mathcal K^\circ$ with (9), $G(x^k)+y^k\in\mathcal K$ and $\langle\Lambda^k,G(x^k)+y^k\rangle=0$ for every $k$ (32).
--   4. **Local minimizer.** $\bar x\in\Omega$ and $f(\bar x)\le f(x)$ for all $x\in\Omega$ with $\|x-\bar x\|\le\delta$, for some $\delta>0$.
--   5. **(NLP) and AGP as in (4).** For $\mathbb E=\mathbb R^m$ and $\mathcal K=\mathbb R^m_-=\{z:z_i\le0\ \forall i\}$, let
--   $$L(\Omega,x)=\{d\in\mathbb R^n:\ \min\{0,G_i(x)\}+\nabla G_i(x)^\top d\le0\ \text{ for all } i \text{ with } G_i(\bar x)=0\}.$$
--   AGP as in (4) holds at a feasible $\bar x$ if some $x^k\to\bar x$ has $\|\Pi_{L(\Omega,x^k)}(-\nabla f(x^k))\|\to0$.
--   6. **The sets of Definition 7.1.** For $x\in\mathbb R^n$ and $r\in\mathbb R$,
--   $$\begin{aligned}\mathbb K_A(x,r)&=\{DG(x)^*\Lambda:\ \|y\|\le r,\ \Lambda\in\mathcal K^\circ,\ G(x)+y\in\mathcal K\cap\{\Lambda\}^\perp\},\\ \mathbb K_T(x,r)&=\{DG(x)^*\Lambda:\ |\langle\Lambda,G(x)\rangle|\le r,\ \Lambda\in\mathcal K^\circ\},\\ \mathbb K_{AGP}(x,r)&=\{DG(x)^*\Lambda:\ |\langle\Lambda,\Pi_{\mathcal K}(G(x))\rangle|\le r,\ \Lambda\in\mathcal K^\circ\},\\ \mathbb K_C(x,r)&=\{DG(x)^*\Lambda:\ \max\{|\langle\Lambda,\Pi_{\mathcal K}(G(x))\rangle|,|\langle\Lambda,\Pi_{\mathcal K^\circ}(G(x))\rangle|\}\le r,\ \Lambda\in\mathcal K^\circ\}.\end{aligned}$$
--   7. **Outer semicontinuity and regularity.** The sequential outer limit of $\Gamma:\mathbb R^n\times\mathbb R\rightrightarrows\mathbb R^n$ at $\bar z$ is $\{\bar w:\exists (z^k,w^k)\to(\bar z,\bar w),\ w^k\in\Gamma(z^k)\}$, and $\Gamma$ is outer semicontinuous at $\bar z$ when this set is contained in $\Gamma(\bar z)$. AKKT-, TAKKT-, AGP- and CAKKT-regularity at $\bar x$ mean that $(x,r)\mapsto\mathbb K_A$, $\mathbb K_T$, $\mathbb K_{AGP}$, respectively $\mathbb K_C$, is outer semicontinuous at $(\bar x,0)$.
--   8. **Cones and Abadie's CQ (p. 22).** $T_S(z)=\{d:\exists t_k\downarrow0,\ d^k\to d,\ z+t_kd^k\in S\}$ is the tangent cone of a set $S$ (used for $S=\Omega\subseteq\mathbb R^n$ and $S=\mathcal K\subseteq\mathbb E$), $L_\Omega(\bar x)=\{d:DG(\bar x)d\in T_{\mathcal K}(G(\bar x))\}$ is the linearized tangent cone, and Abadie's CQ holds at $\bar x$ when $T_\Omega(\bar x)=L_\Omega(\bar x)$ and $\mathbb K_C(\bar x,0)$ is closed.
--
--   These objects state the paper's characterization of the four regularity conditions as the weakest strict constraint qualifications for the corresponding sequential optimality conditions, and their relation to Abadie's CQ.
--
--   **Formalization Note** The outer limit is the published `StrictCQ.AGP.outerLimitWithin` with the whole space $\mathbb R^n\times\mathbb R$ as domain; $T_\Omega$ is the published Bouligand cone `StrictCQ.CAKKT.tangentCone` on $\mathbb R^n$, and `tangentConeE` is the same definition on $\mathbb E$. "$t_k\downarrow0$" is encoded as $t_k>0$, $t_k\to0$, which gives the same cone (pass to a decreasing subsequence). The page prints $|y|$ in $\mathbb K_A$; since $y\in\mathbb E$ this is the norm $\|y\|$. In $L(\Omega,x)$, $\nabla G_i(x)^\top d$ is the $i$-th coordinate of $DG(x)d$. $\Pi_{L(\Omega,x)}$ uses the published `proj`, which is the true projection because $L(\Omega,x)$ is a nonempty ($0\in L(\Omega,x)$) closed convex set. The sets of Definition 7.1 are empty for $r<0$. KKT, TAKKT, AKKT and AGP (4) include feasibility of $\bar x$, as the definitions are stated at a feasible point; the regularity conditions and Abadie's CQ do not, and the theorems assume feasibility.
--
--   Differences from the source:
--   - encoding: |y| in 𝕂_A → ‖y‖; reason: y belongs to the inner product space 𝔼; this is its norm.
--   - encoding: t_k ↓ 0 in the tangent cone → t_k > 0 and t_k → 0; reason: the same cone results by passing to a strictly decreasing subsequence.
--   - encoding: ∇G_i(x)ᵀd → the i-th coordinate of DG(x)d; reason: these are equal under the standing C¹ assumption on G.
--   - encoding: local minimizer of (NCP) → minimality on the feasible set in a closed ball of positive radius; reason: equivalent to neighbourhood minimality by shrinking the radius, as in the proof on p. 7.
--   - encoding: the sequential outer limit and the regular and limiting normal cones → published outerLimitWithin, regNormal and limNormal; reason: their bodies are exactly the sequential and epsilon formulations of the objects on pp. 3 and 22; no extra constraint condition is used.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), §2.1 p. 3 (outer limit), (4) p. 4, (7)–(8) and Definition 3.1 p. 5, Definition 5.1 p. 12, Definition 7.1 p. 21, Abadie's CQ and cones p. 22

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting
import Definitions.Def_StrictCQ_CAKKT_Setting

namespace NCPSeqOpt.AugLag.Supplement

open MoreauProx.Decomposition NCPSeqOpt.AugLag
open scoped InnerProductSpace
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ}

/-- The feasible set `Ω = {x ∈ ℝⁿ : G(x) ∈ 𝒦}` of (NCP), p. 1. -/
def feasSet (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | G x ∈ K}

/-- The KKT conditions (7)–(8), p. 5, at a feasible point `x̄`: there is `Λ̄ ∈ 𝒦°` with
`∇f(x̄) + DG(x̄)*Λ̄ = 0` and `⟨Λ̄, G(x̄)⟩ = 0`. -/
def IsKKT (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  G xbar ∈ K ∧ ∃ Λ ∈ polarCone K, gradient f xbar + adjD G xbar Λ = 0 ∧ ⟪Λ, G xbar⟫_ℝ = 0

/-- Definition 3.1 (TAKKT), p. 5: `x̄` is feasible and there are sequences `x^k → x̄` and
`Λ^k ∈ 𝒦°` with `∇f(x^k) + DG(x^k)*Λ^k → 0` (9) and `⟨Λ^k, G(x^k)⟩ → 0` (10). -/
def IsTAKKT (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  G xbar ∈ K ∧ ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (Λ : ℕ → E),
    (∀ k, Λ k ∈ polarCone K) ∧
    Tendsto x atTop (𝓝 xbar) ∧
    Tendsto (fun k => gradient f (x k) + adjD G (x k) (Λ k)) atTop (𝓝 0) ∧
    Tendsto (fun k => ⟪Λ k, G (x k)⟫_ℝ) atTop (𝓝 0)

/-- Definition 5.1 (AKKT), p. 12: `x̄` is feasible and there are sequences `y^k → 0` in `𝔼`,
`x^k → x̄` and `Λ^k ∈ 𝒦°` such that (9) holds and, for every `k`, `G(x^k) + y^k ∈ 𝒦` and
`⟨Λ^k, G(x^k) + y^k⟩ = 0` (32). -/
def IsAKKT (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  G xbar ∈ K ∧ ∃ (y : ℕ → E) (x : ℕ → EuclideanSpace ℝ (Fin n)) (Λ : ℕ → E),
    (∀ k, Λ k ∈ polarCone K) ∧
    Tendsto y atTop (𝓝 0) ∧
    Tendsto x atTop (𝓝 xbar) ∧
    Tendsto (fun k => gradient f (x k) + adjD G (x k) (Λ k)) atTop (𝓝 0) ∧
    (∀ k, G (x k) + y k ∈ K) ∧
    (∀ k, ⟪Λ k, G (x k) + y k⟫_ℝ = 0)

/-- A local minimizer of (NCP) (p. 7): `x̄` is feasible and, for some `δ > 0`,
`f(x̄) ≤ f(x)` for every feasible `x` in the closed ball `B[x̄, δ]`. -/
def IsLocalMinNCP (f : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → E)
    (K : Set E) (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  G xbar ∈ K ∧ ∃ δ > (0 : ℝ), ∀ x ∈ Metric.closedBall xbar δ, G x ∈ K → f xbar ≤ f x

/-! ### (NLP) and AGP as in (4), p. 4 -/

/-- The nonpositive orthant `ℝᵐ₋ = {z ∈ ℝᵐ : z_i ≤ 0 for all i}`, the cone of (NLP), p. 4. -/
def negOrthant (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {z | ∀ i, z i ≤ 0}

/-- The set `L(Ω, x) := {d ∈ ℝⁿ : min{0, G_i(x)} + ∇G_i(x)ᵀ d ≤ 0 for all i with G_i(x̄) = 0}`
of (4), p. 4. The index set is the set of constraints active at `x̄`; `∇G_i(x)ᵀ d` is the `i`-th
coordinate of `DG(x) d`. -/
def linL {m : ℕ} (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xbar x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | ∀ i, G xbar i = 0 → min 0 (G x i) + (fderiv ℝ G x d) i ≤ 0}

/-- AGP as in (4), p. 4, for (NLP): `x̄` is feasible and there is a sequence `x^k → x̄` with
`‖Π_{L(Ω,x^k)}(−∇f(x^k))‖ → 0`. -/
def IsAGP4 {m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  G xbar ∈ negOrthant m ∧ ∃ x : ℕ → EuclideanSpace ℝ (Fin n),
    Tendsto x atTop (𝓝 xbar) ∧
    Tendsto (fun k => ‖proj (linL G xbar (x k)) (-gradient f (x k))‖) atTop (𝓝 0)

/-! ### Definition 7.1, p. 21: the sets `𝕂_A, 𝕂_T, 𝕂_AGP, 𝕂_C` and the regularity conditions -/

/-- `𝕂_A(x, r) := {DG(x)*Λ : ‖y‖ ≤ r, Λ ∈ 𝒦°, G(x) + y ∈ 𝒦 ∩ {Λ}^⊥}` (the page prints `|y|`). -/
def KA (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {w | ∃ Λ ∈ polarCone K, ∃ y : E, ‖y‖ ≤ r ∧ G x + y ∈ K ∧ ⟪Λ, G x + y⟫_ℝ = 0 ∧
    adjD G x Λ = w}

/-- `𝕂_T(x, r) := {DG(x)*Λ : |⟨Λ, G(x)⟩| ≤ r, Λ ∈ 𝒦°}`. -/
def KT (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {w | ∃ Λ ∈ polarCone K, |⟪Λ, G x⟫_ℝ| ≤ r ∧ adjD G x Λ = w}

/-- `𝕂_AGP(x, r) := {DG(x)*Λ : |⟨Λ, Π_𝒦(G(x))⟩| ≤ r, Λ ∈ 𝒦°}`. -/
def KAGP (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {w | ∃ Λ ∈ polarCone K, |⟪Λ, proj K (G x)⟫_ℝ| ≤ r ∧ adjD G x Λ = w}

/-- `𝕂_C(x, r) := {DG(x)*Λ : max{|⟨Λ, Π_𝒦(G(x))⟩|, |⟨Λ, Π_𝒦°(G(x))⟩|} ≤ r, Λ ∈ 𝒦°}`. -/
def KC (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {w | ∃ Λ ∈ polarCone K,
    max |⟪Λ, proj K (G x)⟫_ℝ| |⟪Λ, proj (polarCone K) (G x)⟫_ℝ| ≤ r ∧ adjD G x Λ = w}

/-- Outer semicontinuity (§2.1, p. 3) of a set-valued map `Γ : ℝⁿ × ℝ ⇒ ℝⁿ` at `z̄`: the
sequential (Painlevé–Kuratowski) outer limit `limsup_{z → z̄} Γ(z)` is contained in `Γ(z̄)`.
The outer limit is the published `StrictCQ.AGP.outerLimitWithin` with the whole space as domain:
`{w̄ : ∃ (z^k, w^k) → (z̄, w̄), w^k ∈ Γ(z^k)}`. -/
def IsOuterSemicontAt (Γ : EuclideanSpace ℝ (Fin n) × ℝ → Set (EuclideanSpace ℝ (Fin n)))
    (zbar : EuclideanSpace ℝ (Fin n) × ℝ) : Prop :=
  StrictCQ.AGP.outerLimitWithin Γ Set.univ zbar ⊆ Γ zbar

/-- AKKT-regularity at `x̄` (Definition 7.1): `(x, r) ↦ 𝕂_A(x, r)` is outer semicontinuous at
`(x̄, 0)`. -/
def IsAKKTRegular (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsOuterSemicontAt (fun p => KA G K p.1 p.2) (xbar, 0)

/-- TAKKT-regularity at `x̄` (Definition 7.1), with `𝕂_T`. -/
def IsTAKKTRegular (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsOuterSemicontAt (fun p => KT G K p.1 p.2) (xbar, 0)

/-- AGP-regularity at `x̄` (Definition 7.1), with `𝕂_AGP`. -/
def IsAGPRegular (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsOuterSemicontAt (fun p => KAGP G K p.1 p.2) (xbar, 0)

/-- CAKKT-regularity at `x̄` (Definition 7.1), with `𝕂_C`. -/
def IsCAKKTRegular (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  IsOuterSemicontAt (fun p => KC G K p.1 p.2) (xbar, 0)

/-! ### Tangent cones and Abadie's CQ, p. 22 -/

/-- The (Bouligand) tangent cone `T_S(z) := {d : ∃ t_k ↓ 0, d^k → d with z + t_k d^k ∈ S}` of a
set `S ⊆ 𝔼`, p. 22, with `t_k > 0`, `t_k → 0`. Same shape as the published
`StrictCQ.CAKKT.tangentCone`, which is the case `𝔼 = ℝⁿ`. -/
def tangentConeE (S : Set E) (z : E) : Set E :=
  {d | ∃ t : ℕ → ℝ, ∃ dk : ℕ → E, (∀ k, 0 < t k) ∧
    Tendsto t atTop (𝓝 0) ∧ Tendsto dk atTop (𝓝 d) ∧ ∀ k, z + t k • dk k ∈ S}

/-- The linearized tangent cone `L_Ω(x̄) := {d ∈ ℝⁿ : DG(x̄) d ∈ T_𝒦(G(x̄))}`, p. 22. -/
def linTangentCone (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | fderiv ℝ G xbar d ∈ tangentConeE K (G xbar)}

/-- Abadie's CQ at `x̄`, p. 22: `T_Ω(x̄) = L_Ω(x̄)` and the set
`𝕂_C(x̄, 0) = {DG(x̄)*Λ : ⟨Λ, G(x̄)⟩ = 0, Λ ∈ 𝒦°}` is closed. `T_Ω(x̄)` is the published
Bouligand tangent cone `StrictCQ.CAKKT.tangentCone` of `Ω ⊆ ℝⁿ`. -/
def IsAbadieCQ (G : EuclideanSpace ℝ (Fin n) → E) (K : Set E)
    (xbar : EuclideanSpace ℝ (Fin n)) : Prop :=
  StrictCQ.CAKKT.tangentCone (feasSet G K) xbar = linTangentCone G K xbar ∧
    IsClosed (KC G K xbar 0)

end NCPSeqOpt.AugLag.Supplement


