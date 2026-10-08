-- Prove2me | Definitions.Def_ProgHedging_Convex_Duality
-- name    : ProgHedging_Convex_Duality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:33.251165+00:00
-- url     : https://prove2.me/theorems/b8563087-4931-42f3-b837-b211ab58bb05
-- title:
--   The Lagrangian L, the dual (D), its objective G, min (P), sup (D), optimality conditions (4.1)/(4.4), saddle points, Φ, α̂ and ℓ (pp. 8–26)
-- statement:
--   Within the scenario model (policies $X$, price systems $W\in\mathcal M$, admissible set $\mathcal C$, implementable subspace $\mathcal N$, objective $F$), define the following.
--
--   1. The **Lagrangian** $L(X,W)=F(X)+\langle X,W\rangle$ (2.9).
--   2. The **dual objective** $G(W)=\inf_{X\in\mathcal C}L(X,W)\in[-\infty,\infty)$ (4.20).
--   3. The optimal values $\min(P)=\inf\{F(X)\mid X\in\mathcal C\cap\mathcal N\}$ (equal to $+\infty$ when $\mathcal C\cap\mathcal N=\emptyset$) and $\sup(D)=\sup\{G(W)\mid W\in\mathcal M\}$.
--   4. $X^*$ **solves (P)** if $X^*\in\mathcal C\cap\mathcal N$ and $F(X^*)\le F(X)$ for all $X\in\mathcal C\cap\mathcal N$; $W^*$ **solves (D)** if $W^*\in\mathcal M$, $G(W^*)>-\infty$, and $G(W)\le G(W^*)$ for all $W\in\mathcal M$ — i.e. $W^*$ maximizes $G$ over $\mathcal D\cap\mathcal M$ with $\mathcal D=\{W\mid G(W)>-\infty\}$ (4.21).
--   5. $(X^*,W^*)\in\mathcal N\times\mathcal M$ is a **saddle point** of $L$ if $X^*\in\mathcal C$, $L(X^*,W^*)\le L(X,W^*)$ for all $X\in\mathcal C$, and $L(X^*,W)\le L(X^*,W^*)$ for all $W\in\mathcal M$.
--   6. The **subgradient set** $\partial f(x)=\{y\mid f(z)\ge f(x)+y\cdot(z-x)\ \forall z\}$, and the **optimality conditions** (4.1), (4.4): $X^*\in\mathcal N$, $W^*\in\mathcal M$ and, for every $s$, $X^*(s)\in C_s$ and
--   $$
--   -W^*(s)\in\partial f_s(X^*(s))+N_{C_s}(X^*(s)),
--   $$
--   with $N_{C}(x)=\{w\mid w\cdot(y-x)\le0\ \forall y\in C\}$ the normal cone of convex analysis.
--   7. The **perturbation function** $\Phi(U)=\inf\{F(X)\mid X\in\mathcal C,\ KX=U\}$, regarded as $+\infty$ when no such $X$ exists (4.22); the value $\hat\alpha=\inf_{X\in\mathcal C}F(X)$ (3.2); and $\ell(V,W)=\inf\{F(X)+\langle X,W\rangle\mid X\in\mathcal C,\ \hat X=V\}$ (5.31).
--
--   These are the objects in which the paper states its duality theory (Theorems 4.2, 4.6, Proposition 4.5) and the saddle-point form of the algorithm (Proposition 5.3).
--
--   **Formalization Note.** All infima and suprema are taken in `EReal`, so an empty infimum is $+\infty$ and $G$ may take the value $-\infty$; `SolvesD` requires $G(W^*)>-\infty$ explicitly, so that (D) is not trivially solved when $G\equiv-\infty$. The paper's $\min$ in (3.2), (4.22) is written as an infimum; that it is attained is the content of Propositions 3.1 and 4.5. The subgradient set and the normal cone are those of convex analysis, which is what the paper's $\partial f_s$ and $N_{C_s}$ mean in the convex case (p. 14); these objects are only used under the convex-case hypothesis. The normal cone is the published definition `FirstOrderOpt.ConvexTheory.normalCone`.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), pp. 8, 10, 14–15, 17–18, 26, (2.9), (3.2), (4.1), (4.4), (4.20)–(4.22), (5.31), Theorem 4.2

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem
import Definitions.Def_FirstOrderOpt_ConvexTheory_normalCone

open scoped RealInnerProductSpace Pointwise

namespace ProgHedging.Convex

/-- (2.9), p. 8: the ordinary Lagrangian `L(X, W) = F(X) + ⟨X, W⟩`. -/
noncomputable def Problem.L {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (X W : Policy S n) : ℝ :=
  pr.F X + pr.ip X W

/-- (4.20), p. 18: the dual objective `G(W) = inf_{X ∈ 𝒞} L(X, W)`, valued in `[-∞, ∞]`. -/
noncomputable def Problem.G {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (W : Policy S n) : EReal :=
  ⨅ X ∈ pr.adm, ((pr.L X W : ℝ) : EReal)

/-- p. 7, (P): `min (P) = inf {F(X) | X ∈ 𝒞 ∩ 𝒩}`, equal to `∞` when `𝒞 ∩ 𝒩 = ∅`. -/
noncomputable def Problem.minP {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) : EReal :=
  ⨅ X ∈ pr.adm ∩ pr.N, ((pr.F X : ℝ) : EReal)

/-- p. 18, (D): `sup (D) = sup {G(W) | W ∈ 𝒟 ∩ ℳ}`; the supremum over all of `ℳ` has the same
value, since `G(W) = −∞` for `W ∉ 𝒟`. -/
noncomputable def Problem.supD {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) : EReal :=
  ⨆ W ∈ pr.M, pr.G W

/-- `X*` is an optimal solution of (P): feasible (`X* ∈ 𝒞 ∩ 𝒩`) and `F(X*) ≤ F(X)` for every
feasible `X`. -/
def Problem.SolvesP {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (Xs : Policy S n) : Prop :=
  Xs ∈ pr.adm ∩ pr.N ∧ ∀ X ∈ pr.adm ∩ pr.N, pr.F Xs ≤ pr.F X

/-- `W*` is an optimal solution of (D): `W* ∈ 𝒟 ∩ ℳ` (so `G(W*) > −∞`, (4.21)) and
`G(W) ≤ G(W*)` for every `W ∈ ℳ`. -/
def Problem.SolvesD {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (Ws : Policy S n) : Prop :=
  Ws ∈ pr.M ∧ ⊥ < pr.G Ws ∧ ∀ W ∈ pr.M, pr.G W ≤ pr.G Ws

/-- Theorem 4.2, p. 17: `(X*, W*) ∈ 𝒩 × ℳ` is a saddle point of `L` relative to minimizing over
`X ∈ 𝒞` and maximizing over `W ∈ ℳ`. -/
def Problem.IsSaddle {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (Xs Ws : Policy S n) : Prop :=
  Xs ∈ pr.N ∧ Ws ∈ pr.M ∧ Xs ∈ pr.adm ∧ (∀ X ∈ pr.adm, pr.L Xs Ws ≤ pr.L X Ws) ∧
    ∀ W ∈ pr.M, pr.L Xs W ≤ pr.L Xs Ws

/-- p. 14: the subgradient set of convexity theory, `∂f(x) = {y | f(z) ≥ f(x) + y·(z − x) ∀ z}`. -/
def subdiff {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∀ z, f x + ⟪y, z - x⟫ ≤ f z}

/-- (4.1) and (4.4), pp. 14–15, in the convex case: `X* ∈ 𝒩`, `X*(s) ∈ C_s`, `W* ∈ ℳ` and
`−W*(s) ∈ ∂f_s(X*(s)) + N_{C_s}(X*(s))` for all `s`. -/
def Problem.OptCond {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (Xs Ws : Policy S n) : Prop :=
  Xs ∈ pr.N ∧ Xs ∈ pr.adm ∧ Ws ∈ pr.M ∧
    ∀ s, -Ws s ∈ subdiff (pr.f s) (Xs s) +
      FirstOrderOpt.ConvexTheory.normalCone (pr.C s) (Xs s)

/-- (4.22), p. 18: `Φ(U) = min {F(X) | X ∈ 𝒞, KX = U}`, regarded as `∞` when no such `X` exists. -/
noncomputable def Problem.Phi {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (U : Policy S n) : EReal :=
  ⨅ X ∈ {X | X ∈ pr.adm ∧ pr.K X = U}, ((pr.F X : ℝ) : EReal)

/-- (3.2), p. 10: `α̂ = inf_{X ∈ 𝒞} F(X)` (Proposition 3.1 says the infimum is attained). -/
noncomputable def Problem.alphaHat {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) :
    EReal :=
  ⨅ X ∈ pr.adm, ((pr.F X : ℝ) : EReal)

/-- (5.31), p. 26: `ℓ(V, W) = inf {F(X) + ⟨X, W⟩ | X ∈ 𝒞, X̂ = V}`. -/
noncomputable def Problem.ell {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T)
    (V W : Policy S n) : EReal :=
  ⨅ X ∈ {X | X ∈ pr.adm ∧ pr.J X = V}, ((pr.F X + pr.ip X W : ℝ) : EReal)

end ProgHedging.Convex


