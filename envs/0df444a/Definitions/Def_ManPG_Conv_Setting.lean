-- Prove2me | Definitions.Def_ManPG_Conv_Setting
-- name    : ManPG_Conv_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:47.619499+00:00
-- url     : https://prove2.me/theorems/087a8dd0-3d46-460f-99f0-587bcd08f623
-- title:
--   Problem (1.1) on St(n, r) with assumptions (i)–(ii), retractions with (3.1)–(3.2), subproblem (4.3), Algorithm 1 (ManPG), Definitions 3.3 and 5.4
-- statement:
--   The model of the convergence analysis of the manifold proximal gradient method (ManPG). Let $\mathcal M=\mathrm{St}(n,r)$, and let $\langle\cdot,\cdot\rangle$, $\|\cdot\|_F$, $\partial h$, $T_X\mathcal M$ and $\operatorname{Proj}_{T_X\mathcal M}$ be as in the basic definitions. The problem is
--   $$\min_{X\in\mathcal M}\ F(X):=f(X)+h(X).\tag{1.1}$$
--
--   1. **Standing assumptions** (`StandingAssumptions f ∇f h L L_h`): $r\le n$, and
--      - (i) $f:\mathbb R^{n\times r}\to\mathbb R$ is differentiable with gradient $\nabla f$, in the sense that for all $X,V$ the function $s\mapsto f(X+sV)$ has derivative $\langle\nabla f(X),V\rangle$ at $s=0$, and $\nabla f$ is $L$-Lipschitz: $\|\nabla f(X)-\nabla f(Y)\|_F\le L\|X-Y\|_F$, with $L>0$;
--      - (ii) $h:\mathbb R^{n\times r}\to\mathbb R$ is convex and $L_h$-Lipschitz: $|h(X)-h(Y)|\le L_h\|X-Y\|_F$, with $L_h\ge0$.
--
--      Both hold on the whole ambient space $\mathbb R^{n\times r}$, not only on $\mathcal M$.
--   2. **Retraction** (`RetrBounds R M₁ M₂`): a map $(X,\xi)\mapsto \mathrm{Retr}_X(\xi)$ such that $\mathrm{Retr}_X(\xi)\in\mathcal M$ and $\mathrm{Retr}_X(0)=X$ for $X\in\mathcal M$, $\xi\in T_X\mathcal M$, together with constants $M_1>0$, $M_2>0$ such that for all $X\in\mathcal M$ and $\xi\in T_X\mathcal M$
--   $$\|\mathrm{Retr}_X(\xi)-X\|_F\le M_1\|\xi\|_F,\tag{3.1}$$
--   $$\|\mathrm{Retr}_X(\xi)-(X+\xi)\|_F\le M_2\|\xi\|_F^2.\tag{3.2}$$
--   3. **Gradient bound** (`GradBound ∇f G`): $G>0$ and $\|\nabla f(X)\|_F\le G$ for all $X\in\mathcal M$.
--   4. **Stationarity** (Definition 3.3): $X$ is stationary if $X\in\mathcal M$ and $0\in\operatorname{grad}f(X)+\operatorname{Proj}_{T_X\mathcal M}(\partial h(X))$. Here $\operatorname{grad}f(X)=\operatorname{Proj}_{T_X\mathcal M}\nabla f(X)$, so the condition reads: some $G\in\partial h(X)$ satisfies $\operatorname{Proj}_{T_X\mathcal M}(\nabla f(X)+G)=0$.
--   5. **Subproblem** (4.3) with objective (5.1): for an iterate $X$ and stepsize $t>0$,
--   $$g(V)=\langle\nabla f(X),V\rangle+\frac1{2t}\|V\|_F^2+h(X+V),$$
--   and $V$ solves (4.3) if $V\in T_X\mathcal M$ and $g(V)\le g(W)$ for every $W\in T_X\mathcal M$.
--   6. **Algorithm 1 (ManPG)** with parameters $\gamma$, $t$: sequences $(X_k)$, $(V_k)$, $(\alpha_k)$ form a run if $X_0\in\mathcal M$ and, for every $k\ge0$:
--      - $V_k$ solves (4.3) at $X_k$;
--      - $\alpha_k=\gamma^{j}$ for the least $j\in\{0,1,2,\dots\}$ such that
--   $$F(\mathrm{Retr}_{X_k}(\gamma^jV_k))\le F(X_k)-\frac{\gamma^j\|V_k\|_F^2}{2t};$$
--      this is the backtracking loop started at $\alpha=1$;
--      - $X_{k+1}=\mathrm{Retr}_{X_k}(\alpha_kV_k)$.
--   7. **$\varepsilon$-stationarity** (Definition 5.4): $X$ is $\varepsilon$-stationary if $X\in\mathcal M$ and every solution $V$ of (4.3) at $X$ with $t=1/L$ satisfies $\|V\|_F\le\varepsilon/L$.
--   8. **Optimal value**: $F^*$ is the optimal value of (1.1) if $F^*\le F(X)$ for all $X\in\mathcal M$ and $F^*=F(X)$ for some $X\in\mathcal M$.
--   9. **Constants** of the proof of Lemma 5.2: $c_0=M_2G+LM_1^2/2$ and $\bar\alpha=1/(2(c_0+L_hM_2)t)$.
--
--   This is the setting of every result in the convergence analysis of ManPG (Section 5).
--
--   **Formalization Note**
--   - Assumption (i) is stated as directional derivatives along lines plus a Lipschitz gradient. This gives $f\in C^{1,1}$, which is all the analysis uses; the paper's "smooth" is not required.
--   - The retraction is any map with the listed properties. Smoothness of the retraction and condition 2 of Definition 3.4 are not imposed: (3.2) implies condition 2, and no proof uses smoothness. By Fact 3.6 every retraction on the compact manifold $\mathcal M$ qualifies, so the results hold in this greater generality.
--   - The remark "the proximal mapping of $h$ is easy to find" is computational and is omitted.
--   - The subproblem is an argmin predicate. Existence and uniqueness of its solution (strong convexity) are theorems, not part of the definition.
--   - A run is a predicate on given sequences, with the backtracking loop encoded as "the least passing $j$".
--   - $\varepsilon$-stationarity quantifies over all solutions of the subproblem. The solution is unique, so this agrees with the paper's "the solution".
--   - $F^*$ is pinned by "lower bound and attained" rather than by an infimum, so it cannot take a junk value.
-- source:
--   Chen, Ma, So, Zhang, Proximal gradient method for nonsmooth optimization over the Stiefel manifold, SIAM J. Optim. (2020), pp. 1–3, 7–10, 12–13: (1.1) and assumptions (i)–(ii), Definition 3.3, Definition 3.4 (condition 1), Fact 3.6 ((3.1)–(3.2)), (4.3), Algorithm 1, (5.1), proof of Lemma 5.2 (G, c₀, ᾱ), Definition 5.4

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel
import Definitions.Def_ManPG_Conv_Basic

open scoped Matrix

namespace ManPG.Conv

open ProjLikeRetr.Stiefel

/-- Problem (1.1) and its standing assumptions (i)–(ii), pp. 1–2, read in the ambient space
`ℝ^{n×r}` (p. 2: "interpreted when the function … is considered as a function in the ambient
Euclidean space"):
* `r ≤ n` ((1.1));
* (i) `f` is differentiable with gradient `gradf` — along every line `s ↦ f(X + sV)` the derivative
  at `s = 0` is `⟨∇f(X), V⟩` — and `∇f` is `L`-Lipschitz in the Frobenius norm, `L > 0`;
* (ii) `h` is convex and `L_h`-Lipschitz in the Frobenius norm, `L_h ≥ 0`. -/
structure StandingAssumptions {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r)
    (h : Mat n r → ℝ) (L Lh : ℝ) : Prop where
  r_le_n : r ≤ n
  L_pos : 0 < L
  hasDerivAt_line : ∀ X V : Mat n r,
    HasDerivAt (fun s : ℝ => f (X + s • V)) (frobInner (gradf X) V) 0
  grad_lipschitz : ∀ X Y : Mat n r, frobNorm (gradf X - gradf Y) ≤ L * frobNorm (X - Y)
  Lh_nonneg : 0 ≤ Lh
  h_convex : ConvexOn ℝ Set.univ h
  h_lipschitz : ∀ X Y : Mat n r, |h X - h Y| ≤ Lh * frobNorm (X - Y)

/-- The retraction `Retr_X(ξ) = R X ξ` used by Algorithm 1, with the properties the analysis uses:
it maps the tangent bundle of `M = St(n, r)` into `M`, `Retr_X(0) = X` (Definition 3.4, condition 1),
and the two bounds of Fact 3.6 with constants `M₁ > 0`, `M₂ > 0`:
(3.1) `‖R_X(ξ) − X‖_F ≤ M₁‖ξ‖_F` and (3.2) `‖R_X(ξ) − (X + ξ)‖_F ≤ M₂‖ξ‖_F²`
for all `X ∈ M`, `ξ ∈ T_X M`. -/
structure RetrBounds {n r : ℕ} (R : Mat n r → Mat n r → Mat n r) (M1 M2 : ℝ) : Prop where
  mem : ∀ X ∈ stiefel n r, ∀ ξ ∈ tangent X, R X ξ ∈ stiefel n r
  zero : ∀ X ∈ stiefel n r, R X 0 = X
  M1_pos : 0 < M1
  M2_pos : 0 < M2
  bound_3_1 : ∀ X ∈ stiefel n r, ∀ ξ ∈ tangent X, frobNorm (R X ξ - X) ≤ M1 * frobNorm ξ
  bound_3_2 : ∀ X ∈ stiefel n r, ∀ ξ ∈ tangent X,
    frobNorm (R X ξ - (X + ξ)) ≤ M2 * frobNorm ξ ^ 2

/-- Proof of Lemma 5.2, p. 12: `G > 0` bounds the Euclidean gradient on `M`,
`‖∇f(X)‖_F ≤ G` for all `X ∈ M`. -/
structure GradBound {n r : ℕ} (gradf : Mat n r → Mat n r) (G : ℝ) : Prop where
  G_pos : 0 < G
  bound : ∀ X ∈ stiefel n r, frobNorm (gradf X) ≤ G

/-- Definition 3.3, p. 7: `X ∈ M` is a stationary point of (1.1) if
`0 ∈ grad f(X) + Proj_{T_X M}(∂h(X))`; since `grad f(X) = Proj_{T_X M} ∇f(X)` and the projection is
linear, this says: some `G ∈ ∂h(X)` has `Proj_{T_X M}(∇f(X) + G) = 0`. -/
def IsStationary {n r : ℕ} (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ) (X : Mat n r) : Prop :=
  X ∈ stiefel n r ∧ ∃ G : Mat n r, IsSubgrad h X G ∧ projT X (gradf X + G) = 0

/-- (5.1), p. 11: the objective of subproblem (4.3) at the iterate `X`,
`g(V) = ⟨∇f(X), V⟩ + ‖V‖_F²/(2t) + h(X + V)`. -/
noncomputable def subObj {n r : ℕ} (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ) (X : Mat n r)
    (t : ℝ) (V : Mat n r) : ℝ :=
  frobInner (gradf X) V + frobNorm V ^ 2 / (2 * t) + h (X + V)

/-- (4.3), p. 9: `V` solves the subproblem at `X` with stepsize `t`, i.e. `V ∈ T_X M` minimizes
`g` over `T_X M`. -/
def IsSubSol {n r : ℕ} (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ) (X : Mat n r) (t : ℝ)
    (V : Mat n r) : Prop :=
  V ∈ tangent X ∧ ∀ W ∈ tangent X, subObj gradf h X t V ≤ subObj gradf h X t W

/-- Algorithm 1 (ManPG), p. 9: the sequences `X k`, `V k`, `α k` are a run of ManPG with parameters
`γ` and `t` started at `X 0 ∈ M`: in each iteration `V k` solves (4.3) at `X k`; the stepsize is
`α k = γ^j` for the first `j = 0, 1, 2, …` with
`F(Retr_{X_k}(γ^j V_k)) ≤ F(X_k) − γ^j ‖V_k‖_F²/(2t)` (the backtracking loop started at `α = 1`),
where `F = f + h`; and `X (k+1) = Retr_{X_k}(α_k V_k)`. -/
def IsManPGRun {n r : ℕ} (f : Mat n r → ℝ) (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ)
    (R : Mat n r → Mat n r → Mat n r) (γ t : ℝ) (X V : ℕ → Mat n r) (α : ℕ → ℝ) : Prop :=
  X 0 ∈ stiefel n r ∧
  ∀ k : ℕ,
    IsSubSol gradf h (X k) t (V k) ∧
    (∃ j : ℕ, α k = γ ^ j ∧
      f (R (X k) (γ ^ j • V k)) + h (R (X k) (γ ^ j • V k))
        ≤ f (X k) + h (X k) - γ ^ j * frobNorm (V k) ^ 2 / (2 * t) ∧
      ∀ i < j, f (R (X k) (γ ^ i • V k)) + h (R (X k) (γ ^ i • V k))
        > f (X k) + h (X k) - γ ^ i * frobNorm (V k) ^ 2 / (2 * t)) ∧
    X (k + 1) = R (X k) (α k • V k)

/-- Definition 5.4, p. 13: `X ∈ M` is an `ε`-stationary point of (1.1) if the solution `V` of the
subproblem (4.4) (= (4.3)) at `X` with `t = 1/L` satisfies `‖V‖_F ≤ ε/L`. -/
def IsEpsStationary {n r : ℕ} (gradf : Mat n r → Mat n r) (h : Mat n r → ℝ) (L ε : ℝ)
    (X : Mat n r) : Prop :=
  X ∈ stiefel n r ∧ ∀ V : Mat n r, IsSubSol gradf h X (1 / L) V → frobNorm V ≤ ε / L

/-- `F*` is the optimal value of (1.1): a lower bound of `F = f + h` on `M` that is attained. -/
def IsOptimalValue {n r : ℕ} (f : Mat n r → ℝ) (h : Mat n r → ℝ) (Fstar : ℝ) : Prop :=
  (∀ X ∈ stiefel n r, Fstar ≤ f X + h X) ∧ ∃ X ∈ stiefel n r, f X + h X = Fstar

/-- Proof of Lemma 5.2, p. 12: `c₀ = M₂G + LM₁²/2`. -/
noncomputable def c0 (L M1 M2 G : ℝ) : ℝ :=
  M2 * G + L * M1 ^ 2 / 2

/-- Proof of Lemma 5.2, p. 13: `ᾱ = 1/(2(c₀ + L_h M₂)t)`. -/
noncomputable def abar (L Lh M1 M2 G t : ℝ) : ℝ :=
  1 / (2 * (c0 L M1 M2 G + Lh * M2) * t)

end ManPG.Conv


