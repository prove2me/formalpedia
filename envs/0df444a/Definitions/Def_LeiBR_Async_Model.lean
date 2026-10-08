-- Prove2me | Definitions.Def_LeiBR_Async_Model
-- name    : LeiBR_Async_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:06:19.559613+00:00
-- url     : https://prove2.me/theorems/419108cc-54b7-466b-bbf2-8a0d9cf202a0
-- title:
--   Assumption 1, the proximal best response (7), $\zeta_{i,\min}$, $\zeta_{ij,\max}$, $\Gamma$ (3)–(4), $\|\Gamma\|_\infty$, Assumption 5 and $Q_i$
-- statement:
--   This definition fixes the stochastic Nash game of the paper and the constants of its analysis. The players, profiles and $X = \prod_i X_i$ are those of the game definition.
--
--   **Assumption 1** is split in two parts.
--
--   1. (a) Every $X_i$ is nonempty, closed, compact and convex. (b) There are open convex sets $U_i \supseteq X_i$ such that every $f_i$ is twice continuously differentiable, as a function of the whole profile, on $\prod_j U_j$, and $z \mapsto f_i(z, y_{-i})$ is convex on $U_i$ for every $y \in X$.
--   2. Let $\xi : \Omega \to \mathbb R^d$ be a random vector on a probability space $(\Omega,\mathcal F,\mathbb P)$ and $\psi_i(x;\xi)$ a scalar function. On profiles with $x_j \in U_j$ (for open sets $U_j \supseteq X_j$), $\psi_i(x;\xi)$ is integrable and $f_i(x) = \mathbb E[\psi_i(x;\xi)]$. (c) For $y \in X$, $z \in U_i$ and every $\omega$, $z \mapsto \psi_i(z, y_{-i}; \xi(\omega))$ has gradient $\nabla_{x_i}\psi_i(z, y_{-i};\xi(\omega))$ at $z$, and $\nabla_{x_i} f_i(z, y_{-i}) = \mathbb E[\nabla_{x_i}\psi_i(z, y_{-i};\xi)]$. (d) There are $M_i > 0$ with $\mathbb E[\|\nabla_{x_i}\psi_i(x;\xi)\|^2] \le M_i^2$ for all $x \in X$.
--
--   For $\mu > 0$ the **proximal best response** of player $i$ to a profile $y \in X$ is
--   $$\hat x_i(y) = \operatorname*{argmin}_{x_i \in X_i}\Big[f_i(x_i, y_{-i}) + \frac{\mu}{2}\|x_i - y_i\|^2\Big].$$
--
--   The curvature constants (4) are
--   $$\zeta_{i,\min} = \inf_{x\in X}\lambda_{\min}\big(\nabla^2_{x_i} f_i(x)\big),\qquad \zeta_{ij,\max} = \sup_{x \in X}\big\|\nabla^2_{x_i x_j} f_i(x)\big\| \quad (j \ne i),$$
--   where $\lambda_{\min}(A)$ is the smallest eigenvalue of $(A + A^\top)/2$ and $\|\cdot\|$ is the spectral norm. The $N\times N$ matrix $\Gamma$ of (3) has entries
--   $$\gamma_{ii} = \frac{\mu}{\mu + \zeta_{i,\min}},\qquad \gamma_{ij} = \frac{\zeta_{ij,\max}}{\mu + \zeta_{i,\min}}\quad (j\neq i),$$
--   and $a_\infty = \|\Gamma\|_\infty = \max_i \sum_j |\gamma_{ij}|$ is its maximum absolute row sum.
--
--   **Assumption 5** (strict diagonal dominance) requires $\zeta_{i,\min} > \sum_{j\neq i}\zeta_{ij,\max}$ for every $i$.
--
--   Finally $Q_i = 2M_i^2/\mu^2 + 2D_{X_i}^2$, with $D_{X_i} = \sup\{\|x_i - x_i'\| : x_i, x_i' \in X_i\}$ the diameter of $X_i$ (16).
--
--   These are the objects in which the asynchronous rate and complexity results are stated.
--
--   **Formalization Note** The page asks only for $C^2$ regularity in $x_i$, but (4) uses the mixed blocks $\nabla^2_{x_ix_j}f_i$, so joint $C^2$ regularity is assumed; nonemptiness of $X_i$ is implicit on the page. Parts (c)–(d) carry their own open sets $U_i$, and the integrability that makes each expectation meaningful is stated explicitly. The proximal best response is a predicate on a map $\hat x$ (`IsProxBR`): for $y \in X$, $\hat x_i(y) \in X_i$ minimizes the proximal objective; values off $X$ are unconstrained. $\lambda_{\min}$ of the Hessian block is written as the smallest Rayleigh quotient $\inf_{\|v\|=1} v^\top \nabla^2_{x_i} f_i(x) v$, and the block norm as $\sup_{\|v\|,\|w\|\le 1}|v^\top \nabla^2_{x_ix_j} f_i(x) w|$, both through the second Fréchet derivative of $f_i$ applied to the embedded vectors `Pi.single i v`. These are real `sInf`/`sSup`; under Assumption 1 the sets are bounded, and for $n_i \ge 1$ nonempty (if $n_i = 0$ the infimum defaults to $0$, which Assumption 5 then excludes). $\|\Gamma\|_\infty$ is written as a `Finset.sup` of row sums, equal to $0$ when $N=0$.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 4 (Notations, (SNash_i)), p. 5 (Assumption 1, (2), (3), (4)), p. 6 ((7)), p. 8 ((16)), p. 10 (Q_i in Lemma 3), p. 18 (Assumption 5 and a_∞ = ‖Γ‖_∞)

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Sync_StochGame
import Definitions.Def_LeiBR_Sync_Algorithm1

namespace LeiBR.Async

open MeasureTheory

/-- **Assumption 1(a),(b)** (Lei, Shanbhag, Pang & Sen, arXiv:1704.04578v2, p. 5), the deterministic
part, with the regularity that (4) needs.

(a) every `X_i` is closed, compact, convex and nonempty;
(b) there are open convex sets `U_i ⊇ X_i` such that every `f_i` is twice continuously differentiable
(jointly in the whole profile) on `∏_j U_j`, and `z ↦ f_i(z, y_{-i})` is convex on `U_i` for every
`y ∈ X`.

Formalization Note: the page asks for `f_i` to be `C²` in `x_i`; (4) uses the mixed blocks
`∇²_{x_i x_j} f_i`, so joint `C²` regularity is assumed. Nonemptiness of `X_i` is implicit on the page. -/
structure Assumption1ab {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) : Prop where
  closed : ∀ i, IsClosed (X i)
  compact : ∀ i, IsCompact (X i)
  convex : ∀ i, Convex ℝ (X i)
  nonempty : ∀ i, (X i).Nonempty
  smooth : ∃ U : ∀ i, Set (LeiBR.Sync.Strat n i),
    (∀ i, IsOpen (U i) ∧ Convex ℝ (U i) ∧ X i ⊆ U i) ∧
    (∀ i, ContDiffOn ℝ 2 (f i) (Set.univ.pi U)) ∧
    (∀ i, ∀ y ∈ profileSet X, ConvexOn ℝ (U i) (fun z : LeiBR.Sync.Strat n i => f i (Function.update y i z)))

/-- **Assumption 1(c),(d)** and the definition of `f_i` in (SNash_i) (p. 4–5), the stochastic part.
`ξ0 : Ω → ℝ^d` is the random vector `ξ`, `ψ i x s = ψ_i(x; s)` and `gψ i x s = ∇_{x_i} ψ_i(x; s)`.

(SNash) `f_i(x) = E[ψ_i(x; ξ)]` (with `ψ_i(x; ξ)` integrable) at every profile `x` with `x_j ∈ U_j`;
(c) for all `y ∈ X`, `z ∈ U_i` and every `ω`, `z ↦ ψ_i(z, y_{-i}; ξ(ω))` has gradient
`∇_{x_i}ψ_i(z, y_{-i}; ξ(ω))` at `z`, this gradient is integrable, and
`∇_{x_i} f_i(z, y_{-i}) = E[∇_{x_i}ψ_i(z, y_{-i}; ξ)]`;
(d) `M_i > 0` and `E[‖∇_{x_i}ψ_i(x; ξ)‖²] ≤ M_i²` for all `x ∈ X` (the squared norm integrable).

`U_i` is an open set containing `X_i` (see `Assumption1`). -/
structure Assumption1cd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N d : ℕ}
    {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (U : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (ξ0 : Ω → EuclideanSpace ℝ (Fin d)) (M : Fin N → ℝ) : Prop where
  meas_ξ : Measurable ξ0
  expect : ∀ i, ∀ x ∈ Set.univ.pi U,
    Integrable (fun ω => ψ i x (ξ0 ω)) P ∧ f i x = ∫ ω, ψ i x (ξ0 ω) ∂P
  grad : ∀ i, ∀ y ∈ profileSet X, ∀ z ∈ U i,
    (∀ ω, HasGradientAt (fun z' : LeiBR.Sync.Strat n i => ψ i (Function.update y i z') (ξ0 ω))
        (gψ i (Function.update y i z) (ξ0 ω)) z) ∧
    Integrable (fun ω => gψ i (Function.update y i z) (ξ0 ω)) P ∧
    partialGrad (f i) i (Function.update y i z) = ∫ ω, gψ i (Function.update y i z) (ξ0 ω) ∂P
  M_pos : ∀ i, 0 < M i
  moment : ∀ i, ∀ x ∈ profileSet X,
    Integrable (fun ω => ‖gψ i x (ξ0 ω)‖ ^ 2) P ∧ ∫ ω, ‖gψ i x (ξ0 ω)‖ ^ 2 ∂P ≤ M i ^ 2

/-- **Assumption 1** (p. 5): parts (a)–(b), and parts (c)–(d) over some open sets `U_i ⊇ X_i`
("over an open set containing `X_i`"). -/
def Assumption1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N d : ℕ}
    {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (ξ0 : Ω → EuclideanSpace ℝ (Fin d)) (M : Fin N → ℝ) : Prop :=
  Assumption1ab X f ∧
    ∃ U : ∀ i, Set (LeiBR.Sync.Strat n i), (∀ i, IsOpen (U i) ∧ X i ⊆ U i) ∧ Assumption1cd P X U f ψ gψ ξ0 M

/-- `‖A‖_∞ = max_i Σ_j |a_ij|`, the maximum absolute row sum (the operator norm induced by the
`∞`-norm); equal to `0` when there are no rows. -/
noncomputable def normInf {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ((Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ : NNReal) : ℝ)

/-- **Assumption 5** (Strict Diagonal Dominance, p. 18): `ζ_{i,min} > Σ_{j ≠ i} ζ_{ij,max}` for every `i`. -/
def Assumption5 {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, LeiBR.Sync.zetaMax X f i j < LeiBR.Sync.zetaMin X f i

end LeiBR.Async


