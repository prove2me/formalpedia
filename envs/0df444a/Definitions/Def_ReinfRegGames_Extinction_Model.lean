-- Prove2me | Definitions.Def_ReinfRegGames_Extinction_Model
-- name    : ReinfRegGames_Extinction_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:13:14.473431+00:00
-- url     : https://prove2.me/theorems/1e08760e-cc45-4de5-b272-d69869f5208c
-- title:
--   Definitions 2.1–2.2, (2.2), (4.4)–(4.5), (RL), (RLγ), pp. 5–18 — payoff vectors, penalty functions, choice maps, the conjugate, the Fenchel coupling and orbits of (RL)
-- statement:
--   Consider a finite game in normal form: a finite set $\mathcal N$ of players, for each player $k$ a finite set $\mathcal A_k$ of pure strategies, and payoff functions $u_k:\prod_\ell \mathcal A_\ell\to\mathbb R$. A mixed strategy of player $k$ is a point $x_k$ of the simplex $\mathcal X_k=\Delta(\mathcal A_k)$, and $u_k(x)$ denotes the multilinear extension (2.1) of $u_k$ to mixed profiles $x=(x_1,\dots,x_N)$. This module fixes the objects shared by every statement of the mission.
--
--   1. **Payoff vector (2.2).** For $\alpha\in\mathcal A_k$, $v_{k\alpha}(x)=u_k(\alpha;x_{-k})$ is the expected payoff of player $k$ when $k$ plays the pure strategy $\alpha$ and every other player $\ell$ plays $x_\ell$.
--   2. **Penalty function (Definition 2.1).** Let $\Delta=\Delta(B)$ be the simplex over a finite set $B$. A function $h:\Delta\to\mathbb R$ is a penalty function with strong convexity constant $K$ if (1) $h$ is continuous on $\Delta$; (2) $h$ is smooth on the relative interior of every face of $\Delta$, in the sense that $h\circ\gamma$ is $C^\infty$ for every $C^\infty$ curve $\gamma:(-\varepsilon,\varepsilon)\to\Delta$ that stays in the relative interior of one face; and (3) $K>0$ and
--   $$
--   h(tx_1+(1-t)x_2)\le t\,h(x_1)+(1-t)\,h(x_2)-\tfrac12 K\,t(1-t)\,\|x_1-x_2\|_2^2\qquad (x_1,x_2\in\Delta,\ t\in[0,1]).
--   $$
--   3. **Choice map (Definition 2.2).** $x=Q(y)$ means that $x\in\Delta$ maximizes $\langle y|x'\rangle-h(x')$ over $x'\in\Delta$, where $\langle y|x\rangle=\sum_\beta y_\beta x_\beta$.
--   4. **Convex conjugate (4.5), (C.1).** $h^*(y)=\max_{x\in\Delta}\{\langle y|x\rangle-h(x)\}$.
--   5. **Fenchel coupling (4.4), (C.10).** $F_h(p,y)=h(p)+h^*(y)-\langle y|p\rangle$.
--   6. **Orbits of (RLγ) and (RL).** Given rates $\gamma_k$ and a penalty function $h_k$ for each player, a pair of trajectories $(y(t),x(t))$ is an orbit of (RLγ) if for every $t\ge0$ and every player $k$, $x_k(t)=Q_k(y_k(t))$ and $\dot y_{k\alpha}(t)=\gamma_k\,v_{k\alpha}(x(t))$ (a right derivative at $t=0$). An orbit of (RL) is an orbit of (RLγ) with every $\gamma_k=1$, i.e. $\dot y_k=v_k(x)$, $x_k=Q_k(y_k)$.
--
--   These objects carry the whole analysis of the paper: the payoff vector drives the scores $y$, the penalty function turns scores into mixed strategies through the choice map, and the Fenchel coupling measures how far $Q(y)$ is from a target strategy.
--
--   **Formalization Note** The norm in (2.5) is taken to be the Euclidean norm; the paper leaves it unnamed, and since $K$ is only required to exist, the class of penalty functions does not depend on the choice, while explicit constants such as the $\tfrac12K$ of Proposition C.3 are those of the Euclidean norm. Steepness is not part of Definition 2.1 and is not assumed. The choice map is a predicate (`IsChoice`), not a chosen maximizer. The page writes (RL) in integral form $y_k(t)=y_k(0)+\int_0^t v_k(x(s))\,ds$; the differential form (3.1) used here is equivalent because $x(t)$ is continuous along an orbit, and it avoids Lean's convention that a non-integrable integral equals $0$. The conjugate is a supremum over the compact simplex; every statement using it assumes $h$ is a penalty function, so the supremum is attained.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 5–10 and 18, Definitions 2.1–2.2, (2.2), (2.5), (2.8), (4.4)–(4.5), (RL), (3.1), (RLγ); pp. 33–34, (C.1), (C.10)

import Mathlib
import Definitions.Def_agt_games

namespace ReinfRegGames.Extinction

open Finset
open scoped ContDiff

/-- The payoff (co)vector entry `v_{kα}(x) = u_k(α; x_{-k})` of (2.2), arXiv:1407.6267v2, p. 5:
player `k`'s expected payoff when `k` plays the pure strategy `α` and every other player `ℓ`
plays `x ℓ` independently. -/
noncomputable def payoffVec {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (x : ∀ k, A k → ℝ) (k : ι) (α : A k) : ℝ :=
  AGT.expectedPayoff u (Function.update x k (Pi.single α 1)) k

/-- The squared Euclidean distance `‖x − x'‖₂² = ∑_β (x_β − x'_β)²` on `ℝ^B`, the norm of (2.5)
(p. 5) and of (C.6), (C.14), Proposition C.3 (pp. 34–35). -/
def sqDist {B : Type*} [Fintype B] (x x' : B → ℝ) : ℝ :=
  ∑ β, (x β - x' β) ^ 2

/-- The relative interior of the face of the simplex `Δ(B)` spanned by `S ⊆ B`: the points of
`Δ(B)` whose support is exactly `S` (Definition 2.1(2) and footnote 5, p. 5). -/
def faceRelInt {B : Type*} [Fintype B] (S : Set B) : Set (B → ℝ) :=
  {x | x ∈ stdSimplex ℝ B ∧ ∀ β, (0 < x β ↔ β ∈ S)}

/-- **Definition 2.1** (p. 5): `h` is a penalty function on `Δ(B)` with strong convexity
constant `K`: (1) `h` is continuous on `Δ`; (2) `h` is smooth on the relative interior of every
face of `Δ`, in the sense of footnote 5 (`h ∘ γ` is `C^∞` for every `C^∞` curve `γ : (−ε, ε) → Δ`
that stays in the relative interior of one face); (3) `0 < K` and (2.5) holds for the Euclidean
norm. -/
def IsPenalty {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (K : ℝ) : Prop :=
  ContinuousOn h (stdSimplex ℝ B) ∧
  (∀ (S : Set B) (ε : ℝ) (γ : ℝ → B → ℝ), ContDiffOn ℝ ∞ γ (Set.Ioo (-ε) ε) →
      Set.MapsTo γ (Set.Ioo (-ε) ε) (faceRelInt S) →
      ContDiffOn ℝ ∞ (h ∘ γ) (Set.Ioo (-ε) ε)) ∧
  0 < K ∧
  ∀ x₁ ∈ stdSimplex ℝ B, ∀ x₂ ∈ stdSimplex ℝ B, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    h (t • x₁ + (1 - t) • x₂) ≤ t * h x₁ + (1 - t) * h x₂ - 1 / 2 * K * t * (1 - t) * sqDist x₁ x₂

/-- `x = Q(y)`: `x` solves the regularized problem (2.7) and is the value of the choice map (2.8)
(Definition 2.2, p. 6), `x ∈ argmax_{x' ∈ Δ} {⟨y|x'⟩ − h(x')}`. -/
def IsChoice {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (y x : B → ℝ) : Prop :=
  x ∈ stdSimplex ℝ B ∧ ∀ x' ∈ stdSimplex ℝ B, y ⬝ᵥ x' - h x' ≤ y ⬝ᵥ x - h x

/-- The convex conjugate `h*(y) = max_{x ∈ Δ} {⟨y|x⟩ − h(x)}` of (4.5) and (C.1) (pp. 18, 33). -/
noncomputable def conj {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (y : B → ℝ) : ℝ :=
  sSup ((fun x => y ⬝ᵥ x - h x) '' stdSimplex ℝ B)

/-- The Fenchel coupling `F_h(p, y) = h(p) + h*(y) − ⟨y|p⟩` of (4.4) and (C.10) (pp. 18, 34). -/
noncomputable def fenchelCoupling {B : Type*} [Fintype B] (h : (B → ℝ) → ℝ) (p y : B → ℝ) : ℝ :=
  h p + conj h y - y ⬝ᵥ p

/-- `(y, x)` is an orbit of the reinforcement learning dynamics (RLγ) (p. 10) with rates `γ`:
for every `t ≥ 0` and every player `k`, `x_k(t) = Q_k(y_k(t))` and `ẏ_{kα}(t) = γ_k v_{kα}(x(t))`
(right derivative at `t = 0`). With `γ ≡ 1` this is (RL) of p. 7 in the differential form (3.1). -/
def IsRLγOrbit {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (γ : ι → ℝ)
    (y x : ℝ → ∀ k, A k → ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ k, IsChoice (h k) (y t k) (x t k) ∧
    ∀ α, HasDerivWithinAt (fun s => y s k α) (γ k * payoffVec u (x t) k α) (Set.Ici 0) t

/-- `(y, x)` is an orbit of (RL) (p. 7): (RLγ) with every `γ_k = 1`. -/
def IsRLOrbit {ι : Type*} [Fintype ι] [DecidableEq ι] {A : ι → Type*}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    (u : ι → (∀ k, A k) → ℝ) (h : ∀ k, (A k → ℝ) → ℝ) (y x : ℝ → ∀ k, A k → ℝ) : Prop :=
  IsRLγOrbit u h (fun _ => 1) y x

end ReinfRegGames.Extinction


