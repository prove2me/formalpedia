-- Prove2me | Definitions.Def_ConvexSDDP_Stoch_Model
-- name    : ConvexSDDP_Stoch_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:23.571228+00:00
-- url     : https://prove2.me/theorems/f5464bda-de1f-421f-b73d-63e0f6361f51
-- title:
--   (19), (20), (H₂), (24) and Ṽₙ, pp. 12–16 — the multistage stochastic convex program on a scenario tree and its future cost functions
-- statement:
--   Fix a scenario tree with nodes $\mathcal N$, root $0$, parent map $p$, children $r(n)$ and leaves $\mathcal L$. Stocks lie in $\mathbb R^d$ and controls in $\mathbb R^p$. The data of problem (19), p. 12, are node probabilities $\Phi_n$, stock constraint sets $\mathcal X_n\subseteq\mathbb R^d$, for every $m\neq 0$ a control multifunction $\mathcal U_m:\mathbb R^d\rightrightarrows\mathbb R^p$, a cost $C_m:\mathbb R^d\times\mathbb R^p\to\mathbb R\cup\{+\infty\}$ and linear dynamics $f_m:\mathbb R^d\times\mathbb R^p\to\mathbb R^d$, final costs $V_m$ at the leaves $m\in\mathcal L$, an initial stock $x_0$ and a radius $\delta$.
--
--   **Assumptions $(H_2)$** (p. 13), together with the standing data of §3.1 ($\Phi$ are node probabilities, $x_0\in\mathcal X_0$):
--   1. every $\mathcal X_n$ is convex and compact;
--   2. for $m\neq 0$, $\mathcal U_m$ is a convex multifunction with convex compact values;
--   3. the costs $C_m$ ($m\ne 0$) and the final costs $V_m$ ($m\in\mathcal L$) are convex, lower semicontinuous and proper;
--   4. the $f_m$ are linear;
--   5. every final cost $V_m$ is finite and Lipschitz continuous on $\mathcal X_m$;
--   6. there is $\delta>0$ such that for every $n\in\mathcal N\setminus\mathcal L$, every $x\in\mathcal X_n+B(\delta)$ and every $m\in r(n)$: (a) $f_m(x,\mathcal U_m(x))\cap\mathcal X_m\ne\emptyset$, and (b) $C_m(x,u)<\infty$ for all $u\in\mathcal U_m(x)$.
--
--   **Derived objects.** $\tilde{\mathcal U}_m(x)=\{u\in\mathcal U_m(x): f_m(x,u)\in\mathcal X_m\}$ (p. 14). The **future cost functions** (20) are defined backwards on the tree: for $x\in\mathcal X_n$,
--   $$V_n(x)=\sum_{m\in r(n)}\frac{\Phi_m}{\Phi_n}\ \inf_{u\in\mathcal U_m(x)}\Big(C_m(x,u)+V_m\big(f_m(x,u)\big)\Big)\quad(n\notin\mathcal L),$$
--   $V_n$ is the given final cost at a leaf, and $V_n(x)=+\infty$ for $x\notin\mathcal X_n$. Further
--   $$W_m(x,u)=C_m(x,u)+V_m\big(f_m(x,u)\big)\ \ \text{(24)},\qquad \tilde V_n(x)=\sum_{m\in r(n)}\frac{\Phi_m}{\Phi_n}\inf_{u\in\tilde{\mathcal U}_m(x)}W_m(x,u)\ \ (n\notin\mathcal L),$$
--   the extended value function of §3.2, p. 16, defined for every $x\in\mathbb R^d$.
--
--   **Formalization Note** The costs are indexed by the child node $m$, as in (19a), (20) and (24); $(H_2)(3)$ and $(6)(b)$ print $C_n$. $\mathcal X_n+B(\delta)$ uses the full Euclidean ball of radius $\delta$, as printed. The value $+\infty$ off $\mathcal X_n$ encodes constraint (19d); (20) has no such clause on the page. The recursion is computed with a level counter equal to the number of nodes, which exceeds the length of every path to a leaf, so it returns (20) exactly. Infima are taken in $\overline{\mathbb R}$ (an empty infimum is $+\infty$); attainment is a separate claim. Finite and Lipschitz in (5) is stated on the real values of $V_m$ on $\mathcal X_m$, where $V_m$ is finite.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, pp. 12–16, (19), (20), (H₂), (24), definition of Ũ_m (p. 14) and of Ṽ_n (p. 16)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_ConvexSDDP_Det_Basic
import Definitions.Def_ConvexSDDP_Stoch_Tree

namespace ConvexSDDP.Stoch

open StochasticProg.Multistage
open scoped Pointwise

/-- The data of the stochastic multistage problem (19), p. 12, on the scenario tree `T`, with
stocks in `ℝᵈ` and controls in `ℝᵖ`:
* `Φ n` the probability of node `n`;
* `X n` the stock constraint set `𝒳_n`;
* `U m x` the control constraint set `𝒰_m(x)` of node `m ≠ root`, given the parent stock `x`;
* `C m x u` the cost `C_m(x, u) ∈ ℝ ∪ {+∞}` of node `m ≠ root` (indexed by the child `m`, as in
  (19a), (20), (24));
* `f m` the linear dynamics `x_m = f_m(x_{p(m)}, u_m)`;
* `VL m` the final cost `V_m` of a leaf `m`;
* `x0` the given initial stock `x_0`, and `δ` the radius of assumption (H₂)(6). -/
structure Model {H : ℕ} (T : Tree H) (d p : ℕ) where
  Φ : T.Node → ℝ
  X : T.Node → Set (EuclideanSpace ℝ (Fin d))
  U : T.Node → EuclideanSpace ℝ (Fin d) → Set (EuclideanSpace ℝ (Fin p))
  C : T.Node → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin p) → EReal
  f : T.Node → (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p)) →ₗ[ℝ]
    EuclideanSpace ℝ (Fin d)
  VL : T.Node → EuclideanSpace ℝ (Fin d) → EReal
  x0 : EuclideanSpace ℝ (Fin d)
  δ : ℝ

namespace Model

variable {H : ℕ} {T : Tree H} {d p : ℕ} (M : Model T d p)

/-- Assumptions (H₂), p. 13, clause by clause, together with the standing data of §3.1:
`Φ` are node probabilities on the tree and `x_0 ∈ 𝒳_root`.
(1) every `𝒳_n` is convex and compact;
(2) for `m ≠ root`, `𝒰_m` is a convex multifunction with convex compact values;
(3) the costs `C_m` (`m ≠ root`) and the leaf costs `V_m` (`m ∈ ℒ`) are convex, lower
    semicontinuous and proper;
(4) the dynamics `f_m` are linear (built into the type of `f`);
(5) every leaf cost `V_m` is finite and Lipschitz continuous on `𝒳_m`;
(6) there is `δ > 0` such that for every non-leaf `n`, every `x ∈ 𝒳_n + B(δ)` and every child
    `m` of `n`: (a) `f_m(x, 𝒰_m(x)) ∩ 𝒳_m ≠ ∅` and (b) `C_m(x, u) < ∞` for all `u ∈ 𝒰_m(x)`. -/
def H2 : Prop :=
  IsNodeProb T M.Φ ∧ M.x0 ∈ M.X T.root ∧
  (∀ n, Convex ℝ (M.X n) ∧ IsCompact (M.X n)) ∧
  (∀ m, m ≠ T.root → ConvexSDDP.Det.ConvexMultifunction (M.U m) ∧
    ∀ x, Convex ℝ (M.U m x) ∧ IsCompact (M.U m x)) ∧
  (∀ m, m ≠ T.root →
    ConvexSDDP.Det.EProper (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => M.C m z.1 z.2) ∧
    LowerSemicontinuous
      (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => M.C m z.1 z.2) ∧
    ConvexSDDP.Det.EConvex (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin p) => M.C m z.1 z.2)) ∧
  (∀ m, IsLeaf T m → ConvexSDDP.Det.EProper (M.VL m) ∧ LowerSemicontinuous (M.VL m) ∧ ConvexSDDP.Det.EConvex (M.VL m)) ∧
  (∀ m, IsLeaf T m → (∀ x ∈ M.X m, M.VL m x ≠ ⊤) ∧
    ∃ L : ℝ, ∀ x ∈ M.X m, ∀ y ∈ M.X m,
      |(M.VL m x).toReal - (M.VL m y).toReal| ≤ L * ‖x - y‖) ∧
  (0 < M.δ ∧ ∀ n, ¬ IsLeaf T n →
    ∀ x ∈ M.X n + Metric.ball (0 : EuclideanSpace ℝ (Fin d)) M.δ, ∀ m ∈ T.children n,
      (∃ u ∈ M.U m x, M.f m (x, u) ∈ M.X m) ∧ ∀ u ∈ M.U m x, M.C m x u < ⊤)

/-- p. 14: the multifunction `𝒰̃_m(x) = {u ∈ 𝒰_m(x) | f_m(x, u) ∈ 𝒳_m}`. -/
def Ut (m : T.Node) (x : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin p)) :=
  {u | u ∈ M.U m x ∧ M.f m (x, u) ∈ M.X m}

open Classical in
/-- The backward recursion (20), p. 13, run for `h` levels (`Vfuel 0 ≡ +∞` is never reached
below, see `V`): at a leaf the final cost `V_m`, at a non-leaf `n`
`Σ_{m ∈ r(n)} (Φ_m/Φ_n) inf_{u ∈ 𝒰_m(x)} C_m(x, u) + V_m(f_m(x, u))`, and `+∞` off `𝒳_n`
(constraint (19d)). -/
noncomputable def Vfuel : ℕ → T.Node → EuclideanSpace ℝ (Fin d) → EReal
  | 0, _, _ => ⊤
  | h + 1, n, x =>
    if x ∈ M.X n then
      (if IsLeaf T n then M.VL n x
       else ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) *
         ⨅ u ∈ M.U m x, (M.C m x u + Vfuel h m (M.f m (x, u))))
    else ⊤

/-- The future cost function `V_n` of (20), p. 13. Every path from a node down to a leaf has
fewer than `card N` nodes, so `card N` levels of the recursion compute it exactly. -/
noncomputable def V (n : T.Node) (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  M.Vfuel (Fintype.card T.Node) n x

/-- (24), p. 15: `W_m(x, u) = C_m(x, u) + V_m(f_m(x, u))`. -/
noncomputable def W (m : T.Node) (x : EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin p)) : EReal :=
  M.C m x u + M.V m (M.f m (x, u))

/-- §3.2, p. 16: the extended value function of a non-leaf node `n`,
`Ṽ_n(x) = Σ_{m ∈ r(n)} (Φ_m/Φ_n) inf_{u ∈ 𝒰̃_m(x)} C_m(x, u) + V_m(f_m(x, u))`, defined for
every `x ∈ ℝᵈ`. -/
noncomputable def Vtilde (n : T.Node) (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  ∑ m ∈ T.children n, ((M.Φ m / M.Φ n : ℝ) : EReal) * ⨅ u ∈ M.Ut m x, M.W m x u

end Model

end ConvexSDDP.Stoch


