-- Prove2me | Definitions.Def_OnlineLinearOptimization
-- name    : OnlineLinearOptimization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-29T17:01:25.607092+00:00
-- url     : https://prove2.me/theorems/752ac17a-da75-4fd5-9f9d-40f325e3dfe8
-- statement:
--   Online linear optimization over a convex action set $\mathcal{A} \subseteq \mathbb{R}^d$: in round $t$ the learner plays $a_t \in \mathcal{A}$, the adversary reveals a loss vector $y_t$, and the regret against a comparator $a_0$ (`oloRegret`) is
--
--   $$R_n(a_0) = \sum_{t<n} \langle a_t - a_0, y_t\rangle.$$
--
--   A potential is a real-valued $F$ with an explicit effective-domain set $D$; `IsLegendre F D` is the book's Definition (§26.4): $\mathrm{int}\,D \neq \emptyset$, $F$ differentiable and strictly convex on $\mathrm{int}\,D$, and $\|\nabla F\| \to \infty$ along interior sequences approaching the boundary. The Bregman divergence (§26.3, `bregmanDiv F x y`) is
--
--   $$D_F(x, y) = F(x) - F(y) - \langle \nabla F(y), x-y\rangle.$$
--
--   `IsMirrorDescentIterates` encodes Eqs. (28.1)–(28.2) and the two-step process (28.7)–(28.9):
--
--   - $a_1 = \mathrm{argmin}_{\mathcal{A} \cap D} F$;
--   - $a_{t+1} = \mathrm{argmin}_{a \in \mathcal{A} \cap D}\,(\eta\langle a, y_t\rangle + D_F(a, a_t))$;
--   - $\tilde a_{t+1} \in \mathrm{int}\,D$ with $\nabla F(\tilde a_{t+1}) = \nabla F(a_t) - \eta y_t$;
--   - $a_{t+1}$ is the Bregman projection $\mathrm{argmin}_{a \in \mathcal{A} \cap D} D_F(a, \tilde a_{t+1})$
--
--   (argmins as membership + `IsMinOn`). `IsFTRLIterates` encodes Eq. (28.3):
--
--   $$a_{t+1} = \mathrm{argmin}_{a\in\mathcal{A} \cap D}\,\Big(\eta\sum_{s\le t}\langle a, y_s\rangle + F(a)\Big).$$
-- source:
--   L&S Ch 26.3-26.4, 28.1, pp.308-331

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.Extr

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), §26.3–26.6 and
§28.1 (pp. 308–331): online linear optimisation, Legendre potentials,
Bregman divergences, and the mirror-descent / follow-the-regularised-leader
iterates.

**Online linear optimisation** (§28.1): the learner keeps an action
`a t ∈ 𝒜 ⊆ ℝ^d`, the adversary reveals a loss vector `y t`, and the regret
relative to a comparator `a₀` is `R_n(a₀) = ∑_{t<n} ⟪a t - a₀, y t⟫`.

**Legendre functions** (§26.4, p. 310): since Mathlib has no extended-real
proper convex functions, a potential is modelled as a real-valued
`F : E → ℝ` together with an explicit effective-domain set `D` (the book's
`dom F`; `F` is understood as `+∞` off `D`).  `F` is *Legendre on `D`* if
(with `C = int D`): (a) `C` is non-empty; (b) `F` is differentiable and
strictly convex on `C`; (c) `‖∇F(xₙ)‖ → ∞` along any sequence in `C`
converging to a boundary point of `C`.

**Bregman divergence** (§26.3, p. 308, differentiable case):
`D_F(x, y) = F x - F y - ⟪∇F y, x - y⟫`, via Mathlib's Hilbert-space
`gradient` (junk when `F` is not differentiable at `y`; all uses below are
at points of differentiability).

**Mirror descent** (Eqs. (28.1), (28.2) and the two-step form
(28.7)–(28.9), pp. 328–330): `a 0 = argmin_{𝒜 ∩ D} F` and, under the
standing condition Eq. (28.6) (`∇F(a) - η y ∈ int (dom F*)`, here
internalised as the existence of the dual iterate `ã (t+1) ∈ int D`),

* `a (t+1) = argmin_{b ∈ 𝒜 ∩ D} (η ⟪b, y t⟫ + D_F(b, a t))`   (Eq. 28.2),
* `ã (t+1) ∈ int D` with `∇F(ã (t+1)) = ∇F(a t) - η • y t`     (Eqs. 28.7/28.9),
* `a (t+1) = argmin_{b ∈ 𝒜 ∩ D} D_F(b, ã (t+1))`               (Eq. 28.8),

together with `a t ∈ int D` (the book's Exercise 28.1, which always holds
for Legendre `F`).  Argmins are encoded as membership plus `IsMinOn`.

**FTRL** (Eq. (28.3), p. 328): `a (t+1)` minimises
`b ↦ η ∑_{s ≤ t} ⟪b, y s⟫ + F b` over `𝒜 ∩ D`.

Indexing: rounds are `0`-based, so the book's `a_1, a_2, …` and losses
`y_1, y_2, …` are `a 0, a 1, …` and `y 0, y 1, …`.
-/

open RealInnerProductSpace

namespace BanditAlgorithm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `IsLegendre F D`: the convex function `F : E → ℝ` with effective domain
`D` is a *Legendre function* (L&S §26.4, p. 310).  Writing `C = int D`:
`C ≠ ∅`, `F` is differentiable and strictly convex on `C`, and `‖∇F‖`
blows up along any sequence in `C` approaching the boundary of `C`. -/
structure IsLegendre (F : E → ℝ) (D : Set E) : Prop where
  /-- `F` is convex on its domain `D` (in particular `D` is convex). -/
  convexOn : ConvexOn ℝ D F
  /-- (a) the interior of the domain is non-empty. -/
  interior_nonempty : (interior D).Nonempty
  /-- (b) `F` is differentiable on `int D`. -/
  differentiableAt : ∀ x ∈ interior D, DifferentiableAt ℝ F x
  /-- (b) `F` is strictly convex on `int D`. -/
  strictConvexOn : StrictConvexOn ℝ (interior D) F
  /-- (c) `‖∇F(xₙ)‖ → ∞` for any sequence in `int D` converging to a
  boundary point of `int D`. -/
  gradient_tendsto_atTop : ∀ x ∈ frontier (interior D), ∀ z : ℕ → E,
    (∀ k, z k ∈ interior D) → Filter.Tendsto z Filter.atTop (nhds x) →
      Filter.Tendsto (fun k => ‖gradient F (z k)‖) Filter.atTop Filter.atTop

/-- The Bregman divergence induced by `F` at a point `y` of
differentiability (L&S §26.3, p. 308):
`D_F(x, y) = F x - F y - ⟪∇F y, x - y⟫`. -/
noncomputable def bregmanDiv (F : E → ℝ) (x y : E) : ℝ :=
  F x - F y - ⟪gradient F y, x - y⟫

/-- The online-linear-optimisation regret of the action sequence `a`
against the loss sequence `y` over `n` rounds, relative to the comparator
`a₀` (L&S §28.1, p. 327): `R_n(a₀) = ∑_{t<n} ⟪a t - a₀, y t⟫`. -/
noncomputable def oloRegret (a y : ℕ → E) (n : ℕ) (a₀ : E) : ℝ :=
  ∑ t ∈ Finset.range n, ⟪a t - a₀, y t⟫

/-- `IsMirrorDescentIterates η F D 𝒜 y a ã`: the sequences `a` (primal
iterates) and `ã` (unprojected dual iterates) are the mirror-descent
iterates with learning rate `η`, potential `F` with domain `D`, action set
`𝒜` and losses `y` (L&S Eqs. (28.1), (28.2), and the two-step form
(28.7)–(28.9), pp. 328–330, run under the standing condition Eq. (28.6)):

* `a 0` minimises `F` over `𝒜 ∩ D`                                 (28.1);
* `a (t+1)` minimises `b ↦ η ⟪b, y t⟫ + D_F(b, a t)` over `𝒜 ∩ D`  (28.2);
* `ã (t+1) ∈ int D` and `∇F(ã (t+1)) = ∇F(a t) - η • y t`     (28.7)/(28.9);
* `a (t+1)` is the Bregman projection of `ã (t+1)` onto `𝒜 ∩ D`,
  i.e. it minimises `b ↦ D_F(b, ã (t+1))` over `𝒜 ∩ D`              (28.8);
* every primal iterate lies in `int D` (Exercise 28.1). -/
structure IsMirrorDescentIterates (η : ℝ) (F : E → ℝ) (D 𝒜 : Set E)
    (y a ã : ℕ → E) : Prop where
  /-- `a 0 ∈ 𝒜 ∩ D`. -/
  init_mem : a 0 ∈ 𝒜 ∩ D
  /-- Eq. (28.1): `a 0` minimises the potential over `𝒜 ∩ D`. -/
  init_isMinOn : IsMinOn F (𝒜 ∩ D) (a 0)
  /-- The primal iterates stay in the interior of the domain
  (L&S Exercise 28.1; automatic for Legendre `F`). -/
  mem_interior : ∀ t, a t ∈ interior D
  /-- `a (t+1) ∈ 𝒜 ∩ D`. -/
  step_mem : ∀ t, a (t + 1) ∈ 𝒜 ∩ D
  /-- Eq. (28.2): `a (t+1)` minimises `b ↦ η ⟪b, y t⟫ + D_F(b, a t)`
  over `𝒜 ∩ D`. -/
  step_isMinOn : ∀ t,
    IsMinOn (fun b => η * ⟪b, y t⟫ + bregmanDiv F b (a t)) (𝒜 ∩ D) (a (t + 1))
  /-- The dual iterate lives in the interior of the domain. -/
  dual_mem_interior : ∀ t, ã (t + 1) ∈ interior D
  /-- Eqs. (28.7)/(28.9): the unprojected iterate satisfies
  `∇F(ã (t+1)) = ∇F(a t) - η • y t`. -/
  dual_gradient_eq : ∀ t, gradient F (ã (t + 1)) = gradient F (a t) - η • y t
  /-- Eq. (28.8): `a (t+1)` is the `D_F`-projection of `ã (t+1)` onto
  `𝒜 ∩ D`. -/
  proj_isMinOn : ∀ t,
    IsMinOn (fun b => bregmanDiv F b (ã (t + 1))) (𝒜 ∩ D) (a (t + 1))

/-- `IsFTRLIterates η F D 𝒜 y a`: the sequence `a` is the
follow-the-regularised-leader iterates with learning rate `η`, potential
`F` with domain `D`, action set `𝒜` and losses `y` (L&S Eq. (28.3),
p. 328): `a 0` minimises `F` over `𝒜 ∩ D`, and `a (t+1)` minimises
`b ↦ η ∑_{s ≤ t} ⟪b, y s⟫ + F b` over `𝒜 ∩ D`. -/
structure IsFTRLIterates (η : ℝ) (F : E → ℝ) (D 𝒜 : Set E)
    (y a : ℕ → E) : Prop where
  /-- `a 0 ∈ 𝒜 ∩ D`. -/
  init_mem : a 0 ∈ 𝒜 ∩ D
  /-- `a 0` minimises the potential over `𝒜 ∩ D`. -/
  init_isMinOn : IsMinOn F (𝒜 ∩ D) (a 0)
  /-- `a (t+1) ∈ 𝒜 ∩ D`. -/
  step_mem : ∀ t, a (t + 1) ∈ 𝒜 ∩ D
  /-- Eq. (28.3): `a (t+1)` minimises the regularised cumulative loss
  `b ↦ η ∑_{s ≤ t} ⟪b, y s⟫ + F b` over `𝒜 ∩ D`. -/
  step_isMinOn : ∀ t,
    IsMinOn (fun b => η * ∑ s ∈ Finset.range (t + 1), ⟪b, y s⟫ + F b)
      (𝒜 ∩ D) (a (t + 1))

end BanditAlgorithm


