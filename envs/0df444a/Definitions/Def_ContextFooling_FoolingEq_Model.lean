-- Prove2me | Definitions.Def_ContextFooling_FoolingEq_Model
-- name    : ContextFooling_FoolingEq_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:02.830235+00:00
-- url     : https://prove2.me/theorems/fabd7830-1692-4488-a092-a7f36c64e661
-- title:
--   §II, pp. 6–9 — retail market with context-sensitive consumers: surplus (1)–(3), two-stage choice, fooling (Definition 3), competitive equilibrium with footnote 4
-- statement:
--   This file sets up the market model of Apffelstaedt and Mechtenberg.
--
--   **Products and contexts.** A product $j=(q_j,p_j,\theta_j)$ has a quality $q_j\in\mathbb R$, a price $p_j\in\mathbb R$ and a store context $\theta_j\in\{N,Q,P\}$ (no distortion, quality-inflating, price-inflating). Its undistorted surplus is $u_j=q_j-p_j$ (eq. (1)); the outside option is worth $0$. Inside a store, a consumer with context sensitivity $\gamma$ values it at
--
--   $$\hat u_j(\gamma)=\begin{cases} q_j-p_j & \theta_j=N,\\ \gamma q_j-p_j & \theta_j=Q,\\ q_j-\gamma p_j & \theta_j=P.\end{cases}$$
--
--   The true sensitivity is $\beta$ (eq. (2)); a consumer of type $\tilde\beta$ predicts her in-store valuation as $\hat u_j(\tilde\beta)$ (eq. (3)).
--
--   **Parameters and standing assumptions.** The data are $\beta$, a minimum quality $\underline q$, a maximum price $b$, a cost function $c$, the number $K$ of firms, the type distribution $\mu$ of beliefs $\tilde\beta$, and the cost-efficient qualities $q^*,q^Q,q^P$. They are assumed to satisfy:
--   1. $\beta>1$, $\underline q>0$, $b>0$, $K\ge 2$;
--   2. $c$ is twice continuously differentiable with $c(0)=c'(0)=0$, $c'(q)>0$ for $q>0$ and $c''(q)>0$ for $q\ge 0$;
--   3. $q^*,q^Q,q^P\ge 0$ satisfy $c'(q^*)=1$, $c'(q^Q)=\beta$, $c'(q^P)=1/\beta$;
--   4. $\underline q\le q^P$ and $c(q^Q)\le b$;
--   5. $\mu$ is a probability measure with a density and no mass on $\tilde\beta\le 1$.
--
--   **Fooling (Definition 3).** Write $a$ for the attraction product and $t$ for the target, with $a\neq t$. A type $\tilde\beta$ is fooled by the pair $(a,t)$ if both
--   $$\hat u_t(\beta)\ge \hat u_a(\beta)\ \text{(IC)},\qquad \hat u_t(\tilde\beta)\le \hat u_a(\tilde\beta)\ \text{(PCC)}$$
--   hold, and at least one of them holds strictly.
--
--   **Choice.** A product is acceptable when $q\ge\underline q$ and $p\le b$. At a store with menu $M$, type $\gamma$ predicts to buy the acceptable maximizers of $\hat u(\gamma)$. Her expected surplus there is the largest $u$ among these products. She enters a store when three conditions hold: she predicts some purchase there, her expected surplus there is at least $0$, and it is at least her expected surplus at every other store where she predicts a purchase. Entrants buy the acceptable maximizers of $\hat u(\beta)$. The firm's margin is the largest $p-c(q)$ among the products bought, so ties are resolved in the firm's favour. A firm has positive demand when the types that enter it have positive $\mu$-mass.
--
--   **Competitive equilibrium (§II.D and footnote 4).** Fix a context technology: store-wide (every product of a menu has the same context) or product-specific (no restriction). A profile of menus $(M^k)_{k\le K}$ is a competitive equilibrium when:
--   1. every menu is feasible for the technology;
--   2. every firm with positive demand has margin $0$ (zero profit);
--   3. no firm has a feasible deviation that gives it both positive demand and a positive margin (Nash);
--   4. a firm without positive demand offers the empty menu;
--   5. no feasible menu with fewer products (or as many products and fewer distorted ones) gives an active firm positive demand at a margin at least its current one.
--
--   The file also defines the switching surpluses $\nu^{(Q,Q)}=[q^Q-c(q^Q)]+(\beta-1)(q^Q-\underline q)$, $\nu^{(P,P)}=[q^P-c(q^P)]+(\beta-1)[b-c(q^P)]$ and $\nu^{(P,Q)}=\beta q^Q-c(q^Q)+(\beta-1)b$. It also defines the candidate menus (Q\*), (P\*) and (PQ\*) of Proposition 2, and the predicate "menu $M$ consists of target $t$, which is sold, and attraction product $a\ne t$, which every type $\tilde\beta\in(1,\beta)$ predicts to buy".
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Profit is $\pi^k=D^k\cdot(\text{margin})$ with $D^k>0$ exactly when the firm has positive demand. Every equilibrium condition is a sign condition, so no demand-sharing rule is needed. Footnote 4's infinitesimal costs are encoded as conditions 4 and 5, not as a lexicographic cost; a lexicographic cost would make $\emptyset$ strictly better than any zero-profit menu. Added relative to the page: $K\ge 2$, $C^2$ smoothness of $c$, and the existence of the three roots (asserted on p. 8). $c''>0$ is required on $q\ge 0$ only, and the derivatives are Mathlib's `deriv`. The "smallest monetary unit" (p. 9) is modelled by firm-favourable ties at purchase, and ties in prediction by the largest $u$. Predicted ties have $\mu$-measure zero under a density, or else the tied products have equal $u$, so the latter convention does not matter.
-- source:
--   Apffelstaedt & Mechtenberg, Competition for Context-Sensitive Consumers, MPRA Paper No. 99509 (version of November 2016; published in Management Science, doi:10.1287/mnsc.2020.3675), pp. 6–11 (PDF 7–12), §II.A–D, Definitions 1–3, eqs. (1)–(3), footnotes 4–5; ν^(Q,Q), ν^(P,P) from Proposition 2, p. 15 (PDF 16); (Q*), (P*), (PQ*) from the proof of Proposition 2, pp. 44, 47 (PDF 45, 48)

import Mathlib

namespace ContextFooling.FoolingEq

/-- Store-context effect on one product (§II.B, p. 7): none, quality-inflating, price-inflating. -/
inductive Ctx
  | N
  | Q
  | P
  deriving DecidableEq

/-- A product: quality `q`, price `p` (both in dollars, `ℝ`) and its store-context `θ`. -/
structure Product where
  q : ℝ
  p : ℝ
  θ : Ctx

noncomputable instance : DecidableEq Product := Classical.decEq _

/-- Model parameters (§II, pp. 6–8): context sensitivity `β`, minimum quality `qlow` (q̲),
maximum price `b`, cost `c`, number of firms `K`, type distribution `μ` of beliefs β̃, and the
cost-efficient qualities `qS` (q*), `qQ` (q^Q), `qP` (q^P). -/
structure Params where
  β : ℝ
  qlow : ℝ
  b : ℝ
  c : ℝ → ℝ
  K : ℕ
  μ : MeasureTheory.Measure ℝ
  qS : ℝ
  qQ : ℝ
  qP : ℝ

/-- The standing assumptions of §II–§III (pp. 6–10). Added relative to the page: `2 ≤ K`
("a large number K of firms"), `ContDiff ℝ 2 c` (the page uses c′, c″), and the existence of
nonnegative roots `qS`, `qQ`, `qP` of c′ = 1, β, 1/β (asserted on p. 8). The type law has a
density (`μ ≪ volume`) and no mass on β̃ ≤ 1 (f(β̃) = 0 for β̃ ≤ 1, p. 7). -/
def Params.Standing (P : Params) : Prop :=
  1 < P.β ∧ 0 < P.qlow ∧ 0 < P.b ∧ 2 ≤ P.K ∧
  ContDiff ℝ 2 P.c ∧ P.c 0 = 0 ∧ deriv P.c 0 = 0 ∧
  (∀ q : ℝ, 0 < q → 0 < deriv P.c q) ∧ (∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv P.c) q) ∧
  0 ≤ P.qS ∧ deriv P.c P.qS = 1 ∧
  0 ≤ P.qQ ∧ deriv P.c P.qQ = P.β ∧
  0 ≤ P.qP ∧ deriv P.c P.qP = 1 / P.β ∧
  P.qlow ≤ P.qP ∧ P.c P.qQ ≤ P.b ∧
  MeasureTheory.IsProbabilityMeasure P.μ ∧ P.μ.AbsolutelyContinuous MeasureTheory.volume ∧
  P.μ (Set.Ioi 1)ᶜ = 0

/-- In-store valuation at sensitivity `γ`: eq. (2) at `γ = β`, eq. (3) at `γ = β̃`. -/
def val (γ : ℝ) (j : Product) : ℝ :=
  match j.θ with
  | .N => j.q - j.p
  | .Q => γ * j.q - j.p
  | .P => j.q - γ * j.p

/-- Undistorted ("global") surplus, eq. (1). -/
def u (j : Product) : ℝ := j.q - j.p

/-- Definition 3 (Fooling), for attraction product `a`, target `t`, true sensitivity `β` and
belief `β'`: `a ≠ t`, (IC), (PCC), with at least one of the two strict. -/
def Fools (β β' : ℝ) (a t : Product) : Prop :=
  a ≠ t ∧ val β a ≤ val β t ∧ val β' t ≤ val β' a ∧ (val β a < val β t ∨ val β' t < val β' a)

/-- A product consumers are willing to accept: `q̲ ≤ q` and `p ≤ b` (p. 6). -/
def Acceptable (P : Params) (j : Product) : Prop := P.qlow ≤ j.q ∧ j.p ≤ P.b

/-- The acceptable products of a menu. -/
noncomputable def acc (P : Params) (M : Finset Product) : Finset Product :=
  by classical exact M.filter (Acceptable P)

/-- The acceptable products of `M` that maximize `val γ`: the predicted purchases of type `γ`
(Definition 1) at `γ = β̃`, the actual purchases (Definition 2) at `γ = β`. -/
noncomputable def Pred (P : Params) (M : Finset Product) (γ : ℝ) : Finset Product :=
  by classical exact (acc P M).filter (fun j => ∀ j' ∈ acc P M, val γ j' ≤ val γ j)

/-- Expected undistorted surplus of type `γ` at a store with menu `M`: the largest `u` among
her predicted purchases (0 if she predicts none; every use is guarded by nonemptiness). -/
noncomputable def ExpSurplus (P : Params) (M : Finset Product) (γ : ℝ) : ℝ :=
  if h : (Pred P M γ).Nonempty then (Pred P M γ).sup' h u else 0

/-- The products an entrant actually buys: the acceptable maximizers of `val β`. -/
noncomputable def Bought (P : Params) (M : Finset Product) : Finset Product := Pred P M P.β

/-- Per-unit margin `p − c(q)` of the firm; ties among bought products are resolved in the
firm's favour (smallest monetary unit, p. 9). It is 0 if nothing is bought. -/
noncomputable def margin (P : Params) (M : Finset Product) : ℝ :=
  if h : (Bought P M).Nonempty then (Bought P M).sup' h (fun j => j.p - P.c j.q) else 0

/-- `t` is the target (Definition 2): it is bought, and strictly more profitable than any
other bought product. -/
def Sells (P : Params) (M : Finset Product) (t : Product) : Prop :=
  t ∈ Bought P M ∧ ∀ j ∈ Bought P M, j = t ∨ j.p - P.c j.q < t.p - P.c t.q

/-- A profile of menus, one per firm. -/
abbrev Profile (P : Params) := Fin P.K → Finset Product

/-- Stage 1: type `γ` enters store `k` (with positive probability) iff she predicts an
acceptable purchase there, expects at least the outside option `0`, and at least as much as at
every other store where she predicts a purchase. -/
def Enters (P : Params) (σ : Profile P) (k : Fin P.K) (γ : ℝ) : Prop :=
  (Pred P (σ k) γ).Nonempty ∧ 0 ≤ ExpSurplus P (σ k) γ ∧
  ∀ k' : Fin P.K, (Pred P (σ k') γ).Nonempty → ExpSurplus P (σ k') γ ≤ ExpSurplus P (σ k) γ

/-- Firm `k` has strictly positive demand: the types that enter it have positive mass. -/
def PosDemand (P : Params) (σ : Profile P) (k : Fin P.K) : Prop :=
  0 < P.μ {γ | Enters P σ k γ}

/-- Store-wide context technology (Proposition 2 a): all products of a menu share one context. -/
def StoreWide (M : Finset Product) : Prop := ∀ j ∈ M, ∀ j' ∈ M, j.θ = j'.θ

/-- Product-specific context technology (Proposition 2 b): no restriction. -/
def ProductSpecific (_M : Finset Product) : Prop := True

/-- Number of distorted products (`θ ≠ N`) of a menu. -/
noncomputable def nDist (M : Finset Product) : ℕ :=
  by classical exact (M.filter (fun j => j.θ ≠ Ctx.N)).card

/-- `M'` is cheaper than `M` under footnote 4's infinitesimal costs: fewer products, or as many
products and fewer distorted ones. -/
def Cheaper (M' M : Finset Product) : Prop :=
  M'.card < M.card ∨ (M'.card = M.card ∧ nDist M' < nDist M)

/-- Competitive equilibrium (§II.D, p. 9, with footnote 4, p. 8) for a technology `Tech`.
Profit is `π^k = D^k · margin^k` with `D^k > 0` iff `PosDemand`, so the conditions are:
(1) menus are feasible; (2) zero profit; (3) Nash: no deviation with positive demand and
positive margin; (4) a firm without demand offers nothing; (5) no cheaper menu with positive
demand earns at least the current margin. -/
def IsCompEq (P : Params) (Tech : Finset Product → Prop) (σ : Profile P) : Prop :=
  (∀ k, Tech (σ k)) ∧
  (∀ k, PosDemand P σ k → margin P (σ k) = 0) ∧
  (∀ k (M' : Finset Product), Tech M' → PosDemand P (Function.update σ k M') k →
      margin P M' ≤ 0) ∧
  (∀ k, ¬ PosDemand P σ k → σ k = ∅) ∧
  (∀ k, PosDemand P σ k → ∀ M' : Finset Product, Tech M' → Cheaper M' (σ k) →
      PosDemand P (Function.update σ k M') k → margin P M' < margin P (σ k))

/-- The firms with strictly positive demand. -/
noncomputable def active (P : Params) (σ : Profile P) : Finset (Fin P.K) :=
  by classical exact Finset.univ.filter (fun k => PosDemand P σ k)

/-- ν^(Q,Q) (Proposition 2 a). -/
def nuQQ (P : Params) : ℝ := (P.qQ - P.c P.qQ) + (P.β - 1) * (P.qQ - P.qlow)

/-- ν^(P,P) (Proposition 2 a). -/
def nuPP (P : Params) : ℝ := (P.qP - P.c P.qP) + (P.β - 1) * (P.b - P.c P.qP)

/-- ν^(P,Q) := βq^Q − c(q^Q) + (β − 1)b, the switching surplus (4) at the (P,Q) optimum. -/
def nuPQ (P : Params) : ℝ := P.β * P.qQ - P.c P.qQ + (P.β - 1) * P.b

/-- (Q*): target (q^Q, c(q^Q)), context Q. -/
def tQ (P : Params) : Product := ⟨P.qQ, P.c P.qQ, Ctx.Q⟩

/-- (Q*): attraction product (q̲, c(q^Q) − β(q^Q − q̲)), context Q. -/
def aQ (P : Params) : Product := ⟨P.qlow, P.c P.qQ - P.β * (P.qQ - P.qlow), Ctx.Q⟩

/-- (P*): target (q^P, c(q^P)), context P. -/
def tP (P : Params) : Product := ⟨P.qP, P.c P.qP, Ctx.P⟩

/-- (P*) as corrected by Proposition 2 (p. 16): attraction product
(q^P + β[b − c(q^P)], b), context P. -/
def aP (P : Params) : Product := ⟨P.qP + P.β * (P.b - P.c P.qP), P.b, Ctx.P⟩

/-- (PQ*): target (q^Q, c(q^Q)), context Q. -/
def tPQ (P : Params) : Product := ⟨P.qQ, P.c P.qQ, Ctx.Q⟩

/-- (PQ*): attraction product (β(q^Q + b) − c(q^Q), b), context P. -/
def aPQ (P : Params) : Product := ⟨P.β * (P.qQ + P.b) - P.c P.qQ, P.b, Ctx.P⟩

/-- Menu `M` consists of a target `t` and an attraction product `a ≠ t`: `t` is sold, and every
type β̃ ∈ (1, β) predicts exactly `a`. -/
def Roles (P : Params) (M : Finset Product) (t a : Product) : Prop :=
  M = {t, a} ∧ t ≠ a ∧ Sells P M t ∧ ∀ γ ∈ Set.Ioo 1 P.β, Pred P M γ = {a}

end ContextFooling.FoolingEq


