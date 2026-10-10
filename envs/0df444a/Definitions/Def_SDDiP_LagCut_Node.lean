-- Prove2me | Definitions.Def_SDDiP_LagCut_Node
-- name    : SDDiP_LagCut_Node
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:45:27.930888+00:00
-- url     : https://prove2.me/theorems/6306364e-e2ef-46a6-98ea-9795f26b1894
-- title:
--   A node of SDDiP: $X_n$, $f_n$, the cuts $\psi^{i+1}_n$, $X'_n$, $X''_n$, the Lagrangian $\mathcal L^i_n$ (4.3)–(4.4), and the values (2.3), (3.1)
-- statement:
--   Fix a node $n$ of the scenario tree of a multistage stochastic integer program with binary state variables, and an iteration $i$ of the stochastic nested decomposition (SND) or SDDiP algorithm. The node carries the following data.
--
--   1. A **nodal constraint set** $X_n \subseteq \mathbb R^d \times \mathbb R^d \times \mathbb R^\ell$ of triples $(z_n, x_n, y_n)$: $x_n$ is the node's state, $y_n$ its local variables, and $z_n$ the **local copy** of the parent's state $x_{a(n)}$. By assumption (A1), $X_n$ is a nonempty, compact, mixed integer polyhedral set.
--   2. A **linear objective** $f_n(x_n, y_n) = c^\top x_n + e^\top y_n$ (assumption (A1)).
--   3. A lower bound $L_n \in \mathbb R$.
--   4. The children $m \in \mathcal C(n)$ of the node with conditional probabilities $q_{nm} \ge 0$, and for every child $m$ and every earlier iteration $\ell = 1, \dots, i$ the cut coefficients $(v^\ell_m, \pi^\ell_m) \in \mathbb R \times \mathbb R^d$ generated at $m$.
--
--   From these data the paper builds the following objects.
--
--   - The **approximate expected cost-to-go** (3.2), with the cuts of iterations $1,\dots,i$:
--   $$\psi^{i+1}_n(x) = \min\Big\{\theta : \theta \ge L_n,\ \theta \ge \sum_{m\in\mathcal C(n)} q_{nm}\big(v^\ell_m + (\pi^\ell_m)^\top x\big)\ \ \forall \ell = 1,\dots,i\Big\}.$$
--   - The sets $X'_n = \{(z,x,y) \in X_n : x \in \{0,1\}^d,\ z \in [0,1]^d\}$ and
--   $$X''_n = \Big\{(z,x,y,\theta) : (z,x,y) \in X'_n,\ \theta \ge L_n,\ \theta \ge \sum_{m\in\mathcal C(n)} q_{nm}\big(v^\ell_m + (\pi^\ell_m)^\top x\big)\ \forall \ell = 1,\dots,i\Big\}.$$
--   - The **Lagrangian function** (4.4) and the **Lagrangian dual** $(R^i_n)$ (4.3) at a parent state $\hat x$:
--   $$\mathcal L^i_n(\pi) = \min\big\{ f_n(x,y) + \theta - \pi^\top z : (z,x,y,\theta) \in X''_n \big\},\qquad (R^i_n):\ \max_{\pi \in \mathbb R^d} \big\{\mathcal L^i_n(\pi) + \pi^\top \hat x\big\}.$$
--     A multiplier $\hat\pi$ is *optimal* for $(R^i_n)$ if it maximizes $\pi \mapsto \mathcal L^i_n(\pi) + \pi^\top\hat x$ over all of $\mathbb R^d$.
--   - The **updated forward problem** $P^i_n(\hat x, \psi^{i+1}_n)$ of (3.1) and its optimal value
--   $$\underline Q^i_n(\hat x, \psi^{i+1}_n) = \min\big\{ f_n(x,y) + \psi^{i+1}_n(x) : (z,x,y) \in X_n,\ z \in [0,1]^d,\ z = \hat x,\ x \in \{0,1\}^d \big\}.$$
--   - For given true value functions $Q_m$ of the children, the expected cost-to-go $\mathcal Q_n(x) = \sum_{m\in\mathcal C(n)} q_{nm} Q_m(x)$ and the **true nodal problem** (2.3) at a parent state $x_a$,
--   $$Q_n(x_a) = \min\big\{ f_n(x,y) + \mathcal Q_n(x) : (z,x,y) \in X_n,\ z \in [0,1]^d,\ z = x_a,\ x \in \{0,1\}^d\big\}.$$
--
--   These are the objects of §4.3 of the paper: Theorem 3 compares the value of the Lagrangian dual with the forward value $\underline Q^i_n$ (tightness) and with the true value $Q_n$ (validity).
--
--   **Formalization Note** States, copies and duals live in $\mathbb R^d$ = `Fin d → ℝ`; a state is binary when each coordinate is $0$ or $1$. Elements of $X''_n$ are tuples `(z, x, y, θ)`. The cuts are indexed by `ℓ : Fin i` and the children by `m : Fin nC`; a last-stage node has `nC = 0`, and then every aggregated cut is the constant $0$. The constraint (2.1c) $z \in [0,1]^d$ is folded into $X_n$ in (2.3) and (3.1), as the paper does outside §4.3 (p. 468). $\psi^{i+1}_n$, $\mathcal L^i_n$, $\underline Q^i_n$ and $Q_n$ are written as infima (`sInf`) of the corresponding sets of objective values; the theorems that use them state every minimum as an attained least element (`IsLeast`) or as a lower bound over the feasible points, so no value of `sInf` on an empty or unbounded set is ever relied on. The value sets themselves (`lagValues`, `fwdValues`, `trueValues`) are part of the definition. Assumption (A1) is carried by the fields `X_nonempty`, `X_compact`, `X_polyhedral`; the probabilities $q_{nm}$ are only required to be nonnegative.
-- source:
--   Zou, Ahmed, Sun, Stochastic dual dynamic integer programming, Math. Program. 175 (2019), pp. 467–471 and 478: (A1), (2.1), (2.3), (3.1)–(3.2), (4.3)–(4.4) and the definitions of X′_n, X″_n

import Mathlib
import Definitions.Def_SDDiP_LagCut_MixedIntegerPolyhedral

namespace SDDiP.LagCut

/-- A vector of `ℝᵈ` is binary when every coordinate is `0` or `1` (the state space `{0,1}ᵈ`, (2.1d)). -/
def IsBinary {d : ℕ} (x : Fin d → ℝ) : Prop := ∀ j, x j = 0 ∨ x j = 1

/-- A vector of `ℝᵈ` lies in the unit box `[0,1]ᵈ` (constraint (2.1c)). -/
def InUnitBox {d : ℕ} (z : Fin d → ℝ) : Prop := ∀ j, 0 ≤ z j ∧ z j ≤ 1

/-- The coordinates `(z, x, y)` of `ℝᵈ × ℝᵈ × ℝˡ` written as one vector of `ℝ^{d+d+l}`. -/
def flatten {d l : ℕ} (w : (Fin d → ℝ) × (Fin d → ℝ) × (Fin l → ℝ)) : Fin (d + d + l) → ℝ :=
  Fin.append (Fin.append w.1 w.2.1) w.2.2

/-- The data of one node `n` of the scenario tree in the backward step of an iteration `i` of SND/SDDiP
(Zou, Ahmed, Sun, Math. Program. 175 (2019), §2, (A1) and (2.1), pp. 467–468; §3.1, (3.1)–(3.2),
pp. 470–471; §4.3, (4.4), p. 478).

* `X ⊆ ℝᵈ × ℝᵈ × ℝˡ` is the nodal constraint set `X_n` of triples `(z_n, x_n, y_n)`: local copy `z_n` of
  the parent state, state `x_n`, local variables `y_n`. Assumption (A1): `X` is a nonempty compact mixed
  integer polyhedral set.
* `f_n(x, y) = cᵀx + eᵀy` is the linear nodal objective (A1).
* `L` is the lower bound `L_n` of (3.2a).
* The node has `nC` children `m`, with conditional probabilities `q m = q_{nm} ≥ 0`.
* `i` is the number of cuts so far: for `ℓ = 1, …, i` (index `ℓ : Fin i`) and each child `m`, the cut
  coefficients `(v ℓ m, π ℓ m) = (v^ℓ_m, π^ℓ_m)` generated at `m`. These are the cuts of (4.4), i.e. those
  defining `ψ^{i+1}_n` in (3.2b). -/
structure Node (d l : ℕ) where
  X : Set ((Fin d → ℝ) × (Fin d → ℝ) × (Fin l → ℝ))
  X_nonempty : X.Nonempty
  X_compact : IsCompact X
  X_polyhedral : IsMixedIntegerPolyhedral (flatten '' X)
  c : Fin d → ℝ
  e : Fin l → ℝ
  L : ℝ
  nC : ℕ
  q : Fin nC → ℝ
  q_nonneg : ∀ m, 0 ≤ q m
  i : ℕ
  v : Fin i → Fin nC → ℝ
  π : Fin i → Fin nC → Fin d → ℝ

namespace Node

variable {d l : ℕ} (N : Node d l)

/-- The linear nodal objective `f_n(x, y) = cᵀx + eᵀy`. -/
def f (x : Fin d → ℝ) (y : Fin l → ℝ) : ℝ := N.c ⬝ᵥ x + N.e ⬝ᵥ y

/-- The aggregated cut `ℓ` of (3.2b)/(4.4): `x ↦ ∑_{m ∈ C(n)} q_{nm} (v^ℓ_m + (π^ℓ_m)ᵀ x)`. -/
def cut (ℓ : Fin N.i) (x : Fin d → ℝ) : ℝ := ∑ m, N.q m * (N.v ℓ m + N.π ℓ m ⬝ᵥ x)

/-- The approximate expected cost-to-go `ψ^{i+1}_n` of (3.2):
`ψ(x) = min {θ : θ ≥ L_n, θ ≥ ∑_m q_{nm}(v^ℓ_m + (π^ℓ_m)ᵀx) ∀ ℓ}`.
(The set is a closed half-line, so the infimum is its least element.) -/
noncomputable def ψ (x : Fin d → ℝ) : ℝ := sInf {θ : ℝ | N.L ≤ θ ∧ ∀ ℓ, N.cut ℓ x ≤ θ}

/-- `X_n` with the constraint (2.1c) `z_n ∈ [0,1]ᵈ` folded in, as the paper does outside §4.3 (p. 468). -/
def Xbox : Set ((Fin d → ℝ) × (Fin d → ℝ) × (Fin l → ℝ)) := {w | w ∈ N.X ∧ InUnitBox w.1}

/-- `X′_n` (p. 478): the triples `(z, x, y) ∈ X_n` with `x ∈ {0,1}ᵈ` and `z ∈ [0,1]ᵈ`. -/
def X' : Set ((Fin d → ℝ) × (Fin d → ℝ) × (Fin l → ℝ)) :=
  {w | w ∈ N.X ∧ IsBinary w.2.1 ∧ InUnitBox w.1}

/-- `X″_n` (p. 478): the quadruples `(z, x, y, θ)` with `(z, x, y) ∈ X′_n`, `θ ≥ L_n` and
`θ ≥ ∑_m q_{nm}(v^ℓ_m + (π^ℓ_m)ᵀx)` for every cut `ℓ`. -/
def X'' : Set ((Fin d → ℝ) × (Fin d → ℝ) × (Fin l → ℝ) × ℝ) :=
  {p | (p.1, p.2.1, p.2.2.1) ∈ N.X' ∧ N.L ≤ p.2.2.2 ∧ ∀ ℓ, N.cut ℓ p.2.1 ≤ p.2.2.2}

/-- The objective `f_n(x, y) + θ` on quadruples `(z, x, y, θ)`. -/
def obj (p : (Fin d → ℝ) × (Fin d → ℝ) × (Fin l → ℝ) × ℝ) : ℝ := N.f p.2.1 p.2.2.1 + p.2.2.2

/-- The values of the Lagrangian objective `f_n(x, y) + θ − πᵀz` over `X″_n`. -/
def lagValues (π : Fin d → ℝ) : Set ℝ := (fun p => N.obj p - π ⬝ᵥ p.1) '' N.X''

/-- The Lagrangian function `𝓛^i_n(π)` of (4.4): the minimum of `f_n(x, y) + θ − πᵀz` over `X″_n`.
(When `X″_n` is nonempty this set of values is bounded below and attains its infimum, since `X` is
compact and the objective is increasing in `θ`.) -/
noncomputable def lag (π : Fin d → ℝ) : ℝ := sInf (N.lagValues π)

/-- The objective `𝓛^i_n(π) + πᵀx̂` of the Lagrangian dual (4.3) at the parent state `x̂`. -/
noncomputable def dualObj (xhat π : Fin d → ℝ) : ℝ := N.lag π + π ⬝ᵥ xhat

/-- `π̂` is an optimal solution of the Lagrangian dual `(R^i_n)` of (4.3) at the parent state `x̂`:
it maximizes `π ↦ 𝓛^i_n(π) + πᵀx̂` over all of `ℝᵈ`. -/
def IsDualOptimal (xhat πhat : Fin d → ℝ) : Prop := ∀ π, N.dualObj xhat π ≤ N.dualObj xhat πhat

/-- The objective values of the updated forward problem `P^i_n(x̂, ψ^{i+1}_n)` of (3.1):
`f_n(x, y) + ψ^{i+1}_n(x)` over `(z, x, y) ∈ X_n` (with (2.1c)), `z = x̂`, `x ∈ {0,1}ᵈ`. -/
noncomputable def fwdValues (xhat : Fin d → ℝ) : Set ℝ :=
  {t | ∃ x y, (xhat, x, y) ∈ N.Xbox ∧ IsBinary x ∧ t = N.f x y + N.ψ x}

/-- The optimal value `Q̲^i_n(x̂, ψ^{i+1}_n)` of the forward problem (3.1) with the updated
approximation `ψ^{i+1}_n`. -/
noncomputable def fwdValue (xhat : Fin d → ℝ) : ℝ := sInf (N.fwdValues xhat)

/-- The expected cost-to-go `𝒬_n(x) = ∑_{m ∈ C(n)} q_{nm} Q_m(x)` built from the children's true value
functions `Qc m = Q_m`. -/
def expCostToGo (Qc : Fin N.nC → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := ∑ m, N.q m * Qc m x

/-- The objective values of the true nodal problem `(P_n)` of (2.3) at the parent state `x_a`:
`f_n(x, y) + 𝒬(x)` over `(z, x, y) ∈ X_n` (with (2.1c)), `z = x_a`, `x ∈ {0,1}ᵈ`, for a given expected
cost-to-go `𝒬`. -/
def trueValues (Qexp : (Fin d → ℝ) → ℝ) (xa : Fin d → ℝ) : Set ℝ :=
  {t | ∃ x y, (xa, x, y) ∈ N.Xbox ∧ IsBinary x ∧ t = N.f x y + Qexp x}

/-- The true value `Q_n(x_a)` of (2.3) for a given expected cost-to-go `𝒬` (the minimum of
`trueValues`; the paper's value is `+∞` when the set is empty). -/
noncomputable def trueValue (Qexp : (Fin d → ℝ) → ℝ) (xa : Fin d → ℝ) : ℝ := sInf (N.trueValues Qexp xa)

end Node

end SDDiP.LagCut


