-- Prove2me | Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
-- name    : ArrowDebreu_Shared_AbstractEconomy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:37:02.610395+00:00
-- url     : https://prove2.me/theorems/a8f2c06d-7616-488e-b672-d0ee09f6f0f0
-- title:
--   Abstract economy, its equilibrium points, and continuity of constraint correspondences
-- statement:
--   An **abstract economy** (a generalized game) consists of finitely many players $\iota$, each with an action set $\mathfrak A_\iota \subseteq \mathbb R^l$, a real pay-off function $f_\iota$ on profiles $a = (a_\iota)_\iota$, and a constraint correspondence $A_\iota$ assigning to the actions $\bar a_\iota$ of the *other* players a set $A_\iota(\bar a_\iota) \subseteq \mathfrak A_\iota$. Write $\mathfrak A = \prod_\iota \mathfrak A_\iota$ and $\bar{\mathfrak A}_\iota = \prod_{\iota' \ne \iota} \mathfrak A_{\iota'}$.
--
--   1. A profile $a^*$ is an **equilibrium point** if $a^* \in \mathfrak A$ and, for every $\iota$, $a_\iota^* \in A_\iota(\bar a_\iota^*)$ and
--   $$f_\iota(\bar a_\iota^*, a_\iota^*) = \max_{a_\iota \in A_\iota(\bar a_\iota^*)} f_\iota(\bar a_\iota^*, a_\iota).$$
--   2. The **graph** of $A_\iota$ is $\{a : \bar a_\iota \in \bar{\mathfrak A}_\iota,\ a_\iota \in A_\iota(\bar a_\iota)\}$.
--   3. $A_\iota$ is **continuous at** $\bar a_\iota^0 \in \bar{\mathfrak A}_\iota$ if for every $a_\iota^0 \in A_\iota(\bar a_\iota^0)$ and every sequence $\bar a_\iota^k \to \bar a_\iota^0$ in $\bar{\mathfrak A}_\iota$ there is a sequence $a_\iota^k \to a_\iota^0$ with $a_\iota^k \in A_\iota(\bar a_\iota^k)$ for **all** $k$; it is **continuous** if it is continuous at every point of $\bar{\mathfrak A}_\iota$.
--
--   When every $A_\iota$ is constant the abstract economy is a game and an equilibrium point is a Nash equilibrium. The generalization lets one agent's choice restrict another's feasible actions, as prices restrict a consumer's budget; the existence proof of Arrow and Debreu is built on it.
--
--   **Formalization Note** Constraint sets and pay-offs are functions of whole profiles; a structure field requires $A_\iota$ to ignore the $\iota$-th coordinate, and another requires $A_\iota(\bar a_\iota) \subseteq \mathfrak A_\iota$ whenever $\bar a_\iota \in \bar{\mathfrak A}_\iota$. The maximum in the equilibrium condition is written as "no $b \in A_\iota(\bar a_\iota^*)$ gives a larger pay-off", without a supremum. Continuity is the sequential lower hemicontinuity of the paper, with convergence required only in the other players' coordinates.
--
--   It serves both missions of the series: `01-theorem-i` (Lemma 2.5, p. 274, PDF p. 11, and the abstract economies $E$, $\tilde E$ of §3, pp. 274–279, PDF pp. 11–16) and `02-theorem-ii` (the abstract economies $E_\varepsilon$, $\tilde E_\varepsilon$ of §5, pp. 282–284, PDF pp. 19–21); both use §2.1 and the Definition of §2.3 (p. 273, PDF p. 10), and `01-theorem-i` also the graph and continuity notions of §2.4 (pp. 273–274, PDF pp. 10–11). It is reviewed once for both.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, pp. 273–274 (PDF pp. 10–11), §2.1 (abstract economy), §2.3 (Definition of equilibrium point), §2.4 (graph, continuity)

import Mathlib

namespace ArrowDebreu.Shared

open Filter Topology

/-- **Abstract economy** (Arrow & Debreu 1954, §2.1, p. 273, PDF p. 10).

There are players indexed by `ι` (the paper's `ι = 1, ⋯, ν`), each choosing an action in a set
`act ι = 𝔄_ι ⊆ R^l`. A *profile* `a : ι → R^l` lists every player's action; `𝔄 = Π_ι 𝔄_ι`. Each
player has a real pay-off function `payoff ι = f_ι` on profiles, and a constraint set
`constr ι a = A_ι(ā_ι) ⊆ 𝔄_ι` which depends only on the actions `ā_ι` of the *other* players.

**Formalization Note.** The paper types `A_ι` on `𝔄̄_ι = Π_{ι' ≠ ι} 𝔄_{ι'}`. Here `constr ι` is a
function of the whole profile, and the field `constr_indep` says it ignores the `ι`-th coordinate,
so it is a function of `ā_ι`; `constr_subset` is the paper's requirement that `A_ι(ā_ι)` be a subset
of `𝔄_ι` for every `ā_ι ∈ 𝔄̄_ι`. The pay-off `f_ι` is total on `ι → R^l`; only its values on `𝔄`
enter any hypothesis. -/
structure AbstractEconomy (ι : Type*) (l : ℕ) where
  /-- The action sets `𝔄_ι ⊆ R^l`. -/
  act : ι → Set (Fin l → ℝ)
  /-- The pay-off functions `f_ι`, functions of the whole profile. -/
  payoff : ι → (ι → Fin l → ℝ) → ℝ
  /-- The constraint sets `A_ι(ā_ι)`. -/
  constr : ι → (ι → Fin l → ℝ) → Set (Fin l → ℝ)
  /-- `A_ι` depends only on the other players' actions `ā_ι`. -/
  constr_indep : ∀ i (a b : ι → Fin l → ℝ), (∀ k, k ≠ i → a k = b k) → constr i a = constr i b
  /-- `A_ι(ā_ι) ⊆ 𝔄_ι` whenever `ā_ι ∈ 𝔄̄_ι`. -/
  constr_subset : ∀ i (a : ι → Fin l → ℝ), (∀ k, k ≠ i → a k ∈ act k) → constr i a ⊆ act i

namespace AbstractEconomy

variable {ι : Type*} {l : ℕ}

/-- The product `𝔄 = 𝔄_1 × ⋯ × 𝔄_ν` of the action sets (§2.1, p. 273, PDF p. 10). -/
def profiles (G : AbstractEconomy ι l) : Set (ι → Fin l → ℝ) :=
  Set.univ.pi G.act

/-- `ā_ι ∈ 𝔄̄_ι`: every player other than `i` plays in its action set (§2.1, p. 273, PDF p. 10). -/
def OthersIn (G : AbstractEconomy ι l) (i : ι) (a : ι → Fin l → ℝ) : Prop :=
  ∀ k, k ≠ i → a k ∈ G.act k

/-- **Equilibrium point** (Definition, §2.3, p. 273, PDF p. 10): `a^*` is an equilibrium point if,
for every player `ι`, `a_ι^* ∈ A_ι(ā_ι^*)` and `f_ι(ā_ι^*, a_ι^*) = max_{a_ι ∈ A_ι(ā_ι^*)} f_ι(ā_ι^*, a_ι)`.

**Formalization Note.** The maximum is written without a supremum: `a^*` lies in `𝔄`, `a^*_ι` lies in
`A_ι(ā^*_ι)`, and replacing `a^*_ι` by any `b ∈ A_ι(ā^*_ι)` (`Function.update a ι b`) does not raise
`f_ι`. -/
def IsEquilibriumPoint [DecidableEq ι] (G : AbstractEconomy ι l) (a : ι → Fin l → ℝ) : Prop :=
  a ∈ G.profiles ∧
    ∀ i, a i ∈ G.constr i a ∧ ∀ b ∈ G.constr i a, G.payoff i (Function.update a i b) ≤ G.payoff i a

/-- The **graph** of `A_ι(ā_ι)` (§2.4, p. 273, PDF p. 10): the set `{a | a_ι ∈ A_ι(ā_ι)}`, `a`
ranging over profiles with `ā_ι ∈ 𝔄̄_ι` (so, by `constr_subset`, over `𝔄`). -/
def graph (G : AbstractEconomy ι l) (i : ι) : Set (ι → Fin l → ℝ) :=
  {a | G.OthersIn i a ∧ a i ∈ G.constr i a}

/-- **Continuity of `A_ι` at a point** (§2.4, p. 274, PDF p. 11): `A_ι(ā_ι)` is continuous at
`ā_ι^0` if for every `a_ι^0 ∈ A_ι(ā_ι^0)` and every sequence `{ā_ι^k}` (in `𝔄̄_ι`) converging to
`ā_ι^0`, there is a sequence `{a_ι^k}` converging to `a_ι^0` with `a_ι^k ∈ A_ι(ā_ι^k)` for all `k`.

**Formalization Note.** This is lower hemicontinuity, stated with sequences as in the paper. The
point `ā^0_ι` and the sequence are given as profiles whose `ι`-th coordinate is ignored:
convergence is required only in the coordinates `κ ≠ ι`, and membership only in `𝔄̄_ι`. -/
def ConstrContinuousAt (G : AbstractEconomy ι l) (i : ι) (a₀ : ι → Fin l → ℝ) : Prop :=
  ∀ b₀ ∈ G.constr i a₀, ∀ s : ℕ → ι → Fin l → ℝ, (∀ k, G.OthersIn i (s k)) →
    (∀ κ, κ ≠ i → Tendsto (fun k => s k κ) atTop (𝓝 (a₀ κ))) →
    ∃ t : ℕ → Fin l → ℝ, Tendsto t atTop (𝓝 b₀) ∧ ∀ k, t k ∈ G.constr i (s k)

/-- `A_ι` is **continuous** (§2.4, as used in Lemma 2.5, p. 274, PDF p. 11): continuous at every
point `ā_ι ∈ 𝔄̄_ι`. -/
def ConstrContinuous (G : AbstractEconomy ι l) (i : ι) : Prop :=
  ∀ a₀, G.OthersIn i a₀ → G.ConstrContinuousAt i a₀

end AbstractEconomy

end ArrowDebreu.Shared


