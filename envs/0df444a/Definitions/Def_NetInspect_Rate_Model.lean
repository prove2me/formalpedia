-- Prove2me | Definitions.Def_NetInspect_Rate_Model
-- name    : NetInspect_Rate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:21.811094+00:00
-- url     : https://prove2.me/theorems/db36b00c-8f14-4111-aff9-4bf2ced28ca8
-- title:
--   §2–§3.2, (1)–(7), (EC.1)–(EC.2), (EC.8)–(EC.11) — detection model, detection function, set covers and packings, n*, m*, the game Γ(b1,b2), detection rate, value, (LP̄1)/(LP̄2), cyclic strategies
-- statement:
--   This file sets up the network inspection game of Dahan, Sela and Amin.
--
--   **Detection model.** A detection model $\mathcal G=(\mathcal V,\mathcal E,\{\mathcal C_i,\ i\in\mathcal V\})$ consists of a finite set $\mathcal V$ of nodes, a finite set $\mathcal E$ of network components, and for each node $i$ the set $\mathcal C_i\subseteq\mathcal E$ of components monitored by a detector placed at $i$. Every component is monitored from at least one node. For $S\subseteq\mathcal V$ write $\mathcal C_S=\bigcup_{i\in S}\mathcal C_i$. The **detection function** is
--   $$
--   F(S,T)=|\mathcal C_S\cap T|,\qquad S\subseteq\mathcal V,\ T\subseteq\mathcal E,
--   $$
--   the number of components of $T$ monitored by at least one detector of $S$.
--
--   **Covers and packings.** $S\subseteq\mathcal V$ is a **set cover** if $F(S,\{e\})=1$ for every $e\in\mathcal E$, and a **minimal set cover** if moreover no $S\setminus\{i\}$, $i\in S$, is a set cover. $T\subseteq\mathcal E$ is a **set packing** if $F(\{i\},T)\le 1$ for every node $i$. The number $n^*$ is the smallest size of a set cover and $m^*$ the largest size of a set packing.
--
--   **The game $\Gamma(b_1,b_2)$.** The defender (P1) places at most $b_1$ detectors: her pure actions are $\mathcal A_1=\{S\subseteq\mathcal V: |S|\le b_1\}$. The attacker (P2) attacks at most $b_2$ components: $\mathcal A_2=\{T\subseteq\mathcal E:|T|\le b_2\}$. Mixed strategies $\sigma^1\in\Delta(\mathcal A_1)$, $\sigma^2\in\Delta(\mathcal A_2)$ are probability vectors on these finite sets. The attacker's payoff is the expected number of undetected attacks
--   $$
--   U(\sigma^1,\sigma^2)=\sum_{S\in\mathcal A_1}\sum_{T\in\mathcal A_2}\sigma^1_S\,\sigma^2_T\,\bigl(|T|-F(S,T)\bigr),
--   $$
--   and the defender's payoff is $-U$. A profile $(\sigma^{1*},\sigma^{2*})$ is a **Nash equilibrium** if $U(\sigma^{1*},\sigma^2)\le U(\sigma^{1*},\sigma^{2*})\le U(\sigma^1,\sigma^{2*})$ for all mixed $\sigma^1,\sigma^2$. The **expected detection rate** is
--   $$
--   r(\sigma^1,\sigma^2)=\sum_{S}\sum_{T}\sigma^1_S\,\sigma^2_T\,\frac{F(S,T)}{|T|},
--   $$
--   where the ratio for the empty attack plan $T=\emptyset$ is taken to be $1$.
--
--   **Values and linear programs.** $\max_{T\in\mathcal A_2}U(\sigma^1,T)$ and $\min_{S\in\mathcal A_1}U(S,\sigma^2)$ are the objectives of (LP1) and (LP2), and the **value** $U^*(b_1,b_2)$ is the optimal value of (LP1), $\min_{\sigma^1\in\Delta(\mathcal A_1)}\max_{T\in\mathcal A_2}U(\sigma^1,T)$. With $\bar{\mathcal A}_1=\{S:|S|=b_1\}$ and $\bar{\mathcal A}_2=\{T:|T|=b_2\}$, an optimal solution of $(\overline{\mathrm{LP}}_1)$ is a $\sigma^1\in\Delta(\bar{\mathcal A}_1)$ minimizing $\max_{T\in\bar{\mathcal A}_2}U(\sigma^1,T)$, and an optimal solution of $(\overline{\mathrm{LP}}_2)$ is a $\sigma^2\in\Delta(\bar{\mathcal A}_2)$ maximizing $\min_{S\in\bar{\mathcal A}_1}U(S,\sigma^2)$. The marginal $\rho_\sigma(a)=\sum_{X\ni a}\sigma_X$ is the inspection probability of a node (EC.1) or the attack probability of a component (EC.2).
--
--   **Cyclic strategies.** For a set $\{x_0,\dots,x_{n-1}\}$ listed without repetition and $b\ge 0$, the window $W_k=\{x_k,x_{k+1},\dots,x_{k+b-1}\}$ (indices mod $n$), $0\le k<n$, is the paper's $S^{k+1}$ of (EC.8)–(EC.9), and the cyclic strategy $\sigma(S,b)$ of (EC.10)–(EC.11) gives probability $1/n$ to each of the $n$ windows.
--
--   These objects carry every statement of the mission: the bounds on the value (Proposition 1), the structure of equilibria (Theorem 1), and the invariance of the equilibrium detection rate in $b_2$ (Theorem 2).
--
--   **Formalization Note** The game is an instance of the published finite zero-sum game `BlottoLP.Flow.ZeroSum`: the row player is the attacker (rows indexed by $\mathcal A_2$), the column player the defender, and the matrix entry is $|T|-F(S,T)$; `IsNE` is that file's `IsNashEq`, which is exactly (5). Mixed strategies are real weight functions on the subtypes $\{X : |X|\le b\}$ (or $|X|=b$ for $\bar{\mathcal A}$), so an inspection strategy never uses more than $b_1$ detectors. Maxima and minima over the finite action sets are `sSup`/`sInf` of finite ranges, which are attained whenever the action set is nonempty ($\mathcal A_1,\mathcal A_2$ always contain $\emptyset$; $\bar{\mathcal A}_1,\bar{\mathcal A}_2$ are nonempty under the standing assumptions $b_1<n^*$, $b_2<m^*$). $U^*$ is an infimum over the mixed strategies of values bounded below by $0$. The paper leaves $F(S,\emptyset)/|\emptyset|$ undefined; the convention that it equals $1$ is pinned here (with Lean's $0/0=0$ the equilibrium rate would vary when $b_1\ge n^*$). The coverage assumption makes the set of cover sizes nonempty, so $n^*$ is not the junk value of `sInf ∅`; the set of packing sizes is nonempty and bounded by $|\mathcal E|$.
-- source:
--   Dahan, Sela & Amin, Network Inspection for Detecting Strategic Attacks, arXiv:1705.00349v4, pp. 6–11, §2–§3.2, (1)–(7); p. 14, Theorem 1 ((LP̄1), (LP̄2)); p. ec1, (EC.1)–(EC.2); p. ec2, Lemma EC.3, (EC.8)–(EC.11)

import Mathlib
import Definitions.Def_BlottoLP_Flow_ZeroSum

namespace NetInspect.Rate

open Finset

/-- The detection model `G = (V, E, {C i, i ∈ V})` of §2.1 (pp. 6–7): finite sets `V` of nodes and
`E` of components, and for every node `i` the set `C i ⊆ E` of components monitored by a detector
at `i`. The field `coverable` is the standing assumption of p. 7: every component can be monitored
from at least one node. -/
structure DetectionModel (V E : Type*) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] where
  /-- `C i`: the components monitored by a detector positioned at node `i`. -/
  C : V → Finset E
  /-- Each component in `E` can be monitored from at least one node in `V` (p. 7). -/
  coverable : ∀ e : E, ∃ i : V, e ∈ C i

/-- The pure actions of a player with `b` resources over the ground set `α`: subsets of size at
most `b`. `Act V b1` is the set `A1` of detector positionings and `Act E b2` the set `A2` of
attack plans (p. 7). -/
abbrev Act (α : Type*) (b : ℕ) := {X : Finset α // X.card ≤ b}

/-- Subsets of size exactly `b`: `ActEx V b1` is `Ā1 = {S | |S| = b1}` and `ActEx E b2` is
`Ā2 = {T | |T| = b2}` (Theorem 1, p. 14). -/
abbrev ActEx (α : Type*) (b : ℕ) := {X : Finset α // X.card = b}

/-- The restriction of a weight function on `Act α b` to the subsets of size exactly `b`. -/
def restrictEx {α : Type*} {b : ℕ} (σ : Act α b → ℝ) : ActEx α b → ℝ :=
  fun X => σ ⟨X.1, X.2.le⟩

/-- The marginal `ρ_σ(a) = Σ_{X ∋ a} σ_X` of a weight function `σ` on a family of subsets of `α`:
the inspection probability (EC.1) of a node, or the attack probability (EC.2) of a component. -/
def marg {α : Type*} [Fintype α] [DecidableEq α] {p : Finset α → Prop} [DecidablePred p]
    (σ : {X : Finset α // p X} → ℝ) (a : α) : ℝ :=
  ∑ X, if a ∈ X.1 then σ X else 0

/-- The cyclic window of Lemma EC.3 (EC.8)/(EC.9), 0-based: for an enumeration
`x 0, …, x (n-1)` of a set and `k < n`, the set `{x k, x (k+1), …, x (k+b-1)}`, indices taken
mod `n`. Window `k` is the book's `S^{k+1}`. -/
def window {α : Type*} [DecidableEq α] {n : ℕ} (x : Fin n → α) (b : ℕ) (k : Fin n) : Finset α :=
  (Finset.range b).image fun j => x ⟨(k.val + j) % n, Nat.mod_lt _ k.pos⟩

theorem window_card_le {α : Type*} [DecidableEq α] {n : ℕ} (x : Fin n → α) (b : ℕ) (k : Fin n) :
    (window x b k).card ≤ b :=
  card_image_le.trans (by simp)

/-- The cyclic strategy `σ(S, b)` of Lemma EC.3 (EC.10)/(EC.11): probability `1/n` on each of
the `n` windows `window x b k`, `k < n` (windows that coincide add up their probabilities). -/
noncomputable def cycStrat {α : Type*} [DecidableEq α] {n : ℕ} (x : Fin n → α) (b : ℕ) :
    Act α b → ℝ :=
  fun X => ((Finset.univ.filter fun k => window x b k = X.1).card : ℝ) / n

namespace DetectionModel

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- `C_S = ⋃_{i ∈ S} C i`, the components monitored by at least one detector in `S` (p. 7). -/
def CS (G : DetectionModel V E) (S : Finset V) : Finset E := S.biUnion G.C

/-- The detection function (1): `F(S, T) = |C_S ∩ T|`, the number of attacked components in `T`
monitored by the positioning `S`. -/
def F (G : DetectionModel V E) (S : Finset V) (T : Finset E) : ℕ := (G.CS S ∩ T).card

/-- `S` is a set cover (p. 11): `F(S, e) = 1` for every component `e`. -/
def IsSetCover (G : DetectionModel V E) (S : Finset V) : Prop := ∀ e : E, G.F S {e} = 1

/-- `S` is a minimal set cover (p. 11): a set cover such that removing any node of `S` leaves a
set that is not a set cover. -/
def IsMinimalSetCover (G : DetectionModel V E) (S : Finset V) : Prop :=
  G.IsSetCover S ∧ ∀ i ∈ S, ¬ G.IsSetCover (S.erase i)

/-- `T` is a set packing (p. 11): `F({i}, T) ≤ 1` for every node `i`. -/
def IsSetPacking (G : DetectionModel V E) (T : Finset E) : Prop := ∀ i : V, G.F {i} T ≤ 1

/-- `n*`, the size of a minimum set cover, the optimal value of (6). The set is nonempty by the
field `coverable` (`univ` is a set cover). -/
noncomputable def nStar (G : DetectionModel V E) : ℕ :=
  sInf {k | ∃ S : Finset V, S.card = k ∧ G.IsSetCover S}

/-- `m*`, the size of a maximum set packing, the optimal value of (7). The set is nonempty
(`∅` is a packing) and bounded by `|E|`. -/
noncomputable def mStar (G : DetectionModel V E) : ℕ :=
  sSup {k | ∃ T : Finset E, T.card = k ∧ G.IsSetPacking T}

/-- The number of undetected attacks `|T| − F(S, T)`, P2's payoff in (2). -/
def undet (G : DetectionModel V E) (S : Finset V) (T : Finset E) : ℝ :=
  (T.card : ℝ) - (G.F S T : ℝ)

/-- The payoff matrix of `Γ(b1, b2)` (p. 10), rows indexed by P2's attack plans `T ∈ A2` (the
maximizer), columns by P1's positionings `S ∈ A1` (the minimizer). -/
def payoff (G : DetectionModel V E) (b1 b2 : ℕ) : Act E b2 → Act V b1 → ℝ :=
  fun T S => G.undet S.1 T.1

/-- The same payoff restricted to `Ā2 × Ā1` (the matrix of (LP̄1)/(LP̄2), p. 14). -/
def payoffEx (G : DetectionModel V E) (b1 b2 : ℕ) : ActEx E b2 → ActEx V b1 → ℝ :=
  fun T S => G.undet S.1 T.1

/-- The expected number of undetected attacks (2), `U(σ1, σ2) = E_{(σ1,σ2)}[|T| − F(S, T)]`. -/
def U (G : DetectionModel V E) {b1 b2 : ℕ} (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) : ℝ :=
  BlottoLP.Flow.expPay (G.payoff b1 b2) σ2 σ1

/-- The detection ratio `F(S, T)/|T|` of (3), with the convention `F(S, ∅)/|∅| := 1` (an empty
attack plan counts as fully detected); the paper leaves this case undefined. -/
noncomputable def ratio (G : DetectionModel V E) (S : Finset V) (T : Finset E) : ℝ :=
  if T = ∅ then 1 else (G.F S T : ℝ) / (T.card : ℝ)

/-- The expected detection rate (3), `r(σ) = E_σ[F(S, T)/|T|]`. -/
noncomputable def rate (G : DetectionModel V E) {b1 b2 : ℕ} (σ1 : Act V b1 → ℝ)
    (σ2 : Act E b2 → ℝ) : ℝ :=
  BlottoLP.Flow.expPay (fun (T : Act E b2) (S : Act V b1) => G.ratio S.1 T.1) σ2 σ1

/-- `(σ1, σ2)` is a mixed Nash equilibrium (5) of `Γ(b1, b2)`: `σ1 ∈ Δ(A1)`, `σ2 ∈ Δ(A2)`, and
`U(σ1, τ2) ≤ U(σ1, σ2) ≤ U(τ1, σ2)` for all `τ1 ∈ Δ(A1)`, `τ2 ∈ Δ(A2)`. -/
def IsNE (G : DetectionModel V E) (b1 b2 : ℕ) (σ1 : Act V b1 → ℝ) (σ2 : Act E b2 → ℝ) : Prop :=
  BlottoLP.Flow.IsNashEq (G.payoff b1 b2) σ2 σ1

/-- P2's best pure-response value against `σ1`: `max_{T ∈ A2} U(σ1, T)`, the objective of (LP1). -/
noncomputable def worst1 (G : DetectionModel V E) {b1 : ℕ} (b2 : ℕ) (σ1 : Act V b1 → ℝ) : ℝ :=
  sSup (Set.range fun T : Act E b2 => G.U σ1 (BlottoLP.Flow.pureMixed T))

/-- P1's best pure-response value against `σ2`: `min_{S ∈ A1} U(S, σ2)`, the objective of (LP2). -/
noncomputable def best2 (G : DetectionModel V E) (b1 : ℕ) {b2 : ℕ} (σ2 : Act E b2 → ℝ) : ℝ :=
  sInf (Set.range fun S : Act V b1 => G.U (BlottoLP.Flow.pureMixed S) σ2)

/-- The value `U*(b1, b2)` of `Γ(b1, b2)`, the optimal value of
(LP1) `min_{σ1 ∈ Δ(A1)} max_{T ∈ A2} U(σ1, T)` (p. 10). -/
noncomputable def gameValue (G : DetectionModel V E) (b1 b2 : ℕ) : ℝ :=
  sInf ((G.worst1 b2) '' {σ1 : Act V b1 → ℝ | BlottoLP.Flow.IsMixed σ1})

/-- The objective of (LP̄1): `max_{T ∈ Ā2} U(σ1, T)` for `σ1 ∈ Δ(Ā1)`. -/
noncomputable def worst1Ex (G : DetectionModel V E) {b1 : ℕ} (b2 : ℕ) (σ1 : ActEx V b1 → ℝ) : ℝ :=
  sSup (Set.range fun T : ActEx E b2 =>
    BlottoLP.Flow.expPay (G.payoffEx b1 b2) (BlottoLP.Flow.pureMixed T) σ1)

/-- The objective of (LP̄2): `min_{S ∈ Ā1} U(S, σ2)` for `σ2 ∈ Δ(Ā2)`. -/
noncomputable def best2Ex (G : DetectionModel V E) (b1 : ℕ) {b2 : ℕ} (σ2 : ActEx E b2 → ℝ) : ℝ :=
  sInf (Set.range fun S : ActEx V b1 =>
    BlottoLP.Flow.expPay (G.payoffEx b1 b2) σ2 (BlottoLP.Flow.pureMixed S))

/-- `σ1` is an optimal solution of (LP̄1): `σ1 ∈ Δ(Ā1)` minimizes `max_{T ∈ Ā2} U(·, T)` over
`Δ(Ā1)`. -/
def IsOptLP1bar (G : DetectionModel V E) (b1 b2 : ℕ) (σ1 : ActEx V b1 → ℝ) : Prop :=
  BlottoLP.Flow.IsMixed σ1 ∧
    ∀ τ1 : ActEx V b1 → ℝ, BlottoLP.Flow.IsMixed τ1 → G.worst1Ex b2 σ1 ≤ G.worst1Ex b2 τ1

/-- `σ2` is an optimal solution of (LP̄2): `σ2 ∈ Δ(Ā2)` maximizes `min_{S ∈ Ā1} U(S, ·)` over
`Δ(Ā2)`. -/
def IsOptLP2bar (G : DetectionModel V E) (b1 b2 : ℕ) (σ2 : ActEx E b2 → ℝ) : Prop :=
  BlottoLP.Flow.IsMixed σ2 ∧
    ∀ τ2 : ActEx E b2 → ℝ, BlottoLP.Flow.IsMixed τ2 → G.best2Ex b1 τ2 ≤ G.best2Ex b1 σ2

end DetectionModel

end NetInspect.Rate


