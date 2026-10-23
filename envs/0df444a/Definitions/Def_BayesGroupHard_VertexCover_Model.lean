-- Prove2me | Definitions.Def_BayesGroupHard_VertexCover_Model
-- name    : BayesGroupHard_VertexCover_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:49.661773+00:00
-- url     : https://prove2.me/theorems/426ebe62-5f80-4a50-9463-f3daf9362873
-- title:
--   §2, §2.1, §4 (4)–(6) and Appendix A, pp. 6–29 — the binary action model, information sets, posteriors, MAP actions and the vertex-cover network
-- statement:
--   **The binary action model.** A finite set of agents $\mathcal A$ is given, together with a neighbourhood $\mathcal N_i \subseteq \mathcal A$ for every agent $i$, with $i \in \mathcal N_i$: agent $i$ observes the actions of the agents in $\mathcal N_i$, herself included. The state of the world is $\theta \in \{0,1\}$, drawn from the uniform prior $\nu(0) = \nu(1) = \tfrac12$. Every agent $i$ receives a private signal $s_i \in \{0,1\}$ with law $\mathbb P_{i,\theta}(1) = p_{i,\theta}$, $\mathbb P_{i,\theta}(0) = 1 - p_{i,\theta}$; conditionally on $\theta$ the signals are independent, so a profile $s = (s_i)_i$ has probability
--   $$\mathbb P_\theta(s) = \prod_{i \in \mathcal A} \mathbb P_{i,\theta}(s_i).$$
--
--   For a set $\mathcal I$ of signal profiles the **posterior** is (4)
--   $$\mu(\theta \mid \mathcal I) = \frac{\nu(\theta) \sum_{s \in \mathcal I} \mathbb P_\theta(s)}{\sum_{\theta' \in \{0,1\}} \nu(\theta') \sum_{s \in \mathcal I} \mathbb P_{\theta'}(s)},$$
--   and, since the utility is $u(a,\theta) = \mathbf 1(a = \theta)$, the **action** (5)–(6) on $\mathcal I$ is the maximum a posteriori state, with ties broken towards the lowest action $0$: it is $1$ iff $\mu(0 \mid \mathcal I) < \mu(1 \mid \mathcal I)$.
--
--   Actions and **information sets** are defined jointly by recursion on time $t \in \mathbb N$. On the signal profile $s$, the information set of agent $i$ at time $t$ is
--   $$\mathcal I_{i,t}(s) = \{ s' : s'_i = s_i \text{ and } a_{j,\tau}(s') = a_{j,\tau}(s) \text{ for all } j \in \mathcal N_i,\ \tau < t \},$$
--   the profiles consistent with $i$'s history $h_{i,t} = \{s_i\} \cup \{a_{j,\tau} : j \in \mathcal N_i,\ \tau < t\}$ of (1); her belief is $\mu_{i,t}(\theta) = \mu(\theta \mid \mathcal I_{i,t}(s))$ and her action $a_{i,t}(s)$ is the action on $\mathcal I_{i,t}(s)$. The **log-belief ratio** (2) is $\phi_{i,t} = \log(\mu_{i,t}(1)/\mu_{i,t}(0))$.
--
--   **The vertex-cover network** (Appendix A). For a simple graph $G$ on the vertex set $\{0,\dots,n-1\}$ with $m$ edges the network has $n + m + 2$ agents: a vertex agent $\tau_v$ for every vertex, an edge agent $\varepsilon_e$ for every edge, and two agents $i$ and $\kappa$. The neighbourhoods are $\mathcal N_{\tau_v} = \{\tau_v\}$, $\mathcal N_{\varepsilon_e} = \{\varepsilon_e, \tau_u, \tau_w\}$ for $e = \{u,w\}$, $\mathcal N_i = \{i, \kappa\} \cup \{\varepsilon_e : e \in E(G)\}$ and $\mathcal N_\kappa = \{\kappa\}$. The signal structures are
--   $$\mathbb P_{\tau,1}(1) = 0.4 =: \bar p, \qquad \mathbb P_{\tau,0}(1) = 0.3 =: \underline p$$
--   for vertex agents, the non-informative $\mathbb P_{\cdot,\theta}(1) = \tfrac12$ for edge agents and for $i$, and, for $\kappa$, $\mathbb P_{\kappa,0}(0) = k_0$ and $\mathbb P_{\kappa,1}(0) = k_1$, two parameters.
--
--   Finally, with $\bar q(\alpha) = \bar p^{\alpha}(1-\bar p)^{1-\alpha}$ and $\underline q(\alpha) = \underline p^{\alpha}(1-\underline p)^{1-\alpha}$ (p. 28), the log-ratio $\tilde q(\alpha) = \log(\bar q(\alpha)/\underline q(\alpha))$ and the value
--   $$\lambda_\kappa(0) = -\frac n2\bigl(\tilde q(0.998) + \tilde q(0.999)\bigr)$$
--   that the paper prescribes for $\kappa$'s log-likelihood ratio $\log(\mathbb P_{\kappa,1}(0)/\mathbb P_{\kappa,0}(0))$ (p. 29).
--
--   These are the objects of the paper's main hardness theorem: Theorems 1 and 6 assert that the belief of agent $i$ at time two in this network separates graphs with small vertex covers from graphs whose vertex covers are all large.
--
--   **Formalization Note.** States, signals and actions are `Bool` with `false = 0`, `true = 1`. The network is `BinNet` (neighbourhoods, the axiom $i \in \mathcal N_i$, and `p i θ` $= \mathbb P_{i,\theta}(1)$); no range condition on `p` is built in, theorems state what they need. `post`, `mapAct`, `infoSet`, `act`, `logBelief` are (4), (5)/(6), $\mathcal I_{i,t}$, $a_{i,t}$, $\phi_{i,t}$; the prior $\tfrac12$ is written out. The actions at all earlier times are computed by structural recursion on $t$ (`actUpTo N t τ j s` is $a_{j,\tau}(s)$ for $\tau < t$). The conjunct $s'_i = s_i$ comes from the history $h_{i,t}$ of (1); Function I of Algorithm 0 (p. 17) leaves it implicit. The decimals are rationals: $0.4 = 4/10$, $0.998 = 998/1000$, etc. `qbar`, `qund`, `qtil` use real powers; the paper writes the log-ratio $\tilde q$ also as $q$ on p. 29. Agents of the network are the inductive type `Agent n G` with constructors `vtx v`, `edg e` (for `e : G.edgeSet`), `iAg`, `kap`; `vcNet G k₀ k₁` is the network.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, pp. 6–8 (§2, (1), §2.1, §2.2 (2)), p. 16 (§4, (4)–(6)), p. 17 (Algorithm 0), pp. 27–29 (Appendix A, (10), (11), choice of λκ(0))

import Mathlib
import Definitions.Def_bernoulliRelativeEntropy

namespace BayesGroupHard.VertexCover

open Finset

/-! ### The binary action model (§2, §2.1, §4 of Hązła–Jadbabaie–Mossel–Rahimian)

States, signals and actions are `Bool`, with `false = 0` and `true = 1`. -/

/-- A network of agents in the binary action model: the neighbourhoods `N_i` (each agent
observes herself, p. 6) and the signal structure `p i θ = P_{i,θ}(1)`. -/
structure BinNet (Ag : Type) where
  /-- `nbr i = N_i`, the agents whose actions agent `i` observes. -/
  nbr : Ag → Finset Ag
  /-- `i ∈ N_i` (p. 6). -/
  self_mem : ∀ i, i ∈ nbr i
  /-- `p i θ = P_{i,θ}(1)`, the probability that agent `i`'s signal is `1` in state `θ`. -/
  p : Ag → Bool → ℝ

variable {Ag : Type} [Fintype Ag] [DecidableEq Ag]

/-- The law of one signal: `sig N i θ b = P_{i,θ}(b)`. -/
def sig (N : BinNet Ag) (i : Ag) (θ : Bool) (b : Bool) : ℝ :=
  if b then N.p i θ else 1 - N.p i θ

/-- The joint law of a signal profile, `P_θ(s) = ∏_i P_{i,θ}(s_i)` (conditional
independence, p. 6). -/
def jointProb (N : BinNet Ag) (θ : Bool) (s : Ag → Bool) : ℝ :=
  ∏ i, sig N i θ (s i)

/-- The posterior (4), p. 16, on a set `I` of signal profiles, with the uniform prior
`ν(θ) = 1/2`. -/
noncomputable def post (N : BinNet Ag) (θ : Bool) (I : Finset (Ag → Bool)) : ℝ :=
  ((1 / 2) * ∑ s ∈ I, jointProb N θ s) /
    (∑ θ' : Bool, (1 / 2) * ∑ s ∈ I, jointProb N θ' s)

/-- The action (5)/(6) in the binary action model (`u(a, θ) = 1(a = θ)`): the MAP estimate,
with ties broken towards the lowest-ranked action `false = 0`. -/
noncomputable def mapAct (N : BinNet Ag) (I : Finset (Ag → Bool)) : Bool :=
  decide (post N false I < post N true I)

/-- The signal profiles `s'` agent `i` cannot distinguish from `s` at time `t`, when the
actions at times `τ < t` are given by `past τ j`: `s'_i = s_i` and every neighbour `j ∈ N_i`
took the same actions at all times `τ < t` (the history `h_{i,t}` of (1), p. 6). -/
def infoUsing (N : BinNet Ag) (t : ℕ) (past : ℕ → Ag → (Ag → Bool) → Bool) (i : Ag)
    (s : Ag → Bool) : Finset (Ag → Bool) :=
  univ.filter (fun s' => s' i = s i ∧ ∀ j ∈ N.nbr i, ∀ τ < t, past τ j s' = past τ j s)

/-- `actUpTo N t τ j s` is the action `a_{j,τ}` on the signal profile `s` for every time
`τ < t` (and `false` for `τ ≥ t`), defined by recursion on `t`. -/
noncomputable def actUpTo (N : BinNet Ag) : ℕ → ℕ → Ag → (Ag → Bool) → Bool
  | 0 => fun _ _ _ => false
  | t + 1 => fun τ j s =>
      if τ < t then actUpTo N t τ j s
      else if τ = t then mapAct N (infoUsing N t (actUpTo N t) j s)
      else false

/-- The information set `I_{i,t}` of agent `i` at time `t` on the signal profile `s`
(p. 16): the profiles agreeing with `s` in `s_i` and in the actions of all neighbours at all
times `τ < t`. -/
noncomputable def infoSet (N : BinNet Ag) (t : ℕ) (i : Ag) (s : Ag → Bool) : Finset (Ag → Bool) :=
  infoUsing N t (actUpTo N t) i s

/-- The action `a_{i,t}` of agent `i` at time `t` on the signal profile `s`. -/
noncomputable def act (N : BinNet Ag) (t : ℕ) (i : Ag) (s : Ag → Bool) : Bool :=
  mapAct N (infoSet N t i s)

/-- The log-belief ratio (2), `φ_{i,t} = log(µ_{i,t}(1) / µ_{i,t}(0))`. -/
noncomputable def logBelief (N : BinNet Ag) (t : ℕ) (i : Ag) (s : Ag → Bool) : ℝ :=
  Real.log (post N true (infoSet N t i s) / post N false (infoSet N t i s))

/-! ### The VERTEX-COVER reduction network (Appendix A, pp. 27–29) -/

/-- The agents of the network built from a graph `G` on `n` vertices: vertex agents `τ_v`,
edge agents `ε_e`, agent `i` and agent `κ`. -/
inductive Agent (n : ℕ) (G : SimpleGraph (Fin n)) : Type
  | vtx : Fin n → Agent n G
  | edg : G.edgeSet → Agent n G
  | iAg : Agent n G
  | kap : Agent n G
  deriving DecidableEq

namespace Agent

variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-- `Agent n G` is `Fin n ⊕ G.edgeSet ⊕ Bool`. -/
def equivSum : Agent n G ≃ Fin n ⊕ G.edgeSet ⊕ Bool where
  toFun
    | .vtx v => .inl v
    | .edg e => .inr (.inl e)
    | .iAg => .inr (.inr false)
    | .kap => .inr (.inr true)
  invFun
    | .inl v => .vtx v
    | .inr (.inl e) => .edg e
    | .inr (.inr false) => .iAg
    | .inr (.inr true) => .kap
  left_inv := by intro a; cases a <;> rfl
  right_inv := by
    intro x
    rcases x with v | e | b
    · rfl
    · rfl
    · cases b <;> rfl

instance [DecidableRel G.Adj] : Fintype (Agent n G) :=
  Fintype.ofEquiv _ equivSum.symm

end Agent

open Agent

/-- The reduction network of Appendix A for the graph `G`, with agent `κ`'s signal structure
given by `k₀ = P_{κ,0}(0)` and `k₁ = P_{κ,1}(0)`:
* `N_{τ_v} = {τ_v}`, `N_{ε_e} = {ε_e, τ_u, τ_w}` for `e = {u, w}`,
  `N_i = {i, κ} ∪ {all ε_e}`, `N_κ = {κ}`;
* `P_{τ,1}(1) = 0.4`, `P_{τ,0}(1) = 0.3` for vertex agents; edge agents and `i` have the
  non-informative `P_{·,θ}(1) = 1/2`; `P_{κ,θ}(1) = 1 - P_{κ,θ}(0)`. -/
noncomputable def vcNet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ) :
    BinNet (Agent n G) where
  nbr
    | .vtx v => {.vtx v}
    | .edg e => insert (.edg e)
        ((univ.filter (fun v : Fin n => v ∈ (e : Sym2 (Fin n)))).image Agent.vtx)
    | .iAg => insert .iAg (insert .kap (univ.image Agent.edg))
    | .kap => {.kap}
  self_mem := by intro i; cases i <;> simp
  p
    | .vtx _, true => 4 / 10
    | .vtx _, false => 3 / 10
    | .edg _, _ => 1 / 2
    | .iAg, _ => 1 / 2
    | .kap, θ => 1 - (if θ then k₁ else k₀)

/-- `q̄(α) = p̄^α (1 - p̄)^(1-α)` with `p̄ = 0.4` (p. 28, (10)). -/
noncomputable def qbar (α : ℝ) : ℝ := (4 / 10 : ℝ) ^ α * (6 / 10 : ℝ) ^ (1 - α)

/-- `q(α) = p^α (1 - p)^(1-α)` with `p = 0.3` (p. 28, (11); underlined in print). -/
noncomputable def qund (α : ℝ) : ℝ := (3 / 10 : ℝ) ^ α * (7 / 10 : ℝ) ^ (1 - α)

/-- The log-ratio `q̃(α) = log(q̄(α) / q(α))` of p. 29 (printed there as `q(α)`). -/
noncomputable def qtil (α : ℝ) : ℝ := Real.log (qbar α / qund α)

/-- Agent `κ`'s log-likelihood ratio `λ_κ(0) = -(n/2)(q̃(0.998) + q̃(0.999))` (p. 29). -/
noncomputable def lamKappa0 (n : ℕ) : ℝ :=
  -((n : ℝ) / 2) * (qtil (998 / 1000) + qtil (999 / 1000))

end BayesGroupHard.VertexCover


