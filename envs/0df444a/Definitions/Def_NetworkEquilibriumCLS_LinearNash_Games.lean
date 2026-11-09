-- Prove2me | Definitions.Def_NetworkEquilibriumCLS_LinearNash_Games
-- name    : NetworkEquilibriumCLS_LinearNash_Games
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:55.835407+00:00
-- url     : https://prove2.me/theorems/52d88eef-ced2-43e3-8743-bc141e534994
-- title:
--   Succinct directed networks and binary common-payoff coordination games
-- statement:
--   A network consists of explicitly indexed vertices, directed edges, players, terminals, and rational edge coefficients α_e. Validity requires positive player and vertex counts, nonnegative coefficients, and a simple directed path between each player's terminals. Every such path is available; a path is a list of edges with a vertex list having no repetition. Equal terminals admit the empty path. Distinct parallel edges can be represented. A DAG has a strict topological order. The separate simplicity predicate excludes parallel edges for the stronger hardness restriction.
--
--   For a pure profile P the number of users of edge e is k_e(P), and
--
--   $$\operatorname{cost}_i(P)=\sum_{e\in P_i}\alpha_e k_e(P).$$
--
--   Mixed profiles are independent lotteries from the published finite-game interface. Expected payoffs are negative expected costs. Nash requires genuine lotteries and the expected-cost inequality against every feasible pure path. A supporting theorem relates this to all-lottery unilateral deviations.
--
--   A coordination game has binary actions and one rational common-payoff matrix for each undirected edge, indexed once by i<j. Valid entries lie in [0,1]. Utility sums incident edge expectations, and Φ_G sums each edge expectation once. A real vector x in the cube specifies the independent probability of action 1 at each vertex. Nash compares each player's current expected utility with both pure deviations. These definitions supply all real-profile semantics independently of the computational answer format.
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.2 (PDF 3), §1.1; pp.6–8 (PDF 7–9), §§2.2–2.3, Definitions 2.3 and 2.6.

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics

open Finset

noncomputable section

namespace NetworkEquilibriumCLS.LinearNash

/-- Succinct directed-network data of §1.1 and §2.3. Strategies are not input fields. -/
structure Network where
  vertices : ℕ
  edges : ℕ
  players : ℕ
  tail : Fin edges → Fin vertices
  head : Fin edges → Fin vertices
  source : Fin players → Fin vertices
  sink : Fin players → Fin vertices
  alpha : Fin edges → ℚ

/-- An edge list is a simple directed path, including the empty path when s=t. -/
def IsPath (G : Network) (i : Fin G.players) (es : List (Fin G.edges)) : Prop :=
  ∃ vs : List (Fin G.vertices), vs.Nodup ∧ vs.length = es.length + 1 ∧
    vs.head? = some (G.source i) ∧ vs.getLast? = some (G.sink i) ∧
    ∀ j : Fin es.length,
      vs[j.val]? = some (G.tail es[j.val]) ∧
      vs[j.val + 1]? = some (G.head es[j.val])

def FeasibleEdges (G : Network) (i : Fin G.players) (S : Finset (Fin G.edges)) : Prop :=
  ∃ es, IsPath G i es ∧ es.toFinset = S

abbrev PathAction (G : Network) (i : Fin G.players) :=
  {S : Finset (Fin G.edges) // FeasibleEdges G i S}

instance (G : Network) (i : Fin G.players) : Fintype (PathAction G i) := Fintype.ofFinite _

def NetworkValid (G : Network) : Prop :=
  0 < G.players ∧ 0 < G.vertices ∧ (∀ e, 0 ≤ G.alpha e) ∧
    ∀ i, ∃ es, IsPath G i es

/-- No parallel edges. This additional hardness promise is satisfied by the source construction. -/
def NetworkSimple (G : Network) : Prop :=
  ∀ e f, G.tail e = G.tail f → G.head e = G.head f → e = f

/-- A topological order exists; irrelevant vertices and zero coefficients are permitted. -/
def NetworkDAG (G : Network) : Prop :=
  ∃ order : Fin G.vertices → ℕ, ∀ e, order (G.tail e) < order (G.head e)

def edgeLoad (G : Network) (P : ∀ i, PathAction G i) (e : Fin G.edges) : ℕ :=
  (univ.filter fun i => e ∈ (P i).val).card

def pathCost (G : Network) (P : ∀ i, PathAction G i) (i : Fin G.players) : ℝ :=
  ∑ e ∈ (P i).val, (G.alpha e : ℝ) * edgeLoad G P e

def networkPayoff (G : Network) (i : Fin G.players) (P : ∀ j, PathAction G j) : ℝ :=
  -pathCost G P i

/-- Definition 2.6: all pure deviations, product-distribution costs, with genuine lotteries. -/
def NetworkNash (G : Network) (σ : ∀ i, PathAction G i → ℝ) : Prop :=
  AGT.IsMixedProfile σ ∧ ∀ i (P : PathAction G i),
    AGT.expectedPayoff (networkPayoff G)
        (Function.update σ i (fun S => if S = P then 1 else 0)) i ≤
      AGT.expectedPayoff (networkPayoff G) σ i

/-- Binary common-payoff network of §2.2. Only entries with i<j and edge=true are used. -/
structure Coordination (N : ℕ) where
  edge : Fin N → Fin N → Bool
  payoff : Fin N → Fin N → Bool → Bool → ℚ

def CoordinationValid {N : ℕ} (G : Coordination N) : Prop :=
  ∀ i j, i < j → G.edge i j = true → ∀ a b, 0 ≤ G.payoff i j a b ∧ G.payoff i j a b ≤ 1

def edgeExpectation {N : ℕ} (G : Coordination N) (x : Fin N → ℝ) (i j : Fin N) : ℝ :=
  (1-x i)*(1-x j)*(G.payoff i j false false : ℝ) +
  (1-x i)*x j*(G.payoff i j false true : ℝ) +
  x i*(1-x j)*(G.payoff i j true false : ℝ) +
  x i*x j*(G.payoff i j true true : ℝ)

def coordinationPotential {N : ℕ} (G : Coordination N) (x : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ univ.filter (fun j => i < j ∧ G.edge i j = true), edgeExpectation G x i j

def coordinationUtility {N : ℕ} (G : Coordination N) (x : Fin N → ℝ) (i : Fin N) : ℝ :=
  (∑ j ∈ univ.filter (fun j => i < j ∧ G.edge i j = true), edgeExpectation G x i j) +
  ∑ j ∈ univ.filter (fun j => j < i ∧ G.edge j i = true), edgeExpectation G x j i

def CoordinationNash {N : ℕ} (G : Coordination N) (x : Fin N → ℝ) : Prop :=
  InCube x ∧ ∀ i (a : Bool),
    coordinationUtility G (Function.update x i (if a then 1 else 0)) i ≤
      coordinationUtility G x i

end NetworkEquilibriumCLS.LinearNash


