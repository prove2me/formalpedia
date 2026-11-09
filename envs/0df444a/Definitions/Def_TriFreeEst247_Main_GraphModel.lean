-- Prove2me | Definitions.Def_TriFreeEst247_Main_GraphModel
-- name    : TriFreeEst247_Main_GraphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:56:38.956411+00:00
-- url     : https://prove2.me/theorems/1b8d2de7-82c8-4fd2-bb7a-c2f6f9e3431e
-- title:
--   Dense graph distance, query algorithms, and triangle-freeness complexities
-- statement:
--   Let $G$ be a finite simple graph on $[n]$, with $n\ge1$. Its triangle count $\operatorname{Tri}(G)$ counts unordered three-vertex cliques. Write $\mathrm{TF}$ for triangle-freeness. Define
--
--   $$\operatorname{dist}(G,\mathrm{TF})=\frac{1}{n^2}\min_{H\in\mathrm{TF}}|E(G)\mathbin{\triangle}E(H)|.$$
--
--   The minimum ranges over every triangle-free graph on the same vertices. An adjacency algorithm is a family of randomized decision trees, given only $n$, querying ordered vertex pairs and receiving the corresponding adjacency bit. A worst-case bound $q$ holds for every tree in the distribution's support, every oracle, and every graph order. Correctness is required only on graph oracles with $n\ge1$.
--
--   An $\varepsilon$-tester accepts triangle-free graphs and rejects graphs at distance at least $\varepsilon$, in each case with probability at least $2/3$. An $\varepsilon$-estimator outputs a real number within $\varepsilon$ of the distance with probability at least $2/3$. The minima of their uniform query bounds are $T_\triangle(\varepsilon)$ and $E_\triangle(\varepsilon)$.
--
--   $$R_\triangle(\varepsilon)=\inf\{R\ge1:\ \operatorname{dist}(G,\mathrm{TF})\ge\varepsilon\Longrightarrow\operatorname{Tri}(G)\ge n^3/R\text{ for all }n,G\}.$$
--
--   These objects specify the information available to algorithms and the exact complexities compared by the goal.
--
--   **Formalization Note** Vertices are `Fin n`; diagonal queries return false. The query minima lie in $\mathbb N\cup\{\infty\}$ and the removal infimum in $[0,\infty]$, with infinity for an empty feasible set. The finite graph minimum is attained. At $n=0$ the helper distance is zero; algorithm correctness excludes this order. Event probabilities are computed by pushing the output law to its Boolean event indicator. The finite-behavior reduction described in MODERATION_NOTES preserves the source's arbitrary randomness exactly.
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.1–3, §§1.1–1.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical

open scoped ENNReal symmDiff

noncomputable section

namespace TriFreeEst247.Main

/-- Sections 1.1--1.3, pp.1--3: finite simple graphs with ordered-pair adjacency queries. -/
abbrev Graph (n : ℕ) := SimpleGraph (Fin n)
abbrev EdgeSet (n : ℕ) := Finset (Sym2 (Fin n))

def edges {n : ℕ} (G : Graph n) : EdgeSet n := by
  classical
  exact G.edgeFinset

def triangles {n : ℕ} (G : Graph n) : ℕ := by
  classical
  exact (G.cliqueFinset 3).card

def triangleFree {n : ℕ} (G : Graph n) : Prop := G.CliqueFree 3

/-- A genuine minimum: its defining set is finite and contains the empty graph's cost.
At n=0 every cost is 0. No deletion-only equivalence is assumed here. -/
def distance {n : ℕ} (G : Graph n) : ℝ := by
  classical
  exact sInf {r : ℝ | ∃ H : Graph n, triangleFree H ∧
    r = ((edges G ∆ edges H).card : ℝ) / (n : ℝ)^2}

def graphOracle {n : ℕ} (G : Graph n) : Fin n × Fin n → Bool := by
  classical
  exact fun p => decide (G.Adj p.1 p.2)

abbrev GraphAlgorithm (α : Type) :=
  (n : ℕ) → QAlgorithms.RandDecisionTree (Fin n × Fin n) Bool α

/-- Probability of an event in the output law; the Bool pushforward avoids any
measurability convention on the arbitrary output type. -/
def outputProb {ι κ α : Type} (A : QAlgorithms.RandDecisionTree ι κ α)
    (oracle : ι → κ) (event : α → Prop) : ℝ≥0∞ := by
  classical
  exact (((A.map (fun t => t.eval oracle)).map (fun a => decide (event a))) true)

def hasQueryBound {α : Type} (A : GraphAlgorithm α) (q : ℕ) : Prop :=
  ∀ n, QAlgorithms.RandMakesAtMost (A n) q

def isTester (ε : ℝ) (A : GraphAlgorithm Bool) : Prop :=
  ∀ n, 1 ≤ n → ∀ G : Graph n,
    (triangleFree G → (2 / 3 : ℝ≥0∞) ≤ outputProb (A n) (graphOracle G) (· = true)) ∧
    (ε ≤ distance G → (2 / 3 : ℝ≥0∞) ≤ outputProb (A n) (graphOracle G) (· = false))

def isEstimator (ε : ℝ) (A : GraphAlgorithm ℝ) : Prop :=
  ∀ n, 1 ≤ n → ∀ G : Graph n,
    (2 / 3 : ℝ≥0∞) ≤ outputProb (A n) (graphOracle G) (fun z => |z - distance G| ≤ ε)

/-- Minima of the finite worst-case bounds, with top if no uniform algorithm exists. -/
def testingComplexity (ε : ℝ) : ℕ∞ :=
  sInf {q : ℕ∞ | ∃ k : ℕ, q = (k : ℕ∞) ∧
    ∃ A : GraphAlgorithm Bool, hasQueryBound A k ∧ isTester ε A}

def estimationComplexity (ε : ℝ) : ℕ∞ :=
  sInf {q : ℕ∞ | ∃ k : ℕ, q = (k : ℕ∞) ∧
    ∃ A : GraphAlgorithm ℝ, hasQueryBound A k ∧ isEstimator ε A}

def isRemovalBound (ε R : ℝ) : Prop :=
  1 ≤ R ∧ ∀ n, 1 ≤ n → ∀ G : Graph n,
    ε ≤ distance G → (n : ℝ)^3 / R ≤ (triangles G : ℝ)

/-- Infimum of real removal bounds, embedded in ENNReal. Empty set gives top.
For positive ε the removal lemma ensures finiteness; closedness gives attainment. -/
def removalParameter (ε : ℝ) : ℝ≥0∞ :=
  sInf (ENNReal.ofReal '' {R : ℝ | isRemovalBound ε R})

end TriFreeEst247.Main


