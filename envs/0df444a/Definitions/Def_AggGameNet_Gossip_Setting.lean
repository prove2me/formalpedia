-- Prove2me | Definitions.Def_AggGameNet_Gossip_Setting
-- name    : AggGameNet_Gossip_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:27.213961+00:00
-- url     : https://prove2.me/theorems/69e7645d-b5cc-4c15-8e76-563623f75b85
-- title:
--   Aggregative game and gossip update model, §§2 and 4.1
-- statement:
--   There are $N\ge1$ agents. Agent $i$ chooses $x_i$ in a set $K_i\subseteq\mathbb R^n$, and the aggregate is $\bar x=\sum_jx_j$. The map $F_i(x_i,u)$ is evaluated at the player's decision and an aggregate argument. The associated variational inequality asks for $x^*\in\prod_iK_i$ such that
--
--   $$
--   \sum_i\langle x_i-x_i^*,F_i(x_i^*,\bar x^*)\rangle\ge0
--   \quad\text{for every }x\in\prod_iK_i.
--   $$
--
--   A connected undirected graph carries positive contact probabilities $p_{ij}$ on its edges, with each row summing to one. At each discrete tick, a waking agent $I^k$ is uniform and contacts $J^k$ with conditional probability $p_{I^kJ^k}$; the pairs are independent across ticks. The two selected agents average their aggregate estimates, take projected steps with $\alpha_{k,i}=1/\Gamma_k(i)$, and update their estimates by their decision changes. Here $\Gamma_k(i)$ counts updates through tick $k$.
--
--   These definitions provide the exact state and stochastic law used by the convergence result and its milestones.
--
--   **Formalization Note** The continuous-time Poisson clocks are represented by their induced independent sequence of tick pairs. The initial strategy profile is deterministic. Projections are represented by the nearest-point relation. The Lipschitz condition on $F_i(x_i,\cdot)$ is imposed on all of $\mathbb R^n$, because the paper's algorithm may evaluate it outside $\bar K$; the discrepancy is recorded in the mission description.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, (1), (5)–(8), Assumptions 1–3 and 7, (23)–(29), pp. 4–7, 15–17

import Mathlib
import Definitions.Def_AggGameNet_Sync_Game
import Definitions.Def_AggGameNet_Sync_Setting

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal
noncomputable section

namespace AggGameNet.Gossip

def IsVISol {N n : ℕ} (K : Fin N → Set (AggGameNet.Sync.E n))
    (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n) (xs : Fin N → AggGameNet.Sync.E n) : Prop :=
  (∀ i, xs i ∈ K i) ∧
    ∀ x : Fin N → AggGameNet.Sync.E n, (∀ i, x i ∈ K i) →
      0 ≤ ∑ i, inner ℝ (x i - xs i) (AggGameNet.Sync.phi F xs i)

def IsProj {n : ℕ} (S : Set (AggGameNet.Sync.E n)) (y p : AggGameNet.Sync.E n) : Prop :=
  p ∈ S ∧ ∀ q ∈ S, ‖y - p‖ ≤ ‖y - q‖

def GossipProbs {N : ℕ} (G : SimpleGraph (Fin N))
    (p : Fin N → Fin N → ℝ) : Prop :=
  (∀ i j, G.Adj i j → 0 < p i j) ∧
    (∀ i j, ¬ G.Adj i j → p i j = 0) ∧
    ∀ i, ∑ j, p i j = 1

def GossipDraws {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (I J : ℕ → Ω → Fin N)
    (p : Fin N → Fin N → ℝ) : Prop :=
  (∀ k, Measurable (I k) ∧ Measurable (J k)) ∧
  (∀ k i j, P {ω | I k ω = i ∧ J k ω = j} = ENNReal.ofReal (p i j / (N : ℝ))) ∧
  iIndepFun (fun k ω => (I k ω, J k ω)) P

def upd {N : ℕ} {Ω : Type*} (I J : ℕ → Ω → Fin N)
    (k : ℕ) (ω : Ω) (i : Fin N) : Prop :=
  I k ω = i ∨ J k ω = i

def Gam {N : ℕ} {Ω : Type*} (I J : ℕ → Ω → Fin N)
    (k : ℕ) (ω : Ω) (i : Fin N) : ℕ :=
  by
    classical
    exact ((Finset.range (k + 1)).filter (fun t => upd I J t ω i)).card

def alphaG {N : ℕ} {Ω : Type*} (I J : ℕ → Ω → Fin N)
    (k : ℕ) (ω : Ω) (i : Fin N) : ℝ :=
  1 / (Gam I J k ω i : ℝ)

def gossipW {N : ℕ} (a b : Fin N) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (if i = j then 1 else 0) -
    (1 / 2 : ℝ) * ((if i = a then 1 else 0) - (if i = b then 1 else 0)) *
      ((if j = a then 1 else 0) - (if j = b then 1 else 0))

def vhat {N n : ℕ} {Ω : Type*} (I J : ℕ → Ω → Fin N)
    (v : ℕ → Ω → Fin N → AggGameNet.Sync.E n) (k : ℕ) (ω : Ω) (i : Fin N) : AggGameNet.Sync.E n :=
  ∑ j, (gossipW (I k ω) (J k ω) i j) • v k ω j

def yavg {N n : ℕ} {Ω : Type*} (v : ℕ → Ω → Fin N → AggGameNet.Sync.E n)
    (k : ℕ) (ω : Ω) : AggGameNet.Sync.E n :=
  (1 / (N : ℝ)) • ∑ i, v k ω i

def pbar {N : ℕ} (p : Fin N → Fin N → ℝ) (i : Fin N) : ℝ :=
  (1 / (N : ℝ)) * (1 + ∑ j, p j i)

def IsGossipRun {N n : ℕ} {Ω : Type*}
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (I J : ℕ → Ω → Fin N) (x₀ : Fin N → AggGameNet.Sync.E n)
    (x v : ℕ → Ω → Fin N → AggGameNet.Sync.E n) : Prop :=
  (∀ i, x₀ i ∈ K i) ∧
  ∀ ω, x 0 ω = x₀ ∧ v 0 ω = x₀ ∧
    ∀ k i,
      (upd I J k ω i →
        IsProj (K i)
          (x k ω i - alphaG I J k ω i •
            F i (x k ω i) ((N : ℝ) • vhat I J v k ω i))
          (x (k + 1) ω i)) ∧
      (¬ upd I J k ω i → x (k + 1) ω i = x k ω i) ∧
      v (k + 1) ω i = vhat I J v k ω i + x (k + 1) ω i - x k ω i

def Dz {N : ℕ} (a b : Fin N) (z : Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j, (gossipW a b i j - 1 / (N : ℝ)) * z j

def euclidNorm {N : ℕ} (z : Fin N → ℝ) : ℝ :=
  Real.sqrt (∑ i, z i ^ 2)

end AggGameNet.Gossip


