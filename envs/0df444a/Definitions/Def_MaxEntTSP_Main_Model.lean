-- Prove2me | Definitions.Def_MaxEntTSP_Main_Model
-- name    : MaxEntTSP_Main_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:31.998913+00:00
-- url     : https://prove2.me/theorems/7965867c-7e5f-4e84-b696-3337bb6a0bab
-- title:
--   Algorithm 1 model: node split, maximum entropy tree law, and odd-vertex matching cost
-- statement:
--   Starting from a metric traveling-salesperson instance and a Held–Karp vector, split a chosen city $u$ into $u_0,v_0$. Assign half of each edge formerly incident to $u$ to each copy and insert the zero-cost unit edge $e_0=\{u_0,v_0\}$. Let $E$ be the positive LP support after removing $e_0$.
--
--   A tree law $\mu$ is a probability distribution supported on spanning trees of $E$ with edge marginals $x_e$. Its entropy is $H(\mu)=\sum_T-\mu(T)\log\mu(T)$, with the continuous convention at zero. `IsMaxEntropy` selects a law that maximizes this entropy among all laws with those marginals.
--
--   If $M_T$ is the minimum-cost perfect matching on the odd-degree vertices of a tree $T$, the algorithmic cost is
--   $$\operatorname{algCost}(c,\mu)=\sum_T\mu(T)\bigl(c(T)+c(M_T)\bigr).$$
--
--   These definitions specify the distribution and output cost in the main theorem. Matchings use an involution, so each matched edge appears twice in the vertex sum and receives a factor of $1/2$.
--
--   **Formalization Note** The law is exactly maximum entropy with exact marginals; the polynomial-time approximately marginal-preserving sampler is outside this mission. The minimum over matchings uses a real infimum of a finite, nonempty set.
-- source:
--   Karlin, Klein & Oveis Gharan, A (Slightly) Improved Approximation Algorithm for Metric TSP, arXiv:2007.01409v6, pp. 2–3 (PDF 4–5), §1.1 and Algorithm 1; p. 6 (PDF 8), §2.2

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost

namespace MaxEntTSP.Main

open MetricTSP Finset

/-- Identify the two copies of the split city with the original city. -/
def proj {n : ℕ} (u : Fin n) : Fin (n + 1) → Fin n := Fin.lastCases u id

def u0 {n : ℕ} (u : Fin n) : Fin (n + 1) := Fin.castSucc u
def v0 (n : ℕ) : Fin (n + 1) := Fin.last n

def splitCost {n : ℕ} (c : Fin n → Fin n → ℝ) (u : Fin n) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => c (proj u i) (proj u j)

noncomputable def halfAt {n : ℕ} (u : Fin n) (i : Fin (n + 1)) : ℝ :=
  if i = u0 u ∨ i = v0 n then 1 / 2 else 1

/-- Split the mass incident to `u` equally and insert a unit zero-cost edge. -/
noncomputable def splitLP {n : ℕ} (x : Fin n → Fin n → ℝ) (u : Fin n) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => if s(i, j) = s(u0 u, v0 n) then 1
    else halfAt u i * halfAt u j * x (proj u i) (proj u j)

/-- Positive support of the LP vector, with the distinguished edge removed. -/
noncomputable def lpSupport {m : ℕ} (x : Fin m → Fin m → ℝ) (a b : Fin m) :
    Finset (Sym2 (Fin m)) :=
  univ.filter (fun e => ¬ e.IsDiag ∧ e ≠ s(a, b) ∧ 0 < pairCost x e)

def IsSpanningTreeOf {m : ℕ} (E T : Finset (Sym2 (Fin m))) : Prop :=
  T ⊆ E ∧ (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin m)))).IsTree

/-- A finite tree law with the prescribed edge marginals. -/
def IsTreeDistribution {m : ℕ} (E : Finset (Sym2 (Fin m)))
    (x : Fin m → Fin m → ℝ) (μ : Finset (Sym2 (Fin m)) → ℝ) : Prop :=
  (∀ T, 0 ≤ μ T) ∧
  (∀ T, μ T ≠ 0 → IsSpanningTreeOf E T) ∧
  (∑ T, μ T) = 1 ∧
  ∀ e ∈ E, (∑ T ∈ (univ.filter (fun T => e ∈ T)), μ T) = pairCost x e

noncomputable def entropy {m : ℕ} (μ : Finset (Sym2 (Fin m)) → ℝ) : ℝ :=
  ∑ T, Real.negMulLog (μ T)

/-- Entropy maximization over every tree law with the same marginals. -/
def IsMaxEntropy {m : ℕ} (E : Finset (Sym2 (Fin m)))
    (x : Fin m → Fin m → ℝ) (μ : Finset (Sym2 (Fin m)) → ℝ) : Prop :=
  IsTreeDistribution E x μ ∧
  ∀ ν, IsTreeDistribution E x ν → entropy ν ≤ entropy μ

/-- Degree in the underlying simple graph; diagonal pairs are discarded. -/
def treeDeg {m : ℕ} (T : Finset (Sym2 (Fin m))) (v : Fin m) : ℕ :=
  (T.filter (fun e => ¬ e.IsDiag ∧ v ∈ e)).card

/-- An involution pairing exactly the odd degree vertices. -/
def IsOddPairing {m : ℕ} (T : Finset (Sym2 (Fin m))) (f : Fin m → Fin m) : Prop :=
  (∀ v, f (f v) = v) ∧ ∀ v, (f v ≠ v ↔ Odd (treeDeg T v))

/-- Each matched edge appears twice in the sum, hence the factor one half. -/
noncomputable def minMatchCost {m : ℕ} (c : Fin m → Fin m → ℝ)
    (T : Finset (Sym2 (Fin m))) : ℝ :=
  sInf {t | ∃ f, IsOddPairing T f ∧ t = (1 / 2) * ∑ v, c v (f v)}

noncomputable def treeCost {m : ℕ} (c : Fin m → Fin m → ℝ)
    (T : Finset (Sym2 (Fin m))) : ℝ :=
  ∑ e ∈ T, pairCost c e

/-- Expected cost of a sampled tree and its cheapest odd-vertex matching. -/
noncomputable def algCost {m : ℕ} (c : Fin m → Fin m → ℝ)
    (μ : Finset (Sym2 (Fin m)) → ℝ) : ℝ :=
  ∑ T, μ T * (treeCost c T + minMatchCost c T)

end MaxEntTSP.Main


