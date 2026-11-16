-- Prove2me | Definitions.Def_MTSActionPredictions_SyncRestart_Supplement_ConvexChasing
-- name    : MTSActionPredictions_SyncRestart_Supplement_ConvexChasing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:27:55.764207+00:00
-- url     : https://prove2.me/theorems/a24a6992-2e8e-401d-ad3c-b14f1fb0e2da
-- title:
--   Euclidean convex body chasing: greedy projection, feasible paths, and algorithms with action predictions
-- statement:
--   In **convex body chasing** an agent starts at $x_0\in X$ and at each time $t\ge1$ receives a body $K_t$ (a nonempty closed convex set, as in the published convex body chasing model) and must move to $x_t\in K_t$, paying $\|x_t-x_{t-1}\|$.
--
--   1. In $\mathbb R^d$ with the Euclidean norm, $\operatorname{proj}_K(x)$ is a closest point of $K$ to $x$, which exists (and is unique) for every body $K$.
--   2. The greedy algorithm **Project** moves to $x_t=\operatorname{proj}_{K_t}(x_{t-1})$; it is a deterministic online algorithm of the published model.
--   3. A **feasible offline solution** from $x_0$ is a path $y_0=x_0,y_1,\dots,y_T$ with $y_t\in K_t$; its cost is $\mathrm{OFF}=\sum_{t=1}^T\|y_t-y_{t-1}\|$.
--   4. A deterministic online algorithm **with action predictions** receives at time $t$ the pair $(K_t,P_t)$, where the predicted point $P_t$ need not lie in $K_t$, and chooses $x_t\in K_t$ as a function of the revealed pairs only. Its cost is $\sum_{t=1}^T\|x_t-x_{t-1}\|$, and the prediction error against $y$ is $\eta=\sum_{t=1}^T\|P_t-y_t\|$.
--
--   These definitions state Theorem 35 (greedy projection) and Theorem 4 (convex body chasing with action predictions).
--
--   **Formalization Note** Bodies, deterministic algorithms without predictions and their cost come from the published model `CBCLowerBound.EveryNorm.Chasing`. The closest point is chosen by `Classical.epsilon`; a short lemma shows it is a closest point of every body, which makes Project a feasible algorithm.
-- source:
--   Júlia Baligács, Christian Coester, Alexa Tudose, STOC 2027 submission #1248 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1248.pdf; §7, PDF pp. 23–25 / printed pp. 22–24 (Project on PDF p. 24 / printed p. 23)

import Definitions.Def_CBCLowerBound_EveryNorm_Chasing

open scoped BigOperators

namespace MTSActionPredictions.SyncRestart.Supplement

open CBCLowerBound.EveryNorm

/-! # Euclidean convex body chasing, the greedy projection algorithm, and action predictions
(§7, PDF 23–25 / printed 22–24)

Requests are bodies (nonempty closed convex sets, `IsBody` of the published convex body chasing
model). A deterministic online algorithm without predictions is the published `Algorithm`. -/

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A closest point of `K` to `x`: `proj_K(x) = argmin_{z ∈ K} ‖z - x‖`. For a nonempty closed
convex set in a Euclidean space it exists and is unique; elsewhere the value is unspecified. -/
noncomputable def projPoint [Nonempty X] (K : Set X) (x : X) : X :=
  Classical.epsilon (fun z => z ∈ K ∧ ∀ w ∈ K, ‖x - z‖ ≤ ‖x - w‖)

theorem projPoint_spec {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsBody K)
    (x : EuclideanSpace ℝ (Fin d)) :
    projPoint K x ∈ K ∧ ∀ w ∈ K, ‖x - projPoint K x‖ ≤ ‖x - w‖ := by
  obtain ⟨hne, hcl, hcv⟩ := hK
  obtain ⟨v, hvK, hv⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv x
  apply Classical.epsilon_spec (p := fun z => z ∈ K ∧ ∀ w ∈ K, ‖x - z‖ ≤ ‖x - w‖)
  refine ⟨v, hvK, fun w hw => ?_⟩
  rw [hv]
  exact ciInf_le ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩ (⟨w, hw⟩ : K)

/-- The position of `Project` after the revealed prefix `l`:
`x_t = proj_{K_t}(x_{t-1})`, starting from `x_0`. -/
noncomputable def projectPos {d : ℕ} (x₀ : EuclideanSpace ℝ (Fin d))
    (l : List (Set (EuclideanSpace ℝ (Fin d)))) : EuclideanSpace ℝ (Fin d) :=
  l.foldl (fun y K => projPoint K y) x₀

/-- The deterministic greedy projection algorithm `Project` (PDF 24 / printed 23). -/
noncomputable def project (d : ℕ) (x₀ : EuclideanSpace ℝ (Fin d)) :
    Algorithm (EuclideanSpace ℝ (Fin d)) x₀ where
  pos := projectPos x₀
  pos_nil := rfl
  pos_mem := by
    intro l K _ hK
    simp only [projectPos, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact (projPoint_spec K hK _).1

/-- A feasible offline solution from `x₀` for the requests `σ` (only the request sets matter):
`y_0 = x₀` and `y_t ∈ K_t` for `1 ≤ t ≤ T`. -/
def FeasiblePath (x₀ : X) (σ : List (Set X)) (y : ℕ → X) : Prop :=
  y 0 = x₀ ∧ ∀ (t : ℕ) (ht : t < σ.length), y (t + 1) ∈ σ[t]

/-- The movement cost `∑_{t=1}^T ‖y_t − y_{t−1}‖` of a path over `T` steps. -/
noncomputable def pathCost (T : ℕ) (y : ℕ → X) : ℝ :=
  ∑ t ∈ Finset.range T, ‖y (t + 1) - y t‖

/-- A deterministic online algorithm for convex body chasing **with action predictions**, started
at `x₀`. At time `t` it has seen the pairs `(K_1, P_1), …, (K_t, P_t)` (request and predicted
point; the prediction need not lie in its request) and chooses a point of `K_t`. -/
structure PredAlgorithm (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (x₀ : X) where
  /-- The point held after the revealed prefix of (request, prediction) pairs. -/
  pos : List (Set X × X) → X
  /-- Before any request the algorithm is at the start point. -/
  pos_nil : pos [] = x₀
  /-- Feasibility: the point chosen after `(K, P)` lies in `K` (along sequences of bodies). -/
  pos_mem : ∀ (l : List (Set X × X)) (K : Set X) (P : X), (∀ a ∈ l, IsBody a.1) → IsBody K →
    pos (l ++ [(K, P)]) ∈ K

namespace PredAlgorithm

variable {x₀ : X}

/-- The total movement `∑_{t=1}^T ‖x_t − x_{t−1}‖` on the input `σ = [(K_1,P_1), …, (K_T,P_T)]`. -/
noncomputable def cost (A : PredAlgorithm X x₀) (σ : List (Set X × X)) : ℝ :=
  ∑ t ∈ Finset.range σ.length, ‖A.pos (σ.take (t + 1)) - A.pos (σ.take t)‖

end PredAlgorithm

/-- The action-prediction error `η = ∑_{t=1}^T ‖P_t − y_t‖` of the input's predictions against an
offline path `y`. -/
noncomputable def predError (σ : List (Set X × X)) (y : ℕ → X) : ℝ :=
  ∑ t : Fin σ.length, ‖(σ.get t).2 - y (t.val + 1)‖

end MTSActionPredictions.SyncRestart.Supplement


