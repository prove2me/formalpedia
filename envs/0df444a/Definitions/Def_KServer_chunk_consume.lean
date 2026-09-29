-- Prove2me | Definitions.Def_KServer_chunk_consume
-- name    : KServer_chunk_consume
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T20:27:43.662215+00:00
-- url     : https://prove2.me/theorems/dcea34f6-7d4b-463f-815b-c572773f34b4
-- title:
--   Consuming a chunk system
-- statement:
--   The output interface of the chunk-system machinery. For a chunk system $C$ with per-chunk conditional cost claims (every chunk's size is dominated by the conditional bail-cost of any online evader on any escape rule) and expected total at least $T$,
--   $$T \le \sum_\omega P(\omega)\, \mathrm{cost}_E\big(\sigma(\omega)\big)$$
--   for every online evader algorithm $E$, where $\sigma(\omega)$ is the flattened request sequence of outcome $\omega$: the per-chunk claims aggregate over the filtration atoms (sizes are atom-measurable), the never-bail escape rule turns bail costs into plain chunk costs, and the chunk costs telescope to the total movement cost. Dually, the expected offline cost of the system's sequences is at most the marked distance $d(s,t)$. Together these turn a chunk system with total $T$ into an online/offline cost ratio of at least $T / d(s,t)$ on a distribution of request sequences, the form consumed by the Yao averaging step of the BCR lower bound.
-- source:
--   BCR randomized k-server lower bound

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_stopping

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

namespace KServer

variable {X : Type*} [MetricSpace X] {s t : X} {cB T pe : ℝ} {mL : ℕ}

theorem EvaderAlgorithm.cost_nil (E : EvaderAlgorithm X) :
    E.cost ([] : List (Set X)) = 0 := by
  unfold EvaderAlgorithm.cost
  simp

theorem bailTime_never (h χ : List (Set X)) :
    bailTime (fun _ : List (Set X) => false) h χ = none := by
  unfold bailTime
  rw [List.find?_eq_none]
  intro x _
  simp

/-- One chunk step of the flattened prefix. -/
theorem prefix_flatten_succ (C : ChunkSystemB X s t 0 cB T pe mL)
    (ω : C.Ω) {i : ℕ} (hi : i < C.m) :
    ((List.ofFn (C.chunk ω)).take (i + 1)).flatten
      = ((List.ofFn (C.chunk ω)).take i).flatten ++ C.chunk ω ⟨i, hi⟩ := by
  rw [List.take_succ, List.flatten_append]
  congr 1
  rw [List.getElem?_eq_getElem (by
    rw [List.length_ofFn]
    exact hi)]
  simp

/-- The expected per-chunk claim aggregates over the atoms. -/
theorem chunk_claim_le (C : ChunkSystemB X s t 0 cB T pe mL)
    (E : EvaderAlgorithm X) (i : Fin C.m) :
    ∑ ω, C.P ω * C.size ω i
      ≤ ∑ ω, C.P ω * E.bailCost (fun _ => false)
          (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten)
          (C.chunk ω i) pe := by
  classical
  have hfib : ∀ u : C.Ω → ℝ,
      ∑ b ∈ Finset.univ.image (C.hist (i : ℕ)),
        ∑ ω ∈ Finset.univ.filter (fun ω => C.hist (i : ℕ) ω = b), u ω
      = ∑ ω, u ω := fun u =>
    Finset.sum_fiberwise_of_maps_to
      (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x)) u
  rw [← hfib (fun ω => C.P ω * C.size ω i),
    ← hfib (fun ω => C.P ω * E.bailCost (fun _ => false)
      (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten) (C.chunk ω i) pe)]
  refine Finset.sum_le_sum fun b hb => ?_
  rw [Finset.mem_image] at hb
  obtain ⟨ω₀, -, rfl⟩ := hb
  have hc := C.hcost i ω₀ E (fun _ => false)
  have hL : ∑ ω ∈ Finset.univ.filter
      (fun ω => C.hist (i : ℕ) ω = C.hist (i : ℕ) ω₀),
      C.P ω * C.size ω i
      = C.size ω₀ i * ∑ ω ∈ Finset.univ.filter
          (fun ω => C.hist (i : ℕ) ω = C.hist (i : ℕ) ω₀), C.P ω := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω hω => ?_
    rw [Finset.mem_filter] at hω
    rw [C.hsmeas i ω ω₀ hω.2]
    ring
  rw [hL]
  exact hc

/-- Telescoping the never-bail chunk costs into the full cost. -/
theorem sum_costOn_eq_cost (C : ChunkSystemB X s t 0 cB T pe mL)
    (E : EvaderAlgorithm X) (ω : C.Ω) :
    ∑ i : Fin C.m, E.costOn
        (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten) (C.chunk ω i)
      = E.cost (C.seq ω) := by
  have key : ∀ n : ℕ, n ≤ C.m →
      (∑ i ∈ Finset.univ.filter (fun i : Fin C.m => (i : ℕ) < n),
        E.costOn (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten)
          (C.chunk ω i))
      = E.cost (((List.ofFn (C.chunk ω)).take n).flatten) := by
    intro n
    induction n with
    | zero =>
      intro _
      have hempty : (Finset.univ.filter
          (fun i : Fin C.m => (i : ℕ) < 0)) = ∅ := by
        ext i
        simp
      rw [hempty, Finset.sum_empty, List.take_zero]
      show (0 : ℝ) = E.cost ([] : List (Set X))
      rw [E.cost_nil]
    | succ n ih =>
      intro hn
      have hnm : n < C.m := by omega
      have hsplit : (Finset.univ.filter
          (fun i : Fin C.m => (i : ℕ) < n + 1))
          = insert (⟨n, hnm⟩ : Fin C.m)
            (Finset.univ.filter (fun i : Fin C.m => (i : ℕ) < n)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert]
        constructor
        · intro hi
          by_cases hij : (i : ℕ) = n
          · left
            exact Fin.ext hij
          · right
            omega
        · intro hi
          rcases hi with hi | hi
          · rw [hi]
            exact Nat.lt_succ_self n
          · omega
      rw [hsplit, Finset.sum_insert (by simp), ih (by omega),
        prefix_flatten_succ C ω hnm]
      unfold EvaderAlgorithm.costOn
      ring
  have h2 := key C.m (le_refl C.m)
  rw [show (Finset.univ.filter (fun i : Fin C.m => (i : ℕ) < C.m))
      = Finset.univ from by
      ext i
      simp [i.isLt]] at h2
  rw [h2]
  unfold ChunkSystemB.seq
  congr 1
  rw [List.take_of_length_le (by rw [List.length_ofFn])]

/-- **Consuming a chunk system**: every online evader pays expected cost
at least the system's total on the system's request sequences. -/
theorem chunk_system_cost (C : ChunkSystemB X s t 0 cB T pe mL)
    (E : EvaderAlgorithm X) :
    T ≤ ∑ ω, C.P ω * E.cost (C.seq ω) := by
  refine le_trans C.htotal ?_
  have h1 : ∑ ω, C.P ω * ∑ i, C.size ω i
      = ∑ i, ∑ ω, C.P ω * C.size ω i := by
    rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) =>
      (Finset.mul_sum Finset.univ (fun i => C.size ω i) (C.P ω))]
    exact Finset.sum_comm
  have h2 : ∑ ω, C.P ω * E.cost (C.seq ω)
      = ∑ i : Fin C.m, ∑ ω, C.P ω * E.bailCost (fun _ => false)
          (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten)
          (C.chunk ω i) pe := by
    have hcosteq : ∀ ω : C.Ω, E.cost (C.seq ω)
        = ∑ i : Fin C.m, E.bailCost (fun _ => false)
            (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten)
            (C.chunk ω i) pe := by
      intro ω
      rw [← sum_costOn_eq_cost C E ω]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [EvaderAlgorithm.bailCost_of_no_bail E _ _ _ pe
        (bailTime_never _ _)]
    rw [Finset.sum_congr rfl fun ω (_ : ω ∈ Finset.univ) => by
      rw [hcosteq ω, Finset.mul_sum]]
    exact Finset.sum_comm
  rw [h1, h2]
  exact Finset.sum_le_sum fun i _ => chunk_claim_le C E i

/-- The expected offline cost of the system's sequences is at most the
marked distance. -/
theorem chunk_system_opt (C : ChunkSystemB X s t 0 cB T pe mL)
    (hPsum : ∑ ω, C.P ω = 1) :
    ∑ ω, C.P ω * evaderOfflineCost s (C.seq ω) ≤ dist s t := by
  have h1 : ∀ ω, C.P ω * evaderOfflineCost s (C.seq ω)
      ≤ C.P ω * dist s t := fun ω =>
    mul_le_mul_of_nonneg_left (C.hopt ω) (C.hP ω).le
  refine le_trans (Finset.sum_le_sum fun ω _ => h1 ω) (le_of_eq ?_)
  rw [← Finset.sum_mul, hPsum, one_mul]

end KServer


