-- Prove2me | Definitions.Def_BatchMaxService_Metric_PrimTraversal
-- name    : BatchMaxService_Metric_PrimTraversal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:26:05.598578+00:00
-- url     : https://prove2.me/theorems/e440473f-0b37-4d8b-b967-1f6d207e6065
-- title:
--   Deterministic real-comparison Prim and open tree traversal
-- statement:
--   Fix the site order once. For terminal set $A$, Prim starts at its least site and repeatedly scans the cut from reached sites to unreached terminals. It inserts a lightest crossing edge, breaking ties lexicographically. No minimizer oracle or optimality certificate is an input.
--
--   For a returned tree $F$, anchor $s$ and selected endpoint $z$, explicit graph scans construct parent pointers rooted at $s$. Depth-first traversal explores the child leading to $z$ last. Each edge on the $s$–$z$ path is used once and every other edge twice, so its intended length is
--
--   $$\operatorname{len}(P)=2w(F)-d_F(s,z).$$
--
--   These routines supply the concrete MST computation and traversal used by Algorithm 4. Their correctness and work bounds remain proof obligations; neither is stored as an assumed field.
--
--   **Formalization Note** Site pairs are scanned in the fixed order on `Fin n`. The recursion bound is the number of sites. Each scan, comparison, ancestor search and list construction contributes to an explicit charged-work recurrence. Real comparisons are exact primitives in the chosen arithmetic/comparison model.
-- source:
--   Tianhang Lu, Runtian Ren, Shengcai Liu, Ke Tang, Online Service with Per-Batch Maximum Delays, STOC 2027 submission #218 (October 2026), Section 5, fixed tie orders, and Algorithm 4 lines 7, 16–17, printed pp. 13, 18–19 / PDF pp. 14, 19–20

import Mathlib
import Definitions.Def_BatchMaxService_Metric_Trees

namespace BatchMaxService.Metric

variable {n : ℕ}

/-- Fixed lexicographic site/edge order, independent of arrivals. -/
def sitePairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => (u, v)

/-- A scan of all pairs, restricted to the cut (visited, A \ visited). -/
noncomputable def crossing (A V : Finset (Fin n)) : List (Fin n × Fin n) := by
  classical
  exact (sitePairs n).filter fun uv => uv.1 ∈ V ∧ uv.2 ∈ A ∧ uv.2 ∉ V

/-- Linear minimum scan. Strict comparison keeps the first lexicographic edge at ties. -/
noncomputable def cheapest [MetricSpace (Fin n)] (es : List (Fin n × Fin n)) :
    Option (Fin n × Fin n) := by
  classical
  exact es.foldl (fun best e => match best with
    | none => some e
    | some b => if dist e.1 e.2 < dist b.1 b.2 then some e else some b) none

/-- Deterministic Prim; the n-step loop is a bound on vertices inserted, not an MST oracle.
    Each full cut scan is charged for n² pairs, linear set membership and comparisons. -/
noncomputable def primLoop [MetricSpace (Fin n)] : ℕ → Finset (Fin n) →
    Finset (Fin n) → Finset (Sym2 (Fin n)) → Charged (MetricTree n)
  | 0, A, _, E => (⟨A, E⟩, 1)
  | k + 1, A, V, E => by
      classical
      let scan := 40 * (n + 1)^3
      match cheapest (crossing A V) with
      | none => exact (⟨A, E⟩, scan + 1)
      | some (u, v) =>
          let r := primLoop k A (insert v V) (insert s(u, v) E)
          exact (r.1, scan + 4 * (n + 1) + r.2)

/-- A concrete real-comparison Prim implementation for the complete graph on A. -/
noncomputable def primTree [MetricSpace (Fin n)] (A : Finset (Fin n)) : Charged (MetricTree n) := by
  classical
  match (A.sort (· ≤ ·)).head? with
  | none => exact (⟨∅, ∅⟩, 4 * (n + 1)^2)
  | some r =>
      let out := primLoop n A {r} ∅
      exact (out.1, 4 * (n + 1)^2 + out.2)

abbrev Parents (n : ℕ) := Fin n → Option (Fin n)

/-- Rooting is an explicit n-step graph scan. Its parent pointers always point to an
    already reached vertex. On a tree it retains all its edges. -/
noncomputable def rootLoop (F : MetricTree n) : ℕ → Finset (Fin n) → Parents n → Charged (Parents n)
  | 0, _, p => (p, 1)
  | k + 1, V, p => by
      classical
      let es := (sitePairs n).filter fun uv =>
        uv.1 ∈ V ∧ uv.2 ∉ V ∧ s(uv.1, uv.2) ∈ F.edges
      let scan := 20 * (n + 1)^2 * (F.edges.card + n + 1)
      match es.head? with
      | none => exact (p, scan + 1)
      | some (u, v) =>
          let r := rootLoop F k (insert v V) (Function.update p v (some u))
          exact (r.1, scan + 4 * (n + 1) + r.2)

def ancestor (p : Parents n) (x : Fin n) : ℕ → Fin n → Bool
  | 0, y => decide (x = y)
  | k + 1, y => if x = y then true else
      match p y with
      | none => false
      | some z => ancestor p x k z

def toward (p : Parents n) (x : Fin n) (g : Option (Fin n)) : Bool :=
  match g with
  | none => false
  | some y => ancestor p x n y

/-- Open depth first tour. The unique child toward the chosen endpoint is explored last;
    other children return to v. List construction and ancestor scans are charged. -/
def dfsTour (p : Parents n) : ℕ → Fin n → Option (Fin n) → Charged (List (Fin n))
  | 0, v, _ => ([v], 1)
  | k + 1, v, g =>
      let cs := (List.finRange n).filter fun u => p u == some v
      let order := cs.filter (fun u => !(toward p u g)) ++ cs.filter (fun u => toward p u g)
      order.foldl (fun acc u =>
        let along := toward p u g
        let sub := dfsTour p k u (if along then g else none)
        let tail := if along then [] else [v]
        (acc.1 ++ sub.1 ++ tail,
          acc.2 + sub.2 + acc.1.length + 2 * sub.1.length + 4 * (n + 1)))
        ([v], 20 * (n + 1)^2)

noncomputable def openTraversal (F : MetricTree n) (s endpoint : Fin n) :
    Charged (List (Fin n)) := by
  classical
  let rooted := rootLoop F n {s} (fun _ => none)
  let tour := dfsTour rooted.1 n s (some endpoint)
  exact (tour.1, rooted.2 + tour.2 + 2 * (n + 1))

end BatchMaxService.Metric


