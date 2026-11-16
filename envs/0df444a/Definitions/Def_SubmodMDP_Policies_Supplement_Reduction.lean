-- Prove2me | Definitions.Def_SubmodMDP_Policies_Supplement_Reduction
-- name    : SubmodMDP_Policies_Supplement_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:29:08.680043+00:00
-- url     : https://prove2.me/theorems/12d22812-7a7e-4dd8-8b35-127525da6cc7
-- title:
--   General-to-layered reduction and walk reconstruction
-- statement:
--   Given a directed orienteering instance and $H\ge n+2$, the reduction has source $(s,s,1)$, sink $(t,t,H)$, and a middle-layer vertex $(u,v,i)$ for each reachable ordered pair. Consecutive labels are adjacent precisely when the second endpoint of the former equals the first endpoint of the latter. Its oracle is
--
--   $$f'(U)=f(\{v:\exists u,i,\ (u,v,i)\in U\}).$$
--
--   A label has the length of a shortest connecting path. Shortest-path ties are settled by fewest arcs and then lexicographic order; this definition specifies the result of preprocessing, not an instruction to enumerate paths at runtime. Reconstruction concatenates the selected paths with duplicate junction endpoints removed. It preserves length and can increase the reward.
--
--   The length constraint uses one row, supported only on singleton coordinates, with budget clipped to $Hn\max_{a\in A}w(a)$. The maximum of an empty arc family is zero. Parameter choices are $d=2$, $r=\lceil\log_2(n+2)\rceil$ in the logarithmic regime; in the polynomial regime $r=\min\{k,\lceil\log_2(n+2)\rceil\}$ and $d$ is the least integer at least two with $d^r\ge n+2$. The deterministic algorithm applies Algorithm 5 to this reduction using unit lengths solely to choose connecting paths.
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), proof of Theorem 1, p. 14 (PDF p. 15); Appendix A, pp. 24–25 (PDF pp. 25–26)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Supplement_Algorithm5

namespace SubmodMDP.Policies.Supplement

noncomputable section
open Classical

/-- All vertex sequences of a fixed length, in lexicographic order. This finite specification
fixes shortest-path ties; it is not the implementation required by the time bounds. -/
def sequences (n : ℕ) : ℕ → List (List (Fin n))
  | 0 => [[]]
  | k + 1 => (List.finRange n).flatMap (fun v => (sequences n k).map (List.cons v))

/-- Shortest path, breaking ties first by fewest arcs, then lexicographically. A shortest
nonnegative-length walk has a simple representative, so n vertices suffice. In particular the
selected path from a vertex to itself is its singleton, even in the presence of zero cycles. -/
def shortest {n : ℕ} (G : Digraph (Fin n)) (w : Fin n → Fin n → ℕ)
    (s t : Fin n) : Option (List (Fin n)) :=
  let candidates := ((List.range n).flatMap (fun j => sequences n (j + 1))).filter
    (fun W => Walk G s t W)
  candidates.foldl (fun old W => match old with
    | none => some W
    | some P => if walkLength w W < walkLength w P then some W else some P) none

/-- Reachability includes the zero-arc path. -/
def reaches {n : ℕ} (I : Ori n) (u v : Fin n) : Bool :=
  (shortest I.graph (fun _ _ => 1) u v).isSome

/-- Labels (u,v,i) of the reduction, layer first then lexicographic endpoints.
There is one source label and one sink label; only reachable pairs occur in middle layers. -/
def redNodes {n : ℕ} (I : Ori n) (H : ℕ) : List (ℕ × Fin n × Fin n) :=
  [(1, I.s, I.s)] ++ (List.range (H - 2)).flatMap (fun j =>
    (List.finRange n).flatMap (fun u =>
      ((List.finRange n).filter (fun v => reaches I u v)).map (fun v => (j + 2, u, v)))) ++
    [(H, I.t, I.t)]

/-- The reduced graph in exactly the published LGraph representation. -/
def reduced {n : ℕ} (I : Ori n) (H : ℕ) : LGraph where
  N := (redNodes I H).length
  H := H
  layer v := (redNodes I H)[v.val].1
  arc u v := decide ((redNodes I H)[v.val].1 = (redNodes I H)[u.val].1 + 1 ∧
    (redNodes I H)[u.val].2.2 = (redNodes I H)[v.val].2.1)

/-- f′(U)=f({v : (u,v,i)∈U}); the reward counts vertices, never visits or arcs. -/
def redReward {n : ℕ} (I : Ori n) (H : ℕ) (f : Finset (Fin n) → ℚ)
    (X : Finset (Fin (reduced I H).N)) : ℚ :=
  f (X.image (fun v => (redNodes I H)[v.val].2.2))

/-- Vertex length in the reduction. Unreachable labels do not occur; 0 on an absent path is
only a totalization for malformed inputs, never used in a guarantee. -/
def redLength {n : ℕ} (I : Ori n) (H : ℕ) (w : Fin n → Fin n → ℕ)
    (v : Fin (reduced I H).N) : ℕ :=
  match shortest I.graph w (redNodes I H)[v.val].2.1 (redNodes I H)[v.val].2.2 with
  | none => 0
  | some W => walkLength w W

/-- Join shortest paths, omitting each duplicated junction vertex. Starting with [s] keeps
its endpoint even for a zero-length output walk. A failed subpath propagates none. -/
def reconstruct {n : ℕ} (I : Ori n) (H : ℕ) (w : Fin n → Fin n → ℕ)
    (P : List (Fin (reduced I H).N)) : Option (List (Fin n)) :=
  P.foldl (fun acc v => do
    let A ← acc
    let W ← shortest I.graph w (redNodes I H)[v.val].2.1 (redNodes I H)[v.val].2.2
    pure (A ++ W.tail)) (some [I.s])

/-- The effective budget is clipped before LP construction, with no dependence of the cost
on the magnitude of C. For real budgets use floor C, since all walk lengths are integers. -/
def cappedBudget {n : ℕ} (I : Ori n) (H : ℕ) (w : Fin n → Fin n → ℕ) (C : ℕ) : ℕ :=
  min C (H * n * ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => I.graph.Adj e.1 e.2)).sup (fun e => w e.1 e.2))

/-- One singleton-only length row. Empty-set and higher-order coefficients are zero. -/
def lengthRow {n : ℕ} (I : Ori n) (H : ℕ) (w : Fin n → Fin n → ℕ)
    (_ : Fin 1) (X : Finset (Fin (reduced I H).N)) : ℤ :=
  if X.card = 1 then (∑ v ∈ X, (redLength I H w v : ℤ)) else 0

/-- Logarithmic regime. -/
def logDepth (n : ℕ) : ℕ := Nat.clog 2 (n + 2)

/-- Polynomial regime: r=min(k,ceil(log₂(n+2))), d the least integer ≥2 with d^r≥n+2. -/
def polyDepth (n k : ℕ) : ℕ := min (max 1 k) (logDepth n)

def polyDegree (n k : ℕ) : ℕ :=
  ((List.range (n + 3)).find? (fun d => 2 ≤ d ∧ n + 2 ≤ d ^ polyDepth n k)).getD 2

/-- Algorithm 5 plus the general-to-layered reduction, without a length bound. All connecting
paths are chosen with unit lengths, solely to obtain a fixed polynomial-size reconstruction. -/
def combinatorialWalk {n : ℕ} (I : Ori n) (k : ℕ) (f : Finset (Fin n) → ℚ) :
    Option (List (Fin n)) :=
  let d := polyDegree n k
  let r := polyDepth n k
  let H := d ^ r
  let G := reduced I H
  let S := Finset.univ.filter (fun v => G.layer v = 1)
  let T := Finset.univ.filter (fun v => G.layer v = H)
  (alg5 G d r 0 S T (redReward I H f)).bind (reconstruct I H (fun _ _ => 1))

end
end SubmodMDP.Policies.Supplement


