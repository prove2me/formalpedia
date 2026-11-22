-- Prove2me | Definitions.Def_GirvingAKS_Konig_Matching
-- name    : GirvingAKS_Konig_Matching
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:32:32.0059+00:00
-- url     : https://prove2.me/theorems/022bdb12-3a89-4b6c-88b8-84130e90f3b6
-- title:
--   AKS sorting networks (Seiferas port) — Computable Perfect Matching via Augmenting Paths
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Konig/Matching.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Implements Kuhn's augmenting-path algorithm to find a perfect matching in a d-regular bipartite multigraph. This replaces the noncomputable `exists_perfect_matching` (which uses Hall's theorem + `Classical.choice`) with a computable `RegBipartite.matching`.
--
--   The algorithm computes a candidate matching via augmenting paths, then verifies injectivity computationally. The `else` branch (verification failure) falls back to brute-force search over all port assignments.
--
--   Main results:
--
--   - `matchState`             — matching state via augmenting paths
--   - `RegBipartite.matching`  — computable `PerfectMatching`
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Konig/Matching.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Konig_Defs
import Definitions.Def_GirvingAKS_Konig_Hall

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Konig/Matching.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Computable Perfect Matching via Augmenting Paths

  Implements Kuhn's augmenting-path algorithm to find a perfect matching
  in a d-regular bipartite multigraph. This replaces the noncomputable
  `exists_perfect_matching` (which uses Hall's theorem + `Classical.choice`)
  with a computable `RegBipartite.matching`.

  The algorithm computes a candidate matching via augmenting paths, then
  verifies injectivity computationally. The `else` branch (verification
  failure) falls back to brute-force search over all port assignments.

  Main results:
  • `matchState`             — matching state via augmenting paths
  • `RegBipartite.matching`  — computable `PerfectMatching`
-/


section


open Finset BigOperators


/-! **Match State** -/

/-- Matching state: for each top vertex v, `state v = some p` means v is
    matched via port p (to bottom vertex `B.edges v p`). -/
abbrev MatchState (m d : ℕ) := Fin m → Option (Fin d)

/-- The empty matching: no top vertex is matched. -/
def emptyMatchState (m d : ℕ) : MatchState m d := fun _ => none

/-- Find which top vertex (if any) is matched to bottom vertex u. -/
def findMatchedTop {m d : ℕ} (B : RegBipartite m d)
    (state : MatchState m d) (u : Fin m) : Option (Fin m) :=
  (List.finRange m).find? fun v =>
    match state v with
    | some p => B.edges v p == u
    | none => false


/-! **Augmenting Path Search** -/

/-- DFS augmenting path search from unmatched top vertex `v`. -/
def augmentSearch {m d : ℕ} (B : RegBipartite m d)
    (state : MatchState m d) (v : Fin m)
    (visited : Finset (Fin m)) (ports : List (Fin d))
    (fuel : ℕ) : Option (MatchState m d) :=
  match ports with
  | [] => none
  | p :: rest =>
    let u := B.edges v p
    if u ∈ visited then
      augmentSearch B state v visited rest fuel
    else
      match findMatchedTop B state u with
      | none =>
        some (Function.update state v (some p))
      | some v' =>
        match fuel with
        | 0 => augmentSearch B state v visited rest 0
        | fuel' + 1 =>
          match state v' with
          | none => augmentSearch B state v visited rest (fuel' + 1)
          | some _ =>
            let allPorts := (List.finRange d)
            match augmentSearch B state v' (insert u visited) allPorts fuel' with
            | some state' =>
              some (Function.update state' v (some p))
            | none =>
              augmentSearch B state v (insert u visited) rest (fuel' + 1)
termination_by (fuel, ports.length)

/-- Try to find an augmenting path for unmatched top vertex `v`. -/
def augmentOne {m d : ℕ} (B : RegBipartite m d)
    (state : MatchState m d) (v : Fin m) : MatchState m d :=
  match state v with
  | some _ => state
  | none =>
    match augmentSearch B state v ∅ (List.finRange d) m with
    | some state' => state'
    | none => state

/-- Matching state via augmenting paths over all top vertices. -/
def matchState {m d : ℕ} (B : RegBipartite m d) : MatchState m d :=
  (List.finRange m).foldl (fun acc v => augmentOne B acc v) (emptyMatchState m d)


/-! **Candidate Port Assignment** -/

/-- Port assignment from the match state. -/
def candidatePortOf {m d : ℕ} (B : RegBipartite m d) (hd : 0 < d)
    (v : Fin m) : Fin d :=
  match matchState B v with
  | some p => p
  | none => ⟨0, hd⟩

/-- The candidate bottom-vertex assignment. -/
def candidateBottom {m d : ℕ} (B : RegBipartite m d) (hd : 0 < d)
    (v : Fin m) : Fin m :=
  B.edges v (candidatePortOf B hd v)


/-! **Brute-Force Fallback** -/

/-- Enumerate all functions `Fin n → Fin d` as a list (computable). -/
def enumFunctions : (n d : ℕ) → List (Fin n → Fin d)
  | 0, _ => [Fin.elim0]
  | n + 1, d =>
    (enumFunctions n d).flatMap fun f =>
      (List.finRange d).map fun p =>
        fun i => if h : i.val < n then f ⟨i.val, h⟩ else p

/-- Every function `Fin n → Fin d` appears in `enumFunctions n d`. -/
theorem mem_enumFunctions {n d : ℕ} (f : Fin n → Fin d) :
    f ∈ enumFunctions n d := by
  induction n with
  | zero =>
    simp only [enumFunctions, List.mem_singleton]
    funext i; exact i.elim0
  | succ n ih =>
    simp only [enumFunctions, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    refine ⟨fun i => f i.castSucc, ih _, f ⟨n, by omega⟩, ?_⟩
    funext i
    simp only
    by_cases h : i.val < n
    · rw [dif_pos h]; congr 1
    · rw [dif_neg h]; congr 1; ext; show n = i.val; omega

/-- Find an injective port assignment by scanning all functions. -/
def findInjectivePort {m d : ℕ} (B : RegBipartite m d) :
    Option (Fin m → Fin d) :=
  (enumFunctions m d).find? fun f =>
    decide (Function.Injective (fun v => B.edges v (f v)))

private theorem findInjectivePort_spec {m d : ℕ} (B : RegBipartite m d)
    (f : Fin m → Fin d) (h : findInjectivePort B = some f) :
    Function.Injective (fun v => B.edges v (f v)) := by
  simp only [findInjectivePort] at h
  have := List.find?_some h
  exact of_decide_eq_true this

/-- For d-regular bipartite graphs, `findInjectivePort` returns `some`. -/
theorem findInjectivePort_isSome {m d : ℕ} (B : RegBipartite m d) (hd : 0 < d) :
    (findInjectivePort B).isSome = true := by
  have ⟨portOf, hinj⟩ := B.exists_perfect_matching hd
  exact List.find?_isSome.mpr ⟨portOf, mem_enumFunctions portOf, decide_eq_true hinj⟩

/-- Extract the port assignment from the brute-force search. -/
def bruteForcePort {m d : ℕ} (B : RegBipartite m d) (hd : 0 < d) :
    Fin m → Fin d :=
  (findInjectivePort B).get (by
    rw [Option.isSome_iff_ne_none]; intro h
    exact absurd (findInjectivePort_isSome B hd) (by simp [h]))

theorem bruteForcePort_injective {m d : ℕ} (B : RegBipartite m d) (hd : 0 < d) :
    Function.Injective (fun v => B.edges v (bruteForcePort B hd v)) := by
  unfold bruteForcePort
  exact findInjectivePort_spec B _ (Option.some_get _).symm


/-! **Perfect Matching** -/

/-- Perfect matching for a d-regular bipartite graph.
    Uses augmenting paths as the fast path. Falls back to brute-force
    search if the candidate fails injectivity verification. -/
def RegBipartite.matching {m d : ℕ} (B : RegBipartite m d)
    (hd : 0 < d) : PerfectMatching B :=
  if h : Function.Injective (candidateBottom B hd) then
    { portOf := candidatePortOf B hd
      injective := h }
  else
    { portOf := bruteForcePort B hd
      injective := bruteForcePort_injective B hd }

end


