-- Prove2me | Definitions.Def_MCPoise_AssignRun
-- name    : MCPoise_AssignRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:19.189932+00:00
-- url     : https://prove2.me/theorems/673bbd9a-d8e0-4e70-a9cc-a2a8f361696f
-- title:
--   Runs of Algorithm 1 (AssignmentRounding)
-- statement:
--   A **run** of $\mathrm{AssignmentRounding}(P, \rho)$ returning a collection $\mathcal C$ of groups: first discard the pair vertices of weighted degree below $1/32$, then process each connected component $C$.
--
--   1. If $C$ has no pair vertex, it adds nothing.
--   2. If $C$ has a representative $z^*$ and each other $z_i \in Z_C$ reaches $b_i = 0$ in the routing loop, it adds the group $(C, z^*, \{Q_i\})$.
--   3. If an attempt fails, take the sparse cut $S$ and add the runs on the two induced pieces $C[S]$ and $C[V(C) \setminus S]$.
--
--   **Formalization Note** The page leaves the representatives, the shortest paths and the order open, and each is allowed here, so statements about every run cover every implementation. The case of a component without a pair vertex, which the page does not mention, is an isolated root copy.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Algorithm 1, p.12

import Mathlib
import Definitions.Def_MCPoise_RouteState
import Definitions.Def_MCPoise_IsSparseCut

namespace MCPoise

variable {k : ℕ} {A : SimpleGraph (AVert k)}

/-- "Discard all pair vertices of weighted degree below 1/32 from A" (Algorithm 1, p.12). -/
def discard (P : A.Subgraph) : A.Subgraph :=
  P.induce (P.verts \ {v | ∃ i, v = Sum.inl i ∧ wdeg P i < 1 / 32})

/-- The vertex sets of the connected components of a piece. -/
def comps (P : A.Subgraph) : Set (Set (AVert k)) :=
  {c | ∃ v ∈ P.verts, c = {u | P.spanningCoe.Reachable v u}}

/-- A group of Algorithm 1: `(C, z*_C, {Q_i : z_i ∈ Z_C})`. -/
structure AGroup (A : SimpleGraph (AVert k)) where
  C : A.Subgraph
  zstar : Fin k
  Q : Fin k → List (List (AVert k) × ℝ)

/-- **What the body of the loop of Algorithm 1 does to one connected component.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Algorithm 1, p.12:
```
Algorithm 1 AssignmentRounding(A, ρ)
Fix an integer ρ ≥ 128 log(2k)
Discard all pair vertices of weighted degree below 1/32 from A
Let 𝒞 := ∅
for each connected component C of A do
  Let Z_C denote the pair vertices in C
  Choose representative z*_C ∈ Z_C
  for each z_i ∈ Z_C \ {z*_C} do
    Let Q_i := ∅ and let b_i := 1 denote the flow remaining to send
    Give each root copy r_{j,ℓ} in C capacity c_{j,ℓ} := ρ³/2^{ℓ+1}
    while b_i > 0 do
      Find a shortest z_i–z*_C path P in C avoiding root copies with c_{j,ℓ} = 0
      if no such path exists or |E(P)| > ρ² then
        Declare the attempt for z_i failed
        Let (S, V(C) \ S) be the cut given by Lemma 2.4
        Delete the edges crossing this cut and discard all path collections constructed for C
        𝒞 ← 𝒞 ∪ AssignmentRounding(C[S], ρ) ∪ AssignmentRounding(C[V(C) \ S], ρ)
        Stop processing C and continue with the next connected component
      Let α := min{b_i, min_{r_{j,ℓ}∈V(P)} c_{j,ℓ}}
      Add (P, α) to Q_i and set b_i ← b_i − α
      Set c_{j,ℓ} ← c_{j,ℓ} − α for each root copy r_{j,ℓ} ∈ V(P)
  Add (C, z*_C, {Q_i : z_i ∈ Z_C}) to 𝒞
return 𝒞
```
`CompRun ρ C 𝒞` says that processing the component `C` can add exactly `𝒞`: `success` when every `z_i` reaches
`b_i = 0`, `fail` when an attempt fails and the two sides of the cut recurse.

**Formalization Note.** The page leaves the representative, the shortest paths and the order open, and every choice is
allowed here, so a claim about every run implies the paper's claim for any instantiation. A component with no pair
vertex, such as an isolated root copy, has no representative and adds no group (`skip`): the page is silent on this, and
this is its only possible meaning. The recursive calls begin with their own discard step. -/
inductive CompRun (ρ : ℕ) : A.Subgraph → Set (AGroup A) → Prop
  | skip (C : A.Subgraph) : pairsOf C = ∅ → CompRun ρ C ∅
  | success (C : A.Subgraph) (z : Fin k) (Q : Fin k → List (List (AVert k) × ℝ)) :
      z ∈ pairsOf C →
      (∀ i ∈ pairsOf C, i ≠ z → ∃ cap, RouteState ρ C i z 0 cap (Q i)) →
      CompRun ρ C {⟨C, z, Q⟩}
  | fail (C : A.Subgraph) (z i : Fin k) (b : ℝ) (cap : Copy k → ℝ)
      (Q : List (List (AVert k) × ℝ)) (S : Set (AVert k))
      (f g : Set (AVert k) → Set (AGroup A)) :
      z ∈ pairsOf C → i ∈ pairsOf C → i ≠ z →
      RouteState ρ C i z b cap Q → 0 < b → RouteFails ρ C i z cap →
      IsSparseCut ρ C i z (zeroCap cap) S →
      (∀ c ∈ comps (discard (C.induce S)),
        CompRun ρ ((discard (C.induce S)).induce c) (f c)) →
      (∀ c ∈ comps (discard (C.induce (C.verts \ S))),
        CompRun ρ ((discard (C.induce (C.verts \ S))).induce c) (g c)) →
      CompRun ρ C ((⋃ c ∈ comps (discard (C.induce S)), f c) ∪
        ⋃ c ∈ comps (discard (C.induce (C.verts \ S))), g c)

/-- **A run of `AssignmentRounding(P, ρ)` returning `𝒞`** (Algorithm 1, p.12): the discard step, then each connected
component is processed and the results are united. -/
def AssignRun (ρ : ℕ) (P : A.Subgraph) (𝒞 : Set (AGroup A)) : Prop :=
  ∃ f : Set (AVert k) → Set (AGroup A),
    (∀ c ∈ comps (discard P), CompRun ρ ((discard P).induce c) (f c)) ∧
    𝒞 = ⋃ c ∈ comps (discard P), f c

end MCPoise


