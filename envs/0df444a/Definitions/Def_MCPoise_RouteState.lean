-- Prove2me | Definitions.Def_MCPoise_RouteState
-- name    : MCPoise_RouteState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:28:49.928607+00:00
-- url     : https://prove2.me/theorems/409c4e60-616d-4788-8f08-cb4d409cafd8
-- title:
--   The state of the routing loop of Algorithm 1
-- statement:
--   Fix a piece $C$ of the auxiliary graph, a pair vertex $z_i$ and the representative $z^*$. The loop of Algorithm 1 starts with remaining flow $b_i = 1$, capacities $c_{j,\ell} = \rho^3/2^{\ell+1}$ on the root copies, and an empty collection $Q_i$. While $b_i > 0$ it finds a shortest $z_i$-$z^*$ path $P$ in $C$ avoiding copies with $c_{j,\ell} = 0$; if $|E(P)| \le \rho^2$, it lets $\alpha = \min\{b_i, \min_{r_{j,\ell} \in V(P)} c_{j,\ell}\}$, adds $(P, \alpha)$ to $Q_i$, and subtracts $\alpha$ from $b_i$ and from the capacity of each copy on $P$.
--
--   The predicate holds of the states the loop can reach, for every choice of shortest paths. An attempt **fails** at a state with $b_i > 0$ when no such path has at most $\rho^2$ edges.
--
--   The module also defines the set $Z_C$ of pair vertices of a piece, its root copies, and the weighted degree of a pair vertex.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Algorithm 1, p.12

import Mathlib
import Definitions.Def_MCPoise_AVert
import Definitions.Def_MCPoise_IsPathIn

namespace MCPoise

variable {k : ℕ} {A : SimpleGraph (AVert k)}

/-- `Z_C`: the pair vertices of a piece (Algorithm 1, p.12). -/
noncomputable def pairsOf (C : A.Subgraph) : Finset (Fin k) :=
  open scoped Classical in Finset.univ.filter fun i => Sum.inl i ∈ C.verts

/-- The root copies of a piece. -/
noncomputable def copiesOf (C : A.Subgraph) : Finset (Copy k) :=
  open scoped Classical in Finset.univ.filter fun c => Sum.inr c ∈ C.verts

/-- The weighted degree `Σ_{e∈δ_C(z_i)} w(e)` of a pair vertex in a piece (p.12). -/
noncomputable def wdeg (C : A.Subgraph) (i : Fin k) : ℝ :=
  open scoped Classical in ∑ c : Copy k, if C.Adj (Sum.inl i) (Sum.inr c) then wt c else 0

/-- The edges of the piece `C` that avoid the vertex set `U`: the graph `H = C ∖ U` of p.14. -/
def avoid (C : A.Subgraph) (U : Set (AVert k)) : SimpleGraph (AVert k) where
  Adj u v := C.Adj u v ∧ u ∉ U ∧ v ∉ U
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => C.loopless.irrefl _ h.1⟩

/-- The root copies with `c_{j,ℓ} = 0`. -/
def zeroCap (cap : Copy k → ℝ) : Set (AVert k) :=
  {v | ∃ c, v = Sum.inr c ∧ cap c = 0}

/-- `α = min{b_i, min_{r_{j,ℓ}∈V(P)} c_{j,ℓ}}` (Algorithm 1, p.12), written as a minimum without a junk value. -/
def IsMinAlpha (b : ℝ) (cap : Copy k → ℝ) (P : List (AVert k)) (α : ℝ) : Prop :=
  α ≤ b ∧ (∀ c, Sum.inr c ∈ P → α ≤ cap c) ∧ (α = b ∨ ∃ c, Sum.inr c ∈ P ∧ α = cap c)

/-- **The state of the while loop of Algorithm 1 for one pair vertex.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Algorithm 1, p.12:
```
Let Q_i := ∅ and let b_i := 1 denote the flow remaining to send
Give each root copy r_{j,ℓ} in C capacity c_{j,ℓ} := ρ³/2^{ℓ+1}
while b_i > 0 do
  Find a shortest z_i–z*_C path P in C avoiding root copies with c_{j,ℓ} = 0
  if no such path exists or |E(P)| > ρ² then
    Declare the attempt for z_i failed
    ...
  Let α := min{b_i, min_{r_{j,ℓ}∈V(P)} c_{j,ℓ}}
  Add (P, α) to Q_i and set b_i ← b_i − α
  Set c_{j,ℓ} ← c_{j,ℓ} − α for each root copy r_{j,ℓ} ∈ V(P)
```
`RouteState ρ C i z b cap Q` says that `(b, cap, Q)` is reached by the loop from the start.

**Formalization Note.** The page leaves open which shortest path is found, so `step` allows every one. The capacity
`ρ³/2^{ℓ+1}` is `ρ³ · wt c`. A copy's capacity is reset for each `z_i`, as the page does. -/
inductive RouteState (ρ : ℕ) (C : A.Subgraph) (i z : Fin k) :
    ℝ → (Copy k → ℝ) → List (List (AVert k) × ℝ) → Prop
  | init : RouteState ρ C i z 1 (fun c => (ρ : ℝ) ^ 3 * wt c) []
  | step {b : ℝ} {cap : Copy k → ℝ} {Q : List (List (AVert k) × ℝ)} (P : List (AVert k)) (α : ℝ) :
      RouteState ρ C i z b cap Q → 0 < b →
      IsPathIn (avoid C (zeroCap cap)) (Sum.inl i) (Sum.inl z) P →
      (∀ P', IsPathIn (avoid C (zeroCap cap)) (Sum.inl i) (Sum.inl z) P' →
        (pEdges P).length ≤ (pEdges P').length) →
      (pEdges P).length ≤ ρ ^ 2 →
      IsMinAlpha b cap P α →
      open scoped Classical in
      RouteState ρ C i z (b - α) (fun c => if Sum.inr c ∈ P then cap c - α else cap c)
        (Q ++ [(P, α)])

/-- The test of the failing branch: "no such path exists or |E(P)| > ρ²" for a shortest `P`, that is, no `z_i`–`z*_C`
path avoiding the exhausted copies has at most `ρ²` edges. -/
def RouteFails (ρ : ℕ) (C : A.Subgraph) (i z : Fin k) (cap : Copy k → ℝ) : Prop :=
  ∀ P, IsPathIn (avoid C (zeroCap cap)) (Sum.inl i) (Sum.inl z) P → ρ ^ 2 < (pEdges P).length

end MCPoise


