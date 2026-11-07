-- Prove2me | Definitions.Def_MCPoise_IsGroupFlow
-- name    : MCPoise_IsGroupFlow
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:34:41.392918+00:00
-- url     : https://prove2.me/theorems/ec506ff6-d8dd-4f38-b1c4-f5f8b127cc7b
-- title:
--   Group flows: interpreting routes of the auxiliary graph as flows in G
-- statement:
--   Each auxiliary edge $(z_a, r_{j,\ell})$ corresponds to a sub-flow of value $w$ of the Junction-LP flow between $s_a$ and $r_j$. For $(P, \alpha) \in Q_i$, each edge of $P$ is replaced by its flow, scaled by $\alpha / w$, and these are concatenated into a flow of value $\alpha$ from the terminal to $s^*_C$; cycles are deleted to give simple paths. The first edge uses $t_i$ in place of $s_i$ for the flow from $t_i$.
--
--   For the representative pair, one unit from $t^*_C$ goes to the adjacent root copies in proportion to the auxiliary weights and back to $s^*_C$ in the same way. For $t = s^*_C$ the flow is the unit on the length-zero path.
--
--   **Formalization Note** Concatenation is written as a coupling of the scaled path flows of the consecutive edges. All choices of the sub-flows, of the coupling and of the cycle deletion are allowed.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §2.1, p.12, footnote 4

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_MCPoise_IsPathIn
import Definitions.Def_MCPoise_JunctionLPFeasible
import Definitions.Def_MCPoise_AVert
import Definitions.Def_MCPoise_RouteState
import Definitions.Def_MCPoise_AssignRun

namespace MCPoise

/-- The auxiliary edge at position `m` of a path `P` of `A`, as its pair index and its root copy. -/
def stepAt {k : ℕ} (P : List (AVert k)) (m : ℕ) : Option (Fin k × Copy k) :=
  match P[m]?, P[m + 1]? with
  | some (Sum.inl a), some (Sum.inr c) => some (a, c)
  | some (Sum.inr c), some (Sum.inl a) => some (a, c)
  | _, _ => none

/-- An LP path runs from the root to the terminal. At an edge traversed from a pair vertex to a root copy it is
reversed. -/
def orientSeg {k : ℕ} {V : Type*} (P : List (AVert k)) (m : ℕ) (p : List V) : List V :=
  match P[m]? with
  | some (Sum.inl _) => p.reverse
  | _ => p

/-- Concatenation of segments that share their endpoints, as vertex lists. -/
def joinWalk {V : Type*} : List (List V) → List V
  | [] => []
  | p :: ps => p ++ ps.flatMap List.tail

/-- The walk given by one LP path `τ_m` for each position `m` of `P`. -/
def concatWalk {k : ℕ} {V : Type*} (P : List (AVert k)) (τ : List (List V)) : List V :=
  joinWalk (τ.mapIdx fun m p => orientSeg P m p)

/-- "a corresponding flow in G": a sub-flow of value `w` of the LP flow `f` on the path set `P` (p.12). -/
def IsEdgeFlow {V : Type*} (P : Set (List V)) (f g : List V → ℝ) (w : ℝ) : Prop :=
  (∀ p ∈ P, 0 ≤ g p ∧ g p ≤ f p) ∧ (∀ p, p ∉ P → g p = 0) ∧ ∑ᶠ p ∈ P, g p = w

/-- **The flow in `G` that replaces one `(P, α)`.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), p.12: "interpret each pair vertex z_a on P as its source s_a and each root copy r_{j,ℓ} as r_j. By construction,
each edge e = (z_a, r_{j,ℓ}) ∈ A has a corresponding flow in G between the s_a and r_j of value w(e) = 1/2^{ℓ+1}. We replace
each edge e ∈ P by the corresponding fractional flow in G, scaled by α·1/w(e). Concatenating yields a flow of value α from
s_i to s*_C". Footnote 4: "This method of flow concatenation results in walks. Cycles can be deleted to obtain simple
paths without affecting any guarantees."

`gs m` is the corresponding flow of the `m`-th edge of `P`, which uses the label `(a, false, j)`, or `(a, b, j)` at position
`0` (the first terminal, `s_i` or `t_i`). `π` weights tuples of LP paths, one for each position, with the `m`-th marginal equal
to the scaled `gs m`: this is what concatenating fractional flows means. `q τ` is a simple `t`–`s*` path in the edges of
the walk of `τ`, the result of the cycle deletion. `F` lists the weighted simple paths.

**Formalization Note.** The page fixes no way of pairing the path pieces and no corresponding flow, and any cycle deletion
is allowed, so this predicate allows them all; Lemma 2.6 is stated for every such flow. -/
def IsConcatFlow (I : Inst) (L : ℕ) (f : Fin I.k → Bool → Fin I.k → List (Fin I.n) → ℝ)
    (b : Bool) (t sstar : Fin I.n) (P : List (AVert I.k)) (α : ℝ)
    (F : List (List (Fin I.n) × ℝ)) : Prop :=
  ∃ (gs : ℕ → List (Fin I.n) → ℝ) (π : List (List (Fin I.n)) →₀ ℝ)
      (q : List (List (Fin I.n)) → List (Fin I.n)),
    (∀ m a c, stepAt P m = some (a, c) →
      let bm := if m = 0 then b else false
      IsEdgeFlow (JP I L a bm c.1) (f a bm c.1) (gs m) (wt c)) ∧
    (∀ τ ∈ π.support, 0 < π τ ∧ τ.length + 1 = P.length) ∧
    (∀ m a c, stepAt P m = some (a, c) → ∀ p,
      (open scoped Classical in π.support.sum fun τ => if τ[m]? = some p then π τ else 0) =
        α / wt c * gs m p) ∧
    F = π.support.toList.map (fun τ => (q τ, π τ)) ∧
    ∀ τ ∈ π.support, IsPathIn I.graph t sstar (q τ) ∧
      ∀ e ∈ pEdges (q τ), e ∈ pEdges (concatWalk P τ)

/-- **The unit flow of Algorithm 1's group from the terminal `(i, b)` to `s*_C`.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), p.12: for `z_i ≠ z*_C`, the flows of the `(P, α) ∈ Q_i` summed ("summing over all paths in Q_i gives the desired unit
flow. A similar procedure can be done to obtain a t_i-s*_C flow, instead interpreting z_i as t_i"). "Finally, for the pair
(s*_C, t*_C) corresponding to z*_C, route one unit of flow from t*_C to root copies adjacent to z*_C in C in proportion to
their auxiliary weights, and then back to s*_C in the same way."

**Formalization Note.** The last case is the same construction with the pseudo-routes `z*_C, r_{j,ℓ}, z*_C` of value
`w(e)/wdeg(z*_C)`. For `t = s*_C` itself, which the page leaves implicit, the flow is the unit on the length-zero path. -/
def IsGroupFlow (I : Inst) (L : ℕ) (f : Fin I.k → Bool → Fin I.k → List (Fin I.n) → ℝ)
    {A : SimpleGraph (AVert I.k)} (G : AGroup A) (i : Fin I.k) (b : Bool)
    (F : List (List (Fin I.n) × ℝ)) : Prop :=
  open scoped Classical in
  let sstar := I.s G.zstar
  if i ≠ G.zstar then
    ∃ Fs : List (List (List (Fin I.n) × ℝ)),
      List.Forall₂ (fun Pα Fp => IsConcatFlow I L f b (I.term i b) sstar Pα.1 Pα.2 Fp) (G.Q i) Fs ∧
      F = Fs.flatten
  else if b then
    ∃ Fs : List (List (List (Fin I.n) × ℝ)),
      List.Forall₂ (fun (c : Copy I.k) Fp =>
          IsConcatFlow I L f true (I.t i) sstar
            [Sum.inl G.zstar, Sum.inr c, Sum.inl G.zstar] (wt c / wdeg G.C G.zstar) Fp)
        ((Finset.univ.filter fun c => G.C.Adj (Sum.inl G.zstar) (Sum.inr c)).toList) Fs ∧
      F = Fs.flatten
  else
    F = [([sstar], 1)]

/-- The load of a list of weighted paths on the edge `e`. A simple path contains `e` at most once. -/
noncomputable def wLoad {V : Type*} (F : List (List V × ℝ)) (e : Sym2 V) : ℝ :=
  open scoped Classical in (F.map fun pw => if e ∈ pEdges pw.1 then pw.2 else 0).sum

end MCPoise


