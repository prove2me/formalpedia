-- Prove2me | Definitions.Def_ContinualHardness_Linear_SmoothLabelCover
-- name    : ContinualHardness_Linear_SmoothLabelCover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:12:02.378778+00:00
-- url     : https://prove2.me/theorems/3b4761f2-f02d-465a-a6ab-73d3ddf6f579
-- title:
--   Smooth-Label-Cover instances (Definition A.2), labelings, the properties of Theorem A.3, and their binary encoding
-- statement:
--   An instance $L(G(V,E),N,M,\{\pi^{e,v}\})$ of **Smooth-Label-Cover** (`SLCInstance`) has vertex set $[V]$, label set $[M]$, projection range $[N]$ and edges indexed by $[E]$: edge $e$ joins $(v_1,v_2)$ (`ends e`) and carries projections $\pi^{e,v_1},\pi^{e,v_2}:[M]\to[N]$ (`proj e false`, `proj e true`). The end $b$ of $e$ is the vertex `endpt e b` ($v_1$ for `false`, $v_2$ for `true`) and the projection there is `proj e b`; the degree of $w$ is the number of edge-ends at $w$ (`degree`), i.e. the edges incident on $w$ with multiplicity, a loop counted at both ends. A **labeling** $\ell:[V]\to[M]$ **satisfies** $e=(v_1,v_2)$ if $\pi^{e,v_1}(\ell(v_1))=\pi^{e,v_2}(\ell(v_2))$ (`Sat`); `satCount ℓ` counts satisfied edges. $L$ is **satisfiable** if some labeling satisfies every edge, and has **value below** $s$ if every labeling satisfies fewer than $s|E|$ edges (`ValueBelow s`).
--
--   `Props Q R` collects the properties of the instances of Theorem A.3:
--   * $G$ is a regular connected graph: $E\ge1$ (loops and parallel edges allowed), all degrees are equal, and the underlying simple graph is connected;
--   * $M=7^{(Q+1)R}$ and $N=2^R7^{QR}$;
--   * **Smoothness**: for every vertex $w$ and labels $i\ne j$, $\Pr_{e\sim w}[\pi^{e,w}(i)=\pi^{e,w}(j)]\le 1/Q$, over a uniformly random edge incident on $w$ (a uniformly random edge-end at $w$);
--   * every preimage $(\pi^{e,v})^{-1}(i)$ has at most $q=4^R$ elements;
--   * **Consistent label weighting**: there are $\Lambda_v:[M]\to\{1,2,2^2,\dots,2^{(Q+1)R}\}$ with $\sum_{j\in(\pi^{e,v_1})^{-1}(i)}\Lambda_{v_1}(j)=\sum_{j\in(\pi^{e,v_2})^{-1}(i)}\Lambda_{v_2}(j)$ for every edge $e=(v_1,v_2)$ and $i\in[N]$;
--   * **Weak expansion**: for every nonempty $V'\subseteq V$, with $\delta=|V'|/|V|$, at least $\delta^2|E|$ edges have both endpoints in $V'$.
--
--   The **binary code** of $L$ (`encodeSLC`) lists $V,M,N,E$, then for each edge its two endpoints and the value tables of its two projections.
--
--   **Formalization Note.** Edges form an indexed family, so parallel edges and loops are allowed and all edge counts and the random incident edge are with multiplicity (a loop at $w$ counts at both of its ends). Loops cannot be excluded: for $|V'|=1$ weak expansion asks for at least $|E|/|V|^2>0$ edges inside $V'$, which only a loop can be, and the construction of [15] (Appendix B: an edge joins $u$ and $v$ whenever their clause tuples agree off an index set $I$, which includes $u=v$) produces loops. "For any $\delta>0$ and $|V'|=\delta|V|$" is written for every nonempty $V'$ with $\delta:=|V'|/|V|$.
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 16, Definition A.2 (PDF p. 17); p. 17, Theorem A.3 (PDF p. 18); pp. 25-26, Appendix B (PDF pp. 26-27)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Encoding

namespace ContinualHardness.Linear

/-! # Smooth-Label-Cover (Definition A.2), the properties of Theorem A.3, and the binary encoding

Vertices are `Fin V`, labels `Fin M` (the paper's `[M]`), projection range `Fin N` (the paper's
`[N]`). Edges are a finite indexed family `Fin E`, each with two endpoints and one projection per
endpoint, so parallel edges and loops are allowed and every count over edges is with multiplicity.
Loops must be allowed: for `|V'| = 1` the weak expansion property asks for at least `|E|/|V|²`
edges inside `V'`, which only loops can supply (the construction of [15] and Appendix B produces
them). The edges at a vertex are counted by edge-ends, so a loop is counted at both of its ends. -/

/-- An instance `L(G(V, E), N, M, {π^{e,v}})` of Smooth-Label-Cover: `V` vertices, label sets `[M]`
and `[N]`, `E` edges; edge `e` joins `ends e = (v₁, v₂)` and carries the projections
`π^{e,v₁} = proj e false` and `π^{e,v₂} = proj e true`, both `[M] → [N]`. -/
structure SLCInstance where
  /-- Number of vertices. -/
  V : ℕ
  /-- Size of the label set `[M]` of the vertices. -/
  M : ℕ
  /-- Size of the common range `[N]` of the projections. -/
  N : ℕ
  /-- Number of edges. -/
  E : ℕ
  /-- The endpoints `(v₁, v₂)` of each edge. -/
  ends : Fin E → Fin V × Fin V
  /-- `proj e false = π^{e,v₁}`, `proj e true = π^{e,v₂}`. -/
  proj : Fin E → Bool → Fin M → Fin N

namespace SLCInstance

variable (L : SLCInstance)

/-- The endpoint of edge `e` at end `b`: `endpt e false = v₁`, `endpt e true = v₂`; the
projection at that end is `proj e b`. -/
def endpt (e : Fin L.E) (b : Bool) : Fin L.V := if b then (L.ends e).2 else (L.ends e).1

/-- The degree of `w`: the number of edge-ends `(e, b)` at `w`, i.e. the edges incident on `w`
with multiplicity, a loop at `w` counted at both of its ends. -/
def degree (w : Fin L.V) : ℕ :=
  (Finset.univ.filter fun p : Fin L.E × Bool => L.endpt p.1 p.2 = w).card

/-- The underlying simple graph: `u ~ v` iff `u ≠ v` and some edge joins them. -/
def graph : SimpleGraph (Fin L.V) :=
  SimpleGraph.fromRel fun u v => ∃ e, L.ends e = (u, v)

/-- A labeling `ℓ : V → [M]` satisfies edge `e = (v₁, v₂)` iff
`π^{e,v₁}(ℓ(v₁)) = π^{e,v₂}(ℓ(v₂))`. -/
def Sat (ℓ : Fin L.V → Fin L.M) (e : Fin L.E) : Prop :=
  L.proj e false (ℓ (L.ends e).1) = L.proj e true (ℓ (L.ends e).2)

instance (ℓ : Fin L.V → Fin L.M) (e : Fin L.E) : Decidable (L.Sat ℓ e) := by
  unfold Sat; infer_instance

/-- The number of edges satisfied by the labeling `ℓ`. -/
def satCount (ℓ : Fin L.V → Fin L.M) : ℕ := (Finset.univ.filter fun e => L.Sat ℓ e).card

/-- The number of edges with both endpoints in `S` (edges induced by `S`). -/
def inducedCount (S : Finset (Fin L.V)) : ℕ :=
  (Finset.univ.filter fun e => (L.ends e).1 ∈ S ∧ (L.ends e).2 ∈ S).card

/-- The properties of the instances of Theorem A.3 for the parameters `Q, R`:
* `G` has at least one edge (loops and parallel edges allowed), is regular (all degrees, counted
  by edge-ends, are equal) and connected (Def. A.2);
* `M = 7^{(Q+1)R}` and `N = 2^R 7^{QR}`;
* (Smoothness) for every vertex `w` and labels `i ≠ j`, the fraction of edge-ends `(e, b)` at `w`
  (a uniformly random edge incident on `w`) with `π^{e,w}(i) = π^{e,w}(j)` is at most `1/Q`;
* every preimage `(π^{e,v})⁻¹(i)` has at most `q = 4^R` elements;
* (Consistent label weighting) there are `Λ_v : [M] → {1, 2, 2², …, 2^{(Q+1)R}}` with
  `∑_{j ∈ (π^{e,v₁})⁻¹(i)} Λ_{v₁}(j) = ∑_{j ∈ (π^{e,v₂})⁻¹(i)} Λ_{v₂}(j)` for every edge `e` and every
  `i ∈ [N]`;
* (Weak Expansion) for every nonempty `V' ⊆ V`, with `δ = |V'|/|V|`, at least `δ²|E|` edges
  have both endpoints in `V'`. -/
def Props (Q R : ℕ) : Prop :=
  0 < L.E ∧
  (∀ v w, L.degree v = L.degree w) ∧ L.graph.Connected ∧
  L.M = 7 ^ ((Q + 1) * R) ∧ L.N = 2 ^ R * 7 ^ (Q * R) ∧
  (∀ (w : Fin L.V) (i j : Fin L.M), i ≠ j →
    ((Finset.univ.filter fun p : Fin L.E × Bool =>
        L.endpt p.1 p.2 = w ∧ L.proj p.1 p.2 i = L.proj p.1 p.2 j).card : ℝ)
      ≤ (L.degree w : ℝ) / Q) ∧
  (∀ (e : Fin L.E) (b : Bool) (i : Fin L.N),
    (Finset.univ.filter fun j => L.proj e b j = i).card ≤ 4 ^ R) ∧
  (∃ Λ : Fin L.V → Fin L.M → ℕ,
    (∀ v j, ∃ k ≤ (Q + 1) * R, Λ v j = 2 ^ k) ∧
    ∀ (e : Fin L.E) (i : Fin L.N),
      (∑ j ∈ Finset.univ.filter (fun j => L.proj e false j = i), Λ (L.ends e).1 j) =
        ∑ j ∈ Finset.univ.filter (fun j => L.proj e true j = i), Λ (L.ends e).2 j) ∧
  (∀ S : Finset (Fin L.V), S.Nonempty →
    ((S.card : ℝ) / L.V) ^ 2 * L.E ≤ (L.inducedCount S : ℝ))

/-- YES: some labeling satisfies every edge. -/
def Satisfiable : Prop := ∃ ℓ : Fin L.V → Fin L.M, ∀ e, L.Sat ℓ e

/-- NO (for `s`): every labeling satisfies less than a fraction `s` of the edges. -/
def ValueBelow (s : ℝ) : Prop := ∀ ℓ : Fin L.V → Fin L.M, (L.satCount ℓ : ℝ) < s * L.E

end SLCInstance

/-- The binary code of a Smooth-Label-Cover instance: `V`, `M`, `N`, `E`, then for every edge its
two endpoints and the value tables `π^{e,v₁}(1), …, π^{e,v₁}(M)`, `π^{e,v₂}(1), …, π^{e,v₂}(M)`. -/
def encodeSLC (L : SLCInstance) : List Bool :=
  encNat L.V ++ encNat L.M ++ encNat L.N ++ encNat L.E ++
    (List.ofFn fun e : Fin L.E =>
      encNat (L.ends e).1 ++ encNat (L.ends e).2 ++
        (List.ofFn fun j => encNat (L.proj e false j)).flatten ++
        (List.ofFn fun j => encNat (L.proj e true j)).flatten).flatten

end ContinualHardness.Linear


