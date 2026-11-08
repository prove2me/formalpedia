-- Prove2me | Definitions.Def_ZeroExtensionGap_fractionalArboricity
-- name    : ZeroExtensionGap_fractionalArboricity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:15.132219+00:00
-- url     : https://prove2.me/theorems/9b684f3e-8b88-450f-9e05-3c2c5ab25232
-- title:
--   Weighted distance, girth, edge expansion, unweighted diameter and fractional arboricity $\Gamma$
-- statement:
--   For a graph $G=(V,E)$ with positive lengths, $d_G(x,y)$ is the length of a shortest path, and $d_G(x,y)=\infty$ if none exists. The **girth** is the minimum number of edges in a cycle ($\infty$ if acyclic). The **unweighted diameter** is the maximum over pairs of the minimum number of edges of a connecting path. With $\delta_G(S)$ the edges having exactly one endpoint in $S$, the **edge expansion** is
--
--   $$h(G)=\min\Big\{\frac{|\delta_G(S)|}{|S|}:\ S\subseteq V,\ 0<|S|\le|V|/2\Big\},$$
--
--   and the **fractional arboricity** is
--
--   $$\Gamma(G)=\max\Big\{1,\ \max\Big\{\frac{|E(G[S])|}{|S|-1}:\ S\subseteq V,\ |S|\ge2\Big\}\Big\}.$$
--
--   The module also contains the counting-ratio probability `probUniform`.
--
--   **Formalization Note.** `wdist` is valued in `ℝ≥0∞`, as an infimum over walks, which agrees with paths for positive lengths. Girth, diameter and expansion are stated as lower or upper bounds (`GirthAtLeast`, `UnweightedDiameterLE`, `EdgeExpansionAtLeast`), so that Mathlib's `girth` (which is $0$ on acyclic graphs) and `dist` (which is $0$ on disconnected pairs) do not occur. `fracArbOf` writes the max with the $1$ included and takes the counting function as an argument, so that simple graphs and multigraphs share one formula.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), §2, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_ZeroExtensionGap_Instance

open scoped ENNReal

namespace ZeroExtensionGap

variable {V : Type*}

/-- The length of a walk with respect to a length function on ordered vertex pairs. -/
noncomputable def walkLength {G : SimpleGraph V} (len : V → V → ℝ) {x y : V} (p : G.Walk x y) : ℝ :=
  (p.darts.map fun d => len d.fst d.snd).sum

/-- The shortest-path distance `d_G(x, y)` of §2, p.5 (PDF p.7) (Chen, Zhu, *Almost Tight Hardness
of Approximation for 0-Extension*, STOC 2027 submission, manuscript sha256 0cdea87b…), with
`d_G(x, y) = ∞` if no path exists: the infimum over walks.
**Formalization Note.** Valued in `ℝ≥0∞`, so that the disconnected case is `⊤` and not a junk `0`.
For positive lengths a shortest walk is a path, so walks and paths give the same value. -/
noncomputable def wdist (G : SimpleGraph V) (len : V → V → ℝ) (x y : V) : ℝ≥0∞ :=
  ⨅ p : G.Walk x y, ENNReal.ofReal (walkLength len p)

/-- The girth is at least `x` (§2, p.5, PDF p.7: minimum number of edges in a cycle, `∞` if acyclic).
**Formalization Note.** Mathlib's `SimpleGraph.girth` is `0` on acyclic graphs, so it is not used. -/
def GirthAtLeast (G : SimpleGraph V) (x : ℝ) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → x ≤ (c.length : ℝ)

/-- The unweighted diameter is at most `x` (§2, p.5, PDF p.7): every two vertices are joined by a
walk with at most `x` edges. In particular the graph is connected when `V` is nonempty. -/
def UnweightedDiameterLE (G : SimpleGraph V) (x : ℝ) : Prop :=
  ∀ a b : V, ∃ p : G.Walk a b, (p.length : ℝ) ≤ x

section Finite

variable [Fintype V]

open Classical in
/-- The degree of a vertex. -/
noncomputable def vdeg (G : SimpleGraph V) (v : V) : ℕ := (Finset.univ.filter (G.Adj v)).card

/-- The maximum degree is at most `d`. -/
def MaxDegreeLE (G : SimpleGraph V) (d : ℕ) : Prop := ∀ v, vdeg G v ≤ d

open Classical in
/-- `δ_G(S)`, the edges with exactly one endpoint in `S` (§2, p.5, PDF p.7). -/
noncomputable def edgeBoundary (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) :=
  (edgeFin G).filter fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S

/-- The edge expansion `h(G) = min{|δ_G(S)|/|S| : 0 < |S| ≤ |V|/2}` is at least `h₀` (§2, p.5, PDF
p.7), stated without the division. -/
def EdgeExpansionAtLeast (G : SimpleGraph V) (h₀ : ℝ) : Prop :=
  ∀ S : Finset V, 0 < S.card → 2 * S.card ≤ Fintype.card V →
    h₀ * (S.card : ℝ) ≤ ((edgeBoundary G S).card : ℝ)

open Classical in
/-- `|E(G[S])|`, the number of edges with both endpoints in `S`. -/
noncomputable def inducedEdgeCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  ((edgeFin G).filter fun e => ∀ v ∈ e, v ∈ S).card

open Classical in
/-- The formula `max{1, max{count(S)/(|S| − 1) : S ⊆ V, |S| ≥ 2}}` of §2, p.5 (PDF p.7), for an
arbitrary edge-counting function. The value `1` is included literally, so the inner maximum over an
empty family (`|V| ≤ 1`) gives `1`. -/
noncomputable def fracArbOf (count : Finset V → ℕ) : ℝ :=
  (Finset.univ.filter fun S : Finset V => 2 ≤ S.card).fold max (1 : ℝ)
    fun S => (count S : ℝ) / ((S.card : ℝ) - 1)

/-- The fractional arboricity `Γ(G)` of §2, p.5 (PDF p.7). -/
noncomputable def fracArb (G : SimpleGraph V) : ℝ := fracArbOf (inducedEdgeCount G)

end Finite

open Classical in
/-- The probability of an event under the uniform law on a finite type, as a counting ratio. -/
noncomputable def probUniform {α : Type*} [Fintype α] (P : α → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card α : ℝ)

end ZeroExtensionGap


