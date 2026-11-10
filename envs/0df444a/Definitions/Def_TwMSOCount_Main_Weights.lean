-- Prove2me | Definitions.Def_TwMSOCount_Main_Weights
-- name    : TwMSOCount_Main_Weights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:38:47.398371+00:00
-- url     : https://prove2.me/theorems/6eac0123-0559-4f56-bf16-c5ac128e5941
-- title:
--   Color weights, the weight W(G, χ) of a colored graph and the partition function Z_{k,n}(ψ)
-- statement:
--   Fix $r \ge 1$ colors $C = \{0,\dots,r-1\}$, nonnegative rational **vertex weights** $\lambda_c$ and **present-edge weights** $\beta_{c,d} = \beta_{d,c}$ (zeros allowed). For a coloring $\zeta$ of a set $U$ and a set $F$ of pairs in $U$, the weight of the edges $F$ is $\omega_\zeta(F) = \prod_{\{a,b\}\in F} \beta_{\zeta(a),\zeta(b)}$. The weight of a colored graph $(G,\chi)$ is
--   $$W(G,\chi) = \prod_{v \in V} \lambda_{\chi(v)} \cdot \omega_\chi(E),$$
--   so absent edges contribute no factor. For $k, n \in \mathbb N$ and an MSO2 sentence $\psi$ over $V_C$,
--   $$Z_{k,n}(\psi) = \sum_{\substack{V(G) = [n],\ \chi : [n] \to C \\ \mathrm{tw}(G) \le k,\ (G,\chi) \models \psi}} W(G,\chi),$$
--   the sum over all simple graphs on the labeled vertex set $[n]$ and all colorings; distinct edge sets or colorings are distinct terms, disconnected and nonchordal graphs included, and each satisfying pair is counted once. Treewidth is the published `PlantedSubgraphLD.tw` (minimum width of a tree decomposition; $0$ for the empty graph).
--
--   **Formalization Note.** `Weights r` bundles `vtx`, `edge` and the symmetry of `edge`; `Weights.omega`, `Weights.W`, `ModelsPsi`, `Z k n r ψ w : ℚ≥0`. The vertex set $[n]$ is `Fin n` (labels $0,\dots,n-1$).
-- source:
--   Zou, Wang, Chang, Wang, Kuželka, Exact Counting and Sampling of Labeled Graphs of Bounded Treewidth with MSO Properties, STOC 2027 submission (manuscript sha256 2715a74f…775b), §2, p. 4 (PDF 5)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_tw
import Definitions.Def_TwMSOCount_Main_MSO2

namespace TwMSOCount.Main

/-- Color weights for `r` colors `Fin r`: nonnegative rational vertex weights `λ_c` and
present-edge weights `β_{c,d} = β_{d,c}` (Section 2). Zero weights are allowed. -/
structure Weights (r : ℕ) where
  vtx : Fin r → ℚ≥0
  edge : Fin r → Fin r → ℚ≥0
  edge_symm : ∀ c d, edge c d = edge d c

/-- The factor `β_{χ(a), χ(b)}` of an unordered pair `{a, b}`. -/
def Weights.edgeFactor {r : ℕ} {V : Type} (w : Weights r) (χ : V → Fin r) (e : Sym2 V) : ℚ≥0 :=
  Sym2.lift ⟨fun a b => w.edge (χ a) (χ b), fun a b => w.edge_symm (χ a) (χ b)⟩ e

/-- `ω_χ(F) = ∏_{{a,b} ∈ F} β_{χ(a), χ(b)}`, the weight of a finite set of edges. -/
def Weights.omega {r : ℕ} {V : Type} (w : Weights r) (χ : V → Fin r) (F : Finset (Sym2 V)) :
    ℚ≥0 :=
  ∏ e ∈ F, w.edgeFactor χ e

open Classical in
/-- `W(G, χ) = ∏_{v ∈ V} λ_{χ(v)} · ω_χ(E)`; absent edges contribute no factor. -/
noncomputable def Weights.W {r : ℕ} {V : Type} [Fintype V] (w : Weights r) (G : SimpleGraph V)
    (χ : V → Fin r) : ℚ≥0 :=
  (∏ v, w.vtx (χ v)) * w.omega χ G.edgeFinset

/-- `(G, χ) ⊨ ψ` for a sentence `ψ` over `V_C` (no constant symbols). -/
def ModelsPsi {r : ℕ} {V : Type} (G : SimpleGraph V) (χ : V → Fin r) (ψ : Formula r Empty) :
    Prop :=
  Formula.Models G χ (fun e => e.elim) ψ

open Classical in
/-- The partition function `Z_{k,n}(ψ) = Σ W(G, χ)` over all simple graphs `G` with vertex set
`Fin n` (the output labels `[n]`, `0`-based), all colorings `χ : Fin n → Fin r`, with
`tw(G) ≤ k` and `(G, χ) ⊨ ψ` (Section 2, p. 4). Each satisfying pair is counted once. -/
noncomputable def Z (k n r : ℕ) (ψ : Formula r Empty) (w : Weights r) : ℚ≥0 :=
  ∑ G : SimpleGraph (Fin n), ∑ χ : Fin n → Fin r,
    if PlantedSubgraphLD.tw G ≤ k ∧ ModelsPsi G χ ψ then w.W G χ else 0

end TwMSOCount.Main


