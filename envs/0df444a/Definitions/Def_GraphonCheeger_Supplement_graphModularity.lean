-- Prove2me | Definitions.Def_GraphonCheeger_Supplement_graphModularity
-- name    : GraphonCheeger_Supplement_graphModularity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:22:27.508506+00:00
-- url     : https://prove2.me/theorems/9ea6ffb4-8f64-40be-ac94-2bb703aee6a7
-- title:
--   Modularity of finite graphs: $q^*(G)$, $q^*_\kappa(G)$, fractional $q^*_{\mathrm{frac}}(G)$, blow-ups $G[b]$ and edge density $\rho_G$
-- statement:
--   Let $G$ be a graph with $m\ge1$ edges and degrees $d_u$. For a partition $\mathcal A$ of $V(G)$ and a fractional $\kappa$-partition $\Phi=(\phi_1,\dots,\phi_\kappa)$ (functions $\phi_j:V(G)\to[0,1]$ with $\sum_j\phi_j(v)=1$), the modularity scores are
--   $$
--   q(G,\mathcal A)=\frac1{2m}\sum_{A\in\mathcal A}\sum_{u,v\in A}\Bigl(\mathbf 1\{uv\in E(G)\}-\frac{d_ud_v}{2m}\Bigr),\qquad
--   q(G,\Phi)=\frac1{2m}\sum_{u,v\in V(G)}\Bigl(\mathbf 1[uv\in E(G)]-\frac{d_ud_v}{2m}\Bigr)\sum_{j=1}^\kappa\phi_j(u)\phi_j(v),
--   $$
--   and both are $0$ when $G$ has no edges. The modularity is $q^*(G)=\max_{\mathcal A}q(G,\mathcal A)$; the $\kappa$-modularity $q^*_\kappa(G)$ is the maximum over partitions into at most $\kappa$ parts; $q^*_{\kappa,\mathrm{frac}}(G)=\sup_\Phi q(G,\Phi)$ over fractional $\kappa$-partitions; and $q^*_{\mathrm{frac}}(G)=\sup_{\kappa\ge1}q^*_{\kappa,\mathrm{frac}}(G)$. The $b$-blow-up $G[b]$ replaces each vertex $v$ by copies $(v,1),\dots,(v,b)$, with $(u,i)\sim(v,j)$ iff $uv\in E(G)$. The edge density is $\rho_G=e(G)/\binom{|G|}{2}$.
--
--   These are the graph parameters of Theorems 5.19, 5.22, 5.29 and 6.9.
--
--   **Formalization Note** Graphs are simple graphs on a finite type $V$ with classical decidability. Partitions are `Finpartition` of the whole vertex set and the inner sum runs over all ordered pairs in a part, including $u=v$, as in (5.1). The paper uses $q^*_\kappa(G)$ and $q^*_{\kappa,\mathrm{frac}}(G)$ in Lemma 5.21 and the proof of Theorem 5.19 without displaying a definition; they are written here as the maximum of $q(G,\Phi_\chi)$ over maps $\chi:V\to[\kappa]$, where $\Phi_\chi$ is the point-mass partition (so $q(G,\Phi_\chi)$ is $q$ of the partition into the fibres of $\chi$), and as the supremum over fractional $\kappa$-partitions. `blowUp G b` lives on $V\times$`Fin b`. For $|G|\le1$ the density is the junk value $0$.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813a65d248922299a3380e10f238dbc5dcd3be060f7810b462bd5d3d10f), Definition 5.1, p.51; (5.74), p.62; Definition 5.18, p.63; §5.1, p.66; notation table, p.82

import Mathlib
import Definitions.Def_GraphonCheeger_Supplement_homDens

namespace GraphonCheeger.Supplement

/-!
# Modularity of finite graphs: `q(G, A)`, `q*(G)`, `q*_κ(G)`, fractional `q(G, Φ)`, `q*_frac(G)`,
blow-ups `G[b]` and the edge density `ρ_G`

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…): Definition 5.1 (p.51), (5.74) (p.62),
Definition 5.18 (p.63), §5.1 (p.66), §6 and Appendix B (pp.73, 82).

**Formalization Note.**
* Graphs are simple graphs on a finite vertex type `V`; decidability is classical. `m = e(G)` is
  the number of edges and `d_u` the degree.
* `qPart G P` is (5.1) for a partition `P` of `V` (`Finpartition` of the whole vertex set), with
  the inner sum over all ordered pairs `u, v ∈ A` (including `u = v`), and `modularity G = q*(G)`
  is its maximum (5.2). `qFrac G Φ` is (5.75) for a fractional partition `Φ`; both are `0` when
  `G` has no edges, as on pp.51 and 63.
* The paper uses `q*_κ(G)` and `q*_{κ,frac}(G)` in Lemma 5.21 and the proof of Theorem 5.19
  without a displayed definition; they are the maximum over partitions into at most `κ` parts,
  written as maps `χ : V → [κ]` (`modularityK`), and the supremum over fractional `κ`-partitions
  (`modularityFracK`). For a map `χ`, `qFrac G (ofColour χ)` is `q(G, A_χ)` for the partition into
  the nonempty fibres of `χ`, since `Σ_j 1[χu = j] 1[χv = j] = 1[χu = χv]`.
* `modularityFrac G = q*_frac(G) = sup_{κ ≥ 1} sup_Φ q(G, Φ)` (5.76).
* `blowUp G b` is `G[b]` on `V × Fin b`: `(u, i) ∼ (v, j)` iff `uv ∈ E(G)` (p.66).
* `edgeDensityG G = e(G) / C(|G|, 2)` (notation table, p.82); for `|G| ≤ 1` it is the junk `0`.
-/

open Classical

variable {V : Type*} [Fintype V]

/-- The number of edges `m = e(G)`. -/
noncomputable def numEdges (G : SimpleGraph V) : ℕ := G.edgeFinset.card

/-- The modularity score `q(G, A) = (1/2m) Σ_{A ∈ A} Σ_{u,v ∈ A} (1{uv ∈ E(G)} − d_u d_v / 2m)`
of a vertex partition ((5.1), p.51); `0` when `G` has no edges. -/
noncomputable def qPart (G : SimpleGraph V) (P : Finpartition (Finset.univ : Finset V)) : ℝ :=
  if numEdges G = 0 then 0 else
    (1 / (2 * (numEdges G : ℝ))) * ∑ A ∈ P.parts, ∑ u ∈ A, ∑ v ∈ A,
      ((if G.Adj u v then (1 : ℝ) else 0) -
        (G.degree u : ℝ) * (G.degree v : ℝ) / (2 * (numEdges G : ℝ)))

/-- The modularity `q*(G) = max_A q(G, A)` over all vertex partitions ((5.2), p.51). -/
noncomputable def modularity (G : SimpleGraph V) : ℝ :=
  sSup (Set.range (qPart G))

/-- A fractional `κ`-partition `Φ = (ϕ_1, …, ϕ_κ)` of `V(G)`: `ϕ_j : V → [0, 1]` with
`Σ_j ϕ_j(v) = 1` ((5.74), p.62). -/
def IsFracPartition {κ : ℕ} (Φ : V → Fin κ → ℝ) : Prop :=
  (∀ v j, Φ v j ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ v, ∑ j, Φ v j = 1

/-- The fractional modularity score
`q(G, Φ) = (1/2m) Σ_{u,v} (1[uv ∈ E(G)] − d_u d_v / 2m) Σ_j ϕ_j(u) ϕ_j(v)` ((5.75), p.63); `0` when
`G` has no edges. -/
noncomputable def qFrac {κ : ℕ} (G : SimpleGraph V) (Φ : V → Fin κ → ℝ) : ℝ :=
  if numEdges G = 0 then 0 else
    (1 / (2 * (numEdges G : ℝ))) * ∑ u, ∑ v,
      ((if G.Adj u v then (1 : ℝ) else 0) -
        (G.degree u : ℝ) * (G.degree v : ℝ) / (2 * (numEdges G : ℝ))) * ∑ j, Φ u j * Φ v j

/-- The `κ`-modularity `q*_κ(G)`: the maximum of `q(G, A)` over partitions into at most `κ` parts,
i.e. over maps `χ : V → [κ]` (pp.63–65, proof of Theorem 5.19 and Lemma 5.21). -/
noncomputable def modularityK (κ : ℕ) (G : SimpleGraph V) : ℝ :=
  sSup {r : ℝ | ∃ χ : V → Fin κ, r = qFrac G (ofColour χ)}

/-- The fractional `κ`-modularity `q*_{κ,frac}(G) = sup_Φ q(G, Φ)` over fractional `κ`-partitions
(pp.63–65). -/
noncomputable def modularityFracK (κ : ℕ) (G : SimpleGraph V) : ℝ :=
  sSup {r : ℝ | ∃ Φ : V → Fin κ → ℝ, IsFracPartition Φ ∧ r = qFrac G Φ}

/-- The fractional modularity `q*_frac(G) = sup_{κ ≥ 1} sup_Φ q(G, Φ)` ((5.76), p.63). -/
noncomputable def modularityFrac (G : SimpleGraph V) : ℝ :=
  sSup {r : ℝ | ∃ κ : ℕ, 1 ≤ κ ∧ r = modularityFracK κ G}

/-- The `b`-blow-up `G[b]` (p.66): vertices `(v, i)`, `i ∈ [b]`, with `(u, i) ∼ (v, j)` iff
`uv ∈ E(G)`. -/
def blowUp (G : SimpleGraph V) (b : ℕ) : SimpleGraph (V × Fin b) :=
  G.comap Prod.fst

/-- The edge density `ρ_G = e(G) / C(|G|, 2)` (notation table, p.82). -/
noncomputable def edgeDensityG (G : SimpleGraph V) : ℝ :=
  (numEdges G : ℝ) / ((Fintype.card V).choose 2 : ℝ)

end GraphonCheeger.Supplement


