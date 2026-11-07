-- Prove2me | Definitions.Def_PlantedSubgraphLD_restrictTriple
-- name    : PlantedSubgraphLD_restrictTriple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:38.559239+00:00
-- url     : https://prove2.me/theorems/e7089458-bcb8-41f7-88da-54a2d6cdc663
-- title:
--   The restriction map $\Delta_F$ on isomorphism triples
-- statement:
--   Let $F$ be a nonempty abstract graph with $N_\Gamma(F)>0$, and fix for every copy $F^\circ\in C_\Gamma(F)$ an ordered edge decomposition $\mathcal T(F^\circ)=(T^\circ_1,\dots,T^\circ_m)$. For a triple $(F^\circ_1,F^\circ_2,\psi)\in\mathrm{Tri}(F)$ with $\mathcal T(F^\circ_1)=(T^\circ_{1,1},\dots,T^\circ_{1,m})$ put $T^\circ_{2,i}=\psi(T^\circ_{1,i})$ and $\psi_i=\psi|_{T^\circ_{1,i}}$. The **restriction map** (4.4) is
--
--   $$
--   \Delta_F:(F^\circ_1,F^\circ_2,\psi)\longmapsto\big((T^\circ_{1,1},T^\circ_{2,1},\psi_1),\dots,(T^\circ_{1,m},T^\circ_{2,m},\psi_m)\big)\in\mathrm{Tri}(T_1)\times\cdots\times\mathrm{Tri}(T_m).
--   $$
--
--   This definition gives the $i$-th component of $\Delta_F$.
--
--   **Formalization Note** The component is recorded as the pair $(T^\circ_{1,i},\psi_i)$, with $\psi_i$ a map from the vertices of $T^\circ_{1,i}$ into $V$ (via `extendIso`, $\psi$ extended by the identity). The second piece $T^\circ_{2,i}=\psi_i(T^\circ_{1,i})$ is determined by this pair, so the record carries the same information as the triple and is injective exactly when $\Delta_F$ is. Building $\Delta_F$ with values in $\mathrm{Tri}(T_i)$ itself would put isomorphism proofs into a definition.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, (4.4), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_Tri

namespace PlantedSubgraphLD

/-- The map `ψ : V(F°₁) → V(F°₂)` of a triple, extended by the identity to a map `V → V`. -/
noncomputable def extendIso {V : Type} [Fintype V] [DecidableEq V] {S₁ S₂ : Finset (Sym2 V)}
    (ψ : spanned S₁ ≃g spanned S₂) (v : V) : V :=
  if h : v ∈ (edgeSupp S₁ : Set V) then (ψ ⟨v, h⟩ : V) else v

/-- The `i`-th component of the restriction map `Δ_F` of (4.4).

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, p.18: "let T(F°1) = (T°1,1, …, T°1,m) be
the chosen compatible ordered edge decomposition of F°1. For i = 1, 2, …, m, let
T°2,i := ψ(T°1,i), ψi = ψ|T°1,i. Then (T°1,i, T°2,i, ψi) ∈ Tri(Ti). […]
∆F : Tri(F) → Tri(T1) × ⋯ × Tri(Tm), (F°1, F°2, ψ) ↦ ((T°1,1, T°2,1, ψ1), …, (T°1,m, T°2,m, ψm))."
(4.4)

`dec` is the fixed decomposition of each copy. For a triple `(F°₁, F°₂, ψ)` the `i`-th component
records the piece `T°₁,ᵢ = dec F°₁ i` and the restriction `ψᵢ = ψ|_{V(T°₁,ᵢ)}`.

**Formalization Note** The restriction `ψᵢ` is recorded as a map from the vertices of `T°₁,ᵢ`
into `V`; the second piece `T°₂,ᵢ = ψ(T°₁,ᵢ)` is determined by `T°₁,ᵢ` and `ψᵢ`, so this record
carries the same information as the triple `(T°₁,ᵢ, T°₂,ᵢ, ψᵢ)`, and the record map is injective
exactly when `Δ_F` is. Building `Δ_F` with values in `Tri(Tᵢ)` would need the isomorphism proofs
inside the definition. -/
noncomputable def restrictTriple {V : Type} [Fintype V] [DecidableEq V] {Γ : SimpleGraph V}
    {F : AbsGraph Γ} {m : ℕ} (dec : Copy Γ F → Fin m → Finset (Sym2 V)) (t : Tri Γ F)
    (i : Fin m) : Σ A : Finset (Sym2 V), (↥(edgeSupp A : Set V) → V) :=
  Sigma.mk (dec t.1.1 i) (fun v : (edgeSupp (dec t.1.1 i) : Set V) => extendIso t.2 (v : V))

end PlantedSubgraphLD


