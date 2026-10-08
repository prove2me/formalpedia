-- Prove2me | Definitions.Def_NashWilliams61_TreePacking_Fusions
-- name    : NashWilliams61_TreePacking_Fusions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:08.253135+00:00
-- url     : https://prove2.me/theorems/28d045ec-40cf-4e74-913e-91505d37028f
-- title:
--   Fusions $\Phi$ at a vertex $\xi$, the graph $\Phi G$ and the subgraph $\Phi^{-1}H$ (p. 447)
-- statement:
--   Let $G$ be a graph with vertex set $V$ and edge set $F$.
--
--   1. **Fusion.** If $\xi, \eta, \zeta$ are distinct vertices and $\lambda, \mu$ are edges of $G$ joining $\xi$ to $\eta$ and to $\zeta$ respectively, the operation $\Phi$ that removes $\lambda$ and $\mu$ and inserts a new edge $\rho = \rho(\Phi)$ joining $\eta$ and $\zeta$ is a *fusion at $\xi$*; the resulting graph is $\Phi G$, with edge set $(F \setminus \{\lambda, \mu\}) \cup \{\rho\}$ and the same vertices.
--   2. **Inverse image.** For a subgraph $H$ of $\Phi G$, $\Phi^{-1}H$ is $H$ if $\rho \notin E(H)$, and otherwise the subgraph with
--   $$V(\Phi^{-1}H) = V(H) \cup \{\xi\}, \qquad E(\Phi^{-1}H) = (E(H) \setminus \{\rho\}) \cup \{\lambda, \mu\}.$$
--   3. **Sequences.** For fusions $\Phi_1, \dots, \Phi_n$, the graph $L = \Phi_1 \cdots \Phi_n G$ is obtained by applying $\Phi_n$ first; each $\Phi_i$ must be a fusion of the graph $\Phi_{i+1} \cdots \Phi_n G$. For a subgraph $T$ of $L$, $\Phi_n^{-1} \cdots \Phi_1^{-1} T$ applies $\Phi_1^{-1}$ first.
--
--   Fusions model the splitting-off of pairs of edges at a vertex, which the closing argument of the paper uses to return from the supergraph of Corollary 3A to $G$.
--
--   **Formalization Note** Edges live in an ambient type `E`; the graph is $(V, F)$ for `F : Finset E`, and the new edge $\rho$ is a given element of `E` that is not in the current edge set and joins $\eta, \zeta$. A sequence of fusions is a list `[Φ₁, …, Φₙ]`; its validity condition requires each $\Phi_i$ to be a fusion of the graph produced by $\Phi_{i+1}, \dots, \Phi_n$, which also forces the new edges to be distinct and outside $F$.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 447, Definitions (fusion at ξ, ΦG, ρ(Φ), Φ⁻¹H)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph

namespace NashWilliams61.TreePacking

/-! Fusions `Φ` at a vertex `ξ`, the graph `ΦG`, the subgraph `Φ⁻¹H`, and finite sequences of
fusions (Nash-Williams 1961, p. 447).

The edges live in an ambient type `E` with `ends : E → Sym2 V`; the graph `G` is `(V, F)` for
an edge set `F : Finset E`, and the new edge `ρ` of a fusion is a given element of `E` outside
the current edge set. A subgraph is a pair `(W, F_H) : Finset V × Finset E`. -/

variable {V E : Type*}

/-- The data of a fusion at `xi`: the edges `lam` (`λ`) and `mu` (`μ`) to be removed, the
new edge `rho` (`ρ`), and the other ends `eta` (`η`) of `λ` and `zeta` (`ζ`) of `μ`. -/
structure Fusion (V E : Type*) where
  xi : V
  eta : V
  zeta : V
  lam : E
  mu : E
  rho : E

/-- `φ` is a fusion at `φ.xi` of the graph `(V, F)`: `ξ, η, ζ` are distinct vertices, `λ` and
`μ` are edges of `F` joining `ξ` to `η` and to `ζ` respectively, and the new edge `ρ` is not
in `F` and joins `η` and `ζ`. -/
def Fusion.IsValid (ends : E → Sym2 V) (F : Finset E) (φ : Fusion V E) : Prop :=
  φ.xi ≠ φ.eta ∧ φ.xi ≠ φ.zeta ∧ φ.eta ≠ φ.zeta ∧
    φ.lam ∈ F ∧ φ.mu ∈ F ∧ ends φ.lam = s(φ.xi, φ.eta) ∧ ends φ.mu = s(φ.xi, φ.zeta) ∧
    φ.rho ∉ F ∧ ends φ.rho = s(φ.eta, φ.zeta)

/-- The edge set of `ΦG`: remove `λ` and `μ`, insert `ρ`. -/
def Fusion.apply [DecidableEq E] (φ : Fusion V E) (F : Finset E) : Finset E :=
  insert φ.rho ((F.erase φ.lam).erase φ.mu)

/-- `Φ⁻¹H` for a subgraph `H = (W, F_H)` of `ΦG`: `H` itself if `ρ ∉ E(H)`; otherwise
`V(Φ⁻¹H) = V(H) ∪ {ξ}` and `E(Φ⁻¹H) = (E(H) − {ρ}) ∪ {λ, μ}`. -/
def Fusion.inv [DecidableEq V] [DecidableEq E] (φ : Fusion V E) (H : Finset V × Finset E) :
    Finset V × Finset E :=
  if φ.rho ∈ H.2 then (insert φ.xi H.1, insert φ.lam (insert φ.mu (H.2.erase φ.rho))) else H

/-- For the list `[Φ₁, …, Φₙ]`, the edge set of `Φ₁ … Φₙ G` (`Φₙ` is applied first). -/
def applyList [DecidableEq E] : List (Fusion V E) → Finset E → Finset E
  | [], F => F
  | φ :: rest, F => φ.apply (applyList rest F)

/-- The list `[Φ₁, …, Φₙ]` is a sequence of fusions of `(V, F)`: `Φₙ` is a fusion of `G`, and
each `Φᵢ` is a fusion of the graph `Φᵢ₊₁ … Φₙ G` produced by the later ones. -/
def ValidList [DecidableEq E] (ends : E → Sym2 V) : List (Fusion V E) → Finset E → Prop
  | [], _ => True
  | φ :: rest, F => ValidList ends rest F ∧ φ.IsValid ends (applyList rest F)

/-- For the list `[Φ₁, …, Φₙ]`, the subgraph `Φₙ⁻¹ … Φ₁⁻¹ H` (`Φ₁⁻¹` is applied first). -/
def invList [DecidableEq V] [DecidableEq E] :
    List (Fusion V E) → Finset V × Finset E → Finset V × Finset E
  | [], H => H
  | φ :: rest, H => invList rest (φ.inv H)

end NashWilliams61.TreePacking


