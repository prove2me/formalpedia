-- Prove2me | Definitions.Def_ClusterSim_EdgeCut_TensorNetwork
-- name    : ClusterSim_EdgeCut_TensorNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:26.205766+00:00
-- url     : https://prove2.me/theorems/5d4fc45d-dccd-45d1-8583-f0f350227e5e
-- title:
--   Tensor networks over Π = {0,1}², the single-qubit tensors (5)–(7) and the value T(G, A) of eq. (9) (pp. 7–8)
-- statement:
--   This file fixes the tensor-network model of Supplemental Material §II.
--
--   1. **Edge indices.** Every edge carries an index $\alpha=(\alpha^1,\alpha^2)\in\Pi=\{0,1\}^2$, and $M(\alpha)=|\alpha^1\rangle\langle\alpha^2|$ is the corresponding elementary $2\times 2$ matrix.
--   2. **Single-qubit tensors.** For a state $\rho$, a gate $U$ and an observable $O$ (complex $2\times2$ matrices), with the incoming index on the left and the outgoing one on the right,
--   $$A(\rho)_\alpha=\operatorname{Tr}\big[\rho\,M(\alpha)^\dagger\big],\qquad {}_\alpha A(U)_\beta=\operatorname{Tr}\big[U M(\alpha)U^\dagger M(\beta)^\dagger\big],\qquad {}_\beta A(O)=\operatorname{Tr}\big[M(\beta)\,O\big].$$
--   These are eqs. (5), (6) and (7).
--   3. **Tensor networks.** A tensor network $(G,\mathcal A)$ is a finite directed multigraph $G$ with vertex set $V$ and edge set $E$ (edge $e$ runs from $\mathrm{src}(e)$ to $\mathrm{tgt}(e)$; parallel edges and loops are allowed) together with a complex tensor $\mathcal A(v)$ at every vertex. The tensor of $v$ is evaluated on an edge labelling $\alpha=(\alpha_e)_{e\in E}\in\Pi^E$.
--   4. **Value.** The value of the network is eq. (9),
--   $$T(G,\mathcal A)=\sum_{\alpha\in\Pi^E}\ \prod_{v\in V}\mathcal A(v)_{\alpha(v)}.$$
--
--   The value is the quantity a circuit simulation approximates: by eq. (10) of the paper (cited there from the literature and not formalized here) it equals the expected output $\mathbb E_y f(y)$ of the corresponding quantum-classical algorithm.
--
--   **Formalization Note** $\Pi$ is `Fin 2 × Fin 2` and $M(\alpha)$ is `Matrix.single α.1 α.2 1`. The tensor of $v$ is a function `G.A v : (E → Π) → ℂ` of the whole labelling; the paper's $\mathcal A(v)_{\alpha(v)}$ depends only on the edges incident to $v$, but this locality is not imposed, which makes every statement of the mission about networks slightly more general than the paper's. Vertex types (◁, □, ▷) are not recorded: a ◁ vertex is a vertex without incoming edges.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, pp. 7–8, Supplemental Material §II, eqs. (5)–(7) and (9)

import Mathlib

namespace ClusterSim.EdgeCut

open Matrix

noncomputable section

/-- The index set `Π = {0, 1}²` of a single edge (Supplemental Material §II, p. 7): an index
`α = (α¹, α²)` is a pair of binary indices. -/
abbrev Idx := Fin 2 × Fin 2

/-- The elementary matrix `M(α) = |α¹⟩⟨α²|` of an edge index `α = (α¹, α²)` (p. 8). -/
def M (a : Idx) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.single a.1 a.2 1

/-- Tensor of a single-qubit state `ρ`, eq. (5): `A(ρ)_α = Tr[ρ · M(α)†]`. -/
def stateTensor (ρ : Matrix (Fin 2) (Fin 2) ℂ) (a : Idx) : ℂ := (ρ * (M a)ᴴ).trace

/-- Tensor of a single-qubit gate `U`, eq. (6): `_αA(U)_β = Tr[U M(α) U† · M(β)†]`
(`α` incoming, `β` outgoing). -/
def gateTensor (U : Matrix (Fin 2) (Fin 2) ℂ) (a b : Idx) : ℂ :=
  (U * M a * Uᴴ * (M b)ᴴ).trace

/-- Tensor of a single-qubit observable `O`, eq. (7): `_βA(O) = Tr[M(β) · O]`. -/
def obsTensor (O : Matrix (Fin 2) (Fin 2) ℂ) (b : Idx) : ℂ := (M b * O).trace

/-- A tensor network (Supplemental Material §II, pp. 7–8): a finite directed multigraph with
vertex type `V`, edge type `E`, edge `e` running from `src e` to `tgt e`, and a complex tensor
`A v` at every vertex. Every edge carries an index in `Π = {0,1}²`; the tensor of `v` is read off
a full edge assignment `α : E → Π` (the paper's `A(v)_{α(v)}` is `A v α`, where only the edges
incident to `v` are meant to matter; locality is not imposed). -/
structure TensorNetwork where
  /-- vertices -/
  V : Type
  /-- edges -/
  E : Type
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  [fintypeE : Fintype E]
  [decEqE : DecidableEq E]
  /-- source vertex of an edge -/
  src : E → V
  /-- target vertex of an edge -/
  tgt : E → V
  /-- the tensor of each vertex, as a function of the edge labelling -/
  A : V → (E → Idx) → ℂ

attribute [instance] TensorNetwork.fintypeV TensorNetwork.decEqV TensorNetwork.fintypeE
  TensorNetwork.decEqE

/-- The value of a tensor network, eq. (9): `T(G, A) = Σ_{α ∈ Π^E} Π_{v ∈ V} A(v)_{α(v)}`. -/
def value (G : TensorNetwork) : ℂ := ∑ α : G.E → Idx, ∏ v : G.V, G.A v α

end

end ClusterSim.EdgeCut


