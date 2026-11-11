-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel
-- name    : ZeroFreeRRG_Hardcore_ConfigModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:36:45.919701+00:00
-- url     : https://prove2.me/theorems/be2b34cf-92fc-4ea2-8f2f-e2c58a8c49e7
-- title:
--   Normalized partition function on configuration-model multigraphs, its first moment a_n, short-cycle counts X_{ℓ,n}, Poisson means λ_ℓ and cycle factors δ_ℓ
-- statement:
--   In the configuration model $\mathrm{CM}_{n,d}$ each of $n$ vertices carries $d$ half-edges and a uniform perfect matching of the $dn$ half-edges is drawn; each matched pair is an edge, so self-loops and parallel edges occur. On such a multigraph the **normalized partition function** (Definition 2.4) is
--   $$\mathcal Z_G(z)=\sum_{\sigma:V\to\Omega}\prod_{v\in V}\pi_{\sigma_v}(z)\prod_{uv\in E(G)}M_{\sigma_u\sigma_v}(z),$$
--   the product over $E(G)$ running over edge occurrences (a self-loop at $v$ contributes $M_{\sigma_v\sigma_v}$; for hardcore it forbids $v$), and $a_n(z)=\mathbb E_{\mathrm{CM}_{n,d}}[\mathcal Z_G(z)]$ is its first moment. For $\ell\ge1$, $X_{\ell,n}$ is the number of $\ell$-cycles of the multigraph (self-loops for $\ell=1$, pairs of parallel edges for $\ell=2$), and (Definition 3.1)
--   $$\lambda_\ell=\frac{(d-1)^\ell}{2\ell},\qquad \delta_\ell(z)=\sum_{a_1,\dots,a_\ell\in\Omega}\prod_{r=1}^{\ell}\pi_{a_r}(z)M_{a_r a_{r+1}}(z)-1\quad(a_{\ell+1}=a_1).$$
--   These are the quantities of the small subgraph conditioning argument. A **graph event** is an event that depends only on the multigraph $G$, not on which labelled half-edges were matched to form it (used in Lemma 4.21).
--
--   **Formalization Note.** The multigraph is a pairing `M : AFIsingKS.Matching n d` (published). The product over edges takes, from each matched pair $\{x,Mx\}$, the half-edge with the smaller code $v\cdot d+i$. An $\ell$-cycle is counted through its closed walks: sequences of outgoing half-edges $x_1,\dots,x_\ell$ at $\ell$ distinct vertices with $Mx_i$ at the vertex of $x_{i+1}$ and $Mx_i\neq x_{i+1}$; every $\ell$-cycle has exactly $2\ell$ of them ($\ell$ starting points, two directions; for $\ell=2$, two starting vertices times two orders of the parallel edges), so `cycleCount` divides by $2\ell$. `weight`, `normZ` and `an` are defined over any field ($\mathbb R$ or $\mathbb C$).
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 15, Definitions 2.1 and 2.4 and the multigraph convention; p. 18, Definition 3.1

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels

open scoped Classical

namespace ZeroFreeRRG.Hardcore

open AFIsingKS

/-- A numbering of the half-edges `(v, i) ∈ [n] × [d]`, `(v, i) ↦ v·d + i`; injective. It only
serves to pick one half-edge of each matched pair. -/
def halfEdgeCode {n d : ℕ} (x : Fin n × Fin d) : ℕ := (x.1 : ℕ) * d + x.2

/-- One half-edge `x` of each edge `{x, M x}` of the configuration-model multigraph `M` (the one with
the smaller code). These are in bijection with the edge occurrences `E(G)` of the multigraph,
self-loops and parallel edges included (Definition 2.1). -/
noncomputable def edgeReps {n d : ℕ} (M : Matching n d) : Finset (Fin n × Fin d) :=
  Finset.univ.filter (fun x => halfEdgeCode x < halfEdgeCode (M.1 x))

/-- The weight `∏_v π_{σ_v}(z) ∏_{uv ∈ E(G)} M_{σ_u σ_v}(z)` of a spin assignment `σ` on the
configuration-model multigraph `M` (Definition 2.4, p. 15). The product over `E(G)` runs over edge
occurrences: a self-loop at `v` contributes `M_{σ_v σ_v}`, and parallel edges contribute once each. -/
noncomputable def weight {𝕜 : Type*} [Field 𝕜] (m : Model) (z : 𝕜) {n d : ℕ} (M : Matching n d)
    (σ : Fin n → m.Spin) : 𝕜 :=
  (∏ v, m.pi z (σ v)) * ∏ x ∈ edgeReps M, m.M z (σ x.1) (σ (M.1 x).1)

/-- The normalized partition function `𝒵_G(z) = ∑_σ ∏_v π_{σ_v}(z) ∏_{uv ∈ E(G)} M_{σ_u σ_v}(z)`
(Definition 2.4, p. 15) of the configuration-model multigraph `M`, over `𝕜 = ℝ` or `ℂ`. -/
noncomputable def normZ {𝕜 : Type*} [Field 𝕜] (m : Model) (z : 𝕜) {n d : ℕ} (M : Matching n d) :
    𝕜 :=
  ∑ σ : Fin n → m.Spin, weight m z M σ

/-- The configuration-model first moment `a_n(z) = E_{CM_{n,d}}[𝒵_G(z)]` (Definition 2.4). -/
noncomputable def an {𝕜 : Type*} [Field 𝕜] (m : Model) (d n : ℕ) (z : 𝕜) : 𝕜 :=
  cmE (fun M : Matching n d => normZ m z M)

/-- The multigraph `G` induced by the pairing `M` (Definition 2.1): the multiset of its edge
occurrences `{u, v}`, one per matched pair (a self-loop at `v` is `{v, v}`). -/
noncomputable def multigraph {n d : ℕ} (M : Matching n d) : Multiset (Sym2 (Fin n)) :=
  (edgeReps M).val.map (fun x : Fin n × Fin d => (s(x.1, (M.1 x).1) : Sym2 (Fin n)))

/-- A graph event of the configuration model (Lemma 4.21, p. 32): a set of pairings that depends
only on the induced multigraph `G`, not on the labels of the half-edges. -/
def IsGraphEvent {n d : ℕ} (E : Set (Matching n d)) : Prop :=
  ∀ M M' : Matching n d, multigraph M = multigraph M' → (M ∈ E ↔ M' ∈ E)

/-- The closed walks `v_1 → v_2 → ⋯ → v_ℓ → v_1` through `ℓ` distinct vertices along `ℓ` distinct
edges of the multigraph `M`, recorded by their outgoing half-edges `x_i` (at `v_i`), with
`M x_i` at `v_{i+1}` and `M x_i ≠ x_{i+1}` (the next edge differs from the previous one; this
matters only for `ℓ = 2`). Each `ℓ`-cycle is traversed by exactly `2ℓ` of them. -/
noncomputable def cycleWalks {n d : ℕ} (M : Matching n d) (ℓ : ℕ) : Finset (Fin ℓ → Fin n × Fin d) :=
  Finset.univ.filter (fun x => Function.Injective (fun i => (x i).1) ∧
    ∀ i, (M.1 (x i)).1 = (x (finRotate ℓ i)).1 ∧ M.1 (x i) ≠ x (finRotate ℓ i))

/-- The number `X_{ℓ,n}` of `ℓ`-cycles of the `d`-regular multigraph `M` on `[n]` (Definition 3.1,
p. 18): self-loops for `ℓ = 1`, pairs of parallel edges for `ℓ = 2`, ordinary cycles for `ℓ ≥ 3`.
It is the number of cycle walks divided by `2ℓ` (the division is exact for `ℓ ≥ 1`). -/
noncomputable def cycleCount {n d : ℕ} (M : Matching n d) (ℓ : ℕ) : ℕ :=
  (cycleWalks M ℓ).card / (2 * ℓ)

/-- The Poisson means `λ_ℓ = (d − 1)^ℓ / (2ℓ)` (Definition 3.1). -/
noncomputable def lamCyc (d ℓ : ℕ) : ℝ := ((d : ℝ) - 1) ^ ℓ / (2 * ℓ)

/-- The short-cycle factors (Definition 3.1):
`δ_ℓ(z) = 𝒵_{C_ℓ}(z) − 1 = ∑_{a_1,…,a_ℓ ∈ Ω} ∏_{r=1}^ℓ π_{a_r}(z) M_{a_r, a_{r+1}}(z) − 1`
(`a_{ℓ+1} = a_1`). -/
noncomputable def deltaCyc (m : Model) (ℓ : ℕ) (z : ℂ) : ℂ :=
  (∑ a : Fin ℓ → m.Spin, ∏ r, m.pi z (a r) * m.M z (a r) (a (finRotate ℓ r))) - 1

end ZeroFreeRRG.Hardcore


