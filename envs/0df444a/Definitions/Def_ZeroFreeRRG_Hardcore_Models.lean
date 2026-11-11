-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_Models
-- name    : ZeroFreeRRG_Hardcore_Models
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:36:25.981527+00:00
-- url     : https://prove2.me/theorems/3da1e429-7127-4262-aa28-f75aca69bb7b
-- title:
--   Hardcore and Potts partition functions on graphs, the α-parametrization λ(α), and the neighbourhood D(S, η)
-- statement:
--   Let $G=(V,E)$ be a finite simple graph. Its **hardcore partition function** at fugacity $\lambda\in\mathbb C$ is $Z_{G,\mathrm{fug}}(\lambda)=\sum_{I}\lambda^{|I|}$, the sum over the independent sets $I$ of $G$. The paper parametrizes the hardcore model by the tree occupation density $\alpha$, through
--   $$\lambda(\alpha)=\frac{\alpha(1-\alpha)^{d-1}}{(1-2\alpha)^{d}},\qquad Z_G(\alpha)=Z_{G,\mathrm{fug}}(\lambda(\alpha)),$$
--   and studies $Z_G$ as a function of complex $\alpha$. The **$q$-state Potts partition function** is $Z_{G,q}(\beta)=\sum_{\sigma:V\to[q]}\beta^{m_G(\sigma)}$, where $m_G(\sigma)$ counts monochromatic edges and $0^0=1$. For a set $S\subseteq\mathbb C$, $D(S,\eta)=\{z:\inf_{w\in S}|z-w|<\eta\}$ is its open $\eta$-neighbourhood. `Model.Zgraph` returns the hardcore $Z_G(\alpha)$ or the Potts $Z_{G,q}(\beta)$ according to the model, and `Model.indepEndpoint` is $\alpha=0$, resp. $\beta=1$.
--
--   These are the functions whose zeros Theorems 1.2 and 5.1 exclude.
--
--   **Formalization Note.** At $\alpha=1/2$, where $\lambda(\alpha)$ is undefined, Lean's $x/0=0$ gives $\lambda(1/2)=0$ and $Z_G(1/2)=1$. `nbhd S η` is written $\{z:\exists w\in S,\ |z-w|<\eta\}$, the same set as the infimum form. `realSegment a b` is the image of $[a,b]$ in $\mathbb C$. Vertex sets are finite types; independent sets are `Finset`s with `SimpleGraph.IsIndepSet`.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 3 (hardcore model, λ(α), Z_G(α), D(S, η)); p. 4 (Potts model); p. 16 (unified notation, nontrivial parameters)

import Mathlib
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels

open scoped Classical

namespace ZeroFreeRRG.Hardcore

/-- The hardcore partition function in fugacity, `Z_{G,fug}(λ) = ∑_{I ∈ 𝓘(G)} λ^{|I|}`, the sum
running over the independent sets `I` of the simple graph `G` (Chen, Wang, Zhang, arXiv:2610.40510,
p. 3). It is evaluated at complex fugacity `λ`. -/
noncomputable def hardcoreZfug {V : Type*} [Fintype V] (G : SimpleGraph V) (lam : ℂ) : ℂ :=
  ∑ I ∈ (Finset.univ : Finset (Finset V)).filter (fun I : Finset V => G.IsIndepSet (↑I : Set V)),
    lam ^ Finset.card I

/-- The fugacity as a function of the tree occupation density,
`λ(α) = α (1 − α)^{d−1} / (1 − 2α)^d` (p. 3), at complex `α`.

**Formalization Note.** At `α = 1/2`, where the source's formula is undefined, Lean's `x / 0 = 0`
gives `λ(1/2) = 0`. -/
noncomputable def lam (d : ℕ) (α : ℂ) : ℂ :=
  α * (1 - α) ^ (d - 1) / (1 - 2 * α) ^ d

/-- The hardcore partition function as a function of the occupation density,
`Z_G(α) = Z_{G,fug}(λ(α))` (p. 3), on a simple graph `G`. The regularity degree `d` enters through
`λ(α)`. -/
noncomputable def hardcoreZ {V : Type*} [Fintype V] (d : ℕ) (G : SimpleGraph V) (α : ℂ) : ℂ :=
  hardcoreZfug G (lam d α)

/-- The number `m_G(σ)` of monochromatic edges of the simple graph `G` under the colouring `σ`
(p. 4). -/
noncomputable def monoEdges {V : Type*} [Fintype V] {q : ℕ} (G : SimpleGraph V) (σ : V → Fin q) :
    ℕ :=
  (G.edgeFinset.filter (fun e => Sym2.lift ⟨fun u v => σ u = σ v, fun _ _ => propext eq_comm⟩ e)).card

/-- The `q`-state Potts partition function `Z_{G,q}(β) = ∑_{σ : V → [q]} β^{m_G(σ)}` (p. 4), at
complex `β`, with `0^0 = 1` (Lean's `0 ^ 0 = 1`). -/
noncomputable def pottsZ {V : Type*} [Fintype V] (q : ℕ) (G : SimpleGraph V) (β : ℂ) : ℂ :=
  ∑ σ : V → Fin q, β ^ monoEdges G σ

/-- The open `η`-neighbourhood `D(S, η) = {z ∈ ℂ : inf_{w ∈ S} |z − w| < η}` of a set `S ⊆ ℂ`
(pp. 3, 17), written as `∃ w ∈ S, |z − w| < η`, which is the same set for every `S` (empty `S`
gives the empty set in both readings: the source's infimum over `∅` is `+∞`). -/
def nbhd (S : Set ℂ) (η : ℝ) : Set ℂ :=
  {z | ∃ w ∈ S, ‖z - w‖ < η}

/-- The real segment `[a, b] ⊆ ℂ`, i.e. `{x : x ∈ ℝ, a ≤ x ≤ b}` viewed in the complex plane. -/
def realSegment (a b : ℝ) : Set ℂ :=
  (fun x : ℝ => (x : ℂ)) '' Set.Icc a b

/-- The (unnormalized) partition function of the model on a simple graph, as a function of the
complex model parameter: the hardcore `Z_G(α) = Z_{G,fug}(λ(α))` (with degree parameter `d` in
`λ(α)`), or the Potts `Z_{G,q}(β)` (§2.4, p. 16: "`Z_G(z)` denotes either partition function"). -/
noncomputable def Model.Zgraph {V : Type*} [Fintype V] : Model → ℕ → SimpleGraph V → ℂ → ℂ
  | .hardcore, d, G, z => hardcoreZ d G z
  | .potts q, _, G, z => pottsZ q G z

/-- The independent-spin endpoint (p. 16): `α = 0` for hardcore, `β = 1` for Potts. -/
def Model.indepEndpoint : Model → ℝ
  | .hardcore => 0
  | .potts _ => 1

end ZeroFreeRRG.Hardcore


