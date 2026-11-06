-- Prove2me | Definitions.Def_PottsRapidMixing_ChainM
-- name    : PottsRapidMixing_ChainM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:40.039552+00:00
-- url     : https://prove2.me/theorems/92f14320-6501-448c-a1d2-2a0c0851e1da
-- title:
--   The chains $M(r)$, $\widetilde M$ and the functionals $W_L$, $\mathcal H_M$, $\mathcal H_{\widetilde M}$
-- statement:
--   For $r\in(0,1]$, one step of $M(r)$ from spins $\sigma$ on $G=(V,E)$ is: (1) independently for each edge $e=xy$, include $e$ in $\omega$ with probability $1-e^{-\beta}$ if $\sigma_x=\sigma_y$; (2) independently include $e$ in $\eta$ with probability $r$, and let $H=\omega\cup\eta$; (3) recolour each component of $(V,H)$ independently from its Potts law at $\tilde\beta(r)=\log(1+(e^\beta-1)/r)$. Write $\mathbb P_{\sigma,M}$ for the law of $H$, $\mathbb P_{\nu,M}=\sum_\sigma\nu(\sigma)\mathbb P_{\sigma,M}$, and $\mu_H$ for the $\tilde\beta$-Potts law on $(V,H)$, so that
--   $$M(\sigma,\tau)=\sum_{H}\mathbb P_{\sigma,M}(H)\,\mu_H(\tau).$$
--   With $U^+(H)$ the union of the components with more than $L$ vertices and $W_L(H)=|U^+(H)|$, the chain $\widetilde M$ of Definition 2.3 keeps the spins on $U^+(H)$ and recolours the other components. The entropy functionals are
--   $$\mathcal H_M(f)=\sum_H\mathbb P_{\mu,M}(H)\,\mathrm{Ent}_{\mu_H}(f),\qquad \mathcal H_{\widetilde M}(f)=\sum_H\mathbb P_{\mu,M}(H)\,\mathbb E_{\mu_H}\bigl[\mathrm{Ent}_{\mu_H}(f\mid\sigma_{U^+(H)})\bigr].$$
--
--   The chain $M(r)$ softens the Swendsen–Wang percolation step while keeping $\mu$ stationary; it interpolates between Swendsen–Wang and direct sampling.
--
--   **Formalization Note** $\mu_H$ factorizes over the components of $H$, so it is the recolouring of step 3, and $\mu_H(\cdot\mid\sigma_{U^+(H)})$ is the recolouring of $\widetilde M$, as p.12 says. A verification file proves (2.2), $\mu(\sigma)\mathbb P_{\sigma,M}(H)=\mathbb P_{\mu,M}(H)\mu_H(\sigma)$, for every graph, that rows of $M$ sum to one, and that $M(1)$ draws from $\mu$. The case $r=0$ (Swendsen–Wang) is not used.
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Definition 1.8, p.7; Definition 2.3, p.10; (2.5), p.11; p.13

import Mathlib
import Definitions.Def_PottsRapidMixing_CondLaw
import Definitions.Def_PottsRapidMixing_PottsLaw
import Definitions.Def_PottsRapidMixing_RandomCluster

open scoped Classical

namespace PottsRapidMixing

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

/-- The probability that an edge `e` belongs to `H = ω ∪ η` in steps 1–2 of `M(r)`, given spins `σ`
(Definition 1.8, Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.7): `ω` contains `e` with
probability `1 − e^{−β}` if `e` is monochromatic and never otherwise, `η` contains `e` with
probability `r`, independently. -/
noncomputable def inclProb (β r : ℝ) (σ : V → Fin q) (e : Sym2 V) : ℝ :=
  1 - (1 - (if ∀ a ∈ e, ∀ b ∈ e, σ a = σ b then 1 - Real.exp (-β) else 0)) * (1 - r)

/-- `P_{σ,M}(H)`: the law of the edge set `H` after steps 1–2 of `M(r)` from `σ`
(arXiv:2610.42059, pp.7, 10). Given `σ` the edges are independent. -/
noncomputable def edgeLaw (G : SimpleGraph V) (β r : ℝ) (σ : V → Fin q) (H : G.edgeSet → Bool) : ℝ :=
  ∏ e : G.edgeSet, if H e = true then inclProb β r σ e.1 else 1 - inclProb β r σ e.1

/-- `P_{ν,M}(H) = ∑_σ ν(σ) P_{σ,M}(H)` (arXiv:2610.42059, p.10). -/
noncomputable def edgeMix (G : SimpleGraph V) (β r : ℝ) (ν : (V → Fin q) → ℝ)
    (H : G.edgeSet → Bool) : ℝ :=
  ∑ σ, ν σ * edgeLaw G β r σ H

/-- `β̃(r) = log(1 + (e^β − 1)/r)` (Definition 1.8, arXiv:2610.42059, p.7), for `r ∈ (0, 1]`. -/
noncomputable def betaTilde (β r : ℝ) : ℝ := Real.log (1 + (Real.exp β - 1) / r)

/-- `µ_H`, the `β̃`-Potts law on `(V, H)` (arXiv:2610.42059, p.10). It is a product over the
components of `H`, so it is the recolouring of step 3 of Definition 1.8. -/
noncomputable def muH (G : SimpleGraph V) (β r : ℝ) (q : ℕ) (H : G.edgeSet → Bool) :
    (V → Fin q) → ℝ :=
  pottsLaw (edgeGraph G H) (betaTilde β r) q

/-- The transition matrix of the chain `M(r)` of Definition 1.8 (arXiv:2610.42059, p.7), for
`r ∈ (0, 1]`: `M(σ, τ) = ∑_H P_{σ,M}(H) µ_H(τ)`. -/
noncomputable def chainM (G : SimpleGraph V) (β : ℝ) (q : ℕ) (r : ℝ) :
    Matrix (V → Fin q) (V → Fin q) ℝ :=
  fun σ τ => ∑ H : G.edgeSet → Bool, edgeLaw G β r σ H * muH G β r q H τ

/-- The vertex sets of the connected components of `K`, `C(K)` (arXiv:2610.42059, p.11). -/
noncomputable def compSets (K : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.image (fun v => Finset.univ.filter (fun w => K.Reachable v w))

/-- `U⁺(K)`, the union of the components of `K` with more than `L` vertices, (2.5)
(arXiv:2610.42059, p.11). `L` is real and the cutoff is strict. -/
noncomputable def Uplus (K : SimpleGraph V) (L : ℝ) : Finset V :=
  ((compSets K).filter (fun U => L < (U.card : ℝ))).biUnion id

/-- `W_L(K) = |U⁺(K)|`, (2.5) (arXiv:2610.42059, p.11). -/
noncomputable def WL (K : SimpleGraph V) (L : ℝ) : ℝ := ((Uplus K L).card : ℝ)

/-- The chain `M̃` of Definition 2.3 (arXiv:2610.42059, p.10): draw `H` from `P_{σ,M}`, keep the
spins on the components of `H` with more than `L` vertices, and recolour every other component from
its `β̃`-Potts law.

**Formalization Note.** `µ_H` is a product over the components of `H`, so independent recolouring of
the other components is the conditional law `µ_H(· | σ_{U⁺(H)})`, as p.12 says. -/
noncomputable def chainMtilde (G : SimpleGraph V) (β : ℝ) (q : ℕ) (r L : ℝ) :
    Matrix (V → Fin q) (V → Fin q) ℝ :=
  fun σ τ => ∑ H : G.edgeSet → Bool,
    edgeLaw G β r σ H * condLaw (muH G β r q H) (Uplus (edgeGraph G H) L) σ τ

/-- `H_M(f) = ∑_H P_{µ,M}(H) Ent_{µ_H}(f)` (arXiv:2610.42059, p.13). -/
noncomputable def entM (G : SimpleGraph V) (β : ℝ) (q : ℕ) (r : ℝ) (f : (V → Fin q) → ℝ) : ℝ :=
  ∑ H : G.edgeSet → Bool, edgeMix G β r (pottsLaw G β q) H *
    GibbsCongestion.entropy (muH G β r q H) f

/-- `H_M̃(f) = ∑_H P_{µ,M}(H) E_{µ_H}[Ent_{µ_H}(f | σ_{U⁺(H)})]` (arXiv:2610.42059, p.13). -/
noncomputable def entMtilde (G : SimpleGraph V) (β : ℝ) (q : ℕ) (r L : ℝ)
    (f : (V → Fin q) → ℝ) : ℝ :=
  ∑ H : G.edgeSet → Bool, edgeMix G β r (pottsLaw G β q) H *
    expCondEnt (muH G β r q H) (Uplus (edgeGraph G H) L) f

end PottsRapidMixing


