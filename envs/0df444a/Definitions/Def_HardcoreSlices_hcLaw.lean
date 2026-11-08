-- Prove2me | Definitions.Def_HardcoreSlices_hcLaw
-- name    : HardcoreSlices_hcLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:06.612838+00:00
-- url     : https://prove2.me/theorems/a62c0631-ebb7-4110-8e82-583004a94fcf
-- title:
--   The hardcore law $\mu_\lambda$ on vertex sets
-- statement:
--   Let $G$ be a graph on $X\sqcup Y$ and $\lambda>0$. The **hardcore model** is the distribution on independent sets of $G$ with
--   $$\mu_\lambda(I)=\frac{\lambda^{|I|}}{Z_G(\lambda)},\qquad Z_G(\lambda)=\sum_{I\in\mathcal I(G)}\lambda^{|I|}.$$
--   It is the target of the mission's sampler, and $Z_G(\lambda)$ the target of its counter.
--
--   **Formalization Note** The partition function is the published `hardcoreZ`. The law is defined on all vertex sets, with value $0$ off the independent sets. `hcLawOnBits` reads it on sets of machine indices through the numbering `LowTempGlauber.vIdx`, the output alphabet of the sampler.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), §1, p.1

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting
import Definitions.Def_LowTempGlauber_SamplerInput

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **The hardcore model.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), §1, p.1: "`µλ(I) = λ^{|I|} / ZG(λ)`. We call
`ZG(λ) = Σ_{I∈I(G)} λ^{|I|}` the partition function."

**Formalization Note.** The partition function is the published `hardcoreZ`. The law is a function on
all vertex sets, and `0` off the independent sets. -/
noncomputable def hcLaw {m : ℕ} (G : SimpleGraph (Vertex m)) (lam : ℝ) (I : Finset (Vertex m)) : ℝ :=
  if IsIndependent G I then lam ^ I.card / hardcoreZ G lam else 0

/-- The vertex set numbered by a set of machine indices (`LowTempGlauber.vIdx`). -/
def ofBits {m : ℕ} (S : Finset (Fin (m + m))) : Finset (Vertex m) :=
  S.map (LowTempGlauber.vIdx m).symm.toEmbedding

/-- The machine indices of a vertex set (`LowTempGlauber.vIdx`). -/
def toBits {m : ℕ} (S : Finset (Vertex m)) : Finset (Fin (m + m)) :=
  S.map (LowTempGlauber.vIdx m).toEmbedding

/-- The hardcore law read on sets of machine indices, the output alphabet of the sampler. -/
noncomputable def hcLawOnBits {m : ℕ} (G : SimpleGraph (Vertex m)) (lam : ℝ)
    (S : Finset (Fin (m + m))) : ℝ :=
  hcLaw G lam (ofBits S)

end HardcoreSlices


