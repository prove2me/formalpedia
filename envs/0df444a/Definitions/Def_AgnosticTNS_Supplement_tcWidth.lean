-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_tcWidth
-- name    : AgnosticTNS_Supplement_tcWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:37:57.533211+00:00
-- url     : https://prove2.me/theorems/8fabab95-0161-4406-b3bb-6a527770ec7e
-- title:
--   Width of a tree-cut decomposition
-- statement:
--   The **width** of a tree-cut decomposition $(\mathcal T,\mathcal X)$ of $G$ is
--   $$
--   \max_{t\in V(\mathcal T)} \max\{\mathrm{adh}(t),\mathrm{tor}(t)\}.
--   $$
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Definition 6.6, p.49

import Mathlib
import Definitions.Def_AgnosticTNS_Supplement_adh
import Definitions.Def_AgnosticTNS_Supplement_tor

namespace AgnosticTNS.Supplement

/-- **The width of a tree-cut decomposition** `max_{t ∈ V(𝒯)} max{adh(t), tor(t)}`, Definition 6.6,
p.49 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). -/
noncomputable def tcWidth {n : ℕ} (G : SimpleGraph (Fin n)) (D : TreeCutDecomp n) : ℕ :=
  Finset.univ.sup fun t => max (adh G D t) (tor G D t)

end AgnosticTNS.Supplement


