-- Prove2me | Definitions.Def_ProcessingNetworks_PacketNetworks_SubcriticalRegion
-- name    : ProcessingNetworks_PacketNetworks_SubcriticalRegion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:46:16.295002+00:00
-- url     : https://prove2.me/theorems/245b6c6b-4ba9-42d2-8948-76b24f274ede
-- title:
--   The schedule/configuration hulls and the subcritical region Λ (Eq. 12.24)
-- statement:
--   $\langle S\rangle$ (resp. $\langle C\rangle$) is the convex hull of the realized schedule
--   (resp. configuration) set in $\mathbb R^J_+$ (resp. $\mathbb R^K_+$). The **subcritical
--   region** (Eq. 12.24), $$\Lambda := \{\lambda\in\mathbb R^I_+ : R\hat s=\lambda \text{ for some
--   }\hat s\in\langle S\rangle \text{ and } \hat c\in\langle C\rangle \text{ with } A\hat s <
--   \hat c\},$$ is this chapter's slotted-time analog of the continuous-time static planning
--   problem's subcritical region.
--
--   **Formalization note.** Named `subcriticalRegion` in the `PacketNetworks` sub-namespace,
--   distinct from mission II's `Subcriticality.subcriticalRegion` — same letter $\Lambda$ in the
--   book, but a genuinely different LP (built from this chapter's own discrete schedule/
--   configuration structure). $\Lambda\subset\mathbb R^I_+$ by definition, so membership carries
--   $\lambda\ge 0$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 232-233, Eq. (12.24)

import Mathlib
import Definitions.Def_ProcessingNetworks_PacketNetworks_PacketNetworkModel
import Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations

namespace ProcessingNetworks.PacketNetworks

/-- The real-vector realization of an integer schedule or configuration. -/
def realize {J : ℕ} (s : Fin J → ℕ) : Fin J → ℝ := fun j => (s j : ℝ)

/-- `⟨S⟩`, the convex hull of a finite schedule (or configuration) set, embedded in `ℝ^J_+`. -/
noncomputable def hullFinset {J : ℕ} (S : Finset (Fin J → ℕ)) : Set (Fin J → ℝ) :=
  convexHull ℝ (realize '' (S : Set (Fin J → ℕ)))

/-- `Λ`, the subcritical region of a packet network (Eq. 12.24): `λ ∈ ℝ^I_+` is subcritical if
there is an activity mix `ŝ ∈ ⟨S⟩` and a configuration mix `ĉ ∈ ⟨C⟩` with `Rŝ = λ` and `Aŝ < ĉ`
(componentwise). Named distinctly from mission II's `Subcriticality.subcriticalRegion` (same
letter `Λ` in the book, but a different LP built from this chapter's own discrete schedule
structure `S`, `A`, `C`, not the continuous-time static planning problem), per this chunk's own
`BRIEF.md` pitfall note. -/
def subcriticalRegion {I J K : ℕ} (dat : PacketNetworkData I J) (S : Finset (Fin J → ℕ))
    (cfg : LinkConfigData J K) : Set (Fin I → ℝ) :=
  {lam | (∀ i, 0 ≤ lam i) ∧ ∃ shat ∈ hullFinset S, ∃ chat ∈ hullFinset cfg.C,
    (R dat).mulVec shat = lam ∧ ∀ k, (cfg.A.mulVec shat) k < chat k}

end ProcessingNetworks.PacketNetworks


