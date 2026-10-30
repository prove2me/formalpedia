-- Prove2me | Definitions.Def_OnlineCRS_Combine_combine
-- name    : OnlineCRS_Combine_combine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:17:34.181328+00:00
-- url     : https://prove2.me/theorems/f42b3461-2039-4ddd-ae63-ea0e1d200d46
-- title:
--   Combination of two greedy OCRSs (Definition 2.10)
-- statement:
--   Given greedy OCRSs $\pi^1$ for $\mathcal F_1$ and $\pi^2$ for $\mathcal F_2$, their **combination** $\pi$ is the greedy OCRS for $\mathcal F_1\cap\mathcal F_2$ defined by
--   $$\mathcal F_{\pi,x}=\mathcal F_{\pi^1,x}\cap\mathcal F_{\pi^2,x},$$
--   where $\mathcal F_{\pi^1,x}$ and $\mathcal F_{\pi^2,x}$ are drawn independently from their laws. The intersection of two down-closed subfamilies of $\mathcal F_1$ and $\mathcal F_2$ is a down-closed subfamily of $\mathcal F_1\cap\mathcal F_2$.
--
--   This is the construction behind Theorem 1.9: intersecting the families of two selectable greedy OCRSs gives a selectable greedy OCRS for the intersection of the constraints.
--
--   **Formalization Note** Definition 2.10 does not say how the two random families are coupled; they are drawn independently. Under an arbitrary coupling Lemma 2.11 fails (two $(1,\tfrac12)$-selectable OCRSs on $N=\{e,f\}$ coupled so that the intersection is always $\{\emptyset,\{e\},\{f\}\}$ never select $e$ at $x=(1,1)$). The family is defined for every input $x$. That $P_1\cap P_2$ is a relaxation of $\mathcal F_1\cap\mathcal F_2$ is a separate theorem.
-- source:
--   Feldman, Svensson, Zenklusen, Online Contention Resolution Schemes, arXiv:1508.00142v2, Definition 2.10, p. 15

import Mathlib
import Definitions.Def_OnlineCRS_Combine_DownClosed
import Definitions.Def_OnlineCRS_Combine_GreedyOCRS

namespace OnlineCRS.Combine

/-- **Combination of two greedy OCRSs (Definition 2.10).**
Feldman, Svensson, Zenklusen, *Online Contention Resolution Schemes*, arXiv:1508.00142v2, Definition 2.10, p. 15: "Given two greedy OCRSs `π¹` and `π²` for polytopes `P₁` and `P₂`,
the combination of `π¹` and `π²` is a greedy OCRS `π` for the polytope `P = P₁ ∩ P₂`. For every
input `x ∈ P`, `π` is defined by the down-closed family `F_{π,x} = F_{π¹,x} ∩ F_{π²,x}`."

`combine π₁ π₂` is the greedy OCRS for `F₁ ∩ F₂` whose family at `x` is `G₁ ∩ G₂`, with
`G₁ ∼ π₁.law x` and `G₂ ∼ π₂.law x` drawn independently.

**Formalization Note.** Reading 3: the definition does not say how the two random families are
coupled; they are drawn independently. Under an arbitrary coupling Lemma 2.11 is false
(N = {e, f}, both OCRSs `(1, 1/2)`-selectable, an anti-coupling selects `e` with probability `0`
at `x = (1, 1)`). The family is defined for every `x` (Reading 5). The `law_support` field is
the structural fact that `G₁ ∩ G₂` is a down-closed subfamily of `F₁ ∩ F₂` containing `∅`; that the combination
is a greedy OCRS *for `P₁ ∩ P₂`* (i.e. `P₁ ∩ P₂` is a relaxation of `F₁ ∩ F₂`) is a separate
theorem. -/
noncomputable def combine {N : Type*} [DecidableEq N] {F₁ F₂ : Finset (Finset N)}
    (π₁ : GreedyOCRS F₁) (π₂ : GreedyOCRS F₂) : GreedyOCRS (F₁ ∩ F₂) where
  law x := (π₁.law x).bind fun G₁ => (π₂.law x).map fun G₂ => G₁ ∩ G₂
  law_support x G hG := by
    rw [PMF.mem_support_bind_iff] at hG
    obtain ⟨G₁, h₁, hG⟩ := hG
    rw [PMF.support_map] at hG
    obtain ⟨G₂, h₂, rfl⟩ := hG
    obtain ⟨d₁, e₁, s₁⟩ := π₁.law_support x G₁ h₁
    obtain ⟨d₂, e₂, s₂⟩ := π₂.law_support x G₂ h₂
    refine ⟨fun I hI J hJ => ?_, Finset.mem_inter.mpr ⟨e₁, e₂⟩, Finset.inter_subset_inter s₁ s₂⟩
    rw [Finset.mem_inter] at hI ⊢
    exact ⟨d₁ I hI.1 J hJ, d₂ I hI.2 J hJ⟩

end OnlineCRS.Combine


