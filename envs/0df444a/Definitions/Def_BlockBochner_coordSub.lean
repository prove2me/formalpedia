-- Prove2me | Definitions.Def_BlockBochner_coordSub
-- name    : BlockBochner_coordSub
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:34.986851+00:00
-- url     : https://prove2.me/theorems/670fddbe-9d98-498b-a95c-f174af0c9abf
-- title:
--   Coordinate subspace $\bigoplus_{i\in J}W_i\subseteq\bigoplus_iW_i$
-- statement:
--   For $J\subseteq[n]$, $\bigoplus_{i\in J}W_i$ is the closed subspace of $H_1=\bigoplus_iW_i$ of tuples $(g_i)$ with $g_i=0$ for $i\notin J$. It is $H^T_1$ for $J=T$, and the block subspaces for $J=T_a$ or $J=R$.
--
--   **Formalization Note** The module records that this subspace is closed, hence complete.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.3, pp.23–25

import Mathlib
import Definitions.Def_BlockBochner_bochD0

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **The coordinate subspace `⊕_{i∈J} W_i ⊆ ⊕_i W_i`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.3, p.23: `H^T_1 = ⊕_{i∈T} W_i`
in the decomposition `H₁ = H^T_1 ⊕ ⊕_{i∈R} W_i`; also the block subspaces `⊕_{i∈T_a} W_i` (p.25) and
`⊕_{i∈R} W_i` (p.24).

**Formalization Note** The tuples `(g_i)` with `g_i = 0` for `i ∉ J`, a closed subspace of `H₁`. -/
def coordSub {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (J : Set (Fin n)) :
    Submodule ℝ (PiLp 2 (fun i => (W i : Submodule ℝ H))) where
  carrier := {g | ∀ i ∉ J, g i = 0}
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by intro c a ha i hi; simp [ha i hi]

/-- The coordinate subspace is closed, hence complete. -/
instance instCompleteSpaceCoordSub {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (J : Set (Fin n)) :
    CompleteSpace (coordSub W J) := by
  have : ((coordSub W J : Submodule ℝ (PiLp 2 (fun i => (W i : Submodule ℝ H)))) :
      Set (PiLp 2 (fun i => (W i : Submodule ℝ H)))) =
      ⋂ i ∈ Jᶜ, {g : PiLp 2 (fun i => (W i : Submodule ℝ H)) | g i = 0} := by
    ext g; simp [coordSub]; rfl
  have hc : IsClosed ((coordSub W J : Submodule ℝ (PiLp 2 (fun i => (W i : Submodule ℝ H)))) :
      Set (PiLp 2 (fun i => (W i : Submodule ℝ H)))) := by
    rw [this]
    exact isClosed_biInter fun i _ =>
      isClosed_eq (PiLp.proj (𝕜 := ℝ) 2 (fun i => (W i : Submodule ℝ H)) i).continuous continuous_const
  exact IsClosed.completeSpace_coe

end BlockBochner


