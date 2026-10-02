-- Prove2me | Definitions.Def_ProcessingNetworks_TaskAllocation_AmbientChain
-- name    : ProcessingNetworks_TaskAllocation_AmbientChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:40:33.940822+00:00
-- url     : https://prove2.me/theorems/273c8c09-7489-4fc7-9d97-3329fca7d4d8
-- title:
--   The ambient chain (mission I, flat class index) and the per-class delayed random walks
-- statement:
--   The ambient Markov chain $X$ of Section 11.4 — combining the arrivals-regulating Markov chain
--   $Y$ underlying the MArP with each server's queue contents, categories and service phase — is
--   mission I's `MarkovRepresentation` (Assumption 3.1, a continuous-time Markov chain in the sense
--   of Appendix D) for the augmented SPN formulation of Section 11.3, whose $I = LK$ classes
--   $(\ell, k)$ are indexed flatly by `idx ℓ k` (Mathlib's bijection $[L] \times [K] \simeq [LK]$);
--   the model is stable exactly when that chain is positive recurrent (Definition D.15, mission I's
--   `PositiveRecurrent jump rate`). `taTerm`, `taWalk`, `taMax` are the per-class service-time
--   sequence in the order of its index set $\mathcal{L}_{(\ell,k)}$ (residual times of the tasks
--   present at time $0$ first), its delayed random walk $V_{(\ell,k)}(n)$ (6.47) and the maximum
--   of its first $n$ terms, used in the key relationship (6.51) of the standard setup.
--
--   **Formalization note.** Mission I's continuous-time chain and positive-recurrence notion are
--   imported rather than restated (the previous restatement carried only an embedded jump kernel,
--   which cannot express positive recurrence of a continuous-time chain and admitted transient
--   chains). The flat class index is the one arbitrary choice this chunk otherwise avoided; it is
--   confined to the link with the ambient chain, while all fluid-level statements keep the pair
--   indexing $(\ell, k)$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 217-219, Section 11.4, Theorem 11.5; p. 46-47 (mission I, restated)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_Stability_StabilityConditions

namespace ProcessingNetworks.TaskAllocation

/-- The flat index of the class `(ℓ, k)` among the `I = LK` classes of the augmented SPN
formulation (Section 11.3), through Mathlib's bijection `Fin L × Fin K ≃ Fin (L * K)`. The
ambient Markov chain of Section 11.4 is mission I's `MarkovRepresentation` (Assumption 3.1,
Appendix D) for this flat class index, and the model is stable when that chain is positive
recurrent in the sense of Definition D.15 (mission I's `PositiveRecurrent jump rate`). -/
def idx {L K : ℕ} (ℓ : Fin L) (k : Fin K) : Fin (L * K) := finProdFinEquiv (ℓ, k)

/-- The `n`-th service time of a class in the order of its index set `L_{(ℓ,k)}` (Eqs.
(2.1)–(2.2)): the residual service times `Psi n` of the `N0` tasks of the class already present
at time `0` (only the one in service has a genuinely residual time; the others are whole service
times) come first, then the service times `v` of the tasks routed to the class after time `0`. -/
def taTerm {Ω : Type*} (N0 : ℕ) (Psi : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  if n < N0 then Psi n ω else v (n - N0) ω

/-- The delayed random walk of a class (Eq. (6.47)): the sum of its first `n` service times in
the order of `L_{(ℓ,k)}`. -/
noncomputable def taWalk {Ω : Type*} (N0 : ℕ) (Psi : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range n, taTerm N0 Psi v j ω

/-- The largest of the first `n` service times of a class in the order of `L_{(ℓ,k)}` (the
maximum appearing in (6.51)); `0` when `n = 0`. -/
noncomputable def taMax {Ω : Type*} (N0 : ℕ) (Psi : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ⨆ j ∈ Finset.range n, taTerm N0 Psi v j ω

end ProcessingNetworks.TaskAllocation


