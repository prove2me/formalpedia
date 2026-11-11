-- Prove2me | Definitions.Def_SwapDisk_Main_Regret
-- name    : SwapDisk_Main_Regret
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:16:36.734704+00:00
-- url     : https://prove2.me/theorems/42bc9fb4-7c24-47a6-9b8d-1be2eb88d361
-- title:
--   Realized full swap regret $R_T=\sup_{\phi\text{ Borel}}\sum_t\langle g_t,x_t-\phi(x_t)\rangle$, block regret $R(I)$ and the tag sum $R^{\mathrm{tag}}_T$
-- statement:
--   A realized transcript of horizon $T$ is a sequence $(x_t,g_t)_{t=1}^T$ of played points and loss vectors in $B^2_2$. Let $\Phi$ be the set of **all Borel maps** $\phi:B^2_2\to B^2_2$. The **realized full swap regret** is
--   $$R_T=\sup_{\phi\in\Phi}\sum_{t=1}^T\langle g_t,x_t-\phi(x_t)\rangle ,$$
--   and for a set $I$ of rounds the block regret is $R(I)=\sup_{\phi\in\Phi}\sum_{t\in I}\langle g_t,x_t-\phi(x_t)\rangle$. Every occurrence of the same physical point receives the same replacement.
--
--   For a finite tag set $J$ with attached points $x_j\in B^2_2$ (distinct tags may share a point) and realized tags $J_t$, put $m_j=\sum_t1\{J_t=j\}$, $G_j=\sum_t1\{J_t=j\}g_t$, and define the **tag sum** $R^{\mathrm{tag}}_T=\sum_{j\in J}\psi_{x_j}(G_j)$.
--
--   $R_T$ is the benchmark of the whole mission; the tag sum is the quantity the algorithm controls.
--
--   **Formalization Note.** Rounds are indexed $0,\dots,T-1$. The supremum is the real `⨆` over the subtype `{φ : Disk → Disk // Measurable φ}`: this family is nonempty (the identity) and bounded above by $2T$, so it is the true supremum. $R_T$ is defined as this supremum, not by the regrouping formula (that is Proposition A.1).
-- source:
--   Saravanan, Minimax Realized Full Swap Regret on the Euclidean Disk, STOC 2027 submission (manuscript sha256 e7138cc2…), p. 1 Eq. (1.1), p. 13 Eq. (A.2), p. 14 Eqs. (A.7), (A.8)

import Mathlib
import Definitions.Def_SwapDisk_Main_Geometry

/-!
# Realized full swap regret over Borel deviations, block regret and the tag sum

Saravanan, *Minimax Realized Full Swap Regret on the Euclidean Disk*, STOC 2027 submission
(manuscript sha256 e7138cc2…): p. 1 Eq. (1.1), p. 13 Eq. (A.2), p. 14 Eqs. (A.7), (A.8).

Conventions.
* A realized transcript of horizon `T` is a pair of sequences `x g : Fin T → Disk` (actions and
  loss vectors); rounds are indexed `0, …, T − 1` (the paper's rounds `1, …, T`).
* `Φ` is the set of all Borel maps `ϕ : B²₂ → B²₂`. The regret is the real supremum over the
  subtype `{ϕ // Measurable ϕ}`; this family is nonempty (the identity) and bounded above by
  `2T`, so the real `⨆` is the true supremum (never a junk value). It is defined as this
  supremum, not by the regrouping formula (that is Proposition A.1).
* A tag assignment is `tag : Fin T → J` for a finite tag set `J` with attached points
  `pt : J → Disk`; distinct tags may carry the same physical point.
-/

open MeasureTheory

namespace SwapDisk.Main

/-- The gain `∑_{t ∈ I} ⟨g_t, x_t − ϕ(x_t)⟩` of a deviation `ϕ` on a set `I` of rounds. -/
noncomputable def gain {T : ℕ} (x g : Fin T → Disk) (I : Finset (Fin T)) (φ : Disk → Disk) : ℝ :=
  ∑ t ∈ I, ip (g t : E2) ((x t : E2) - (φ (x t) : E2))

/-- Block regret `R(I) = sup_{ϕ ∈ Φ} ∑_{t ∈ I} ⟨g_t, x_t − ϕ(x_t)⟩`, `Φ` = all Borel maps
`B²₂ → B²₂` (Eq. (A.8)). -/
noncomputable def blockRegret {T : ℕ} (x g : Fin T → Disk) (I : Finset (Fin T)) : ℝ :=
  ⨆ φ : {φ : Disk → Disk // Measurable φ}, gain x g I φ.1

/-- Realized full swap regret `R_T = sup_{ϕ ∈ Φ} ∑_{t=1}^T ⟨g_t, x_t − ϕ(x_t)⟩` (Eqs. (1.1),
(A.2)). -/
noncomputable def swapRegret {T : ℕ} (x g : Fin T → Disk) : ℝ :=
  blockRegret x g Finset.univ

/-- The tag count `m_j = ∑_t 1{J_t = j}`. -/
def tagCount {T : ℕ} {J : Type*} [DecidableEq J] (tag : Fin T → J) (j : J) : ℕ :=
  (Finset.univ.filter (fun t => tag t = j)).card

/-- The tag loss sum `G_j = ∑_t 1{J_t = j} g_t`. -/
noncomputable def tagLoss {T : ℕ} {J : Type*} [DecidableEq J] (tag : Fin T → J)
    (g : Fin T → Disk) (j : J) : E2 :=
  ∑ t ∈ Finset.univ.filter (fun t => tag t = j), (g t : E2)

/-- The tag sum `R^tag_T = ∑_{j ∈ J} ψ_{x_j}(G_j)` (Eq. (A.7)). -/
noncomputable def tagSum {T : ℕ} {J : Type*} [Fintype J] [DecidableEq J] (pt : J → Disk)
    (tag : Fin T → J) (g : Fin T → Disk) : ℝ :=
  ∑ j, psi (pt j : E2) (tagLoss tag g j)

end SwapDisk.Main


