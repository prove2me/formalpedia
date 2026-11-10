-- Prove2me | Definitions.Def_QPSpinProfile_coverNum
-- name    : QPSpinProfile_coverNum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:48.519992+00:00
-- url     : https://prove2.me/theorems/f91f7a91-22ad-4f69-a4a2-cb5892637e5d
-- title:
--   Covering number $N(\varepsilon, A, \|\cdot\|_{n,p})$ in the canonical norm
-- statement:
--   For a set $A$ of functions $\mathcal P_{n,p}\to\mathbb R$ and $\varepsilon>0$, the **covering number** $N(\varepsilon,A,\|\cdot\|_{n,p})$ is the smallest number of closed $\|\cdot\|_{n,p}$-balls of radius $\varepsilon$ whose union contains $A$; the centres may lie anywhere in the ambient space $\mathbb R^{\mathcal P_{n,p}}$. The **metric entropy** of $A$ at scale $\varepsilon$ is $\log N(\varepsilon,A,\|\cdot\|_{n,p})$.
--
--   Applied to a profile class $F_{n,p}(\mathcal C_n)$, its growth in $\varepsilon$ is the *profile complexity* that governs Theorem 1.2.
--
--   **Formalization Note** The value lies in $\mathbb N\cup\{\infty\}$: it is the infimum of the cardinalities of finite sets of centres that cover $A$, and $\infty$ if there is none.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §1.2, p.4 (PDF p.7)

import Mathlib
import Definitions.Def_QPSpinProfile_profile

namespace QPSpinProfile

/-- The covering number `N(ε, A, ‖·‖_{n,p})` of a set `A` of functions `𝒫_{n,p} → ℝ` in the
canonical norm (arXiv:2610.02166, held version sha256 a0a1ec89…, §1.2, p.4, PDF p.7): the smallest
number of closed `‖·‖_{n,p}`-balls of radius `ε` whose union contains `A`, the centres lying
anywhere in the ambient space `ℝ^{𝒫_{n,p}}`.

**Formalization Note** Valued in `ℕ∞`: the infimum over all finite sets of centres covering `A`
is `⊤` when no finite cover exists, never a junk `0`. -/
noncomputable def coverNum {n p : ℕ} (ε : ℝ) (A : Set (PauliString n p → ℝ)) : ℕ∞ :=
  ⨅ (s : Finset (PauliString n p → ℝ))
    (_ : A ⊆ ⋃ c ∈ s, {f | profileNorm (f - c) ≤ ε}), (s.card : ℕ∞)

end QPSpinProfile


