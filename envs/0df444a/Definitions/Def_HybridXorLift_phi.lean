-- Prove2me | Definitions.Def_HybridXorLift_phi
-- name    : HybridXorLift_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:17:42.576115+00:00
-- url     : https://prove2.me/theorems/a759dbd2-babc-434c-8756-ac56e62497f0
-- title:
--   Averaged potential $\Phi^\xi_I(h)$
-- statement:
--   For $J \subseteq [n]$, $\xi \in \{0,1\}^J$ and a nonempty set $I \subseteq \bar J$, the **averaged potential** is
--   $$
--   \Phi^\xi_I(h) = \mathbb E_{\zeta \in \{0,1\}^{\bar I} :\ \zeta_J = \xi}\, \Psi_{I,\zeta}(h).
--   $$
--
--   **Formalization Note** The average is taken over full strings $\zeta$ with $\zeta_J = \xi$; since $\Psi_{I,\zeta}$ reads only $\zeta|_{\bar I}$, each assignment on $\bar I$ is counted exactly $2^{|I|}$ times, so this is the paper's uniform average over $\{0,1\}^{\bar I}$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.3, Eq. (3.11), p.13 (PDF p.15)

import Definitions.Def_HybridXorLift_psi
import Definitions.Def_HybridXorLift_cubeAvg

namespace HybridXorLift

/-- The averaged potential `Φ^ξ_I(h) = E_{ζ ∈ {0,1}^Ī : ζ_J = ξ} Ψ_{I,ζ}(h)` for `J ⊆ [n]`,
`ξ ∈ {0,1}^J` and nonempty `I ⊆ J̄` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.3, Eq. (3.11), p.13 (PDF p.15)).

**Formalization Note** The average is taken over full strings `ζ : Fin n → Bool` with `ζ_J = ξ`.
Since `Ψ_{I,ζ}` reads only `ζ|_Ī`, every assignment `ζ|_Ī` with `ζ_J = ξ` is replicated exactly
`2^{|I|}` times, so this is the paper's uniform average over `{0,1}^Ī`. -/
noncomputable def phi {n r : ℕ} {α : Type} (A : ParallelHybridAlg (Fin n × Fin r) α) (q : ℕ)
    (I J : Finset (Fin n)) (ξ : Fin n → Bool) (h : List (Step (Fin n × Fin r))) : ℝ :=
  cubeAvg J ξ fun ζ => psi A q I ζ h

end HybridXorLift


