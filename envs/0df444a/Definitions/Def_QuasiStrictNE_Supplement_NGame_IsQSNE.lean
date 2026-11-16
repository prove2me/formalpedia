-- Prove2me | Definitions.Def_QuasiStrictNE_Supplement_NGame_IsQSNE
-- name    : QuasiStrictNE_Supplement_NGame_IsQSNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:40:34.355209+00:00
-- url     : https://prove2.me/theorems/9300b1a1-0ba5-4b35-8fe3-3efa6bea2d39
-- title:
--   Quasi-strict Nash equilibrium of an $n$-player game
-- statement:
--   A profile $\nu = (\nu_0,\dots,\nu_{n-1})$ is a **quasi-strict Nash equilibrium** of the $n$-player game $G$ if every $\nu_i$ is a mixed strategy, $\nu_i \in \Delta_{k_i}$, and for every player $i$
--
--   $$
--   \operatorname{supp}(\nu_i) = BR_i(\nu_{-i}).
--   $$
--
--   The inclusion $\subseteq$ is the Nash condition. The reverse inclusion says that every best response is played with positive probability.
--
--   This is Definition 1 in the $n$-player form used in §5, where the proof of Theorem 2 checks $BR_1(\nu_{-1}) = \operatorname{supp}(\nu_1)$, $BR_2(\nu_{-2}) = \operatorname{supp}(\nu_2)$ and $BR_3(\nu_{-3}) = \operatorname{supp}(\nu_3)$.
--
--   **Formalization Note** $\Delta_k$ is `stdSimplex ℝ (Fin k)` and $\operatorname{supp}$ is the base `QuasiStrictNE.supp`. For $n = 2$ the definition coincides with the base bimatrix `QuasiStrictNE.IsQSNE` (proved in the chunk's verification file).
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 1, p.4; proof of Theorem 2, pp.19–20

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_Supplement_NGame_BR

set_option autoImplicit false

namespace QuasiStrictNE.Supplement

/-- **Quasi-strict Nash equilibrium of an `n`-player game** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 1, p.4, in the
`n`-player form used in §5, pp.19–20: "(ν1, ν2, ν3) is a quasi-strict Nash equilibrium of Ĝ, for
BR1(ν−1) = supp(ν1), BR2(ν−2) = supp(ν2), BR3(ν−3) = supp(ν3)").

`G.IsQSNE ν` holds iff every `ν i` is a mixed strategy (a point of `Δ_{k i}`) and, for every player
`i`, the support of `ν i` equals the set of pure best responses of `i` to `ν_{−i}`. This contains the
Nash condition `supp(νᵢ) ⊆ BRᵢ(ν₋ᵢ)`.

**Formalization Note** `Δ_k` is `stdSimplex ℝ (Fin k)` and `supp` is the base `QuasiStrictNE.supp`.
For `n = 2` this is the base `QuasiStrictNE.IsQSNE` with `A = u 0`, `B = u 1` read as matrices. -/
def NGame.IsQSNE {n : ℕ} (G : NGame n) (ν : (j : Fin n) → Fin (G.k j) → ℝ) : Prop :=
  ∀ i : Fin n, ν i ∈ stdSimplex ℝ (Fin (G.k i)) ∧ QuasiStrictNE.supp (ν i) = G.BR ν i

end QuasiStrictNE.Supplement


