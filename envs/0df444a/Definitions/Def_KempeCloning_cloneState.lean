-- Prove2me | Definitions.Def_KempeCloning_cloneState
-- name    : KempeCloning_cloneState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:31.865261+00:00
-- url     : https://prove2.me/theorems/2a533575-8292-418a-ae67-69fcf47bfcc5
-- title:
--   The cloner states $|\mathcal F_l\rangle$ (19)
-- statement:
--   For $m, N, l\in\mathbb N$ with $l\le N$, the state of Eq. (19) is
--
--   $$|\mathcal F_l\rangle := \binom{m+l+1}{l}^{-\frac12}\sum_{i=0}^{l}(-1)^i\sqrt{\binom{m+l-i}{m}}\;\big|(m+l-i)_{a_1}, i_{a_2}, i_{b_1}, (l-i)_{b_2}, (N-l)_c\big\rangle .$$
--
--   Here $l$ is the number of additional photons emitted: $m+l$ photons are in the modes $a_1, a_2$ ($m+l-i$ correct, $i$ wrong), $l$ atoms have decayed to a ground level, and $N-l$ remain excited. The paper shows that the evolved state is a superposition of these states and that each is the output of an optimal $m\to m+l$ cloner.
--
--   **Formalization Note** The power $-\tfrac12$ is the inverse of a real square root. The natural-number differences $m+l-i$, $l-i$, $N-l$ are exact for $i\le l\le N$; the mission uses $|\mathcal F_l\rangle$ only for $l\le N$.
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II C, (19), p.5

import Definitions.Def_KempeCloning_occ
import Definitions.Def_KempeCloning_FockVec

namespace KempeCloning

/-- **The cloner states `|F_l⟩` of (19).**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II C, (19), p.5:
`|F_l⟩ := binom(m+l+1, l)^{−1/2} Σ_{i=0}^{l} (−1)^i √binom(m+l−i, m)
  |(m+l−i)_{a1}, i_{a2}, i_{b1}, (l−i)_{b2}, (N−l)_c⟩`,
"where l denotes the number of additional photons that have been emitted".

**Formalization Note.** The power `−1/2` is `(Real.sqrt _)⁻¹`, cast to `ℂ`. The natural-number
subtractions `m + l − i`, `l − i`, `N − l` are exact for `i ≤ l ≤ N`; the mission's statements only
use `cloneState m N l` with `l ≤ N` (for `l > N` the definition returns a junk vector with `c`
occupation `0`). -/
noncomputable def cloneState (m N l : ℕ) : FockVec :=
  (((Real.sqrt ((m + l + 1).choose l : ℝ))⁻¹ : ℝ) : ℂ) •
    ∑ i ∈ Finset.range (l + 1),
      (((-1 : ℂ) ^ i) * ((Real.sqrt ((m + l - i).choose m : ℝ) : ℝ) : ℂ)) •
        Finsupp.single (occ (m + l - i) i i (l - i) (N - l)) 1

end KempeCloning


