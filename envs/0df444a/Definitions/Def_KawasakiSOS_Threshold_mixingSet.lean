-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_mixingSet
-- name    : KawasakiSOS_Threshold_mixingSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:05:13.296607+00:00
-- url     : https://prove2.me/theorems/657f6d2c-cf6f-4d2a-8a59-db0f59b7424b
-- title:
--   The times with $d(t)\le\varepsilon$ for the lazy chain
-- statement:
--   Writing $\hat P=\tfrac12(I+P)$ for the lazy Kawasaki chain and $d(t)=\max_x\|\hat P^t(x,\cdot)-\pi\|_{TV}$, this is the set of times
--
--   $$\{t\in\mathbb N:\ d(t)\le\varepsilon\}.$$
--
--   **Formalization Note** The mixing time is the least element of this set. Upper bounds on the mixing time in this mission also assert that the set is nonempty, because the infimum of the empty set of naturals is $0$ in Lean.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_gibbs
import Definitions.Def_KawasakiSOS_Threshold_kawasaki

namespace KawasakiSOS.Threshold

/-- The set `{t : d(t) ≤ ε}` of the lazy chain `½(I + P)`. Formalization Note: `tau` is the infimum of this set, and `sInf ∅ = 0` on `ℕ`, so every upper bound on `tau` in this mission also asserts that this set is nonempty.

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
def mixingSet (n k : ℕ) [NeZero k] (lam ε : ℝ) : Set ℕ :=
  {t : ℕ | MarkovMixing.distStationary (MarkovMixing.lazy (kawasaki n k lam)) (gibbs n k lam) t ≤ ε}

end KawasakiSOS.Threshold


