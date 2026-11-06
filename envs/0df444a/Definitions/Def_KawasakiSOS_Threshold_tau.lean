-- Prove2me | Definitions.Def_KawasakiSOS_Threshold_tau
-- name    : KawasakiSOS_Threshold_tau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:05:22.210732+00:00
-- url     : https://prove2.me/theorems/74cae92b-16ba-48d0-a33a-4f13b7c32dd5
-- title:
--   The mixing time $\tau(\varepsilon)$ of the lazy Kawasaki chain
-- statement:
--   The chain analyzed is the lazy chain $\hat P=\tfrac12(I+P)$, and $\tau(\varepsilon)$ is its mixing time:
--
--   $$\tau(\varepsilon)=\min\bigl\{t:\ \max_{x\in\Omega}\|\hat P^{\,t}(x,\cdot)-\pi\|_{TV}\le\varepsilon\bigr\}.$$
--
--   **Formalization Note** The source writes only "its mixing time"; this is the standard worst-case total variation mixing time. The value is the infimum of a set of naturals, so it is $0$ if the set were empty; see `mixingSet`.
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_KawasakiSOS_Threshold_Config
import Definitions.Def_KawasakiSOS_Threshold_gibbs
import Definitions.Def_KawasakiSOS_Threshold_kawasaki

namespace KawasakiSOS.Threshold

/-- `τ(ε)`, the mixing time of the lazy chain `½(I + P)`: the least `t` with `max_x ‖P̂^t(x,·) − π‖_TV ≤ ε`. Formalization Note: the paper says only "its mixing time"; this is the standard worst-case total variation time (reading R3).

Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), unnumbered, p. 1 (PDF p. 2). -/
noncomputable def tau (n k : ℕ) [NeZero k] (lam ε : ℝ) : ℕ :=
  MarkovMixing.mixingTime (MarkovMixing.lazy (kawasaki n k lam)) (gibbs n k lam) ε

end KawasakiSOS.Threshold


