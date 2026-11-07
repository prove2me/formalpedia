-- Prove2me | Definitions.Def_StochAutoreg_isolate
-- name    : StochAutoreg_isolate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:29.90162+00:00
-- url     : https://prove2.me/theorems/27a5d8fe-4e1b-41fb-8f48-3f7ccdbe1c90
-- title:
--   The completion of Lemma 6.1
-- statement:
--   Given a placement $(b_j)_j$ with roots $r_j=b_j1$, a depth $M$ and prescribed laws $\pi_j(z)$ for $|z|<M$, this is the generator with
--
--   $$p_g(r_jz)=\pi_j(z)\ (|z|<M),\qquad p_g(b_j)=0,\qquad p_g(s)=\tfrac12\ \text{at every other state } s.$$
--
--   **Formalization Note** The pair $(j,z)$ is picked by choice; for a placement it is unique.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, Lemma 6.1 (proof), p.12

import Mathlib
import Definitions.Def_StochAutoreg_Generator
import Definitions.Def_StochAutoreg_root
import Definitions.Def_StochAutoreg_clampI

namespace StochAutoreg

/-- The completion of Lemma 6.1's proof: the prescribed law `π j z` at `r_j z` for `|z| < M`, `p_g(b_j) = 0`, and
`p_g(s) = 1/2` at every other state. Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, Lemma 6.1 (proof), p.12.

**Formalization Note.** The pair `(j, z)` with `s = r_j z`, `|z| < M` is picked by choice; for an
`IsPlacement` it is unique (verification file), which is the only case used. -/
noncomputable def isolate {ι : Type} (M : ℕ) (b : ι → List Bool) (π : ι → List Bool → unitInterval) :
    Generator := by
  classical
  exact fun s =>
    if h : ∃ p : ι × List Bool, s = root b p.1 ++ p.2 ∧ p.2.length < M then
      π h.choose.1 h.choose.2
    else if ∃ j, s = b j then 0 else clampI (1 / 2)

end StochAutoreg


