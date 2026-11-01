-- Prove2me | Definitions.Def_ToricMemory_probSAP
-- name    : ToricMemory_probSAP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:41.910508+00:00
-- url     : https://prove2.me/theorems/66c66180-9188-43cc-bb10-888e3cf58fcd
-- title:
--   $\mathrm{Prob}_{\rm SAP}(H,V)$: probability that $E+E_{\min}$ contains a polygon with $(H,V)$ links
-- statement:
--   Let $D$ be a decoder and $E$ the error history drawn from $\mu_{p,q}$, and $E_{\min}=D(\partial E)$. $\mathrm{Prob}_{\rm SAP}(H,V)$ is the probability that $E+E_{\min}$ contains the link set of some rooted self-avoiding polygon on the torus, at any starting site, with $H$ horizontal and $V$ vertical links.
--
--   This is the quantity bounded in (54) and summed in (55).
-- source:
--   Dennis, Kitaev, Landahl & Preskill, Topological quantum memory, arXiv:quant-ph/0110143v1, Sec. V B, eq. (54), p. 19

import Mathlib
import Definitions.Def_ToricMemory_Lattice
import Definitions.Def_ToricMemory_TorusSAP

open Finset

namespace ToricMemory

open Classical in
/-- `Prob_SAP(H, V)` of Dennis–Kitaev–Landahl–Preskill, arXiv:quant-ph/0110143v1, Sec. V B,
p. 19: the probability that `E + E_min` contains any self-avoiding polygon with `H` horizontal and
`V` vertical links. Here `E` is drawn from `chainProb p q`, `E_min = D(∂E)`, and "contains" means
that the link set of some rooted self-avoiding polygon on the torus (at any starting site) with
`H` horizontal and `V` vertical links lies in `E + E_min`. -/
noncomputable def probSAP {L T : ℕ} [NeZero L] [NeZero T] (p q : ℝ)
    (D : Finset (Site L T) → Finset (Link L T)) (H V : ℕ) : ℝ :=
  ∑ E : Finset (Link L T),
    if ∃ (s : Site L T) (w : Fin (H + V) → Link L T × Bool), IsTorusSAP s w ∧
        (univ.filter fun i => IsHorizontal (w i).1).card = H ∧
        linkSet w ⊆ symmDiff E (D (boundary E))
    then chainProb p q E else 0

end ToricMemory


