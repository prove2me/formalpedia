-- Prove2me | Definitions.Def_SybilClinch_outsiderPhi
-- name    : SybilClinch_outsiderPhi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:44.604206+00:00
-- url     : https://prove2.me/theorems/295bd5fd-2622-40bc-99fb-61ec1c657e3c
-- title:
--   Outsider budget function $\Phi_p(t)$
-- statement:
--   For a set $N$ of outside identities and a clock price $p$,
--   $$\Phi_p(t):=\sum_{j\in N:\ v_j>p}\min\{q_j,t\}.$$
--   It is nondecreasing in $t$; by (40) it gives the outsiders' total effective budget at water level $t$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Lemma 4.17, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_SybilClinch_OneSidedProfile

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §4.6, Lemma 4.17, printed p.23 (PDF p.25): `Φ_p(t) := Σ_{j ∈ N : vⱼ > p} min{qⱼ, t}`. -/
noncomputable def outsiderPhi (P : OneSidedProfile) (N : Finset ℕ) (p t : ℝ) : ℝ :=
  ∑ j ∈ N.filter (fun j => (p : WithTop ℝ) < P.v j), min (P.q j) t

end SybilClinch


