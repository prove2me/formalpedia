-- Prove2me | Definitions.Def_SybilClinch_Supplement_fixedMech
-- name    : SybilClinch_Supplement_fixedMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:15:16.362198+00:00
-- url     : https://prove2.me/theorems/efbb4d15-81a4-44b3-a2b4-cf808bc414b2
-- title:
--   Constant-target specification for a fixed divisible supply
-- statement:
--   Fix a divisible supply $s>0$ and a positive initial clock price $p_\star$. The **constant-target specification** has target
--
--   $$
--   T_s^{\mathrm{fix}}(p,X,Y)=s
--   $$
--
--   on the state domain $D_s^{\mathrm{fix}}=\{(p,X,Y):p\ge p_\star,\ 0\le X\le s,\ Y\ge0\}$ and has capacity $s$. Its residual supply $s-X$ is exactly the unallocated supply of the classical adaptive clinching auction.
--
--   **Formalization Note** The paper's trivial environment description is omitted, as in the published `TargetMech` encoding; the target and state domain contain all remaining data. Capacity is represented in `EReal`, although here it is the finite value $s$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), Appendix B.1, Definition B.1, printed p.45 (PDF p.47)

import Mathlib
import Definitions.Def_SybilClinch_TargetMech

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

namespace Supplement

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and
Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256
93c5d05b05cc8b80b5bb5c0ac677b9642e119277d82de797234b0242f7c5021c), Appendix B.1,
Definition B.1 (Constant target), printed p.45 (PDF p.47).

For a divisible supply `s > 0` and a positive initial clock price `pstar`, the constant-target
specification has target `T(p,X,Y)=s`, domain
`{(p,X,Y) : pstar ≤ p ∧ 0 ≤ X ∧ X ≤ s ∧ 0 ≤ Y}`, and capacity `s`.

**Formalization Note.** The paper's trivial environment description is omitted, as in the
published `TargetMech` encoding; the target and domain contain all of the remaining data. -/
def fixedMech (s pstar : ℝ) : TargetMech where
  pstar := pstar
  T := fun _ _ _ => s
  D := {z | pstar ≤ z.1 ∧ 0 ≤ z.2.1 ∧ z.2.1 ≤ s ∧ 0 ≤ z.2.2}
  cap := (s : EReal)

end Supplement

end SybilClinch


