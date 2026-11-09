-- Prove2me | Definitions.Def_OracleStateHSP_uG
-- name    : OracleStateHSP_uG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:39.142513+00:00
-- url     : https://prove2.me/theorems/b80e4a9c-eeb4-442e-b889-582f608334b2
-- title:
--   Uniform superposition $|u_G\rangle$
-- statement:
--   $$
--   |u_G\rangle = \frac{1}{\sqrt{2^n}} \sum_{k \in \mathbb Z_2^r} \sum_{v \in \mathbb Z_2^m} |k\rangle |v\rangle |0\rangle ,
--   $$
--   the uniform superposition over the group with the answer register set to zero ($n = r + m$).
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.3, after eq. (55), p.39

import Mathlib
import Definitions.Def_OracleStateHSP_V
import Definitions.Def_OracleStateHSP_K

namespace OracleStateHSP

/-- The uniform superposition `|u_G⟩ = 2^{−n/2} ∑_{k ∈ Z_2^r} ∑_{v ∈ Z_2^m} |k⟩|v⟩|0⟩` over the
group, with the answer register zero (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, §4.3, after eq. (55), p.39), `n = r + m`. -/
noncomputable def uG (r m : ℕ) : EuclideanSpace ℂ ((K r × V m) × V m) :=
  WithLp.toLp 2 fun p => if p.2 = 0 then ((Real.sqrt (2 ^ (r + m)))⁻¹ : ℂ) else 0

end OracleStateHSP


