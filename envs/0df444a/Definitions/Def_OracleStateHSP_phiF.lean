-- Prove2me | Definitions.Def_OracleStateHSP_phiF
-- name    : OracleStateHSP_phiF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:31:29.539601+00:00
-- url     : https://prove2.me/theorems/41bfe468-cc09-49ef-b08a-132398ce3362
-- title:
--   Simon state $|\varphi_f\rangle$ (eq. (53))
-- statement:
--   For $f : \mathbb Z_2^m \to \mathbb Z_2^m$,
--   $$
--   |\varphi_f\rangle = \frac{1}{\sqrt{2^n}} \sum_{k \in \mathbb Z_2^r} \sum_{v \in \mathbb Z_2^m} |k\rangle_r |v\rangle_m |f(v)\rangle_m ,
--   $$
--   with $n = r + m$. It can be prepared with a single query to Simon's oracle or to the padded oracle.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, eq. (53), p.38

import Mathlib
import Definitions.Def_OracleStateHSP_V
import Definitions.Def_OracleStateHSP_K

namespace OracleStateHSP

/-- The state `|φ_f⟩ = 2^{−n/2} ∑_{k ∈ Z_2^r} ∑_{v ∈ Z_2^m} |k⟩|v⟩|f(v)⟩` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, eq. (53),
p.38), `n = r + m`. -/
noncomputable def phiF (r : ℕ) {m : ℕ} (f : V m → V m) : EuclideanSpace ℂ ((K r × V m) × V m) :=
  WithLp.toLp 2 fun p => if p.2 = f p.1.2 then ((Real.sqrt (2 ^ (r + m)))⁻¹ : ℂ) else 0

end OracleStateHSP


