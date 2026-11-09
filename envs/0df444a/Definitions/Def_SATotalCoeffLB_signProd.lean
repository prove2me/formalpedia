-- Prove2me | Definitions.Def_SATotalCoeffLB_signProd
-- name    : SATotalCoeffLB_signProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:19:54.479297+00:00
-- url     : https://prove2.me/theorems/74e8cb5a-cfdd-47c8-aad3-2914c8214cc3
-- title:
--   Sign product $s^z = \prod_{e: z_e=1} s_e$
-- statement:
--   For signs $s = (s_e)_{e\in E}$ and $z \in \mathbb F_2^E$,
--
--   $$
--   s^z = \prod_{e \in E : z_e = 1} s_e .
--   $$
--
--   For $\pm1$ signs, $z \mapsto s^z$ is a homomorphism from $(\mathbb F_2^E, +)$ to $(\{\pm1\}, \cdot)$, and every such homomorphism has this form.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), Section 9.1, Choice of s, p.52; Section 9.4, p.56

import Mathlib

namespace SATotalCoeffLB

/-- **The sign product `s^z := ∏_{e : z_e = 1} s_e`** of signs `s = (s_e)_e` and a vector `z ∈ F₂^E`
(Section 9.1, p.52; Section 9.4, p.56, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178)). For `±1` signs, `z ↦ s^z` is a homomorphism
from `(F₂^E, +)` to `({±1}, ·)`. -/
noncomputable def signProd {ι : Type*} [Fintype ι] (s : ι → ℝ) (z : ι → ZMod 2) : ℝ :=
  ∏ e, if z e = 1 then s e else 1

end SATotalCoeffLB


