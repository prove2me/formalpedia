-- Prove2me | Definitions.Def_AbelianCayleyHDX_PD
-- name    : AbelianCayleyHDX_PD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:37:32.889208+00:00
-- url     : https://prove2.me/theorems/b66f1652-e5ce-4f26-9ec0-0760ebe8ce40
-- title:
--   The operator $P_D := P_{H_D}$
-- statement:
--   $P_D = P_{H_D}$ is the operator of Eq. (2.1) for $H = H_D$ and $\rho = (q^2 - 2)\hat\nu/2$, where $q^2 = |F|$ and $\hat\nu = |\hat D|$:
--   $$P_D = \frac{\tilde H_D^{\mathsf T}\tilde H_D - \rho I}{2\rho}.$$
--
--   **Formalization Note** $\rho$ is the natural number $(|F| - 2)\hat\nu/2$; the division is exact since $|F| = q^2$ is even.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.5, p.12

import Mathlib
import Definitions.Def_AbelianCayleyHDX_HD
import Definitions.Def_AbelianCayleyHDX_PH

namespace AbelianCayleyHDX

/-- **The operator `P_D := P_{H_D}`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 3.5, p.12): `P_H` of Eq. (2.1) for `H = H_D`
and `ρ = (q² − 2) ν̂ / 2`, where `q² = |F|` and `ν̂ = |D̂|`.

**Formalization Note** `ρ` is the natural number `(|F| − 2)|D̂| / 2`; the division is exact because
`|F| = q²` is even. -/
noncomputable def PD {t : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F] (D : Finset (PG t F)) :
    Matrix (Omega F t) (Omega F t) ℝ :=
  PH (HD D) ((Fintype.card F - 2) * (Dhat D).card / 2)

end AbelianCayleyHDX


