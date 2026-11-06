-- Prove2me | Definitions.Def_ConstrSOSP_Fnorm
-- name    : ConstrSOSP_Fnorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:07:13.730794+00:00
-- url     : https://prove2.me/theorems/3074ceaf-b1b9-4ab9-afa0-f0d71eeb4fb4
-- title:
--   Normalized hard function $F$ on $[0,1]^2$
-- statement:
--   $$
--   F(z)=\frac{\bar f\big(Sz-m(1,1)\big)}{c_0N^4},\qquad z\in[0,1]^2,
--   $$
--   with $N=6\cdot2^n+6$, $m=\lfloor N/8\rfloor$, $S=N+2m$ and $c_0=2^{76}$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), proof of Corollary 5.6, p.56

import Mathlib
import Definitions.Def_ConstrSOSP_gridN
import Definitions.Def_ConstrSOSP_frameM
import Definitions.Def_ConstrSOSP_frameS
import Definitions.Def_ConstrSOSP_fFrame
import Definitions.Def_ConstrSOSP_c0

namespace ConstrSOSP

/-- **The normalized hard function `F` on `[0, 1]²`** (arXiv:2604.02285, 2 Nov 2026, proof of
Corollary 5.6, p.56: "Retain the original normalization constant c0 = 2^76 and set
F(z) = f̄(Sz − m(1, 1))/(c0 N^4), ϵ = ϵ0²/(c0² N⁴), z ∈ [0, 1]^2").

`Fnorm C z = f̄(S z − m(1, 1)) / (c₀ N⁴)` with `N = 6·2ⁿ + 6`, `m = ⌊N/8⌋`, `S = N + 2m` and
`f̄ = fFrame C`. -/
noncomputable def Fnorm (C : Circuit) (z : Fin 2 → ℝ) : ℝ :=
  fFrame C (fun i => (frameS C.n : ℝ) * z i - (frameM C.n : ℝ)) /
    ((c0 : ℝ) * (gridN C.n : ℝ) ^ 4)

end ConstrSOSP


