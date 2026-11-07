-- Prove2me | Definitions.Def_KTUnitary_Synth_UEntry
-- name    : KTUnitary_Synth_UEntry
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:18.97187+00:00
-- url     : https://prove2.me/theorems/adfbb17b-3bb7-4812-8cb6-09c7f7771135
-- title:
--   The entry function $\mathcal U\mathrm{Entry}$
-- statement:
--   For a unitary language $\mathcal U=\{U_n\}$, the encoding function on strings $(x,y,b)$ with $x,y\in\{0,1\}^n$, $b\in\{0,1\}$:
--   $$\mathcal U\mathrm{Entry}(x,y,0)=\operatorname{Re}\langle y|U_n|x\rangle,\qquad \mathcal U\mathrm{Entry}(x,y,1)=\operatorname{Im}\langle y|U_n|x\rangle.$$
--   Its values lie in $[-1,1]$.
--
--   **Formalization Note** A string of length $2n+1$ is split as $x$ (first $n$ bits), $y$ (next $n$), $b$ (last bit). On strings of even length, where the paper leaves it undefined, the value is $0$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.10, p. 27

import Mathlib
import Definitions.Def_KTUnitary_Synth_ULang

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **The entry function `𝒰Entry`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 6.10, p. 27): "Let `𝒰 = {U_n}` be a unitary
language. Then `𝒰Entry : {0,1}^{2n+1} → [−1, 1]` is the encoding function
`𝒰Entry(x, y, 0) := Re ⟨y|U_n|x⟩`, `𝒰Entry(x, y, 1) := Im ⟨y|U_n|x⟩`."

Here a string `s` of odd length `2n + 1` is read as `x = s₀ ⋯ s_{n−1}`, `y = s_n ⋯ s_{2n−1}` and
`b = s_{2n}`, and `𝒰Entry(s)` is the real (`b = 0`) or imaginary (`b = 1`) part of the entry of
`U_n` in row `y`, column `x`.

**Formalization Note** On strings of even length, which the paper leaves undefined, the value is
`0`. -/
noncomputable def UEntry (U : ULang) (s : Str) : ℝ :=
  if s.length % 2 = 1 then
    (if s.getD (2 * (s.length / 2)) false then
      ((U (s.length / 2) : Matrix (Bits (s.length / 2)) (Bits (s.length / 2)) ℂ)
        (fun q => s.getD (s.length / 2 + q) false) (fun q => s.getD q false)).im
    else
      ((U (s.length / 2) : Matrix (Bits (s.length / 2)) (Bits (s.length / 2)) ℂ)
        (fun q => s.getD (s.length / 2 + q) false) (fun q => s.getD q false)).re)
  else 0

end KTUnitary.Synth


