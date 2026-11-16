-- Prove2me | Definitions.Def_PolyEulerFlow_Supplement_branchField
-- name    : PolyEulerFlow_Supplement_branchField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:06:45.754465+00:00
-- url     : https://prove2.me/theorems/9d2b7c0e-57b5-48cb-869a-daf39873a74c
-- title:
--   The compiled branching controller (14), its initialization and the quartic certificate (15)
-- statement:
--   The scalar feedback program (13) has one register $Y$, one test $u(Y)=(Y-1/2)/4$ and the branches
--   $$H_-(Y)=Y/2+1/2\ \ (Y<1/2),\qquad H_+(Y)=Y/2\ \ (Y>1/2).$$
--   Its unchanged compiled field at scale $h$, with $\varepsilon=h^K$, has eleven active coordinates: the eight clock coordinates $p_0,\dots,p_3,\tau_0,\dots,\tau_3$ of the compiler, a comparator $v$, the data $Y$ and the shadow $Y^s$. The clock follows the compiler's eight equations, and
--   $$v'=(1-p_3)\frac{v-v^3}2+p_3\Big(\frac{Y-1/2}4-v\Big),\qquad (Y^s)'=p_1\Big(\frac Y2+\frac{1-v}4-Y^s\Big),\qquad Y'=p_3(Y^s-Y).\tag{14}$$
--   The initialization of Theorem 22 is $p=(1,0,0,0)$, $\tau_i=\varepsilon$, $Y=Y^s=a$, $v=(a-1/2)/4$.
--
--   The source certificate is the quartic
--   $$P(Y)=\big(144(Y-1/2)^2-1\big)\big(16(Y-1/2)^2-1\big),\tag{15}$$
--   whose nonpositive set is $C=C_-\cup C_+$ with $C_-=[1/4,5/12]$ and $C_+=[7/12,3/4]$.
--
--   **Formalization Note** The field is written out from (14) on the published layout `CompiledState 1 1`, with the published `clockField` for the clock. It coincides with the published `compiledField` of the separated affine program (13): the selector $\sum_\sigma\beta_\sigma(v)H_\sigma(Y)$ with $\beta_\pm=(1\pm v)/2$ equals $Y/2+(1-v)/4$.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow: Polynomial Dynamics for P and PSPACE (manuscript, STOC 2027 submission, sha256 c4e01b2beb237b48b48e97294deb3c15dae11d39c5f136914567c5ca2ae1b119), (13)–(15), pp.22–23 (PDF 24–25); Theorem 22, p.23 (PDF 25)

import Mathlib
import Definitions.Def_PolyEulerFlow_compiledField

namespace PolyEulerFlow.Supplement

open PolyEulerFlow

/-- The compiled branching controller (14), p.22 (PDF 24), for the program (13) `H₋(Y) = Y/2 + 1/2` (`Y < 1/2`), `H₊(Y) = Y/2`
(`Y > 1/2`) with test `u(Y) = (Y − 1/2)/4`, at scale `h` with `ε = h^K`:
`v′ = (1 − p₃)(v − v³)/2 + p₃((Y − 1/2)/4 − v)`, `(Y^s)′ = p₁(Y/2 + (1 − v)/4 − Y^s)`, `Y′ = p₃(Y^s − Y)`, and the eight unchanged clock
equations of the published `clockField ε`. Eleven active coordinates, laid out as the published `CompiledState 1 1`.
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), p.22.
**Formalization Note.** The field is written out from (14); it coincides with the published `compiledField` of the separated affine program
(13) (test coefficient `1/4`, constant `−1/8`, `D = 1/2`, `b_true = 0`, `b_false = 1/2`). -/
noncomputable def branchField (K : ℕ) (h : ℝ) (Z : CompiledState 1 1) : CompiledState 1 1
  | .inl c => clockField (h ^ K) (clockPart Z) c
  | .inr (.inl _) =>
      (1 - phaseBit 3 Z) * (compV Z 0 - compV Z 0 ^ 3) / 2 + phaseBit 3 Z * ((dataY Z 0 - 1 / 2) / 4 - compV Z 0)
  | .inr (.inr (.inl _)) => phaseBit 3 Z * (shadowY Z 0 - dataY Z 0)
  | .inr (.inr (.inr _)) => phaseBit 1 Z * (dataY Z 0 / 2 + (1 - compV Z 0) / 4 - shadowY Z 0)

/-- The initialization of Theorem 22 (p.23): `p = (1, 0, 0, 0)`, `τ_i = ε = h^K`, `Y = Y^s = a`, `v = (a − 1/2)/4`. -/
noncomputable def branchInit (K : ℕ) (h a : ℝ) : CompiledState 1 1
  | .inl c => initialClock (h ^ K) c
  | .inr (.inl _) => (a - 1 / 2) / 4
  | .inr (.inr (.inl _)) => a
  | .inr (.inr (.inr _)) => a

/-- The quartic certificate (15), p.23: `P(Y) = (144(Y − 1/2)² − 1)(16(Y − 1/2)² − 1)`. -/
noncomputable def quartic (Y : ℝ) : ℝ :=
  (144 * (Y - 1 / 2) ^ 2 - 1) * (16 * (Y - 1 / 2) ^ 2 - 1)

/-- The low component `C₋ = [1/4, 5/12]` (p.23). -/
def Cminus : Set ℝ := Set.Icc (1 / 4) (5 / 12)

/-- The high component `C₊ = [7/12, 3/4]` (p.23). -/
def Cplus : Set ℝ := Set.Icc (7 / 12) (3 / 4)

end PolyEulerFlow.Supplement


