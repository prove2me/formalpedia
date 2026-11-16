-- Prove2me | Definitions.Def_PNormReg_Supplement_RectOmega
-- name    : PNormReg_Supplement_RectOmega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:51:23.370469+00:00
-- url     : https://prove2.me/theorems/9280e7c8-7ceb-42ea-82a8-4c59b57b1aae
-- title:
--   The rectangular matrix multiplication exponent $\omega(1,a,a)$
-- statement:
--   For $a\ge0$, a real number $\tau$ is an admissible exponent if for every $\varepsilon>0$ there is a constant $C>0$ such that for every $k\ge1$ some correct arithmetic straight-line program multiplies every $k\times\lceil k^a\rceil$ real matrix by every $\lceil k^a\rceil\times\lceil k^a\rceil$ real matrix with at most $C\,k^{\tau+\varepsilon}$ additions, subtractions and multiplications. Then
--
--   $$\omega(1,a,a)=\inf\{\tau:\tau\text{ is admissible}\}.$$
--
--   For $n,d\ge1$ the exponent with $d=n^a$ is $a=\log d/\log N$ with $N=\max(n,2)$, which is exact for $n\ge2$.
--
--   This is the exponent in the preprocessing bound $\widetilde O(n^{\omega(1,a,a)})$ of Theorem 6.
--
--   **Formalization Note** Built on the published arithmetic cost model `OAI.MatrixMultiplication.Arithmetic` that also defines the base mission's $\omega$; that module's `rectangularOmega` has the shape $\omega(1,a,1)$ and is not used.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), ω(a, b, c), p.8

import Mathlib
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

namespace PNormReg

namespace Supplement

open OAI.MatrixMultiplication.Arithmetic

/-!
# The rectangular exponent `ω(1, a, a)`

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), p.8: "`ω(a, b, c)` denote[s] the smallest
exponent for which a `k^a × k^b` matrix can be multiplied by a `k^b × k^c` matrix in
`O(k^{ω(a,b,c)+δ})` time for all `δ > 0`."

**Formalization Note.** Built on the published `OAI.MatrixMultiplication.Arithmetic` cost model
(arithmetic straight-line programs over `ℝ`, one unit per `+ − ×`), the model of the base mission's
`ω = omega ℝ`. The shape is `k × ⌈k^a⌉` by `⌈k^a⌉ × ⌈k^a⌉` (`innerSize k a = ⌈k^a⌉₊`). The published
`rectangularOmega` is `ω(1, a, 1)`, a different shape, so it is not used. Every exponent `τ` in the set is
at least `1` for `a ≥ 0` (a correct program needs one multiplication per output entry), so the
infimum is of a nonempty set bounded below.
-/

/-- `τ` is an admissible exponent for `k × ⌈k^a⌉` by `⌈k^a⌉ × ⌈k^a⌉` multiplication over `ℝ`: for
every `ε > 0` there is one constant `C` with a correct program of cost `≤ C·k^{τ+ε}` at every size. -/
def RectOneAAAdmissible (a τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ k : ℕ, 1 ≤ k → ∃ P : MatrixAlgorithm ℝ k (innerSize k a) (innerSize k a),
      P.Correct ∧ (P.cost : ℝ) ≤ C * (k : ℝ) ^ (τ + ε)

/-- `ω(1, a, a)`, the infimum of the admissible exponents. -/
noncomputable def omegaOneAA (a : ℝ) : ℝ := sInf {τ : ℝ | RectOneAAAdmissible a τ}

/-- The `a` with `d = n^a` used in Theorem 6: `a := log d / log N` with `N := max n 2` (so `N = n`
whenever `n ≥ 2`, and `a = 0` at `n = d = 1`). -/
noncomputable def aExp (n d : ℕ) : ℝ := Real.log d / Real.log (max n 2 : ℕ)

end Supplement

end PNormReg


