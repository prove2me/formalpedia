-- Prove2me | Definitions.Def_MLManagesComplexity_Supplement_CondProbFP
-- name    : MLManagesComplexity_Supplement_CondProbFP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:06:03.812206+00:00
-- url     : https://prove2.me/theorems/dca9931f-2ce0-4fe3-aeb7-2d53d22d6e25
-- title:
--   Cylinder probabilities, the conditional next-bit probability $f_\mu$, and $f_\mu\in\mathrm{FP}$
-- statement:
--   For a distribution $\mu$ on $\{0,1\}^n$ and a prefix $y\in\{0,1\}^k$, the **cylinder probability** is $\mu(y)=\Pr_{x\sim\mu}[x_{1\dots k}=y]$, the total mass of the strings beginning with $y$. The **conditional probability function** is
--
--   $$
--   f_\mu(y)=\Pr_{x\sim\mu}[x_{|y|+1}=1\mid x_{1\dots|y|}=y]=\begin{cases}\mu(y1)/\mu(y), & \mu(y0)+\mu(y1)\neq 0,\\ 0, & \mu(y0)+\mu(y1)=0.\end{cases}
--   $$
--
--   For a family $\mu=(\mu_n)_n$, the function $f_\mu$ is **in FP** if there is a single function $M$ computable in polynomial time such that for every $n$ and every prefix $y\in\{0,1\}^{<n}$, $M(1^n0\,y)=\langle q\rangle$ for a rational $q=f_{\mu_n}(y)$, where $\langle q\rangle$ is the numerator–denominator code of `CDFPolyTime`.
--
--   This is condition 2 of Theorem A.1, the autoregressive (next-bit) view of a computable distribution.
--
--   **Formalization Note** A prefix $y$ does not determine the length $n$, so the machine receives $n$ in unary before $y$ (the published `QAlgorithms.Complexity.encNat`), as the base mission does for generators. Masses are real numbers.
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Theorem A.1 condition 2, p.15 (PDF p.16); proof of Theorem A.1 (cylinder probability), p.15 (PDF p.16)

import Mathlib
import Definitions.Def_MLManagesComplexity_Supplement_CDFPolyTime

set_option autoImplicit false

open AutoregressiveCompression.Main

namespace MLManagesComplexity.Supplement

/-- The **cylinder probability** `µ(y) = Pr_{x∼µ}[x_{1…k} = y]` of a prefix `y ∈ {0,1}^k`
(Fortnow, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), proof of Theorem A.1,
printed p.15, PDF p.16): the total mass of the strings `x ∈ {0,1}^n` whose first `|y|` bits are `y`.

**Formalization Note** A prefix is a list of bits `y₁ … y_k`; `x` has prefix `y` when
`(x₁ … xₙ).take |y| = y`. Masses are reals (published `AutoregressiveCompression.Main.mass`). A
list longer than `n` is the prefix of no string, so its cylinder probability is `0`; the
definition is used only for `|y| ≤ n`. -/
noncomputable def cylinder {n : ℕ} (μ : PMF (Fin n → Bool)) (y : List Bool) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => (List.ofFn x).take y.length = y), mass μ x

/-- The **conditional next-bit probability function** `f_µ(y) = Pr_{x∼µ}[x_{|y|+1} = 1 | x_{1…|y|} = y]`
(Fortnow, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Theorem A.1 condition 2,
printed p.15, PDF p.16, "with the convention that f_µ(y) = 0 if µ(y0) + µ(y1) = 0"; proof of
Theorem A.1: "f_µ(y) = µ(y1)/µ(y)"): `µ(y1)/µ(y)` when `µ(y0) + µ(y1) ≠ 0`, and `0` otherwise. -/
noncomputable def condProb {n : ℕ} (μ : PMF (Fin n → Bool)) (y : List Bool) : ℝ :=
  if cylinder μ (y ++ [false]) + cylinder μ (y ++ [true]) = 0 then 0
  else cylinder μ (y ++ [true]) / cylinder μ y

/-- The **conditional probability function of a family is in FP** (Fortnow, arXiv:2604.07233
(version of 2026-10-31, sha256 4874d83f…), Theorem A.1 condition 2, printed p.15, PDF p.16:
"f_µ(y) … is in FP for all prefixes y ∈ {0, 1}^{<n}"): there is one function
`M : {0,1}* → {0,1}*` computable in polynomial time (published
`QAlgorithms.Complexity.PolyTimeComputable`) such that for every length `n` and every prefix `y`
with `|y| < n`, `M(1^n 0 y)` is the code `encRat q` of a rational `q` equal to `f_{µ_n}(y)`.

**Formalization Note** A prefix `y` does not determine the length `n` of the strings, so the
machine is given `n` in unary (published `QAlgorithms.Complexity.encNat n = 1^n 0`) before `y`, as
the base mission does for generators. On inputs not of this form `M` is unconstrained. -/
def CondProbFP (μ : DistFamily) : Prop :=
  ∃ M : List Bool → List Bool, QAlgorithms.Complexity.PolyTimeComputable M ∧
    ∀ (n : ℕ) (y : List Bool), y.length < n →
      ∃ q : ℚ, M (QAlgorithms.Complexity.encNat n ++ y) = encRat q ∧ (q : ℝ) = condProb (μ n) y

end MLManagesComplexity.Supplement


