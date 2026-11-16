-- Prove2me | Definitions.Def_MLManagesComplexity_Supplement_PredClass
-- name    : MLManagesComplexity_Supplement_PredClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:06:29.98585+00:00
-- url     : https://prove2.me/theorems/0358cc0d-8c5a-426d-85be-f6491c5e3c43
-- title:
--   Log loss, next-bit predictors with precision $m$, $\mu_C$, and the class $\mathcal P_{s,m}$
-- statement:
--   For $p\in(0,1)$ and $b\in\{0,1\}$ the **log loss** is $\ell(p,1)=\log(1/p)$ and $\ell(p,0)=\log(1/(1-p))$, logarithms base 2.
--
--   A **next-bit predictor on $\{0,1\}^n$ with precision $m$** is a well-formed Boolean circuit $C$ with $n$ inputs and $m$ outputs which, on the encoding of every string $y\in\{0,1\}^{<n}$, outputs the binary digits of an integer $j$ with $1\le j\le 2^m-1$; its value is $C(y)=j\cdot 2^{-m}$. A string $y$ with $|y|<n$ is encoded as $y$, then a $1$, then $n-1-|y|$ zeros. The predictor defines
--
--   $$
--   \mu_C(x)=\prod_{i=1}^n 2^{-\ell(C(x_{<i}),x_i)},\qquad x_{<i}=x_1\cdots x_{i-1},
--   $$
--
--   and $\mathcal P_{s,m}$ is the set of such predictors of size at most $s$. The expected log loss of $C$ on $D$ is $\mathbb E_{x\sim D}[\log 1/\mu_C(x)]$.
--
--   These are the explicit models of Appendix B, used in Theorem C.2.
--
--   **Formalization Note** Circuits are the published `PPADSIS.SubexpSIS.Circuit` (gates constant, NOT, AND, OR; well formed means acyclic with distinct existing output wires; size counts input wires and gates). Output bits are read most significant first (published `valBE`). The paper's "standard encoding" is fixed as the end-marker padding above.
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), §B.1 (log loss) and Definition B.1, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Circuit
import Definitions.Def_AutoregressiveCompression_Main_Information

set_option autoImplicit false

open PPADSIS.SubexpSIS AutoregressiveCompression.Main

namespace MLManagesComplexity.Supplement

/-- The **log loss** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233
(version of 2026-10-31, sha256 4874d83f…), §B.1, printed p.17, PDF p.18: "For p ∈ (0, 1) and
b ∈ {0, 1} define the log loss ℓ(p, b) = log(1/p) if b = 1 and ℓ(p, b) = log(1/(1 − p)) if b = 0"),
in bits.

**Formalization Note** Logarithms are base 2 (`Real.logb 2`), matching `2^{−ℓ}` in `µ_C`. The
value outside `p ∈ (0,1)` is Lean's default and is never used: predictor outputs lie in
`[2^{−m}, 1 − 2^{−m}]`. -/
noncomputable def logLoss (p : ℝ) (b : Bool) : ℝ :=
  if b then Real.logb 2 (1 / p) else Real.logb 2 (1 / (1 - p))

/-- The **fixed-length encoding of a short string** used as circuit input: `w` followed by a
marker `1` and `L − |w|` zeros, a string of length `L + 1` for `|w| ≤ L`. Strings of length less
than `n` (predictor inputs) are encoded with `L = n − 1` (length `n`); strings of length at most `n`
(distinguisher inputs, Definition C.1) with `L = n` (length `n + 1`). -/
def padEnc (L : ℕ) (w : List Bool) : List Bool :=
  w ++ true :: List.replicate (L - w.length) false

/-- The integer `j` output by the circuit `C` on the prefix `y` (encoded as `padEnc (n − 1) y`),
its output bits read in binary, most significant bit first (published `valBE`). -/
def predOut (C : Circuit) (n : ℕ) (y : List Bool) : ℕ :=
  valBE (C.eval (padEnc (n - 1) y))

/-- The number `C(y) = j · 2^{−m}` output by a precision-`m` predictor on the prefix `y`. -/
noncomputable def predVal (C : Circuit) (n m : ℕ) (y : List Bool) : ℝ :=
  (predOut C n y : ℝ) / 2 ^ m

/-- A **next-bit predictor on `{0,1}^n` with precision `m`** (Fortnow, arXiv:2604.07233 (version
of 2026-10-31, sha256 4874d83f…), Definition B.1, printed p.17, PDF p.18: "a circuit C that on
input a string y ∈ {0, 1}^{<n} (under a standard encoding of strings of length less than n)
outputs a number C(y) ∈ {1, 2, …, 2^m − 1} · 2^{−m}"): a well-formed Boolean circuit (published
`PPADSIS.SubexpSIS.Circuit`) with `n` input wires and `m` output wires such that on the encoding
`padEnc (n − 1) y` of every `y` with `|y| < n` its output, read as a binary integer `j`, satisfies
`1 ≤ j ≤ 2^m − 1`.

**Formalization Note** The "standard encoding" is fixed as `padEnc (n − 1)`: `y`, a marker `1`,
then zeros, `n` bits in all. Well formed (published `Circuit.WF`) means acyclic with distinct
existing output wires. -/
def IsNextBitPredictor (n m : ℕ) (C : Circuit) : Prop :=
  C.WF ∧ C.nIn = n ∧ C.outs.length = m ∧
    ∀ y : List Bool, y.length < n → 1 ≤ predOut C n y ∧ predOut C n y ≤ 2 ^ m - 1

/-- The **class `P_{s,m}`** (Fortnow, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…),
Definition B.1, printed p.17, PDF p.18: "We let P_{s,m} denote the set of next-bit predictors on
{0, 1}^n with precision m computed by circuits of size at most s"): next-bit predictors on
`{0,1}^n` with precision `m` of size at most `s` (published `Circuit.size`, which counts input
wires and gates). -/
def PredClass (n s m : ℕ) (C : Circuit) : Prop :=
  IsNextBitPredictor n m C ∧ C.size ≤ s

/-- The **distribution `µ_C` of a predictor** (Fortnow, arXiv:2604.07233 (version of 2026-10-31,
sha256 4874d83f…), Definition B.1, printed p.17, PDF p.18):
`µ_C(x) = ∏_{i=1}^n 2^{−ℓ(C(x_{<i}), x_i)}`, where `x_{<i} = x₁ … x_{i−1}`.

**Formalization Note** Lean's index `i : Fin n` is the paper's `i + 1`, so `x_{<i+1}` is the list
of the first `i` bits of `x` and `x_{i+1}` is `x i`. -/
noncomputable def muC (n m : ℕ) (C : Circuit) (x : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, (2 : ℝ) ^ (-logLoss (predVal C n m ((List.ofFn x).take i.val)) (x i))

/-- The **expected log loss** `E_{x∼D}[log 1/µ_C(x)]` of the predictor `C` on `D`, in bits
(published finite `AutoregressiveCompression.Main.expectation`). -/
noncomputable def expectedLogLoss {n : ℕ} (D : PMF (Fin n → Bool)) (m : ℕ) (C : Circuit) : ℝ :=
  expectation D (fun x => Real.logb 2 (1 / muC n m C x))

end MLManagesComplexity.Supplement


