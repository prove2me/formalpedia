-- Prove2me | Definitions.Def_WICanon_NextBit
-- name    : WICanon_NextBit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:54.505162+00:00
-- url     : https://prove2.me/theorems/ce1124ce-0af2-4761-a76c-96fd19614dec
-- title:
--   Next-bit predictors, samplers and simulators
-- statement:
--   For a distribution $Z$ over $\{0,1\}^m$, let $p(z_{<i})=\Pr[Z_i=1\mid Z_{<i}=z_{<i}]$, with $p(z_{<i})=0$ on a null prefix. A function $\mathrm{Pred}:\{0,1\}^*\times\{0,1\}^{\ell_{\mathrm{Pred}}}\to[0,1]$ with binary-fraction values is a **next-bit $\varepsilon$-predictor** for $Z$ if for every $i\in[m]$
--
--   $$\Pr_{z_{<i}\leftarrow Z_{<i},\,r}\bigl[|\mathrm{Pred}(z_{<i};r)-p(z_{<i})|\le\varepsilon\bigr]\ge 1-\varepsilon.$$
--
--   The **sampler** $\mathrm{Samp}^{\mathrm{Pred}}(z_{<i};r_{\mathrm{Pred}},r_S)$ outputs $1$ iff $r_S$ is among the first $\mathrm{Pred}(z_{<i};r_{\mathrm{Pred}})\cdot 2^{\ell_S}$ strings of $\{0,1\}^{\ell_S}$ in lexicographic order. The **simulator** generates bits one at a time from the initial state, $\tilde z_i=\mathrm{Samp}^{\mathrm{Pred}}(\tilde z_{<i};r_i)$. A predictor for a collection $\{Z_a\}$ is a PPT machine that predicts $Z_a$ for all large $n$ and all valid $a$. These objects are what makes a transcript canonical: the same coins give the same output for two nearby distributions.
--
--   **Formalization Note** The prefix $\tilde z_{<i}$ includes the initial state. Footnote 10's integrality $\mathrm{Pred}\cdot 2^{\ell_S}\in\mathbb N$ is the predicate `NoRounding`, a hypothesis of the finite claims. "For every sequence $\{a_n\}$ and every sufficiently large $n$" is equivalent to a threshold uniform in $a$, as a sequence of bad indices would contradict it. The runtime bound $q(n)$ holds for a polynomial-time machine on polynomially long inputs.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Definitions 3.6, 3.8, p.21; footnote 10

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_WICanon_Law
import Definitions.Def_WICanon_TranscriptFamily

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QAdvFew.PoQOracle QiOPoQ

/-- `p(z_{<i}) = Pr[Z_i = 1 | Z_{<i} = z_{<i}]`, for `u = z_{<i}` (Arnon, Mazor, Pass, Silbak, STOC 2027
submission manuscript, sha256 3f78ec3d…, Definition 3.6, p.21).

**Formalization Note.** "with p(z<i) = 0 when Pr[Z<i = z<i] = 0" is Lean's `x / 0 = 0`. -/
noncomputable def condProb (Z : Law) (u : Str) : ℝ :=
  prefixLaw Z (u.length + 1) (u ++ [true]) / prefixLaw Z u.length u

/-- A finite binary fraction (Definition 3.6, p.21). -/
def IsBinaryFraction (q : ℚ) : Prop := ∃ k e : ℕ, q = (k : ℚ) / 2 ^ e

open Classical in
/-- **Next-bit `ε`-predictor** for a distribution `Z` over `{0,1}^m` (Definition 3.6, p.21). `Pred`
takes values in `[0,1]` that are finite binary fractions, and for every `i ∈ [m]`,
`Pr_{z<i←Z<i, r←{0,1}^{ℓPred}}[|Pred(z_{<i}; r) − p(z_{<i})| ≤ ε] ≥ 1 − ε`.

**Formalization Note.** `i` here is the length of the prefix, `0 ≤ i < m`, one less than the printed
index. -/
def IsNextBitPredictor (Z : Law) (m ℓPred : ℕ) (Pred : Str → Str → ℚ) (ε : ℝ) : Prop :=
  (∀ u r, r.length = ℓPred → 0 ≤ Pred u r ∧ Pred u r ≤ 1 ∧ IsBinaryFraction (Pred u r)) ∧
  ∀ i < m, 1 - ε ≤ expect (prefixLaw Z i) fun u =>
    avgCoins ℓPred fun r => if |((Pred u r : ℚ) : ℝ) - condProb Z u| ≤ ε then 1 else 0

/-- Footnote 10, p.21: "Pred(z<i, rPred) · 2^{ℓS} ∈ N, and there are no rounding errors". -/
def NoRounding (Pred : Str → Str → ℚ) (ℓPred ℓS : ℕ) : Prop :=
  ∀ u r, r.length = ℓPred → ∃ K : ℕ, Pred u r * 2 ^ ℓS = K

/-- **The next-bit sampler** `Samp^Pred` (Definition 3.8, p.21): on `u = z_{<i}` and
`r = (r_Pred, r_S) ∈ {0,1}^{ℓPred + ℓS}`, output `1` iff `r_S` is among the first
`Pred(u; r_Pred) · 2^{ℓS}` strings of `{0,1}^{ℓS}` in lexicographic order. -/
def samp (Pred : Str → Str → ℚ) (ℓPred ℓS : ℕ) (u r : Str) : Bool :=
  decide (((lexRank (r.drop ℓPred) : ℕ) : ℚ) < Pred u (r.take ℓPred) * 2 ^ ℓS)

/-- **The simulator** `Sim^Pred` (Definition 3.8, p.21) on initial state `z`: `simBits … z i r` is
`(z̃_1, …, z̃_i)` with `z̃_j = Samp^Pred((z, z̃_{<j}); r_j)`, and `r` is the concatenation of the blocks
`r_j` of length `ℓPred + ℓS`. -/
def simBits (Pred : Str → Str → ℚ) (ℓPred ℓS : ℕ) (z : Str) : ℕ → Str → Str
  | 0, _ => []
  | i + 1, r =>
    let y := simBits Pred ℓPred ℓS z i r
    y ++ [samp Pred ℓPred ℓS (z ++ y) ((r.drop (i * (ℓPred + ℓS))).take (ℓPred + ℓS))]

/-- The law of `(Z, Ỹ)`, `Ỹ ≡ Sim^Pred(Z, R)` (Claim 3.9, p.21): `Z` is the first `n0` bits of `X`,
and `R = (R_1, …, R_n)` is uniform and independent of it. -/
noncomputable def simJoint (X : Law) (n0 n : ℕ) (Pred : Str → Str → ℚ) (ℓPred ℓS : ℕ) : Law :=
  bindLaw (prefixLaw X n0) fun z =>
    coinLaw (n * (ℓPred + ℓS)) fun r => z ++ simBits Pred ℓPred ℓS z n r

/-- A PPT predictor for a collection (Definition 3.6, p.21). A polynomial-time map `run` and a
polynomial `coins` for `ℓPred`. -/
structure PredictorMachine where
  run : Str → Str
  run_poly : PolyTimeComputable run
  coins : Polynomial ℕ

/-- The value `Pred(a, u; r)` of a machine at parameter `n`: its output string `s`, read as the
binary fraction `rank(s)/2^{|s|−1}` and capped at `1`, so that both `0` and `1` are values. -/
def PredictorMachine.value (M : PredictorMachine) (n : ℕ) (a u r : Str) : ℚ :=
  let s := M.run (tup [unary n, a, u, r])
  min 1 (((lexRank s : ℕ) : ℚ) / 2 ^ (s.length - 1))

/-- **Next-bit predictor for a collection** `{Z_a}` (Definition 3.6, p.21): for all large `n` and all
valid `a`, `Pred_a` is a next-bit `ε(n)`-predictor for `Z_a` over `{0,1}^{L(n)}`.

**Formalization Note.** Printed, "for every sequence {a_n} and every sufficiently large n". A threshold
depending on the sequence gives a uniform one: otherwise a sequence of bad indices at larger and larger
`n` contradicts it. "The runtime of Pred_{a_n} is at most q(n)" holds for a polynomial-time `run` on
inputs of length polynomial in `n`. -/
def IsCollectionPredictor (valid : ℕ → Str → Prop) (L : ℕ → ℕ) (Z : ℕ → Str → Law)
    (M : PredictorMachine) (ε : ℕ → ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ a, valid n a →
    IsNextBitPredictor (Z n a) (L n) (M.coins.eval n) (M.value n a) (ε n)

end WICanon


