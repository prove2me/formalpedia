-- Prove2me | Definitions.Def_PrettyGoodCriterion_rateFunction
-- name    : PrettyGoodCriterion_rateFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:32:42.003081+00:00
-- url     : https://prove2.me/theorems/9dde5311-c860-4bd5-a518-d1ff331be90b
-- title:
--   Binary codes: rate $R(\mathcal C)$, $A_2(n,d)$ and the rate function $R_2(\delta)$
-- statement:
--   Binary codes and their rate–distance tradeoff.
--
--   A **binary code** of length $n$ is a subset $\mathcal C\subseteq\{0,1\}^n$, linear or not. Its **rate** is
--   $$R(\mathcal C):=\frac{1}{n}\log_2|\mathcal C| .$$
--   For words $u,v\in\{0,1\}^n$, $d(u,v)$ is their Hamming distance, the number of coordinates in which they differ. The code has **minimum distance at least $d$** if any two distinct codewords are at Hamming distance at least $d$; for $|\mathcal C|\ge 2$ (the paper's standing assumption) this says $d_{\min}(\mathcal C):=\min\{d(c,c') : c,c'\in\mathcal C,\ c\neq c'\}\ge d$.
--
--   $A_2(n,d)$ is the largest cardinality of a binary length-$n$ code with minimum distance at least $d$, and the **asymptotic rate function** is
--   $$R_2(\delta):=\limsup_{n\to\infty}\frac{1}{n}\log_2 A_2\big(n,\lceil\delta n\rceil\big).\qquad(1)$$
--
--   These objects state the main theorem of the paper, which bounds $R(\mathcal C)$ and $R_2(\delta)$ from above by the Holevo information of a classical–quantum channel.
--
--   **Formalization Note** Bits are `Fin 2` and words are `Fin n → Fin 2`; a code is a `Finset` of words and the distance is Mathlib's `hammingDist`. "Minimum distance at least $d$" is the published `BeatingGV42.MinDistAtLeast C d` (any two distinct codewords at distance $\ge d$) with $q=2$. All logarithms are base 2 (`Real.logb 2`). The maximum defining $A_2(n,d)$ also admits codes with fewer than two words, which changes nothing once a two-word code exists. $R_2$ is a real `limsup` along `atTop`; every term of the sequence lies in $[0,1]$ (the term at $n=0$ is $0$ by Lean's total division), so it is the true limit superior. The definition mirrors the published `MetricCodes.Hamming.binaryRate`, whose module is not available in this workspace.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), §1, equation (1), p.1 (PDF 3) (A₂, R₂); §2, p.14 (PDF 16) (rate, d_min, |𝒞| ⩾ 2, base-2 logarithms)

import Mathlib
import Definitions.Def_BeatingGV42_MinDistAtLeast

namespace PrettyGoodCriterion

/-- The **rate** `R(𝒞) := n⁻¹ log |𝒞|` of a binary code `𝒞 ⊆ {0,1}ⁿ`, Alrabiah–Guruswami,
*Binary code rate bounds via classical–quantum channels*, arXiv:2608.09347 (held version),
§2, p.14 (PDF 16); logarithms are base 2 (p.14).

**Formalization Note.** Bits are `Fin 2`, words are `Fin n → Fin 2`, and a code is a `Finset`
of words (arbitrary subsets, linear or not). The logarithm is `Real.logb 2`. -/
noncomputable def rate {n : ℕ} (C : Finset (Fin n → Fin 2)) : ℝ :=
  Real.logb 2 C.card / n

open Classical in
/-- `A₂(n, d)`: the largest cardinality of a (possibly nonlinear) binary length-`n` code with
minimum distance at least `d`, arXiv:2608.09347 (held version), §1, p.1 (PDF 3).

**Formalization Note.** The maximum is over all `Finset`s of words whose distinct elements are
at Hamming distance `⩾ d` (the published `BeatingGV42.MinDistAtLeast` with `q = 2`, which for
`|𝒞| ⩾ 2` is `d_min(𝒞) ⩾ d`, §2, p.14); codes with fewer than two words are admitted, which changes nothing
whenever a two-word code exists (`1 ≤ n` and `d ≤ n`). -/
noncomputable def A2 (n d : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n → Fin 2))).filter
    (fun C => BeatingGV42.MinDistAtLeast C (d : ℝ))).sup Finset.card

/-- The **asymptotic rate function** `R₂(δ) := lim sup_{n→∞} (1/n) log A₂(n, ⌈δn⌉)`,
arXiv:2608.09347 (held version), equation (1), p.1 (PDF 3); base-2 logarithm (p.14).

**Formalization Note.** A real `Filter.limsup` along `atTop`. Every term lies in `[0, 1]`
(`1 ≤ A₂(n, d) ≤ 2ⁿ`; the term at `n = 0` is `0` by Lean's total division), so the sequence is
bounded and this is the true limit superior. `⌈δn⌉` is `Nat.ceil`. This mirrors the published
`MetricCodes.Hamming.binaryRate` (words `Fin n → Bool` there), whose module is not available in
this workspace. -/
noncomputable def rateFunction (δ : ℝ) : ℝ :=
  Filter.limsup (fun n : ℕ => Real.logb 2 (A2 n ⌈δ * n⌉₊) / n) Filter.atTop

end PrettyGoodCriterion


