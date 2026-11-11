-- Prove2me | Definitions.Def_GaussLocalMaxColoring_Main_VectorRounding
-- name    : GaussLocalMaxColoring_Main_VectorRounding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:21:53.153061+00:00
-- url     : https://prove2.me/theorems/0c589934-7272-46cd-8a9e-df9681d189fe
-- title:
--   The algorithm of Theorem 2: Algorithm 2 with the parameters of Lemmas 50 and 57, amplified by $\lceil c_T\log n\rceil$ trials
-- statement:
--   For real $k>2$, $\beta\in(0,1]$ and $c=\sqrt{k/(k-2)}$, $\ell=\lceil\log n\rceil$ (Appendix A):
--   * low degree, $0<\beta\le (k-2)/k$ (Lemma 50): $a=\sqrt{2\log(2n^\beta)}$, $p^*=\overline\Phi(a/c)/2$, $\delta=1/2$, $T=\lfloor np^*/2\rfloor$, $R=\lceil 2\log 4/p^*\rceil$;
--   * high degree, $(k-2)/k<\beta\le1$ (Table 4, Table 2): $\delta=n^{-(k-2)\beta/(2+k\beta)}\ell^{-C_\ell}$ for a constant $C_\ell$, $T=\lceil n\delta/(100\ell^4)\rceil$, $R=\lceil 32\delta^{-2}\log(8n\ell)\rceil$.
--
--   The algorithm of Theorem 2 ("Run $\Theta(\log n)$ independent trials of Algorithm 2 … Return the largest independent set obtained", p. 66) runs $\lceil c_T\log n\rceil$ independent trials and returns a largest set obtained: the SUCCESS set of a successful trial, or the sets sampled by a failed trial. Its input is the graph and real vectors; it is a function of its i.i.d. Gaussian samples, of which it uses `thm2Calls` $=\lceil c_T\log n\rceil\cdot\ell\cdot R$ (one per call of Algorithm 1). `thm2Exponent` is $1-\frac{k-2}{k}\beta$ for $\beta\le\frac{k-2}{k}$ and $1-\frac{(k-2)\beta}{2+k\beta}$ otherwise.
--
--   **Formalization Note.** When some trial succeeds, the returned set is a largest successful set (a failed trial only samples sets of size $<T$).
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Appendix A (Lemma 50, Table 4, Lemma 57, proof of Theorem 2), printed pp. 59–66 (PDF 61–68)

import Mathlib
import Definitions.Def_GaussLocalMaxColoring_Main_Iterative

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical
noncomputable section

namespace GaussLocalMaxColoring.Main

/-! # The algorithm of Theorem 2 (Appendix A): Algorithm 2 with the parameters of Lemmas 50, 57,
amplified by independent trials

Deguchi–Kawarabayashi–Yoneda–Yoneda, arXiv:2610.35859, Appendix A (printed pp. 59–66,
PDF 61–68): Lemma 50 (low degree, `0 < β ≤ (k−2)/k`), Table 4 and Lemma 57 (high degree,
`(k−2)/k < β ≤ 1`), and the proof of Theorem 2 (p. 66): "Run Θ(log n) independent trials of
Algorithm 2 … Return the largest independent set obtained."

Parameters, with `c = √(k/(k−2))`, `ℓ = ⌈log n⌉`:
* low degree (Lemma 50): `a = √(2 log(2n^β))`, `p* = Φ̄(a/c)/2`, `δ = 1/2`, `T = ⌊n p*/2⌋`,
  `R = ⌈2 log 4 / p*⌉`;
* high degree (Table 4 and Table 2): `δ = n^{−(k−2)β/(2+kβ)} ℓ^{−C_ℓ}` with a constant
  `C_ℓ = C_ℓ(k, β)` ("sufficiently large", fixed in the proof of Lemma 55),
  `T = ⌈nδ/(100ℓ⁴)⌉`, `R = ⌈32 δ^{−2} log(8nℓ)⌉`.

**Formalization Note.** The number of trials is `⌈c_T log n⌉` for a constant `c_T > 0`
("Θ(log n)"). A trial that fails still has obtained the independent sets it sampled; the output
is a largest set obtained over all trials: for a trial returning `SUCCESS(I)` its set `I`, for a
failed trial its sampled sets. When some trial succeeds this is a largest successful set. -/

variable {n d : ℕ}

/-- `c = √(k/(k−2))` (Appendix A). -/
def cA (k : ℝ) : ℝ := Real.sqrt (k / (k - 2))

/-- `p* = Φ̄(a/c)/2` with `a = √(2 log(2n^β))` (Lemma 50). -/
def pStarA (k β : ℝ) (n : ℕ) : ℝ :=
  PhiTail (Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ β)) / cA k) / 2

/-- `δ` of Lemma 50 / Table 4. -/
def deltaA (k β Cl : ℝ) (n : ℕ) : ℝ :=
  if β ≤ (k - 2) / k then 1 / 2
  else (n : ℝ) ^ (-((k - 2) * β / (2 + k * β))) * (numLevels n : ℝ) ^ (-Cl)

/-- `T` of Lemma 50 / Table 2 (high degree). -/
def targetA (k β Cl : ℝ) (n : ℕ) : ℕ :=
  if β ≤ (k - 2) / k then ⌊(n : ℝ) * pStarA k β n / 2⌋₊
  else ⌈(n : ℝ) * deltaA k β Cl n / (100 * (numLevels n : ℝ) ^ 4)⌉₊

/-- `R` of Lemma 50 / Table 2 (high degree). -/
def runsA (k β Cl : ℝ) (n : ℕ) : ℕ :=
  if β ≤ (k - 2) / k then ⌈2 * Real.log 4 / pStarA k β n⌉₊
  else ⌈32 * (deltaA k β Cl n)⁻¹ ^ 2 * Real.log (8 * n * (numLevels n : ℝ))⌉₊

/-- The number of independent trials, `⌈c_T log n⌉`. -/
def trialsA (cT : ℝ) (n : ℕ) : ℕ := ⌈cT * Real.log n⌉₊

/-- The sets obtained by one trial: its `SUCCESS` set, or (on `FAIL`) a largest sampled set. -/
def trialObtained (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ) (T : ℕ) {R : ℕ}
    (ω : Fin (numLevels n) × Fin R → Space d) : Finset (Fin n) :=
  match alg2 G v δ T ω with
  | some I => I
  | none => largest (alg2Sampled G v δ ω)

/-- The algorithm of Theorem 2 with constants `C_ℓ` and `c_T`, as a function of its
`N·ℓ·R` i.i.d. Gaussian samples (`N` trials): a largest independent set obtained. -/
def thm2Output (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (k β Cl cT : ℝ)
    (ω : Fin (trialsA cT n) × (Fin (numLevels n) × Fin (runsA k β Cl n)) → Space d) :
    Finset (Fin n) :=
  largest (List.ofFn fun t : Fin (trialsA cT n) =>
    trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) fun p => ω (t, p))

/-- The law of the samples of the algorithm of Theorem 2: i.i.d. standard Gaussian vectors. -/
def thm2Law (n d : ℕ) (k β Cl cT : ℝ) :
    Measure (Fin (trialsA cT n) × (Fin (numLevels n) × Fin (runsA k β Cl n)) → Space d) :=
  Measure.pi fun _ => stdGaussian (Space d)

/-- The number of calls of Algorithm 1 (Gaussian samples) made by the algorithm of Theorem 2. -/
def thm2Calls (k β Cl cT : ℝ) (n : ℕ) : ℕ := trialsA cT n * numLevels n * runsA k β Cl n

/-- The exponent of Theorem 2: `1 − ((k−2)/k)β` for `β ≤ (k−2)/k`, else `1 − (k−2)β/(2+kβ)`. -/
def thm2Exponent (k β : ℝ) : ℝ :=
  if β ≤ (k - 2) / k then 1 - (k - 2) / k * β else 1 - (k - 2) * β / (2 + k * β)

end GaussLocalMaxColoring.Main


