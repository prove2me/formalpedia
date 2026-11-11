-- Prove2me | Definitions.Def_DataDepProb_Discrete_Amp
-- name    : DataDepProb_Discrete_Amp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:10:38.88723+00:00
-- url     : https://prove2.me/theorems/33e7d825-603c-4a93-b84e-3f2b61d8c16f
-- title:
--   Sample amplification $\mathrm{Amp}(s)=(s',y)$, the law $L(\mathrm{Amp}(S))$, the law $D^{n+1}$ and $\delta_n$
-- statement:
--   For $s\in[d]^n$, **sample amplification** (§4.3) appends a copy of a uniformly chosen entry and uniformly shuffles the resulting $n+1$ entries; $\mathrm{Amp}(s)=(s',y)$ is the pair of the first $n$ entries and the last entry. Its coins are a pair $(j,\sigma)$: the index $j\in[n]$ of the copied entry and a permutation $\sigma$ of the $n+1$ positions, uniform over the $n\cdot(n+1)!$ pairs; the shuffled sequence is $i\mapsto t(\sigma(i))$ with $t=(s_1,\dots,s_n,s_j)$.
--
--   For $D\in\Delta_d$ and $S\sim D^n$ with independent coins, $L(\mathrm{Amp}(S))$ is the law on $[d]^n\times[d]$ with probability vector
--   $$z\mapsto\sum_{s\in[d]^n}\ \sum_{(j,\sigma)}\frac{D^n(s)}{n\,(n+1)!}\,\mathbf 1\{\mathrm{Amp}_{(j,\sigma)}(s)=z\},$$
--   and $D^{n+1}$ is the law of an i.i.d. pair $(\bar S,\bar Y)$, $\bar S\sim D^n$, $\bar Y\sim D$, on the same space. Finally $\delta_n=\sqrt{(d-1)/(2n(n+1))}$ (Lemma 4.8).
--
--   **Formalization Note.** Indices are 0-based (`Fin n`, `Fin (n+1)`); the copied entry is appended at position $n$ before shuffling. For $n=0$ there is no coin, and the theorems assume $n\ge1$.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 9, §4.3 and Lemma 4.8

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex

open MeasureTheory

namespace DataDepProb.Discrete

/-!
# Sample amplification by one sample

Feldman, Kale, Majid, Talwar, *Data-Dependent Probability Estimation via Sample Amplification*,
STOC 2027 submission (manuscript sha256 28400f1c…), §4.3 p. 9: "For `s ∈ [d]^n`, append a copy of
a uniformly chosen entry and uniformly shuffle the resulting `n + 1` samples. Write
`Amp(s) = (s′, y)` for the first `n` entries and the last entry."

* The coins of one amplification are a pair `(j, σ)`: the index `j ∈ Fin n` of the copied entry
  and a permutation `σ` of the `n + 1` positions, drawn uniformly from the `n · (n + 1)!` pairs.
  The amplified sequence is `t ∘ σ`, where `t = (s_0, …, s_{n−1}, s_j)`.
* `ampProb D` is the probability vector of `Amp(S)` for `S ∼ D^n` and independent coins, on
  `[d]^n × [d]`; `ampLaw` is that law and `pairLaw D` is `D^{n+1}` on the same space (the first `n`
  coordinates and the last one).
* `deltaN n d = √((d − 1)/(2n(n + 1)))` (Lemma 4.8).
-/

/-- The coins of one amplification of a sample of size `n`: the copied index and the
shuffling permutation. -/
def AmpCoin (n : ℕ) : Type := Fin n × Equiv.Perm (Fin (n + 1))

instance (n : ℕ) : Fintype (AmpCoin n) :=
  inferInstanceAs (Fintype (Fin n × Equiv.Perm (Fin (n + 1))))

instance (n : ℕ) : DecidableEq (AmpCoin n) :=
  inferInstanceAs (DecidableEq (Fin n × Equiv.Perm (Fin (n + 1))))

/-- `Amp(s) = (s′, y)` with coins `c = (j, σ)`: append `s_j`, permute the `n + 1` entries by
`σ`, and split into the first `n` entries and the last entry (§4.3). -/
def amp {n d : ℕ} (s : Fin n → Fin d) (c : AmpCoin n) : (Fin n → Fin d) × Fin d :=
  let t : Fin (n + 1) → Fin d := Fin.snoc (α := fun _ => Fin d) s (s c.1)
  let t' : Fin (n + 1) → Fin d := fun i => t (c.2 i)
  (fun i => t' (Fin.castSucc i), t' (Fin.last n))

/-- The probability vector of `L(Amp(S))` on `[d]^n × [d]`, for `S ∼ D^n` and uniform coins
independent of `S`. -/
noncomputable def ampProb {n d : ℕ} (D : Fin d → ℝ) (z : (Fin n → Fin d) × Fin d) : ℝ :=
  ∑ s : Fin n → Fin d, ∑ c : AmpCoin n,
    sampleProb D s / (Fintype.card (AmpCoin n) : ℝ) * (if amp s c = z then 1 else 0)

/-- The law `L(Amp(S))` of the amplified pair, `S ∼ D^n`. -/
noncomputable def ampLaw (n : ℕ) {d : ℕ} (D : Fin d → ℝ) : Measure ((Fin n → Fin d) × Fin d) :=
  finLaw (ampProb D)

/-- The law `D^{n+1}` of an i.i.d. pair `(S̄, Ȳ)`, `S̄ ∼ D^n`, `Ȳ ∼ D`. -/
noncomputable def pairLaw (n : ℕ) {d : ℕ} (D : Fin d → ℝ) : Measure ((Fin n → Fin d) × Fin d) :=
  finLaw (fun z => sampleProb D z.1 * D z.2)

/-- `δ_n = √((d − 1)/(2n(n + 1)))` (Lemma 4.8). -/
noncomputable def deltaN (n d : ℕ) : ℝ :=
  Real.sqrt (((d : ℝ) - 1) / (2 * (n : ℝ) * ((n : ℝ) + 1)))

end DataDepProb.Discrete


