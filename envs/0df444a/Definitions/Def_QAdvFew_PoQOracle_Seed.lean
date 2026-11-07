-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Seed
-- name    : QAdvFew_PoQOracle_Seed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:10.00982+00:00
-- url     : https://prove2.me/theorems/6510dc76-962a-4c32-9f29-a2270374f3e7
-- title:
--   The random seeds of the oracle distribution $\mathcal D$
-- statement:
--   The distribution $\mathcal D$ is built from independent seeds: the random oracle $\mathrm{RO}=\{\mathrm{RO}_t\}$, one fair bit for each $t$ and $u\in\{0,1\}^t$; and for every level $t$ and string $c$, a sample of $\mathcal F_{2^{t^2}}$ and a uniform string of length $2^{t^2}$. "All random choices in our oracle constructions are independent", so the law of the seeds is the product measure.
--
--   **Formalization Note** The family $\mathcal F$ is a parameter. Every family with the properties of Lemma 3.10 gives a distribution; the paper uses only those properties.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, pp. 21–22 (PDF pp. 23–24); §3.2.2, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open MeasureTheory QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The random seeds of the oracle distribution `D` (Goldin, Lombardi, Morimae, *Quantum Advantage
has Few Complexity Implications*, arXiv:2611.05303v1, §4.1, pp. 21–22 (PDF pp. 23–24)):
1. the random oracle `RO = {RO_t}`: one bit `RO_t(u)` for every `t` and `u ∈ {0,1}^t`;
2. for every level `t` and every string `c` (a candidate code of a pair `(M, x)`), a sample of
   `F_{2^{t²}}`, a string of length `2^{t²}`;
3. for every `t` and `c`, a uniform string of length `2^{t²}`.

"All random choices in our oracle constructions are independent" (§3.2.2, p. 12): the seed
distribution `seedMeasure` is the product. -/
abbrev Seed :=
  ((Σ t : ℕ, Fin t → Bool) → Bool) ×
    ((p : ℕ × Str) → Fin (2 ^ (p.1 ^ 2)) → Bool) × ((p : ℕ × Str) → Fin (2 ^ (p.1 ^ 2)) → Bool)

/-- The distribution of the seeds, for a family `F_N` of distributions on `{0,1}^N`: independent
fair bits for `RO`, independent samples of `F_{2^{t²}}`, and independent uniform strings. -/
noncomputable def seedMeasure (F : (N : ℕ) → PMF (Fin N → Bool)) : Measure Seed :=
  (Measure.infinitePi fun _ : (Σ t : ℕ, Fin t → Bool) => (PMF.uniformOfFintype Bool).toMeasure).prod
    ((Measure.infinitePi fun p : ℕ × Str => (F (2 ^ (p.1 ^ 2))).toMeasure).prod
      (Measure.infinitePi fun p : ℕ × Str =>
        (PMF.uniformOfFintype (Fin (2 ^ (p.1 ^ 2)) → Bool)).toMeasure))

/-- The random oracle `RO_t(u)` of a seed. -/
def roOf (ω : Seed) : (t : ℕ) → (Fin t → Bool) → Bool := fun t u => ω.1 ⟨t, u⟩

end QAdvFew.PoQOracle


