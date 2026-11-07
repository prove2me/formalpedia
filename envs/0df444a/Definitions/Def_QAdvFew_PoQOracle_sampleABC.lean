-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_sampleABC
-- name    : QAdvFew_PoQOracle_sampleABC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:54:22.888962+00:00
-- url     : https://prove2.me/theorems/06746854-8a3d-452f-9edf-be4ca9ba4c60
-- title:
--   The oracle $O=(A,B,C)$ of a seed
-- statement:
--   The oracle triple sampled from a seed: $A$ is the affine oracle of $\mathrm{RO}$, with $A_t(d,x)=\mathrm{ML}_{2^d}[\mathrm{RO}_t](x)$, and $B$, $C$ are the joins of the levels $B_t$, $C_t$. The distributions $\mathcal D$ and $\mathcal D^{(n)}$ are the laws of this map under the seed measure.
--
--   **Formalization Note** "$O$ in the support of $\mathcal D$" is read as "$O$ is the outcome of the sampling map on some seed", which is at least as strong as the topological support.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §4.1, pp. 21–22 (PDF pp. 23–24); §4.4, p. 24 (PDF p. 26)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_levelsBC

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The oracle triple `O = (A, B, C)` sampled from a seed (Goldin, Lombardi, Morimae, *Quantum
Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §4.1, pp. 21–22 (PDF pp. 23–24), and
`D^(n)`, p. 24 (PDF p. 26)): `A = affineOracle RO`, `A_t(d, x) = ML_{2^d}[RO_t](x)`; `B` and `C`
with levels `levelsBC cut ω t`. `cut = ⊤` is `D`, `cut = n` is `D^(n)`; the distribution is the
law of this map under `seedMeasure F`.

**Formalization Note** "`O` in the support of `D`" is read as "`O = sampleABC ⊤ ω` for some seed
`ω`" (every outcome of the sampling map). -/
noncomputable def sampleABC (cut : ℕ∞) (ω : Seed) : Oracle × Oracle × Oracle :=
  (affineOracle (roOf ω), join (fun t => (levelsBC cut ω t).1), join (fun t => (levelsBC cut ω t).2))

/-- The joined oracle `O = (A, B, C)` of a seed. -/
noncomputable def sampleO (cut : ℕ∞) (ω : Seed) : Oracle :=
  join3 (sampleABC cut ω).1 (sampleABC cut ω).2.1 (sampleABC cut ω).2.2

end QAdvFew.PoQOracle


