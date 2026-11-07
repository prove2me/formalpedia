-- Prove2me | Definitions.Def_PRUPermLayer_plEnsemble
-- name    : PRUPermLayer_plEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:29:31.3172+00:00
-- url     : https://prove2.me/theorems/cc414d6c-6d9b-4280-860a-71ff35c63ade
-- title:
--   Ensemble $PL$: random permutation after a layer of uniform single-qubit Cliffords
-- statement:
--   The ensemble **$PL$** on $U(N)$, $N = 2^n$, samples a uniformly random permutation unitary $P$ and, independently, a layer $L = C_1 \otimes \cdots \otimes C_n$ of independent uniformly random single-qubit Clifford gates, and returns $PL$ (the layer is applied first). It is the ensemble $PC$ with $C \sim \mu_{\mathrm{Cl}}^{\otimes n}$.
--
--   This is the construction whose security Theorem 1.1 determines.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, pp.1–2 (PDF pp.3–4); §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_PRUPermLayer_pcEnsemble
import Definitions.Def_PRUPermLayer_layerLaw
import Definitions.Def_PRUPermLayer_cliffordLaw
open MeasureTheory

namespace PRUPermLayer

/-- The ensemble `PL`: a uniformly random permutation unitary `P` times an independent layer
`L = C₁ ⊗ ⋯ ⊗ Cₙ` of i.i.d. uniformly random single-qubit Clifford gates, `L` applied first
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §1.1, pp.1–2 (PDF pp.3–4) and §2.2, p.9 (PDF p.11)). It is `pcEnsemble` of the layer law
`µ_Cl^{⊗n}`. -/
noncomputable def plEnsemble (n : ℕ) : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) :=
  pcEnsemble (layerLaw cliffordLaw n)

end PRUPermLayer


