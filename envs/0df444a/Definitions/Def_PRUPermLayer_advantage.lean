-- Prove2me | Definitions.Def_PRUPermLayer_advantage
-- name    : PRUPermLayer_advantage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:29:20.184268+00:00
-- url     : https://prove2.me/theorems/3014387a-90b8-4439-8bcc-7d4e4b473bb1
-- title:
--   Distinguishing advantage $\mathrm{Adv}_A(E, E')$
-- statement:
--   A **unitary ensemble** $E$ is a probability distribution on $U(N)$; an algorithm gets oracle access to one unitary $U \sim E$, sampled once and used for every query. The **advantage** of an algorithm $A$ in distinguishing two ensembles $E, E'$ is
--   $$
--   \mathrm{Adv}_A(E, E') = \Big|\Pr_{U\sim E}[A^U = 1] - \Pr_{U \sim E'}[A^U = 1]\Big| .
--   $$
--
--   **Formalization Note** The two probabilities are the expectations of the acceptance probability over $U$. For probability measures the advantage lies in $[0,1]$ (checked in the sanity file).
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_PRUPermLayer_acceptProb
open MeasureTheory

namespace PRUPermLayer

/-- The advantage `Adv_A(E, E′) = |Pr_{U∼E}[A^U = 1] − Pr_{U∼E′}[A^U = 1]|` of an algorithm in
distinguishing two unitary ensembles (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)). The oracle `U` is sampled once
and answers every query.

**Formalization Note** A unitary ensemble is a measure on `U(N) = Matrix.unitaryGroup (Fin (2 ^ n)) ℂ`
with the published Borel σ-algebra. The acceptance probability is a continuous function of `U` with
values in `[0, 1]`, so for probability measures the integrals are genuine expectations and the
advantage lies in `[0, 1]` (checked in the sanity file). -/
noncomputable def advantage {n t : ℕ} (alg : FwdAlg n t)
    (E E' : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)) : ℝ :=
  |(∫ U, acceptProb alg (U : Matrix _ _ ℂ) ∂E) - ∫ U, acceptProb alg (U : Matrix _ _ ℂ) ∂E'|

end PRUPermLayer


