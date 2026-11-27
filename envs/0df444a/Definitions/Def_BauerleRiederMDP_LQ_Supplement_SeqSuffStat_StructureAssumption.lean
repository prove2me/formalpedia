-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_StructureAssumption
-- name    : BauerleRiederMDP_LQ_Supplement_SeqSuffStat_StructureAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:32:58.114667+00:00
-- url     : https://prove2.me/theorems/77cb6148-6dc5-4d6b-b16d-9674440e6fb5
-- title:
--   Formalization Note.
-- statement:
--   The Structure Assumption (SA_N) of Theorem 2.3.8 for the information-based Markov Decision Model (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.23, PDF 38, applied in Theorem 5.4.8, p.163, PDF 176), for sets $IM_n$ of functions on $E = E_X \times  I$ ($n = 0, \dots , N$) and $\Delta _n$ of decision rules ($n = 0, \dots , N - 1$), time running forwards: $IM_n \subset  IM(E)$; (i) $ĝ \in  IM_N$; (ii) if $v \in  IM_{n+1}$ then $\hat{T}v$ is well defined and $\hat{T}v \in  IM_n$; (iii) every $v \in  IM_{n+1}$ has a maximizer in $\Delta _n$.
--
--   **Formalization Note.** "$\hat{T}v$ is well defined": for $a \in  D(x)$, $\int  v(\hat{T}) d\hat{Q}^Z$ has a finite positive or negative part. $IM(E)$ is measurable functions into $[-\infty , \infty )$. The stage-indexed families include the stationary single-class version as the constant case.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011)

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_Htil_state
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_BayesModel_posterior
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_ghat
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_QhatZ
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_That
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_SeqSuffStat_IsMaximizer

open MeasureTheory ProbabilityTheory
open MDPFinance.Bellman (erealIntegral)

namespace BauerleRiederMDP.LQ.Supplement

universe u

variable {EX A Z : Type u} {Θ I : Type*} [MeasurableSpace EX] [MeasurableSpace A]
  [MeasurableSpace Z] [MeasurableSpace Θ] [MeasurableSpace I] {M : BayesModel EX A Z Θ}

/-- The Structure Assumption (SA_N) of Theorem 2.3.8 for the information-based Markov Decision Model
(Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), p.23, PDF 38,
applied in Theorem 5.4.8, p.163, PDF 176), for sets `IM_n` of functions on `E = E_X × I`
(`n = 0, …, N`) and `Δ_n` of decision rules (`n = 0, …, N − 1`), time running forwards:
`IM_n ⊂ IM(E)`; (i) `ĝ ∈ IM_N`; (ii) if `v ∈ IM_{n+1}` then `T̂v` is well defined and `T̂v ∈ IM_n`;
(iii) every `v ∈ IM_{n+1}` has a maximizer in `Δ_n`.

**Formalization Note.** "`T̂v` is well defined": for `a ∈ D(x)`, `∫ v(T̂) dQ̂^Z` has a finite positive
or negative part. `IM(E)` is measurable functions into `[−∞, ∞)`. The stage-indexed families
include the stationary single-class version as the constant case. -/
def SeqSuffStat.StructureAssumption (S : SeqSuffStat M I) (N : ℕ) (IMs : ℕ → Set (EX × I → EReal))
    (Deltas : ℕ → Set (EX × I → A)) : Prop :=
  (∀ n ≤ N, ∀ v ∈ IMs n, Measurable v ∧ ∀ p, v p ≠ ⊤) ∧
  (∀ n < N, ∀ f ∈ Deltas n, Measurable f ∧ ∀ p : EX × I, (p.1, f p) ∈ M.D) ∧
  (fun p : EX × I => S.ghat p.1 p.2) ∈ IMs N ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1),
    (∀ (x : EX) (i : I) (a : A), (x, a) ∈ M.D →
      (∫⁻ z, (v (M.TX (x, a, z), S.Phihat (x, i, a, z)) ⊔ 0).toENNReal ∂(S.QhatZ x i a) < ⊤ ∨
        ∫⁻ z, ((-v (M.TX (x, a, z), S.Phihat (x, i, a, z))) ⊔ 0).toENNReal ∂(S.QhatZ x i a) < ⊤)) ∧
    S.That v ∈ IMs n) ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), ∃ f ∈ Deltas n, S.IsMaximizer v f)

end BauerleRiederMDP.LQ.Supplement


