-- Prove2me | Definitions.Def_ShorAdditivityEquiv_holevoValue
-- name    : ShorAdditivityEquiv_holevoValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:28:55.417994+00:00
-- url     : https://prove2.me/theorems/0a45cfc2-5e02-4689-86cc-9dd12bd6dd79
-- title:
--   Holevo quantity $H(N(\sum_i p_i|v_i\rangle\langle v_i|))-\sum_i p_i H(N(|v_i\rangle\langle v_i|))$ of a pure-state ensemble
-- statement:
--   Let $N$ be a map from operators on an input space $\mathcal H_{\mathrm{in}}$ to operators on an output space, and let $\{p_i,|v_i\rangle\}$ be a finite ensemble of unit vectors $|v_i\rangle\in\mathcal H_{\mathrm{in}}$ with weights $p_i\ge 0$, $\sum_i p_i=1$. Its Holevo quantity through $N$ is
--   $$
--   \chi(N;\{p_i,|v_i\rangle\}) = H\Big(N\big(\textstyle\sum_i p_i|v_i\rangle\langle v_i|\big)\Big) - \sum_i p_i\,H\big(N(|v_i\rangle\langle v_i|)\big),
--   $$
--   where $H(\rho)=-\mathrm{Tr}\,\rho\log_2\rho$ is the von Neumann entropy. This is the objective that the Holevo capacity (Eq. (1)) and the constrained Holevo capacity (Eq. (3)) maximize.
--
--   **Formalization Note** $H$ is the platform's `QAlgorithms.vnEntropy` (in bits). The ensemble is a `PureEnsemble` of the platform's P08 bundle (any finite number of members, weights may be zero). $N$ is a bare map on matrices; the channel property is a hypothesis of the statements.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Eq. (1), p. 3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Eq. (1), p.3: the objective
`H(N(Σ_i p_i |v_i⟩⟨v_i|)) − Σ_i p_i H(N(|v_i⟩⟨v_i|))` of the Holevo capacity, evaluated at one
pure-state ensemble `{p_i, |v_i⟩}` ("where the maximization is over ensembles {p_i, |v_i⟩}
where Σ_i p_i = 1 and |v_i⟩ ∈ H_in, the input space of the channel N").

**Formalization Note.** `H` is `QAlgorithms.vnEntropy`, the von Neumann entropy in bits. The
ensemble is a `PureEnsemble` of the published P08 bundle: finitely many weights `p_i ≥ 0` with
`Σ p_i = 1` and **unit** vectors `v_i` (so that `|v_i⟩⟨v_i|` is a state); zero weights are
allowed and contribute nothing. `N` is a bare map on matrices; the channel property is a
hypothesis of the statements that use it. -/
noncomputable def holevoValue {I O : Type} [Fintype I] [Fintype O] [DecidableEq O]
    (N : Superop I O) (e : PureEnsemble I) : ℝ :=
  vnEntropy (N (pureAverage e)) - ∑ x, e.prob x * vnEntropy (N (pureDensity (e.vector x)))

end ShorAdditivityEquiv


