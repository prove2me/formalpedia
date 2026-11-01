-- Prove2me | Definitions.Def_ShorAdditivityEquiv_holevoCapacity
-- name    : ShorAdditivityEquiv_holevoCapacity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:29:55.711739+00:00
-- url     : https://prove2.me/theorems/6975e3b0-a2e8-4d7b-bf1e-abb1b1a996e5
-- title:
--   Holevo capacity $\chi_N$ of a channel (Eq. (1))
-- statement:
--   For a quantum channel $N$ with input space $\mathcal H_{\mathrm{in}}$, the Holevo capacity is
--   $$
--   \chi_N = \max_{\{p_i,|v_i\rangle\}} H\Big(N\big(\textstyle\sum_i p_i|v_i\rangle\langle v_i|\big)\Big) - \sum_i p_i\,H\big(N(|v_i\rangle\langle v_i|)\big),
--   $$
--   "where the maximization is over ensembles $\{p_i,|v_i\rangle\}$ where $\sum_i p_i=1$ and $|v_i\rangle\in\mathcal H_{\mathrm{in}}$, the input space of the channel $N$". It is the classical capacity of $N$ when inputs entangled across channel uses are not allowed; its additivity $\chi_{N_1\otimes N_2}=\chi_{N_1}+\chi_{N_2}$ is statement (ii) of Theorem 1.
--
--   **Formalization Note** The maximum is the real supremum over all finite ensembles of **pure** states (unit vectors), exactly as in Eq. (1); it is not the mixed-ensemble quantity $\chi^*$. For a channel with a nonempty input space the values lie in $[0,\log_2 d_{\mathrm{out}}]$ and the supremum is attained. On a map that is not a channel the value may be a junk value; every statement assumes a channel.
-- source:
--   Shor, Equivalence of Additivity Questions in Quantum Information Theory, arXiv:quant-ph/0305035v4, Eq. (1), p. 3

import Mathlib
import Definitions.Def_ShorAdditivityEquiv_holevoValue

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P08

namespace ShorAdditivityEquiv

/-- Shor, *Equivalence of Additivity Questions in Quantum Information Theory*, arXiv:quant-ph/0305035v4, Eq. (1), p.3: the Holevo capacity of a channel `N`,
`χ_N = max_{p_i, |v_i⟩} H(N(Σ_i p_i |v_i⟩⟨v_i|)) − Σ_i p_i H(N(|v_i⟩⟨v_i|))`, the maximum over
all pure-state ensembles of the input space.

**Formalization Note.** The maximum is encoded as the real supremum `sSup` of the objective
`holevoValue N` over **all** finite pure-state ensembles (every number of members). For a
channel with a nonempty input space the set of values is nonempty and lies in
`[0, log₂ d_out]`, and the supremum is attained (Carathéodory bounds the ensemble size and the
unit sphere is compact), so `sSup` is the paper's maximum. The ensemble consists of pure states,
exactly as in Eq. (1); it is not the mixed-ensemble quantity χ*. -/
noncomputable def holevoCapacity {I O : Type} [Fintype I] [Fintype O] [DecidableEq O]
    (N : Superop I O) : ℝ :=
  sSup (Set.range (holevoValue N))

end ShorAdditivityEquiv


