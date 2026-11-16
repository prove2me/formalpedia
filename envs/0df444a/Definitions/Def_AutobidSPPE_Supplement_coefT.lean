-- Prove2me | Definitions.Def_AutobidSPPE_Supplement_coefT
-- name    : AutobidSPPE_Supplement_coefT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:42:38.927448+00:00
-- url     : https://prove2.me/theorems/9ce276a3-6bfd-477e-b7e1-1ad93b4c8c09
-- title:
--   Rival-set spending coefficient $c_i(S)$
-- statement:
--   For a set $S$ of rivals of bidder $i$ let $M_S=\max_{j\in S}v_j$ ($M_\emptyset=0$) and $\psi_i(u)=u(1-u/\bar v_i)^+$. The **spending coefficient** is
--   $$
--   c_i(S)=\mathbb E\,\psi_i(M_S),
--   $$
--   under independent $v_j\sim\mathrm{Unif}[0,\bar v_j]$. It is bidder $i$'s expected spending conditional on its own participation when exactly the rivals in $S$ participate, and $B_i=\sum_S\pi_S(\alpha)c_i(S)$ (57).
--
--   **Formalization Note** Defined for every $S$; the paper uses it for $S\subseteq[n]\setminus\{i\}$.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §3.3, (57)–(58), p.27

import Mathlib
import Definitions.Def_AutobidSPPE_valueLaw
open MeasureTheory

namespace AutobidSPPE.Supplement

open AutobidSPPE

/-- The rival-set spending coefficient `cᵢ(S) = E ψᵢ(M_S)` (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), §3.3, p.27; (58)), with
`M_S = max_{j∈S} vⱼ` (`max ∅ = 0`) and `ψᵢ(u) = u(1 − u/v̄ᵢ)⁺`, the expectation under independent
`vⱼ ∼ Unif[0, v̄ⱼ]`. It is bidder `i`'s spending conditional on its own participation when exactly the
rivals in `S` participate.

**Formalization Note** Defined for every `S`; the paper uses it for `S ⊆ [n]∖{i}`. -/
noncomputable def coefT {n : ℕ} (vbar : Fin n → ℝ) (i : Fin n) (S : Finset (Fin n)) : ℝ :=
  ∫ v, (let M : ℝ := if h : S.Nonempty then S.sup' h v else 0
        M * max (1 - M / vbar i) 0) ∂(valueLaw vbar)

end AutobidSPPE.Supplement


