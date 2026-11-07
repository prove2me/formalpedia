-- Prove2me | Definitions.Def_OnlineShadow_LogRate_successProb
-- name    : OnlineShadow_LogRate_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:21.867232+00:00
-- url     : https://prove2.me/theorems/1c8ef433-3836-4197-bea9-98e7a856706e
-- title:
--   Probability that all $m$ answers are within $\varepsilon$
-- statement:
--   Let $P$ be an online protocol on $n$ copies, $\mathrm{adv}$ an adaptive adversary, $\rho$ a $d\times d$ density matrix and $\varepsilon\in\mathbb R$. For an outcome sequence $o=(o_0,\dots,o_{m-1})$ run the interaction: in round $t$ the adversary chooses $A_t$ from the transcript of earlier (observable, answer) pairs, the protocol applies its Kraus operator $K_t$ for outcome $o_t$ and answers $\widehat\mu_t$. The outcome sequence has probability
--   $$\Pr(o)=\mathrm{Tr}\big(K_o\,\rho^{\otimes n}K_o^\dagger\big),\qquad K_o=K_{m-1}\cdots K_0 .$$
--   The **success probability** is
--   $$\mathrm{succ}_m(P,\rho,\mathrm{adv},\varepsilon)=\sum_{o:\ |\widehat\mu_t-\mathrm{Tr}(A_t\rho)|\le\varepsilon\ \text{for all }t<m}\Pr(o),$$
--   the probability that all $m$ answers are within $\varepsilon$ simultaneously, as required in Definition 1.1 and Theorem 1.2.
--
--
--   **Formalization Note** Traces are real parts of complex traces; $\rho^{\otimes n}$ is the published `ShadowTomography.UpperBound.tensorPow`.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1 and Theorem 1.2, p. 3

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_OnlineShadow_LogRate_Adversary
import Definitions.Def_OnlineShadow_LogRate_OnlineProtocol

open scoped Matrix

namespace OnlineShadow.LogRate

/-- The **success probability** of an online protocol `P` against the adversary `adv` over `m` rounds,
on `n` copies `ρ^{⊗n}` of the state `ρ` (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Definition 1.1 and Theorem 1.2, p.3): the probability
that every answer is within `ε`, `|μ̂⁽ᵗ⁾ − Tr(A⁽ᵗ⁾ρ)| ≤ ε` for all `t` simultaneously.

For an outcome sequence `o`, round `t` runs as follows: the adversary chooses `Aₜ` from the transcript
of earlier (observable, answer) pairs, the protocol applies `Kₜ := P.kraus hₜ Aₜ (o t)` and answers
`P.answer hₜ Aₜ (o t)`, where `hₜ` is the list of earlier (observable, outcome) pairs. The outcome
sequence has probability `Tr(K_o ρ^{⊗n} K_oᴴ)` with `K_o = K_{m−1} ⋯ K_0`.

**Formalization Note** Traces are real parts of complex traces. The fold carries the protocol history, the
transcript and the accumulated Kraus product (latest round on the left). -/
noncomputable def successProb {d n : ℕ} {O : Type} [Fintype O] (m : ℕ) (P : OnlineProtocol d n O)
    (ρ : Matrix (Fin d) (Fin d) ℂ) (adv : Adversary d) (ε : ℝ) : ℝ :=
  let run : (Fin m → O) → List (Matrix (Fin d) (Fin d) ℂ × O) × List (Matrix (Fin d) (Fin d) ℂ × ℝ) ×
      Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ := fun o =>
    (List.ofFn o).foldl
      (fun st ot =>
        let A := adv.obs st.2.1
        (st.1 ++ [(A, ot)], st.2.1 ++ [(A, P.answer st.1 A ot)], P.kraus st.1 A ot * st.2.2))
      ([], [], 1)
  haveI := Classical.propDecidable
  ∑ o : Fin m → O,
    if ∀ p ∈ (run o).2.1, |p.2 - (p.1 * ρ).trace.re| ≤ ε then
      ((run o).2.2 * ShadowTomography.UpperBound.tensorPow ρ n * ((run o).2.2)ᴴ).trace.re
    else 0

end OnlineShadow.LogRate


