-- Prove2me | Definitions.Def_OptGaussTomo_Learns
-- name    : OptGaussTomo_Learns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:05:51.882336+00:00
-- url     : https://prove2.me/theorems/2a1e257b-eb76-4946-aa59-7762afa14433
-- title:
--   Successful $n$-copy tomography of a class of states
-- statement:
--   Let $\mathcal C$ be a class of density operators on $\ell^2(I)$, $\mathrm{dist}$ a distance (purified or trace distance), $n\in\mathbb N$ and $\varepsilon,\delta\in\mathbb R$. We say that **$\mathcal C$ can be learned from $n$ copies to accuracy $\varepsilon$ with failure probability $\delta$** if there is a single POVM on $\ell^2(I)^{\otimes n}$ whose outcome is a density operator $\hat\rho$ (the estimate) such that for **every** $\rho\in\mathcal C$, when the measurement is applied to $\rho^{\otimes n}$,
--
--   $$
--   \Pr\big[\mathrm{dist}(\rho,\hat\rho)\le\varepsilon\big]\ \ge\ 1-\delta .
--   $$
--
--   **Formalization Note** The measurement is the published `BosonicLearn.FockPOVM` and $\rho^{\otimes n}$ the published `WildeQIT.Schumacher.tensorPow`. The outcome space is the space of density operators with its trace-norm Borel $\sigma$-algebra. Any measurement followed by classical (randomized) post-processing is again a POVM with state-valued outcomes, so every tomography protocol is covered. The measurement is chosen before, and does not depend on, the unknown state.
-- source:
--   Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, Optimal tomography of bosonic and fermionic Gaussian states, arXiv:2607.11847 (held version, sha256 0f7548a2a5cfd55079e5d7f1787c97c8561a818a53d7e29824715104bad416ed), §1 p.2 (pdf p.2) and p.3; §C.5 p.40

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_WildeQIT_Schumacher_tensorPow
import Definitions.Def_BosonicLearn_FockPOVM

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)

namespace OptGaussTomo

/-!
# Successful n-copy tomography of a class of states

Chen, Fanizza, Girardi, Lami, Mele, Walter, Witteveen, *Optimal tomography of bosonic and
fermionic Gaussian states*, arXiv:2607.11847 (held version, sha256 0f7548a2…), §1, p.2: "given
access to independent copies of an unknown quantum state ρ, determine an accurate estimate ρ̂ of
ρ … the minimal number of copies or samples n needed to achieve a desired accuracy ε with
probability at least 1 − δ"; p.3 (purified and trace distance); §C.5, p.40 ("Such a procedure is
described by a POVM μ").

`Learns cls dist n ε δ` says: there is one measurement on `n` copies, fixed before the unknown
state, whose outcome is an estimate `ρ̂` (a density operator) such that for **every** `ρ` in
`cls`, on input `ρ^{⊗n}` the event `dist(ρ, ρ̂) ≤ ε` has probability at least `1 − δ`.

**Formalization Note.** The measurement is the published `BosonicLearn.FockPOVM` (effects between
`0` and `I` summing to `I`, with the Born law on densities) and `ρ^{⊗n}` is the published
`WildeQIT.Schumacher.tensorPow` (coefficients `∏ₜ ρ (x t) (y t)` on `Fin n → I`; one-point basis at
`n = 0`). The outcome space is the published `State I` with its trace-norm Borel
σ-algebra. Any measurement followed by classical (randomized) post-processing is again a POVM
with outcomes in the state space, so every tomography protocol is covered. The measurement does
not depend on `ρ`. The probability is the outcome law of the POVM on `ρ^{⊗n}`; the event is
trace-norm closed for the distances used here.
-/

/-- Some `n`-copy POVM with state-valued outcomes estimates every `ρ ∈ cls` to
`dist(ρ, ρ̂) ≤ ε` with probability at least `1 − δ`. -/
def Learns {I : Type} [DecidableEq I] (cls : Set (State I))
    (dist : Matrix I I ℂ → Matrix I I ℂ → ℝ) (n : ℕ) (ε δ : ℝ) : Prop :=
  ∃ E : BosonicLearn.FockPOVM (Fin n → I) (State I), ∀ ρ ∈ cls,
    ENNReal.ofReal (1 - δ) ≤
      E.law (WildeQIT.Schumacher.tensorPow n ρ.coefficients) {σ | dist ρ.coefficients σ.coefficients ≤ ε}

end OptGaussTomo


