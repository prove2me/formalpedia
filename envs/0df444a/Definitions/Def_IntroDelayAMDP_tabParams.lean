-- Prove2me | Definitions.Def_IntroDelayAMDP_tabParams
-- name    : IntroDelayAMDP_tabParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:03.536445+00:00
-- url     : https://prove2.me/theorems/4a7ee79b-ebf5-4613-892a-ac992448f5b7
-- title:
--   The parameters of Algorithm 1
-- statement:
--   For a constant $C$, a delay cap $\bar d$ and $S,A,H,K,\delta$:
--   $$\iota=2\log(CSAHK/\delta),\quad \nu=10\iota^2,\quad c_1=C\nu,\quad \eta=\min\Bigl\{\frac{1}{C^3H^2(\nu+H)(\iota+\bar d)},\sqrt{\frac{H\log A+\iota^3}{H^3(\nu+H)\iota SAK}}\Bigr\},$$
--   $$\gamma=\eta H^2,\quad\theta=C^2\eta H^2(\nu+H)\iota,\quad M=\lceil4\iota/\theta\rceil,\quad\beta=\log(16S^2AK/\delta).$$
--   Algorithm 1 uses $\bar d=0$; the paper keeps $\bar d$ so that Appendix C can reuse the parameters with $1\le\bar d\le K$.
--
--   **Formalization Note** $\log$ is natural. $\nu$ is a real number, since Algorithm 1 compares a count with it.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), App. A.1, p.30; Eq. (16), p.14

import Mathlib
import Definitions.Def_IntroDelayAMDP_AlgParams

namespace IntroDelayAMDP

/-- **The parameters of Algorithm 1** (App. A.1, p.30; Eq. (16), p.14). Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), printed p.30: "Let
`C` be a large enough universal constant, `ι ≜ 2 log(CSAHK/δ)`, and `d̄` the cap on the delays,
which is `0` for Algorithm 1 and only kept so that Appendix C can reuse the parameters with
`1 ≤ d̄ ≤ K`. We pick `ν = 10ι²`, `c₁ = Cν`, `η = min{1/(C³H²(ν + H)(ι + d̄)),
√((H log A + ι³)/(H³(ν + H)ιSAK))}`, `γ = ηH²`, `θ = C²ηH²(ν + H)ι`, and `M = ⌈4ι/θ⌉` … and
recall `β = log(16S²AK/δ)` from Eq. (16)."

`tabParams C d̄ S A H K δ` has exactly these fields, with `S, A, H, K, d̄` cast to reals.

**Formalization Note.** `log` is the natural logarithm. `ν` is a real number (Algorithm 1
compares a count with it). `M` is `Nat.ceil (4ι/θ)`. Algorithm 1 is run with `d̄ = 0`. -/
noncomputable def tabParams (C : ℝ) (dbar S A H K : ℕ) (δ : ℝ) : AlgParams :=
  let ι : ℝ := 2 * Real.log (C * S * A * H * K / δ)
  let ν : ℝ := 10 * ι ^ 2
  let η : ℝ := min (1 / (C ^ 3 * (H : ℝ) ^ 2 * (ν + H) * (ι + dbar)))
    (Real.sqrt ((H * Real.log A + ι ^ 3) / ((H : ℝ) ^ 3 * (ν + H) * ι * S * A * K)))
  let θ : ℝ := C ^ 2 * η * (H : ℝ) ^ 2 * (ν + H) * ι
  { iota := ι, nu := ν, c1 := C * ν, eta := η, gamma := η * (H : ℝ) ^ 2, theta := θ,
    M := Nat.ceil (4 * ι / θ), beta := Real.log (16 * (S : ℝ) ^ 2 * A * K / δ) }

end IntroDelayAMDP


