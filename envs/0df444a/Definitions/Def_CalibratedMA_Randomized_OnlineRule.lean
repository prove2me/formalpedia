-- Prove2me | Definitions.Def_CalibratedMA_Randomized_OnlineRule
-- name    : CalibratedMA_Randomized_OnlineRule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:53.465204+00:00
-- url     : https://prove2.me/theorems/850beffb-d4d9-4b3b-b41e-6563f11a75a3
-- title:
--   Appendix D — the exponential-potential online prediction rule of Lemma 3.1
-- statement:
--   Let $N\ge1$ and let $\Phi$ be a finite nonempty class of tests $\phi:\mathcal X\times[0,1]\to[-1,1]$. Put $\mathcal F=\Phi\times\{-1,1\}$, $\psi_{(\phi,\sigma)}=\sigma\phi$, $D=|\mathcal F|=2|\Phi|$ and
--   $$\eta=\min\Big\{1,\sqrt{\tfrac{\log D}{N}}\Big\}.$$
--   Before round $t$ the rule keeps the residual sums $R_{t-1}(f)=\sum_{s<t}\psi_f(X_s,S_s)(Y_s-S_s)$, $f\in\mathcal F$. On the context $X_t=x$ it forms
--   $$H_t(p)=\sum_{f\in\mathcal F}\exp\big(\eta R_{t-1}(f)\big)\,\psi_f(x,p),$$
--   and predicts the smallest zero of $H_t$ in $[0,1]$ if there is one. Otherwise it predicts $1$ if $H_t>0$ on $[0,1]$ and $0$ if $H_t<0$ on $[0,1]$. The prediction rule $s_t:\mathcal X\to[0,1]$ is a deterministic function of the earlier examples $(X_s,Y_s)_{s<t}$, the earlier predictions being recomputed by the same rule, and $S_t=s_t(X_t)$ is made before $Y_t$ is observed.
--
--   This is the online learner that Algorithm 1 runs on its training sample (step 3), with $N=n$ and $\Phi=\Phi_{\mathcal G,\mathcal A}$.
--
--   **Formalization Note.** Tests are `X → ℝ → ℝ`, signs $\sigma$ are booleans, and rounds are indexed $t=0,\dots,N-1$ on a sequence `z : Fin N → X × ℝ`. The smallest zero is `sInf {p ∈ [0,1] | H p = 0}`. When $H$ has no zero, the rule tests the sign of $H(0)$: for continuous $H$ the intermediate value theorem makes this the sign of $H$ on all of $[0,1]$.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026), pp. 51–52, Appendix D (proof of Lemma 3.1, the online prediction rule)

import Mathlib

namespace CalibratedMA.Randomized

/-! # Appendix D — the online prediction rule of Lemma 3.1

Lu, Noarov, Roth, *Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity*,
STOC 2027 submission #900, Appendix D, pp. 51–52.

Tests are `ϕ : X → ℝ → ℝ` (only their values on `X × [0,1]` matter), collected in a finite set
`Φ`. The signed family is `F = Φ × {−1, 1}`, with `ψ_{(ϕ,σ)} = σ ϕ`, stored with `σ : Bool`
(`true ↦ +1`, `false ↦ −1`), and `D = |F| = 2|Φ|`. Rounds are indexed `t = 0, …, N − 1`
(the paper's rounds `1, …, N`); the examples are `z : Fin N → X × ℝ`. -/

variable {X : Type*}

/-- The sign `σ ∈ {−1, 1}` encoded by a boolean. -/
def sgnB (b : Bool) : ℝ := if b then 1 else -1

/-- The learning rate `η = min{1, √(log D / N)}` with `D = 2|Φ|`. -/
noncomputable def eta (N : ℕ) (Φ : Finset (X → ℝ → ℝ)) : ℝ :=
  min 1 (Real.sqrt (Real.log (2 * (Φ.card : ℝ)) / N))

/-- The potential `H(p) = Σ_{f ∈ F} exp(η R(f)) ψ_f(x, p)` built from the residual sums `R`. -/
noncomputable def potential (N : ℕ) (Φ : Finset (X → ℝ → ℝ)) (R : (X → ℝ → ℝ) → Bool → ℝ)
    (x : X) (p : ℝ) : ℝ :=
  ∑ ϕ ∈ Φ, ∑ b : Bool, Real.exp (eta N Φ * R ϕ b) * (sgnB b * ϕ x p)

open Classical in
/-- The prediction on context `x` from residual sums `R`: the smallest zero of `H` on `[0,1]`
if `H` has a zero there; otherwise `1` if `H(0) > 0` (then `H > 0` on `[0,1]`, by the
intermediate value theorem for continuous `H`) and `0` otherwise (then `H < 0` on `[0,1]`). -/
noncomputable def predictFrom (N : ℕ) (Φ : Finset (X → ℝ → ℝ)) (R : (X → ℝ → ℝ) → Bool → ℝ)
    (x : X) : ℝ :=
  let H := potential N Φ R x
  if (∃ p ∈ Set.Icc (0 : ℝ) 1, H p = 0) then sInf {p ∈ Set.Icc (0 : ℝ) 1 | H p = 0}
  else if 0 < H 0 then 1 else 0

/-- The residual sums `R_t(f) = Σ_{s < t} ψ_f(X_s, S_s)(Y_s − S_s)` after the first `t` rounds,
where `S_s` is the prediction the rule made in round `s` (computed recursively). Rounds `t ≥ N`
add nothing. -/
noncomputable def residSums (N : ℕ) (Φ : Finset (X → ℝ → ℝ)) (z : Fin N → X × ℝ) :
    ℕ → ((X → ℝ → ℝ) → Bool → ℝ)
  | 0 => fun _ _ => 0
  | t + 1 =>
    let R := residSums N Φ z t
    if ht : t < N then
      let x := (z ⟨t, ht⟩).1
      let y := (z ⟨t, ht⟩).2
      let S := predictFrom N Φ R x
      fun ϕ b => R ϕ b + sgnB b * ϕ x S * (y - S)
    else R

/-- The prediction rule `s_t : X → ℝ` used in round `t` (0-indexed): a deterministic function of
the examples of rounds `< t`. -/
noncomputable def onlineRule (N : ℕ) (Φ : Finset (X → ℝ → ℝ)) (z : Fin N → X × ℝ) (t : ℕ) :
    X → ℝ :=
  predictFrom N Φ (residSums N Φ z t)

/-- The prediction `S_t = s_t(X_t)` made in round `t`, before `Y_t` is observed. -/
noncomputable def onlineScore (N : ℕ) (Φ : Finset (X → ℝ → ℝ)) (z : Fin N → X × ℝ)
    (t : Fin N) : ℝ :=
  onlineRule N Φ z t (z t).1

end CalibratedMA.Randomized


