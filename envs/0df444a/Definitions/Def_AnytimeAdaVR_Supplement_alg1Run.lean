-- Prove2me | Definitions.Def_AnytimeAdaVR_Supplement_alg1Run
-- name    : AnytimeAdaVR_Supplement_alg1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:29:59.131692+00:00
-- url     : https://prove2.me/theorems/51af0994-5413-4b40-b650-783542c8b7b2
-- title:
--   Algorithm 1 — parameter-free optimization with a prescribed budget
-- statement:
--   **Algorithm 1** receives an initial point $x_{\mathrm{init}}\in\mathbb R^d$ and an integer budget $T\ge7$, and access to the stochastic gradient $g$. It sets $n=\lfloor T/7\rfloor$ and:
--
--   1. runs stage S from $x_{\mathrm{init}}$, then stage M from the endpoint of S, then stage D from the endpoint of M (each stage as in `alg1Stage`, on its own independent samples and coins), obtaining candidates $X_S,X_M,X_D$;
--   2. for each $i\in\{S,M,D\}$ forms the validation mean with $n$ fresh samples,
--   $$
--   \hat g_i=\frac1n\sum_{j=1}^n g\big(X_i;\xi^{\mathrm{val}}_{i,j}\big);
--   $$
--   3. returns $\hat x_T=X_{\hat\imath}$ for $\hat\imath\in\arg\min_{i}\|\hat g_i\|$, ties broken in the order S, M, D.
--
--   The algorithm does not use $L$, $\bar L$, $\sigma$, $\Delta_f$, or which oracle condition holds. It also reports the number of gradient evaluations it made.
--
--   **Formalization Note** The randomness is the published tape `AnytimeAdaVR.Tape`: stage $i$ reads samples $\omega_1(i,t)$ and coins $\omega_2(i,r)$, and validation of candidate $i$ reads samples $\omega_3(i,0,j)$, $j<n$. Under `tapeMeasure μ` these are independent, the samples have law $\mu$ and the coins are uniform. The algorithm is a `StateM ℕ` computation whose state counts gradient evaluations; $n$ is natural-number division `T / 7`.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41001434449aea8ba3a6ba5d66658a8f94ea9ffeebad36bbb903374006), Algorithm 1, p.5; eq. (7), p.5; tie order, p.6

import Mathlib
import Definitions.Def_AnytimeAdaVR_Tape
import Definitions.Def_AnytimeAdaVR_Supplement_alg1Stage

namespace AnytimeAdaVR.Supplement

open AnytimeAdaVR

/-- **Algorithm 1 (parameter-free optimization with a prescribed budget).** Jiang–Wang–Yang–Zhang–Li,
*Adaptive Variance Reduction across Smoothness and Noise Conditions* (preprint, 2026), Algorithm 1,
p.5, and eq. (7), p.5: "Require: Initial point xinit, integer budget T ≥ 7. n ← ⌊T/7⌋, Y ← xinit …
for i = S, M, D in this order do x_0 ← Y … Y ← x_n end for; for i ∈ {S, M, D} do
ĝ_i ← n^{−1} Σ_{j=1}^n g(X_i; ξ^val_{i,j}) using fresh samples; return X_î, where
î ∈ arg min_{i∈{S,M,D}} ‖ĝ_i‖", and p.6: "Ties use the order S, M, D."

`alg1Run g xinit T ω` runs the three stages (`alg1Stage`) in the order S, M, D, each starting at the
previous stage's endpoint (S at `xinit`), then validates the three candidates with `n` fresh
samples each and returns the candidate whose validation mean has the smallest norm, ties broken in
the order S, M, D. Its counter (started at `0`) is the number of gradient evaluations made.

Randomness is read from the tape `ω` of `AnytimeAdaVR.Tape`: stage `i` uses the samples
`ω.1 (i, t)` and the coins `ω.2.1 (i, r)`; the validation of candidate `i` uses the samples
`ω.2.2 (i, 0, j)`, `j < n`.

**Formalization Note.** The algorithm takes only the oracle `g`, `xinit`, `T` and the tape: not
`L`, `L̄`, `σ`, `∆f`, nor the applicable oracle condition. `n = T / 7` is natural-number division
(`⌊T/7⌋`). Under `AnytimeAdaVR.tapeMeasure` all used tape coordinates are independent, the samples
have the oracle's law and the coins are uniform on `[0, 1]`; unused coordinates are harmless. -/
noncomputable def alg1Run {d : ℕ} {Ξ : Type*}
    (g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d))
    (xinit : EuclideanSpace ℝ (Fin d)) (T : ℕ) (ω : Tape Ξ) :
    StateM ℕ (EuclideanSpace ℝ (Fin d)) := do
  let n := T / 7
  let (zS, XS) ← alg1Stage g .S n xinit (fun t => ω.1 (.S, t)) (fun r => ω.2.1 (.S, r))
  let (zM, XM) ← alg1Stage g .M n zS (fun t => ω.1 (.M, t)) (fun r => ω.2.1 (.M, r))
  let (_, XD) ← alg1Stage g .D n zM (fun t => ω.1 (.D, t)) (fun r => ω.2.1 (.D, r))
  let validate : Path → EuclideanSpace ℝ (Fin d) → StateM ℕ (EuclideanSpace ℝ (Fin d)) :=
    fun i X => do
      let s ← (List.range n).foldlM
        (fun acc j => do
          let q ← oracleQuery g X (ω.2.2 (i, 0, j))
          pure (acc + q)) 0
      pure (((n : ℝ)⁻¹) • s)
  let gS ← validate .S XS
  let gM ← validate .M XM
  let gD ← validate .D XD
  pure (if ‖gS‖ ≤ ‖gM‖ ∧ ‖gS‖ ≤ ‖gD‖ then XS
    else if ‖gM‖ ≤ ‖gD‖ then XM
    else XD)

end AnytimeAdaVR.Supplement


