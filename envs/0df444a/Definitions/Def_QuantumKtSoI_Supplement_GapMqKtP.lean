-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_GapMqKtP
-- name    : QuantumKtSoI_Supplement_GapMqKtP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:26:35.349483+00:00
-- url     : https://prove2.me/theorems/5aa04076-69f6-4ce7-b4e9-5d315d6256c9
-- title:
--   The gap problem $\mathrm{Gap\text{-}MqKtP}[c,s]$ (Definition 4.12) and its clipped thresholds
-- statement:
--   For a measure $\mu$ of strings and $c,s:\mathbb N\to\mathbb N$, the promise problem $\mathrm{Gap\text{-}M}\mu\mathrm P[c,s]$ has, on inputs of length $N$,
--   $$\mathrm{YES}_N=\{x\in\{0,1\}^N:\mu(x)\le c(N)\},\qquad \mathrm{NO}_N=\{x\in\{0,1\}^N:\mu(x)>s(N)\}.$$
--   With $\mu=\mathrm{qKt}$ this is Definition 4.12. Whenever a statement writes $\mathrm{Gap\text{-}MqKtP}[c,N-2]$, the thresholds are the globally defined
--   $$s_{\mathrm{clip}}(N)=\max(N-2,0),\qquad c_{\mathrm{clip}}(N)=\min(c(N),s_{\mathrm{clip}}(N)),$$
--   which satisfy $c_{\mathrm{clip}}\le s_{\mathrm{clip}}$ at every length.
--
--   The measure is a parameter because Appendix F uses the same definition with $\mathrm{qKt}^{(c)}$ in place of $\mathrm{qKt}$.
--
--   **Formalization Note** The problem is returned as the pair of sets $(\mathrm{YES},\mathrm{NO})$; $\mu$ is real valued; truncated natural subtraction $N-2$ is $\max(N-2,0)$.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 4.12 and the clipped thresholds, p.49

import Mathlib

namespace QuantumKtSoI.Supplement

/-- **Definition 4.12** (Gap problem, p.49), for a measure `µ` of strings: `Gap-MqKtP[c, s]` has
`YES_N = {x ∈ {0,1}^N : µ(x) ≤ c(N)}` and `NO_N = {x ∈ {0,1}^N : µ(x) > s(N)}`; the pair
`(YES, NO)` is returned. With `µ(x) = qKt(x)` this is the paper's problem; Appendix F uses the same
definition with `qKt^{(c)}` in place of `qKt`. -/
def GapMqKtP (μ : List Bool → ℝ) (c s : ℕ → ℕ) : Set (List Bool) × Set (List Bool) :=
  ({x | μ x ≤ c x.length}, {x | (s x.length : ℝ) < μ x})

/-- The clipped thresholds of p.49 used whenever a statement writes `Gap-MqKtP[c, N − 2]`:
`s_clip(N) = max(N − 2, 0)` and `c_clip(N) = min(c(N), s_clip(N))`; the problem
`Gap-MqKtP[c_clip, s_clip]` is returned.

**Formalization Note** `N - 2` is truncated natural subtraction, which is `max(N − 2, 0)`. -/
def GapMqKtPClip (μ : List Bool → ℝ) (c : ℕ → ℕ) : Set (List Bool) × Set (List Bool) :=
  GapMqKtP μ (fun N => min (c N) (N - 2)) (fun N => N - 2)

end QuantumKtSoI.Supplement


