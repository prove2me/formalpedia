-- Prove2me | Definitions.Def_StochAutoreg_Learner
-- name    : StochAutoreg_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:50.721696+00:00
-- url     : https://prove2.me/theorems/56a9e612-b87e-402d-84ae-0814534b1a13
-- title:
--   Learner from $n$ samples
-- statement:
--   A **learner** from $n$ samples in a space $S$ is "a total measurable map on finite samples and random seeds; its behavior on samples outside the model may be arbitrary". Given the samples and a seed it outputs a predictor $\hat q:\Sigma^\star\to[0,1]$, which need not belong to any class. Zero-sample learners are allowed.
--
--   **Formalization Note** The seed is one point of $[0,1]$. Samples and prompts are discrete in this mission, so measurability is required in the seed, for each sample and each prompt.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.3

import Mathlib

namespace StochAutoreg

/-- A **learner** from `n` samples in `S`: "a total measurable map on finite samples and random seeds;
its behavior on samples outside the model may be arbitrary". It outputs a predictor `q̂ : Σ⋆ → [0,1]`,
which "need not belong" to any class. Zero-sample learners (`n = 0`) are allowed.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.3.

**Formalization Note.** The paper names no seed space; the seed is one uniform point of `[0,1]`, which
simulates any standard Borel seed. Samples and prompts live on countable discrete spaces in this
mission, so measurability is required in the seed, for each sample and each prompt. -/
structure Learner (S : Type) (n : ℕ) where
  /-- The predictor output on a sample and a seed. -/
  run : (Fin n → S) → unitInterval → List Bool → unitInterval
  /-- Measurability in the seed. -/
  measurable_seed : ∀ s x, Measurable fun u => run s u x

end StochAutoreg


