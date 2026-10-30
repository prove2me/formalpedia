-- Prove2me | Definitions.Def_FuchsVdGraaf_entropy
-- name    : FuchsVdGraaf_entropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:18.405363+00:00
-- url     : https://prove2.me/theorems/0a1ac233-a4d1-49c2-9ac0-75a176704741
-- title:
--   Shannon entropy of a finite distribution, in bits
-- statement:
--   For a probability distribution $p$ on a finite set $\mathcal X$, the **Shannon entropy** is
--
--   $$
--   H(p) = -\sum_{x\in\mathcal X} p(x)\log_2 p(x),
--   $$
--
--   with the convention $0\log 0 = 0$. The logarithm is to base $2$: the paper records $H(T) = 1$ for a fair coin $T$.
--
--   **Formalization Note** The convention $0\log 0 = 0$ holds automatically since Mathlib sets $\log_2 0 = 0$. The formula is the one of the published `WildeQIT.entropy`, written on a plain function rather than on the `WildeQIT.FinDist` structure so that it applies directly to the outcome distribution of a measurement.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, §4.4, p.15

import Mathlib

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, §4.4, p.15: the Shannon entropy
`H(p) = −∑_{x∈X} p(x) log p(x)` of a distribution on a finite set, in bits (the page's
`H(T) = 1` for a fair coin fixes base 2), with `0 log 0 = 0`.

**Formalization Note.** `Real.logb 2 0 = 0` gives the convention `0 log 0 = 0`. The body is that
of the published `WildeQIT.entropy`, written on a plain function `X → ℝ` instead of the
`WildeQIT.FinDist` structure so that it applies directly to outcome distributions of a POVM. -/
noncomputable def entropy {X : Type} [Fintype X] (p : X → ℝ) : ℝ :=
  -∑ x, p x * Real.logb 2 (p x)

end FuchsVdGraaf


