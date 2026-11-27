-- Prove2me | Definitions.Def_FreeOrderEPTAS_Supplement_PandoraInstance
-- name    : FreeOrderEPTAS_Supplement_PandoraInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:36:14.645969+00:00
-- url     : https://prove2.me/theorems/b60434ae-1a80-5e3d-a7ba-64fcfd8c32e5
-- title:
--   An instance of Pandora's Box with Commitment
-- statement:
--   An instance of **Pandora's Box with Commitment** consists of $n$ independent random variables $X_1,\dots,X_n$, given as an instance of Free-Order Prophets (laws $\mu_1,\dots,\mu_n$ on $[0,\infty)$ with finite means), together with a probing cost $c_i\in\mathbb R_+$ for each $X_i$.
--
--   An algorithm probes the boxes one at a time, paying $c_i$ to observe $X_i$, and on observing a value must decide at once whether to select it and stop.
--
--   **Formalization Note** The laws are the published Free-Order Prophets `Instance`; only the costs and their non-negativity are new.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §6.1, p.30

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Instance

namespace FreeOrderEPTAS.Supplement

/-- An instance of Pandora's Box with Commitment (Segev & Singla, arXiv:2007.13121v3, §6.1, p.30):
`n` independent non-negative random variables `X_1, …, X_n` with finite means, given by a base
Free-Order Prophets instance, and a probing cost `c_i ∈ ℝ_+` for each `X_i`.

**Formalization Note.** The laws are the published `FreeOrderEPTAS.Instance` (probability measures
on `ℝ` carried by `[0, ∞)`, integrable, independent through `Measure.pi`); only the costs are new. -/
structure PandoraInstance (n : ℕ) where
  /-- The laws of `X_1, …, X_n`. -/
  X : Instance n
  /-- The probing cost `c_i`. -/
  c : Fin n → ℝ
  /-- `c_i ∈ ℝ_+`. -/
  c_nonneg : ∀ i, 0 ≤ c i

end FreeOrderEPTAS.Supplement


