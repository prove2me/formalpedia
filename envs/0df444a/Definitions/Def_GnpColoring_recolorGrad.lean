-- Prove2me | Definitions.Def_GnpColoring_recolorGrad
-- name    : GnpColoring_recolorGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:22.216842+00:00
-- url     : https://prove2.me/theorems/736e4ae1-e771-47a5-8a8c-3bb80a1b01b6
-- title:
--   The recoloring gradient $\nabla^c_\sigma f$
-- statement:
--   For a colour $c$, a colouring $\sigma$ and a vertex $s$,
--
--   $$\nabla^c_\sigma f(s)=\begin{cases}f(\sigma_{s\leftarrow c})-f(\sigma), & c\in A_s(\sigma),\\ 0,&\text{otherwise,}\end{cases}$$
--
--   where $\sigma_{s\leftarrow c}$ recolours $s$ with $c$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.3, p.17

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The recoloring gradient** `∇^c_σ f(s) = f(σ_{s←c}) − f(σ)` if `c ∈ A_s(σ)`, and `0` otherwise.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.3, p.17. -/
noncomputable def recolorGrad {n q : ℕ} (G : SimpleGraph (Fin n)) (f : (Fin n → Fin q) → ℝ) (c : Fin q)
    (σ : Fin n → Fin q) (s : Fin n) : ℝ :=
  if ∀ u, G.Adj s u → σ u ≠ c then f (Function.update σ s c) - f σ else 0

end GnpColoring


