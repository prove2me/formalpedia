-- Prove2me | Definitions.Def_KallMayerSLP_SimpleRecourse_msrt
-- name    : KallMayerSLP_SimpleRecourse_msrt
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:12:27.292376+00:00
-- url     : https://prove2.me/theorems/de2750cd-8255-4c2d-9a69-56ed3f0e68f1
-- title:
--   Multiple simple recourse type (MSRT) function $\psi(z,\xi)$
-- statement:
--   For constants $\alpha_k,\beta_k,u_k,l_k$ ($k=0,\dots,K-1$) and $\gamma$, the **multiple simple recourse type function** is
--
--   $$
--   \psi(z,\xi) := \sum_{k=0}^{K-1}\bigl\{\alpha_k[\xi-z-u_k]^+ + \beta_k[\xi-z+l_k]^-\bigr\} - \gamma .
--   $$
--
--   It is piecewise linear and convex in $\xi-z$ with breakpoints $u_k$ and $-l_k$. It models a recourse constraint whose surplus and shortage costs increase in steps.
--
--   **Formalization Note** The admissibility conditions of Definition 2.4 are the separate predicate `IsMSRTData`, assumed in the theorems.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Definition 2.4, p.237 (PDF 246)

import Mathlib

namespace KallMayerSLP.SimpleRecourse

/-- **Multiple simple recourse type (MSRT) function, Definition 2.4.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Definition 2.4, p.237 (PDF 246):
`ψ(z, ξ) := Σ_{k=0}^{K−1} {α_k · [ξ − z − u_k]⁺ + β_k · [ξ − z + l_k]⁻} − γ`.

**Formalization Note.** `x⁺ = max x 0`, `x⁻ = max (−x) 0`. Index base `0` (`Fin K`). The
conditions on the constants (`IsMSRTData`) are hypotheses of the theorems. -/
def msrt {K : ℕ} (α β u l : Fin K → ℝ) (γ z ξ : ℝ) : ℝ :=
  ∑ k, (α k * (ξ - z - u k)⁺ + β k * (ξ - z + l k)⁻) - γ

end KallMayerSLP.SimpleRecourse


