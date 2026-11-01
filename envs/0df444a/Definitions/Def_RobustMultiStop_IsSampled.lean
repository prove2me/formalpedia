-- Prove2me | Definitions.Def_RobustMultiStop_IsSampled
-- name    : RobustMultiStop_IsSampled
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:29:25.987194+00:00
-- url     : https://prove2.me/theorems/cdf22d10-79ff-4c9d-a7b4-31af5673ceb0
-- title:
--   Value of a process at a random time, $V_\tau=\sum_{j\le N}1_{\{\tau=j\}}V_j$
-- statement:
--   For a process $V$, a random time $\tau:\Omega\to\mathbb N$ and a horizon $N$, a class $Z$ **is the value of $V$ at $\tau$** if
--
--   $$Z=\sum_{j=0}^{N}1_{\{\tau=j\}}V_j\qquad P\text{-a.s.}$$
--
--   This gives the stopped reward $H_\tau$ of (2.2) and, applied to $V_j=\rho_j(X)$, the stopped functional $\rho_\tau(X)=\sum_{j=t}^{T}1_{\{\tau=j\}}\rho_j(X)$ of Lemma 2.2.
--
--   **Formalization Note** The relation is stated as a property of a class $Z$; for a stopping time such a $Z$ exists and is unique. For times with $t\le\tau\le N$ a.s., the terms $j<t$ vanish a.s., so the sum from $0$ equals the paper's sum from $t$.
-- source:
--   Laeven, Schoenmakers, Schweizer & Stadje, Robust Multiple Stopping — A Pathwise Duality Approach, arXiv:2006.01802v2, (2.2), p.5 (H_τ) and Lemma 2.2, p.5 (ρ_τ(X) := Σ_{j=t}^T 1_{τ=j} ρ_j(X))

import Mathlib

open MeasureTheory

namespace RobustMultiStop

/-- The value of a process at a random time, `V_τ := Σ_{j ≤ N} 1_{τ = j} V_j`, Laeven,
Schoenmakers, Schweizer & Stadje, *Robust Multiple Stopping — A Pathwise Duality Approach*,
arXiv:2006.01802v2, the stopped reward `H_τ` of (2.2), p.5, and the stopped functional
`ρ_τ(X) := Σ_{j=t}^T 1_{τ=j} ρ_j(X)` of Lemma 2.2, p.5 (taken with `V j := ρ j X`).

`IsSampled N V τ Z` says that the class `Z` is the class of `ω ↦ Σ_{j=0}^{N} 1_{τ(ω) = j} V_j(ω)`.

**Formalization Note** The finite indicator sum is the paper's own form of `ρ_τ`. For the times used
in the mission (`t ≤ τ ≤ N` a.s.) the terms `j < t` vanish a.s., so the sum from `0` agrees with the
paper's sum from `t`. A class `Z` with this property exists whenever `τ` is a stopping time, and it
is unique. -/
def IsSampled {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    (N : ℕ) (V : ℕ → Ω →ₘ[P] ℝ) (τ : Ω → ℕ) (Z : Ω →ₘ[P] ℝ) : Prop :=
  (Z : Ω → ℝ) =ᵐ[P] fun ω => ∑ j ∈ Finset.range (N + 1), {ω' | τ ω' = j}.indicator (V j : Ω → ℝ) ω

end RobustMultiStop


