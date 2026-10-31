-- Prove2me | Definitions.Def_RobustToDynamics_alpha2
-- name    : RobustToDynamics_alpha2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:34.146603+00:00
-- url     : https://prove2.me/theorems/fcbfb937-ca09-4872-a4a6-a058dd09dee3
-- title:
--   The outer level $\alpha_2$ of (2.16)
-- statement:
--   Let $M$ be a real $n\times n$ matrix and $l,u\in\mathbb R^n$ the bounds of a box $\{x: l_i\le x_i\le u_i\}$. Display (2.16) sets
--   $$
--   \alpha_2=\sum_{i=1}^n\sum_{j=1}^n\max\{|M_{ij}u_iu_j|,\ |M_{ij}l_il_j|,\ |M_{ij}u_il_j|,\ |M_{ij}l_iu_j|\}.
--   $$
--   Every $x$ in the box satisfies $x^TMx\le\alpha_2$, so a polyhedron inside the box lies in $E(\alpha_2)$.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, Theorem 2.7, proof, Step 2, display (2.16), p.15

import Mathlib

open Matrix

namespace RobustToDynamics

/-- **The outer-ellipsoid level `α₂` of (2.16).**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, Theorem 2.7, proof,
Step 2, display (2.16), p.15:
"α2 = ∑_{i=1}^{n} ∑_{j=1}^{n} max{|Mi,juiuj|, |Mi,jlilj|, |Mi,juilj|, |Mi,jliuj|}",
for box bounds `lᵢ ≤ xᵢ ≤ uᵢ`.

**Formalization Note.** `l u : Fin n → ℝ` are the lower and upper box bounds; the four-term max
is written with binary `max`. -/
def alpha2 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (l u : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, max (max |M i j * u i * u j| |M i j * l i * l j|)
    (max |M i j * u i * l j| |M i j * l i * u j|)

end RobustToDynamics


