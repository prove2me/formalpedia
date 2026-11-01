-- Prove2me | Definitions.Def_TSDRiem_Lmin
-- name    : TSDRiem_Lmin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:45.992409+00:00
-- url     : https://prove2.me/theorems/05108488-3dc5-4422-84c5-89706e0e1e08
-- title:
--   $L_{\min}=\min_k L_k$
-- statement:
--   For block smoothness constants $L_1,\dots,L_m$,
--
--   $$
--   L_{\min}:=\min_{k\in[m]}L_k .
--   $$
--
--   The paper uses $L_{\min}$ in Lemma 4.3, Lemma 4.4 and Theorem 4.5 without defining it; the minimum is the value its proofs use.
--
--   **Formalization Note** Written as the infimum of finitely many reals, which is their minimum for $m\ge1$ (Lean gives $0$ at $m=0$).
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, Lemma 4.3, p.12; Lemma 4.4, p.13; Theorem 4.5, p.14

import Mathlib

namespace TSDRiem

/-- `L_min := min_{k∈[m]} L_k`, the smallest block smoothness constant of Assumption 4.1.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, used in
Lemma 4.3, p.12, Lemma 4.4, p.13, and Theorem 4.5, p.14 (the paper does not define it; the minimum
is the reading its proofs force).

Formalization Note: the infimum of finitely many reals, which is their minimum when `m ≥ 1`
(at `m = 0` Lean's value is `0`). -/
noncomputable def Lmin {m : ℕ} (L : Fin m → ℝ) : ℝ := ⨅ k, L k

end TSDRiem


