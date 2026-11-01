-- Prove2me | Definitions.Def_TSDRiem_Lmax
-- name    : TSDRiem_Lmax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:43.833681+00:00
-- url     : https://prove2.me/theorems/3326959d-d566-4d32-946d-851e78d33c0b
-- title:
--   $L_{\max}=\max_k L_k$
-- statement:
--   For block smoothness constants $L_1,\dots,L_m$,
--
--   $$
--   L_{\max}:=\max_{k\in[m]}L_k .
--   $$
--
--   The paper uses $L_{\max}$ in (11), Lemma 4.4 and Theorem 4.5 without defining it; the maximum is the value its proofs use.
--
--   **Formalization Note** Written as the supremum of finitely many reals, which is their maximum for $m\ge1$ (Lean gives $0$ at $m=0$).
-- source:
--   Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, eq. (11), p.10; Lemma 4.4, p.13; Theorem 4.5, p.14

import Mathlib

namespace TSDRiem

/-- `L_max := max_{k∈[m]} L_k`, the largest block smoothness constant of Assumption 4.1.

Gutman & Ho-Nguyen, Coordinate Descent Without Coordinates, arXiv:1912.10627v3, used in (11),
p.10, Lemma 4.4, p.13, and Theorem 4.5, p.14 (the paper does not define it; the maximum is the
reading its proofs force).

Formalization Note: the supremum of finitely many reals, which is their maximum when `m ≥ 1`
(at `m = 0` Lean's value is `0`; every statement that uses it with `m = 0` is checked to be
unaffected or assumes `1 ≤ m`). -/
noncomputable def Lmax {m : ℕ} (L : Fin m → ℝ) : ℝ := ⨆ k, L k

end TSDRiem


