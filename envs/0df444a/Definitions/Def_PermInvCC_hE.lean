-- Prove2me | Definitions.Def_PermInvCC_hE
-- name    : PermInvCC_hE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:00.507258+00:00
-- url     : https://prove2.me/theorems/ffe789c5-6fd9-4545-ba65-e451bed9d87c
-- title:
--   Cut separation $h_E(T,U)$ and type separation $h(T,U)=\max_E h_E(T,U)$
-- statement:
--   For tables $T,U$ and a set of cells $E$ write $T(E)=\sum_{e\in E}T_e$. The **cut separation** is
--   $$h_E(T,U)^2:=\frac{\sum_{e\in E}\bigl(\sqrt{T_e}-\sqrt{U_e}\bigr)^2}{T(E)+U(E)},$$
--   a ratio with zero denominator being assigned the value $0$, and the **type-separation parameter** is
--   $$h(T,U):=\max_{E\in\mathcal E}h_E(T,U). \tag{2.3}$$
--
--   $h(T,U)\in(0,1]$ for $T\ne U$; it is the quantity that governs both the classical upper bound and the quantum lower bound.
--
--   **Formalization Note** Real division by zero is $0$ in Lean, which is the paper's convention; $h_E$ is the nonnegative root. The paper defines $h_E$ for tables with the same margins; the formula is evaluated for any two tables. The maximum is a supremum over the finite, nonempty family $\mathcal E$.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.4, eq. (2.3), p.10

import Mathlib
import Definitions.Def_PermInvCC_cutEvents

namespace PermInvCC

/-- `T(E) = ∑_{e ∈ E} T_e`, the total count of a table on a set of cells (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, eq. (2.3), p.10). -/
def cellSum {q : ℕ} (E : Finset (Fin q × Fin q)) (T : Fin q → Fin q → ℕ) : ℕ :=
  ∑ e ∈ E, T e.1 e.2

/-- The **cut separation** `h_E(T, U)` (arXiv:2609.40116, held version sha256 fe1797dd…,
Definition 2.4, eq. (2.3), p.10):
`h_E(T, U)² = ∑_{e∈E} (√T_e − √U_e)² / (T(E) + U(E))`, a ratio with zero denominator being `0`.

**Formalization Note.** Real division by `0` is `0` in Lean, which is exactly the paper's
zero-denominator convention; `h_E` is the nonnegative square root. The paper defines `h_E` for
tables with the same margins; the formula is evaluated for any two tables. -/
noncomputable def hE {q : ℕ} (E : Finset (Fin q × Fin q)) (T U : Fin q → Fin q → ℕ) : ℝ :=
  Real.sqrt ((∑ e ∈ E, (Real.sqrt (T e.1 e.2) - Real.sqrt (U e.1 e.2)) ^ 2) /
    ((cellSum E T : ℝ) + cellSum E U))

/-- The **type-separation parameter** `h(T, U) = max_{E ∈ 𝓔} h_E(T, U)` (Definition 2.4,
eq. (2.3), p.10).

**Formalization Note.** The supremum runs over the finite set `𝓔 = cutEvents q`, which is
nonempty for `q ≥ 1` (it contains the set of all cells), so the real `⨆` is the maximum. -/
noncomputable def hTU {q : ℕ} (T U : Fin q → Fin q → ℕ) : ℝ :=
  ⨆ E : cutEvents q, hE E.1 T U

end PermInvCC


