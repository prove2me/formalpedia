-- Prove2me | Definitions.Def_CoCoNet_Lmat
-- name    : CoCoNet_Lmat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:59.777934+00:00
-- url     : https://prove2.me/theorems/88c98edd-f274-4c49-a436-f3af00d9b19e
-- title:
--   The matrix $L_{B,C}=I+\mathrm{Diag}(m_B)+(I-W)\mathrm{Diag}(m_C)$
-- statement:
--   For sets of banks $B,C\subseteq[n]$,
--   $$L_{B,C}=I+\mathrm{Diag}(m_B)+(I-W)\,\mathrm{Diag}(m_C),$$
--   where $\mathrm{Diag}(v)$ is the diagonal matrix with diagonal $v$ and $m_B$ is $m$ restricted to $B$. For a partition $(B,C,H)$ the equilibrium equations (1)–(2) read $a=L_{B,C}s+(I-W)c_H$.
--
--   **Formalization Note** Defined for arbitrary, possibly overlapping $B$, $C$, since Lemma 5 (p.34) uses $L_{B,C}$ "for any $B,C\subseteq[n]$".
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §2, p.11, after (3)

import Mathlib
import Definitions.Def_CoCoNet_restrictTo

namespace CoCoNet

/-- **The matrix `L_{B,C} = I + Diag(m_B) + (I − W) Diag(m_C)`.**
Balter, Schweizer & Vera, arXiv:2011.06474v1, §2, p.11, after (3): "we have a = L_{B,C}s + b_H
where L_{B,C} = I + Diag(m_B) + (I − W) Diag(m_C) and b_H = (I − W)c_H."

**Formalization Note.** Defined for arbitrary `B C : Finset (Fin n)`, not only for blocks of a
partition, since Lemma 5 (p.34) speaks of `L_{B,C}` "for any B, C ⊆ [n]". `Diag` is
`Matrix.diagonal`, `m_B` is `restrictTo B m`. -/
noncomputable def Lmat {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (B C : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  1 + Matrix.diagonal (restrictTo B m) + (1 - W) * Matrix.diagonal (restrictTo C m)

end CoCoNet


