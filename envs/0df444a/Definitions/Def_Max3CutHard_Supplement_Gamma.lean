-- Prove2me | Definitions.Def_Max3CutHard_Supplement_Gamma
-- name    : Max3CutHard_Supplement_Gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:47:31.138344+00:00
-- url     : https://prove2.me/theorems/b083566d-98f7-4c9e-9d90-8bbcbac8c6a8
-- title:
--   $\Gamma_L=29+18L+3\binom L2$
-- statement:
--   For $L\in\mathbb N$ let
--
--   $$\Gamma_L=29+18L+3\binom L2 .$$
--
--   Its first values are $\Gamma_0,\dots,\Gamma_4=29,47,68,92,119$. Theorem 1.2 states that Max-$k$-Cut is NP-hard to approximate within $1-2/\Gamma_{k-3}+\varepsilon$; for $k=3$ this is the $27/29$ of Theorem 1.1.
--
--   **Formalization Note** A natural number, cast to $\mathbb R$ where it is used.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 1.2, p.1 (values: Proof of Theorem 1.2, p.11)

import Mathlib

namespace Max3CutHard.Supplement

/-- **`Γ_L = 29 + 18L + 3·binom(L, 2)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 1.2, p.1:
"where `Γ_L = 29 + 18L + 3 (L choose 2)`"; values `Γ_0, …, Γ_4 = 29, 47, 68, 92, 119` (Proof of
Theorem 1.2, p.11).

**Formalization Note.** A natural number; Theorem 1.2 casts it to `ℝ`. -/
def Gamma (L : ℕ) : ℕ := 29 + 18 * L + 3 * L.choose 2

end Max3CutHard.Supplement


