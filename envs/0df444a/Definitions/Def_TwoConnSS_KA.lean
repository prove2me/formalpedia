-- Prove2me | Definitions.Def_TwoConnSS_KA
-- name    : TwoConnSS_KA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:42.799861+00:00
-- url     : https://prove2.me/theorems/dfcd8fdd-82c8-4cc1-8241-58ede47ee872
-- title:
--   The counts $m_4$, $m_{\ne 4}$ and the budget $K_A$ of the initial cover
-- statement:
--   For the initial cover $S_0$, $m_4$ is the number of its edges lying in 4-cycle components and $m_{\ne 4} = |S_0| - m_4$ the number of the others. These are edge counts, not numbers of components. The initial budget of Algorithm A is
--   $$K_A = \tfrac54 m_4 + \tfrac{11}{9} m_{\ne 4}.$$
--
--   The final ratio of the paper is a weighted comparison of bounds expressed in these counts.
--
--   **Formalization Note** $m_4$ and $m_{\ne 4}$ are defined as two complementary edge counts, so $m_4 + m_{\ne 4} = |S_0|$ without natural-number subtraction.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1.2, p.35; §8.2.3, p.55

import Mathlib
import Definitions.Def_TwoConnSS_blocks

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- `m₄`: the number of edges of `S₀` in 4-cycle components (p.35). -/
noncomputable def m4 (S₀ : Finset (Sym2 V)) : ℕ :=
  (S₀.filter fun e => ∃ C, IsCycleComp S₀ C 4 ∧ e ∈ edgesIn S₀ C).card

/-- `m_{≠4} = |S₀| − m₄`: the number of edges of `S₀` outside 4-cycle components (p.35). -/
noncomputable def mNe4 (S₀ : Finset (Sym2 V)) : ℕ :=
  (S₀.filter fun e => ¬ ∃ C, IsCycleComp S₀ C 4 ∧ e ∈ edgesIn S₀ C).card

/-- **The initial assignment-A budget** `K_A = (5/4)m₄ + (11/9)m_{≠4}`.
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.1.2, p.35: "For the initial
cover S0, let m4 be the number of its edges in 4-cycle components and let m≠4 = |S0| − m4. These
are edge counts"; §8.2.3, p.55: "KA := (5/4)m4 + (11/9)·m≠4".

**Formalization Note.** `m₄` and `m_{≠4}` are defined as two complementary edge counts, so
`m₄ + m_{≠4} = |S₀|` with no natural-number subtraction. They always refer to the initial cover
`S₀` (after 4-cycle merging), which is an argument. -/
noncomputable def KA (S₀ : Finset (Sym2 V)) : ℚ :=
  5 / 4 * (m4 S₀ : ℚ) + 11 / 9 * (mNe4 S₀ : ℚ)

end TwoConnSS


