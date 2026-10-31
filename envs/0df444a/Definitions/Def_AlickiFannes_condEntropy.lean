-- Prove2me | Definitions.Def_AlickiFannes_condEntropy
-- name    : AlickiFannes_condEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:10.625928+00:00
-- url     : https://prove2.me/theorems/d8611e1b-f0db-4f6c-83e2-24218b5ad430
-- title:
--   Conditional information $S(\rho^{12}\mid\rho^2) = S(\rho^{12}) - S(\rho^2)$
-- statement:
--   Let $\mathfrak h^{12} = \mathfrak h_1 \otimes \mathfrak h_2$ be a finite-dimensional bipartite Hilbert space and $\rho^{12}$ a state on it, with restriction $\rho^2 = \operatorname{Tr}_1 \rho^{12}$ to the second system. The **conditional information** (or conditional entropy) of $\rho^{12}$ with respect to the second system is
--
--   $$
--   S(\rho^{12}\mid\rho^2) := S(\rho^{12}) - S(\rho^2),
--   $$
--
--   where $S(\rho) = -\operatorname{Tr}\rho\log_2\rho$ is the von Neumann entropy. Unlike its classical counterpart it can be negative (for an entangled pure state it equals $-S(\rho^2)$); it always lies between $-\log d_1$ and $\log d_1$, $d_1 = \dim\mathfrak h_1$.
--
--   **Formalization Note** The bipartite space is the index type `A × B`, the first factor `A` being $\mathfrak h_1$, the system traced out. The restriction $\rho^2$ is the published partial trace `QAlgorithms.traceLeft` ($(\operatorname{Tr}_A\rho)_{bb'} = \sum_a \rho_{(a,b),(a,b')}$) and $S$ is the published `QAlgorithms.vnEntropy` (base 2). The definition is total on matrices; the theorems assume density matrices.
-- source:
--   Alicki–Fannes, Continuity of quantum conditional information, arXiv:quant-ph/0312081v2, p.1 (definition of S(ρ¹²| ρ²)); p.2 ("also called conditional entropy")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble

namespace AlickiFannes

/-- Alicki–Fannes, *Continuity of quantum conditional information*, arXiv:quant-ph/0312081v2,
p.1: "The conditional information S(ρ¹²| ρ²) of ρ¹² with respect to the second system is the
quantity S(ρ¹²| ρ²) := S(ρ¹²) − S(ρ²)", where ρ² is the restriction of ρ¹² to the second system
and S is the von Neumann entropy (p.2: "S(ρ¹²| ρ²) is also called conditional entropy").

**Formalization Note.** The bipartite Hilbert space `𝔥¹² = 𝔥₁ ⊗ 𝔥₂` is finite dimensional
(p.1) and is represented by the index type `A × B`: the **first** factor `A` is `𝔥₁`, the
system that is traced out, and `B` is `𝔥₂`. The restriction `ρ²` is the published partial trace
`QAlgorithms.traceLeft ρ` (`(Tr_A ρ)_{b b'} = Σ_a ρ_{(a,b),(a,b')}`), and `S` is the published
`QAlgorithms.vnEntropy` (base-2 logarithm). The definition is total on matrices; the theorems
assume `ρ` is a density matrix. -/
noncomputable def condEntropy {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  QAlgorithms.vnEntropy ρ - QAlgorithms.vnEntropy (QAlgorithms.traceLeft ρ)

end AlickiFannes


