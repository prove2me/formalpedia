-- Prove2me | Definitions.Def_TeschlQM_TraceClass_schattenClass
-- name    : TeschlQM_TraceClass_schattenClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:24:49.586989+00:00
-- url     : https://prove2.me/theorems/35d675a5-dd92-4c0a-83cb-4a56c7cb85e7
-- title:
--   Schatten p-classes 𝔍_p(ℌ), Hilbert–Schmidt and trace class operators, Eqs. (6.14), (6.20)
-- statement:
--   Let $\mathfrak{H}$ be a complex Hilbert space. The **Schatten $p$-class** is
--   $$\mathcal{J}_p(\mathfrak{H}) = \{K \in \mathfrak{C}(\mathfrak{H}) \mid \|K\|_p < \infty\},$$
--   where $\mathfrak{C}(\mathfrak{H})$ is the set of compact operators and $\|K\|_p = (\sum_j s_j(K)^p)^{1/p}$. A compact operator is **Hilbert–Schmidt** if $\sum_j s_j(K)^2 < \infty$, i.e. $K \in \mathcal{J}_2(\mathfrak{H})$, and **trace class** if $\sum_j s_j(K) < \infty$, i.e. $K \in \mathcal{J}_1(\mathfrak{H})$.
--
--   **Formalization Note.** `schattenClass H p` is the set above, `IsHilbertSchmidt K` is `K ∈ schattenClass H 2` and `IsTraceClass K` is `K ∈ schattenClass H 1`. Compactness is part of the definition, as in the book.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 140, Eq. (6.14); p. 141, Eq. (6.20); p. 142

import Mathlib
import Definitions.Def_TeschlQM_Shared_compactOperators
import Definitions.Def_TeschlQM_TraceClass_schattenNorm

namespace TeschlQM.TraceClass

open scoped ENNReal

/-- Teschl (6.20), p. 141: the **Schatten `p`-class** `𝔍_p(ℌ) = {K ∈ ℭ(ℌ) | ‖K‖_p < ∞}`. -/
def schattenClass (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (p : ℝ) : Set (H →L[ℂ] H) :=
  {K | K ∈ TeschlQM.Shared.compactOperators H ∧ schattenNorm p K < ⊤}

/-- Teschl (6.14), p. 140: a compact operator `K` is **Hilbert–Schmidt** if `∑_j s_j(K)² < ∞`,
i.e. `K ∈ 𝔍_2(ℌ)` (p. 142). -/
def IsHilbertSchmidt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : H →L[ℂ] H) : Prop :=
  K ∈ schattenClass H 2

/-- Teschl, p. 142: `𝔍_1(ℌ)` is the space of **trace class** operators, i.e. compact operators with
`∑_j s_j(K) < ∞`. -/
def IsTraceClass {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : H →L[ℂ] H) : Prop :=
  K ∈ schattenClass H 1

end TeschlQM.TraceClass


