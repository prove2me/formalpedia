-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_IM
-- name    : BauerleRiederMDP_TransactionCosts_IM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:26:16.997492+00:00
-- url     : https://prove2.me/theorems/2dd7e6ab-6730-46dd-a8ab-b72ad80737a6
-- title:
--   The set $\mathbb M$ of increasing, concave, $\gamma$-homogeneous functions in $\mathbb B_b^+$
-- statement:
--   With the upper bounding function $b(x)=1+x_0+x_1$ of Proposition 4.5.1,
--   $$\mathbb M:=\{v\in\mathbb B^+_b : v\text{ is increasing, concave and homogeneous of degree }\gamma\},$$
--   where $\mathbb B^+_b=\{v\in\mathbb M(E): v^+(x)\le C\,b(x)\text{ for all }x\in E\text{ and some }C\in\mathbb R_+\}$ and $\mathbb M(E)$ is the set of measurable $v:E\to[-\infty,\infty)$.
--
--   **Formalization Note** Measurability is that of the restriction of $v$ to $E$. The bound $v^+\le Cb$ is written $v\le Cb$, which is equivalent and excludes the value $+\infty$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.5, p.107 (PDF 121); §2.4, p.29 (PDF 44); §2.3, p.19 (PDF 34)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace
import Definitions.Def_BauerleRiederMDP_TransactionCosts_IncreasingOnE
import Definitions.Def_BauerleRiederMDP_TransactionCosts_ConcaveOnE
import Definitions.Def_BauerleRiederMDP_TransactionCosts_HomogeneousOfDegree

namespace BauerleRiederMDP.TransactionCosts

/-- The set `IM := {v ∈ IB⁺_b | v is increasing, concave and homogeneous of degree γ}` of
Bäuerle & Rieder (2011), §4.5, p.107 (PDF 121), for the upper bounding function
`b(x) := 1 + x₀ + x₁` of Proposition 4.5.1. Here (p.29, PDF 44, and p.19, PDF 34)
`IB⁺_b := {v ∈ IM(E) | v⁺(x) ≤ C b(x) for all x ∈ E and some C ∈ ℝ₊}` and
`IM(E) := {v : E → [−∞, ∞) | v measurable}`.

**Formalization Note.** `v` is `EReal`-valued; measurability is that of the restriction of `v`
to `E` (subtype σ-algebra), so values off `E` play no role. `v⁺ ≤ C b` is written `v ≤ C b`
(equivalent since `C b ≥ 0`), which also excludes the value `+∞` on `E`. The book defines
"homogeneous of degree γ" for functions `v : E → ℝ` (p.107), so the elements of `IM` are
real-valued on `E`: the value `−∞` is excluded by `v x ≠ ⊥` for `x ∈ E`. -/
def IM (γ : ℝ) (v : ℝ × ℝ → EReal) : Prop :=
  Measurable (stateSpace.domRestrict v) ∧ (∀ x ∈ stateSpace, v x ≠ ⊥) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ stateSpace, v x ≤ ((C * (1 + x.1 + x.2) : ℝ) : EReal)) ∧
  IncreasingOnE v ∧ ConcaveOnE v ∧ HomogeneousOfDegree γ v

end BauerleRiederMDP.TransactionCosts


