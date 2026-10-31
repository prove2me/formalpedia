-- Prove2me | Definitions.Def_ResistantSets_Diamond
-- name    : ResistantSets_Diamond
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:29.766024+00:00
-- url     : https://prove2.me/theorems/48af2ca0-34fb-42b3-b381-3ddc07047e3c
-- title:
--   Property $(\diamond)$ at a point
-- statement:
--   Let $S\subseteq\{0,1\}^n$. A point $x$ **satisfies $(\diamond)$** if
--   $$
--   x\text{ is feasible}\iff \mathbf 1-x\triangle e_n\text{ is feasible}\iff x\triangle e_n\text{ is infeasible}\iff \mathbf 1-x\text{ is infeasible}.
--   $$
--
--   Property $(\diamond)$ is the invariant propagated by the induction of Lemma 5.4.
--
--   **Formalization Note** The definition takes the coordinate $c$ playing the role of $n$ as a parameter; the paper's $(\diamond)$ is the case $c=n$ (`lastCoord`). $\mathbf 1-x\triangle e_n$ is the antipode of $x\triangle e_n$.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, p.28, §5.2 (property (⋄))

import Mathlib
import Definitions.Def_ResistantSets_twist

namespace ResistantSets

/-- **Property (⋄)** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §5.2, p.28): "For an integer n ≥ 3, we will need the following
property defined on the points x in {0,1}ⁿ: (⋄) x is feasible ⇔ 1 − x△eₙ is feasible ⇔ x△eₙ is
infeasible ⇔ 1 − x is infeasible."

`Diamond S c x` is (⋄) at `x` with `eₙ` replaced by `e_c`; the paper's (⋄) is
`Diamond S (lastCoord n _) x`.

**Formalization Note** `1 − x△eₙ` is the antipode of `x △ eₙ` (equal to `(1 − x) △ eₙ`). The
chain of equivalences is stated as three consecutive `↔`. -/
def Diamond {n : ℕ} (S : Finset (Fin n → Bool)) (c : Fin n) (x : Fin n → Bool) : Prop :=
  (x ∈ S ↔ cmpl (vxor x (unitVec c)) ∈ S) ∧
  (cmpl (vxor x (unitVec c)) ∈ S ↔ vxor x (unitVec c) ∉ S) ∧
  (vxor x (unitVec c) ∉ S ↔ cmpl x ∉ S)

end ResistantSets


