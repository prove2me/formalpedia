-- Prove2me | Definitions.Def_HardyCausaloid_Conditional
-- name    : HardyCausaloid_Conditional
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:19:55.905371+00:00
-- url     : https://prove2.me/theorems/a38eff1e-af63-4e34-add7-6bf54035aef0
-- title:
--   The vectors $\mathbf r_{\alpha_1\alpha_2}$, $\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}$ and well-definedness of $\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$
-- statement:
--   Fix disjoint finite sets $O_1,O_2$ of locations, a label $\alpha_1$ of $R_1=R_{O_1}$, a setting $F_2$ on $O_2$ and an outcome family $Y_2$ under $F_2$; $\alpha_2$ is the label $(Y_2,F_2)$ and $\beta_2$ runs over all outcome families under $F_2$. From a causaloid $C$:
--   $$\mathbf a=\mathbf r_{\alpha_1\alpha_2}(R_1\cup R_2),\qquad \mathbf b=\sum_{\beta_2}\mathbf r_{\alpha_1\beta_2}(R_1\cup R_2).$$
--   From a model, under a generalised preparation $s$ outside $R_1\cup R_2$: the joint probability $\mathrm{num}(s)=p_{\alpha_1\alpha_2}(s)$ and the probability of the conditioning event $\mathrm{den}(s)=\sum_{\beta_2}p_{\alpha_1\beta_2}(s)$.
--
--   A real $c$ is a **value** of the conditional probability $\mathrm{Prob}(Y_2\mid Y_1,F_1,F_2)$ (eq. (7)) if
--   $$\frac{\mathrm{num}(s)}{\mathrm{den}(s)}=c\quad\text{for every preparation }s\text{ with }\mathrm{den}(s)\neq0,$$
--   and the conditional probability is **well defined** if it has a value. The **length** of a vector is its Euclidean norm $\sqrt{\sum_k v_k^2}$.
--
--   These are the objects of §4.5: the first two are computed from the causaloid alone, the last from the probabilities.
--
--   **Formalization Note** The sums over $\beta_2$ are unconditional sums (`tsum`); their summability is part of the goal's conclusion. Preparations with $\mathrm{den}(s)=0$ are excluded, since there the ratio is not a conditional probability (and Lean's $x/0=0$).
-- source:
--   Hardy, Towards Quantum Gravity: A Framework for Probabilistic Theories with Non-Fixed Causal Structure, arXiv:gr-qc/0608043v1, §3, p.9 and eq. (7), p.10; §4.5, eqs. (35)–(37), p.16

import Mathlib
import Definitions.Def_HardyCausaloid_Model
import Definitions.Def_HardyCausaloid_Region
import Definitions.Def_HardyCausaloid_Causaloid

set_option autoImplicit false

namespace HardyCausaloid

universe u v w

variable {X : Type u} {Setting : X → Type v} {Outcome : (x : X) → Setting x → Type w}
variable [DecidableEq X]

/-- **The numerator vector of (35)**, Hardy, arXiv:gr-qc/0608043v1, §4.5, eq. (35), p.16:
`a = r_{α₁α₂}(R₁ ∪ R₂)`, computed from the causaloid `C` alone, where `α₂` is the label of the
setting `F₂` and the outcome family `Y₂` on `O₂`. -/
def condA (C : Causaloid Setting Outcome) {O₁ O₂ : Finset X} (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)) : C.ΩC (O₁ ∪ O₂) → ℝ :=
  C.r (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ Y₂))

/-- **The denominator vector of (35)**, Hardy, arXiv:gr-qc/0608043v1, §4.5, eqs. (35)–(37), p.16:
`b = Σ_{β₂} r_{α₁β₂}(R₁ ∪ R₂)`, "where β2 runs over all outcomes for the measurement associated
with α2", computed from the causaloid `C` alone.

**Formalization Note** The sum over `β₂` is the unconditional sum `tsum` in `ℝ^{Ω₁₂}`; its
summability is part of the goal theorem's conclusion, not a hypothesis. -/
noncomputable def condB (C : Causaloid Setting Outcome) {O₁ O₂ : Finset X}
    (α₁ : Lab Setting Outcome O₁) (F₂ : ∀ x : O₂, Setting x.1) : C.ΩC (O₁ ∪ O₂) → ℝ :=
  ∑' β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)), C.r (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂))

/-- **The joint probability (numerator of the conditional)**, Hardy, arXiv:gr-qc/0608043v1,
§4.3, eq. (18), p.12 and §4.5, p.16: `Prob(Y₁, Y₂, Y_{R−R₁−R₂} | F₁, F₂, F_{R−R₁−R₂})` for the
label `α₁` on `O₁`, the setting `F₂` with outcomes `Y₂` on `O₂`, and the generalised preparation
`s` outside `O₁ ∪ O₂`. -/
def condNum (M : Model Setting Outcome) {O₁ O₂ : Finset X} (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x))
    (s : ∀ x, Label Setting Outcome x) : ℝ :=
  regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ Y₂)) s

/-- **The probability of the conditioning event (denominator of the conditional)**, Hardy,
arXiv:gr-qc/0608043v1, §4.5, p.16: `Σ_{β₂} Prob(Y₁, β₂, Y_{R−R₁−R₂} | F₁, F₂, F_{R−R₁−R₂})`, the
probability of `α₁` on `O₁` with the setting `F₂` on `O₂` (any outcome there), under the
generalised preparation `s`.

**Formalization Note** The sum over the outcome families `β₂` is `tsum`; its summability is part
of the goal theorem's conclusion. -/
noncomputable def condDen (M : Model Setting Outcome) {O₁ O₂ : Finset X}
    (α₁ : Lab Setting Outcome O₁) (F₂ : ∀ x : O₂, Setting x.1)
    (s : ∀ x, Label Setting Outcome x) : ℝ :=
  ∑' β₂ : (∀ x : O₂, Outcome x.1 (F₂ x)), regionTable M (O₁ ∪ O₂) (joinLab α₁ (labOf F₂ β₂)) s

/-- **`c` is the value of the conditional probability `Prob(Y₂ | Y₁, F₁, F₂)`**, Hardy,
arXiv:gr-qc/0608043v1, §3, eq. (7), p.10, and §4.5, p.16 ("the only way for the probability to
be independent of the state p(R1∪R2) (as it must since the state is associated with a
generalised preparation outside R1 ∪ R2)"): for every generalised preparation `s` under which
the conditioning event has nonzero probability, the ratio `condNum / condDen` equals `c`.

**Formalization Note** Preparations with `condDen s = 0` are excluded by the guard
`condDen s ≠ 0`: there the ratio is not a conditional probability (and Lean's `x / 0 = 0`). -/
def IsCondValue (M : Model Setting Outcome) {O₁ O₂ : Finset X} (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)) (c : ℝ) : Prop :=
  ∀ s, condDen M α₁ F₂ s ≠ 0 → condNum M α₁ F₂ Y₂ s / condDen M α₁ F₂ s = c

/-- **The conditional probability `Prob(Y₂ | Y₁, F₁, F₂)` is well defined**, Hardy,
arXiv:gr-qc/0608043v1, §3, p.9 ("To be able to say whether a probability is well defined"),
eq. (7), p.10, and §4.5, p.16: it has a value independent of the generalised preparation. -/
def CondWellDefined (M : Model Setting Outcome) {O₁ O₂ : Finset X} (α₁ : Lab Setting Outcome O₁)
    (F₂ : ∀ x : O₂, Setting x.1) (Y₂ : ∀ x : O₂, Outcome x.1 (F₂ x)) : Prop :=
  ∃ c : ℝ, IsCondValue M α₁ F₂ Y₂ c

/-- **The length of a vector**, Hardy, arXiv:gr-qc/0608043v1, §4.5, p.16 ("equal to the ratio of
the lengths of the vectors"): the Euclidean length `√(Σ_k v_k²)` of `v ∈ ℝ^ι`. -/
noncomputable def euclidLength {ι : Type*} [Fintype ι] (v' : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v' i ^ 2)

end HardyCausaloid


