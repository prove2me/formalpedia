-- Prove2me | Definitions.Def_MultiCorrectPAC_Demo_ScaleFree
-- name    : MultiCorrectPAC_Demo_ScaleFree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:35.691856+00:00
-- url     : https://prove2.me/theorems/c9c38390-6ccd-418c-89c9-3c5914440a56
-- title:
--   Section 15 setting: total hypotheses with finite nonempty correct-label sets, the fixed feedback model, and parameters with the finite-witness property (Definition 85)
-- statement:
--   In Section 15 a hypothesis is a total map $h$ from $\mathcal X$ to the nonempty finite subsets of $\mathcal Y$, with no common bound on $|h(x)|$; the errors (3), the feedback models and Definition 1 apply unchanged. A class **under consideration** in Theorem 86 is a countable nonempty set of such hypotheses. The **feedback model** is fixed to full-set or one-correct-label, and $m_{\mathcal H}(\varepsilon,\delta)$ is $m^{\mathrm{full}}_{\mathcal H}$ or $m^{\mathrm{one}}_{\mathcal H}$ accordingly. A **parameter** $D$ assigns $D(\mathcal H)\in\mathbb N_0\cup\{\infty\}$ to every class; it has the **finite-witness property** (89) if for every nonempty class
--   $$D(\mathcal H)=\sup\{D(\mathcal V):\mathcal V\subseteq\mathcal H,\ 1\le|\mathcal V|<\infty\}.$$
--
--   **Formalization Note** Hypotheses are `X → Finset Y`; `Considered H` = countable, nonempty, every value nonempty. `embedClass` views them as `Hyp X Y` via `x ↦ some (h x)`, so `LearnableFb` and `sampleCx` are the realizable learnability and sample complexity of Definition 1 for the chosen `Feedback`. A parameter is any `Set (X → Finset Y) → ℕ∞`; only its values on classes under consideration enter.
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), pp. 98–99 (PDF 100–101), §15 setting, Definition 85, (89)

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning

namespace MultiCorrectPAC.Demo

/-! Hanneke, Mansouri, Pour, Shaeiri, Wang, *PAC Learning with Multiple Correct Answers*,
§15 setting and Definition 85 (printed pp. 98–99, PDF 100–101). In §15.1 a hypothesis is a
total function from `X` to the nonempty finite subsets of `Y`, with no common bound on their
sizes: `X → Finset Y` with nonempty values. Errors (3), the feedback models and Definition 1
apply unchanged, through the embedding `h ↦ (x ↦ some (h x))` into `Hyp X Y`. -/

/-- The feedback model fixed in §15: full-set or one-correct-label. -/
inductive Feedback
  | full
  | one

/-- A class under consideration in Theorem 86: a countable nonempty set of total hypotheses
with `1 ≤ |h(x)| < ∞`. -/
def Considered {X Y : Type*} (H : Set (X → Finset Y)) : Prop :=
  H.Countable ∧ H.Nonempty ∧ ∀ h ∈ H, ∀ x, (h x).Nonempty

/-- The class as a class of (total) multi-label hypotheses. -/
def embedClass {X Y : Type*} (H : Set (X → Finset Y)) : Set (Hyp X Y) :=
  (fun h x => some (h x)) '' H

/-- Realizable PAC learnability under the fixed feedback model (Definition 1). -/
def LearnableFb {X Y : Type*} : Feedback → Set (X → Finset Y) → Prop
  | .full, H => FullLearnable (embedClass H)
  | .one, H => OneLearnable (embedClass H)

/-- The sample complexity `m_H(ε, δ)` under the fixed feedback model. -/
noncomputable def sampleCx {X Y : Type*} : Feedback → Set (X → Finset Y) → ℝ → ℝ → ℕ∞
  | .full, H, ε, δ => mFull (embedClass H) ε δ
  | .one, H, ε, δ => mOne (embedClass H) ε δ

/-- A parameter `D` (a value in `ℕ₀ ∪ {∞}` for every class) has the finite-witness property (89)
(Definition 85(i)): for every class `H` under consideration,
`D(H) = sup{D(V) : V ⊆ H, 1 ≤ |V| < ∞}`. -/
def FiniteWitness {X Y : Type*} (D : Set (X → Finset Y) → ℕ∞) : Prop :=
  ∀ H, Considered H →
    D H = ⨆ (V : Set (X → Finset Y)) (_ : V ⊆ H) (_ : V.Finite) (_ : V.Nonempty), D V

end MultiCorrectPAC.Demo


