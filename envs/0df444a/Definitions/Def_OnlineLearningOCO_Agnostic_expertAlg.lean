-- Prove2me | Definitions.Def_OnlineLearningOCO_Agnostic_expertAlg
-- name    : OnlineLearningOCO_Agnostic_expertAlg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:09.976121+00:00
-- url     : https://prove2.me/theorems/1108cb4e-71d5-4b92-b06a-93ca1e1acfd7
-- title:
--   Expert(i₁,…,i_L) — the SOA simulator that errs exactly on the rounds i₁,…,i_L (§3.2.1, p. 166)
-- statement:
--   This file defines the experts used in the proof of Theorem 3.6.
--
--   Let $X$ be an instance space and $H \subseteq \{0,1\}^X$ a hypothesis class. For a set $V$ of hypotheses, an instance $x$ and a label $r \in \{0,1\}$ write $V^{(r)} = \{h \in V : h(x) = r\}$. The expert compares the Littlestone dimensions of $V^{(0)}$ and $V^{(1)}$ and sets
--
--   $$
--   \tilde y = \operatorname{argmax}_{r \in \{0,1\}} \operatorname{Ldim}\big(V^{(r)}\big), \qquad \text{with } \tilde y = 0 \text{ in case of a tie},
--   $$
--
--   where an empty class is ranked below every nonempty one (the convention $\operatorname{Ldim}(\emptyset) = -1$).
--
--   Given a set of rounds $I = \{i_1 < \dots < i_L\}$, the algorithm **Expert$(i_1,\dots,i_L)$** starts from $V_1 = H$ and on each round $t$:
--
--   1. receives $x_t$ and computes $\tilde y_t$ from $V_t$ and $x_t$ as above;
--   2. predicts $\hat y_t = \neg \tilde y_t$ if $t \in I$ and $\hat y_t = \tilde y_t$ otherwise;
--   3. updates $V_{t+1} = V_t^{(\hat y_t)} = \{h \in V_t : h(x_t) = \hat y_t\}$.
--
--   The expert simulates the Standard Optimal Algorithm under the assumption that it errs exactly on the rounds of $I$; it never looks at the true labels. It is viewed as a deterministic online algorithm that maps the history of past examples and the current instance to a label in $\{0,1\}$.
--
--   These experts are the reduction from the agnostic to the realizable case: Lemma 3.7 shows that every $h \in H$ is reproduced by some expert with $|I| \le \operatorname{Ldim}(H)$ on any instance sequence, and running Weighted Majority over them gives Theorem 3.6.
--
--   **Formalization Note** Rounds are 0-based: the paper's round $i$ is $i-1$ here, and the round index at a history `hist` is `hist.length`. The comparison uses `ldimBot`, which ranks the empty class below every nonempty one; with plain `ldim` an empty $V^{(r)}$ (dimension $0$) would tie with a nonempty class of dimension $0$. Ties go to $0$ as in the Expert box on p. 166 (the SOA box on p. 163 breaks ties to $1$).
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 166, §3.2.1, algorithm box Expert(i_1,i_2,...,i_L)

import Mathlib
import Definitions.Def_UnderstandingML_Online

namespace OnlineLearningOCO.Agnostic

open UnderstandingML

variable {X : Type*}

/-- The label `ỹ` of the box Expert(i₁,…,i_L) (p. 166): `argmax_r Ldim(V⁽ʳ⁾)` over `r ∈ {0,1}`,
where `V⁽ʳ⁾ = {h ∈ V : h(x) = r}`, with `0` (`false`) in case of a tie. The comparison uses
`ldimBot`, which ranks the empty class below every nonempty one, so an empty `V⁽ʳ⁾` loses. -/
noncomputable def expertTilde (V : Set (X → Bool)) (x : X) : Bool :=
  decide (ldimBot (V ∩ {h | h x = false}) < ldimBot (V ∩ {h | h x = true}))

/-- The prediction `ŷ` of Expert(I) on (0-based) round `t` with current set `V` and instance `x`:
`¬ỹ` if `t ∈ I`, and `ỹ` otherwise (p. 166). -/
noncomputable def expertPred (I : Finset ℕ) (V : Set (X → Bool)) (t : ℕ) (x : X) : Bool :=
  if t ∈ I then !expertTilde V x else expertTilde V x

/-- The set maintained by Expert(I) after processing the instances `xs`, starting from the set `V`
on (0-based) round `t`: each round updates `V ← V⁽ŷ⁾ = {h ∈ V : h(x) = ŷ}` (p. 166). -/
noncomputable def expertSetAux (I : Finset ℕ) : Set (X → Bool) → ℕ → List X → Set (X → Bool)
  | V, _, [] => V
  | V, t, x :: xs => expertSetAux I (V ∩ {h | h x = expertPred I V t x}) (t + 1) xs

/-- The set `V_t` of Expert(I) on the hypothesis class `H` after the instances `xs`
(`V₁ = H`, p. 166). -/
noncomputable def expertSet (H : Set (X → Bool)) (I : Finset ℕ) (xs : List X) : Set (X → Bool) :=
  expertSetAux I H 0 xs

/-- **Expert(i₁,…,i_L)** (§3.2.1, p. 166) as an online algorithm. `I` is the set of rounds
`{i₁,…,i_L}`, 0-based (the paper's round `i` is `i − 1` here). The expert ignores the labels in
the history: on round `t = hist.length` it predicts `expertPred I V_t t x`, where `V_t` is the set
obtained from `H` by the expert's own updates on the instances seen so far. -/
noncomputable def expertAlg (H : Set (X → Bool)) (I : Finset ℕ) : OnlineAlg X Bool :=
  fun hist x ↦ expertPred I (expertSet H I (hist.map Prod.fst)) hist.length x

end OnlineLearningOCO.Agnostic


