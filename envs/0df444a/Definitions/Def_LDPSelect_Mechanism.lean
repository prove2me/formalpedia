-- Prove2me | Definitions.Def_LDPSelect_Mechanism
-- name    : LDPSelect_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:20.703192+00:00
-- url     : https://prove2.me/theorems/7439eed1-8195-4063-aa55-3adebb984001
-- title:
--   Sequentially interactive and non-interactive locally private selection mechanisms
-- statement:
--   Users $1,\dots,n$ arrive in order. User $i$ holds a value $X_i\ge0$ and is seen only through a report $Z_i$ in a measurable output space $\mathcal Z$. A **mechanism** consists of:
--
--   1. for each user $i$, a **report kernel** $Q_i(\cdot\mid z_{<i},x)$: a Markov kernel from the earlier reports $z_1,\dots,z_{i-1}$ and the value $x$ to $\mathcal Z$;
--   2. for each user $i$, an **acceptance kernel**: a Markov kernel giving the probability of adding $i$ to the selected set $A$, as a function of the earlier reports and decisions and the current report $Z_i$.
--
--   Neither kernel receives a value other than the reporting user's own (and the acceptance kernel receives no value at all). With $a=e^{\varepsilon}\ge1$, the mechanism is **$a$-locally private** if
--
--   $$Q_i(B\mid z_{<i},x)\le a\,Q_i(B\mid z_{<i},x')$$
--
--   for every user $i$, every history $z_{<i}$, all values $x,x'$ and every measurable $B\subseteq\mathcal Z$ ("for every realization of the history"). It is **non-interactive** if every $Q_i$ ignores the history, i.e. is fixed before any report is drawn; the acceptance kernels may still use the whole history in both models. It **respects** a family $\mathcal F$ if user $i$ is never accepted when $A\cup\{i\}\notin\mathcal F$.
--
--   **Formalization Note** One output space serves all users (a family $\mathcal Z_i$ embeds in its disjoint union, preserving privacy). Algorithmic randomness is a behaviour strategy: a Markov kernel into $\{\text{accept},\text{reject}\}$ at each step. The report kernel does not see earlier decisions, as Definition 8 prints; a report can carry the independent randomness a decision later uses, so this loses nothing.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §2, p.5 (pdf p.6), Definition 8

import Mathlib
import Definitions.Def_LDPSelect_Family

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-!
# Mechanisms and policies

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), §2, p.5, Definition 8.

**Formalization Note.**
- The privacy parameter is a real `a` (the paper's `a = e^ε`), and comparisons are in `ℝ≥0∞`.
- All reports take values in one measurable output space `Z : Type`. A family `Z_i` embeds in its
  sum, and privacy is preserved.
- `Q i` sees the earlier reports and the current value, and never an earlier value or decision, as
  Definition 8 prints. Fresh randomness can be put in a report without affecting privacy, so reports
  can carry the earlier decisions if a policy needs that.
- `dec i` sees earlier reports and decisions and the current report, never a value. Algorithmic
  randomness is a behaviour strategy: a Markov kernel into `Bool` at each step.
- `Private` holds at every history and every `x, x'`, as Definition 8 and §2 print.
- `NonInteractive` constrains `Q` only: "Both models allow the selection rule to adapt to all past
  reports" (p.5).
- `Respects` holds at every history. A rule that respects `F` only almost surely can be changed on a
  null set of histories, and this does not change its reward.
-/

/-- A sequentially interactive mechanism with output space `Z` (Definition 8, p.5): for each user `i`,
a report kernel `Q i` from (earlier reports, value) to `Z`, and an acceptance kernel `dec i` from
(earlier reports and decisions, current report) to `Bool`. -/
structure Mechanism (n : ℕ) (Z : Type) [MeasurableSpace Z] where
  /-- The report kernel of user `i`. -/
  Q : (i : Fin n) → Kernel ((Fin i → Z) × ℝ≥0) Z
  /-- The acceptance kernel of user `i`. -/
  dec : (i : Fin n) → Kernel ((Fin i → Z × Bool) × Z) Bool
  markovQ : ∀ i, IsMarkovKernel (Q i)
  markovDec : ∀ i, IsMarkovKernel (dec i)

variable {n : ℕ} {Z : Type} [MeasurableSpace Z]

/-- `a`-local privacy at every realization of the history (§2 and Definition 8, p.5). -/
def Mechanism.Private (M : Mechanism n Z) (a : ℝ) : Prop :=
  ∀ (i : Fin n) (h : Fin i → Z) (x x' : ℝ≥0) (A : Set Z), MeasurableSet A →
    M.Q i (h, x) A ≤ ENNReal.ofReal a * M.Q i (h, x') A

/-- Non-interactive: every report kernel is fixed in advance. The acceptance kernels stay
history-dependent (p.5). -/
def Mechanism.NonInteractive (M : Mechanism n Z) : Prop :=
  ∀ (i : Fin n) (h h' : Fin i → Z) (x : ℝ≥0), M.Q i (h, x) = M.Q i (h', x)

/-- The selected set `A` read off a history of reports and decisions of the users before `i`. -/
def selected {i : ℕ} (hi : i ≤ n) (h : Fin i → Z × Bool) : Finset (Fin n) :=
  (Finset.univ.filter fun j : Fin i => (h j).2 = true).map (Fin.castLEEmb hi)

/-- The decision respects `F`: user `i` is never added when `A ∪ {i} ∉ F` (Definition 8, p.5). -/
def Mechanism.Respects (M : Mechanism n Z) (F : Family n) : Prop :=
  ∀ (i : Fin n) (h : Fin i → Z × Bool) (z : Z),
    selected (Nat.le_of_lt i.isLt) h ∪ {i} ∉ F → M.dec i (h, z) {true} = 0

end LDPSelect


