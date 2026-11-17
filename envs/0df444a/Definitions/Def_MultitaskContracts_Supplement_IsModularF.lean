-- Prove2me | Definitions.Def_MultitaskContracts_Supplement_IsModularF
-- name    : MultitaskContracts_Supplement_IsModularF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:04:49.996191+00:00
-- url     : https://prove2.me/theorems/88cc767b-abfb-4e50-a644-7ccd5731ebdb
-- title:
--   Modular full-success probability $f(S)=P_S(K)$
-- statement:
--   Let $I$ be an instance of the multitask model on a finite task set $K$, and let
--   $$f(S)\;:=\;P_S(K)$$
--   be the **full-success probability** of a strategy $S\subseteq K$, the probability that all tasks succeed when the agent works on the tasks of $S$ (Definition 5). The function $f$ is **modular** if
--   $$f(A)+f(B)\;=\;f(A\cup B)+f(A\cap B)\qquad\text{for all } A,B\subseteq K,$$
--   that is, if it is both submodular ($\ge$, the tasks are substitutes) and supermodular ($\le$, the tasks are complements) in the sense of Section 4.2.
--
--   The predicate is the "modular $f$" in the class of Theorem 3, which shows that the price of separation of Min-Pay is unbounded beyond independence.
--
--   **Formalization Note** $f(S)$ is `I.P S Finset.univ`; the predicate is a single equality over all pairs of subsets.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Definition 5 and the classes of f, p.16 (PDF p.18); used in Theorem 3, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance

set_option autoImplicit false

open scoped ENNReal

namespace MultitaskContracts.Supplement

/-- **Modular full-success probability.** With `f(S) := P_S(K)`, the probability that all tasks
succeed when the agent works on `S` (Definition 5, p.16, PDF 18), `f` is *modular* when it is both
submodular and supermodular in the sense of p.16: `f(A) + f(B) = f(A ∪ B) + f(A ∩ B)` for all
`A, B ⊆ K`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Definition 5, p.16 (PDF 18); used in
Theorem 3, p.26 (PDF 28).

**Formalization Note.** `f(S)` is `I.P S Finset.univ`; the equality is the conjunction of the
submodular inequality `≥` and the supermodular inequality `≤` of p.16. -/
def IsModularF {K : Type*} [Fintype K] [DecidableEq K] (I : Instance K) : Prop :=
  ∀ A B : Finset K,
    I.P A Finset.univ + I.P B Finset.univ = I.P (A ∪ B) Finset.univ + I.P (A ∩ B) Finset.univ

end MultitaskContracts.Supplement


