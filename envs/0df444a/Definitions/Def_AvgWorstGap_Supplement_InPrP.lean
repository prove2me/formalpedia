-- Prove2me | Definitions.Def_AvgWorstGap_Supplement_InPrP
-- name    : AvgWorstGap_Supplement_InPrP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:04:35.24552+00:00
-- url     : https://prove2.me/theorems/18a7a109-d94f-4bcf-a10e-730fde2b0ef2
-- title:
--   Deterministic polynomial time for promise problems ($\mathsf{prP}$), $\mathsf{P}$, and the equalities $\mathsf{PH}=\mathsf{P}$, $\mathsf{NP}=\mathsf{P}$
-- statement:
--   A **promise problem** $\Pi=(\mathrm{YES},\mathrm{NO})$ over binary strings is in $\mathsf{prP}$ if there are a deterministic machine $M$ and a polynomial $p$ such that, on every input $z$, $M$ halts within $p(|z|)$ steps, and
--
--   1. $M(z)=1$ for every $z\in\mathrm{YES}$,
--   2. $M(z)=0$ for every $z\in\mathrm{NO}$.
--
--   On strings outside $\mathrm{YES}\cup\mathrm{NO}$ the output is arbitrary. A language $L$ is in $\mathsf{P}$ if the promise problem $(L,\overline{L})$ is in $\mathsf{prP}$. The statement $\mathsf{PH}=\mathsf{P}$ says that a language lies in $\mathsf{PH}=\bigcup_k\Sigma_k^{\mathsf P}$ exactly when it lies in $\mathsf P$, and $\mathsf{NP}=\mathsf{P}$ says the same for $\mathsf{NP}=\Sigma_1^{\mathsf P}$.
--
--   These are the worst-case deterministic notions of §4 of the paper: "$\mathrm{Gap}\text{-}\mathrm{MINKT}^{O}\in\mathsf P$" for a promise problem, and the class equalities in Theorems 4.1 and 4.3.
--
--   **Formalization Note** Machines are the published multi-tape machines of the base mission, run with the empty oracle and empty auxiliary, guess and randomness tapes. $\mathsf P$ is defined from $\mathsf{prP}$ exactly as the base defines $\mathsf{BPP}$ from $\mathsf{prBPP}$; $\Sigma_k^{\mathsf P}$ and $\mathsf{PH}$ are the published alternating-quantifier definitions. Both inclusions of each equality are part of the definition.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §2.3, p.14 ("∈ P" for a promise problem); Theorem 4.1 and Theorem 4.3, p.34

import Mathlib
import Definitions.Def_AvgWorstGap_InPrBPP
import Definitions.Def_AvgWorstGap_InSigmaPO

namespace AvgWorstGap.Supplement

open NKtLB

/-- **A deterministic machine decides a promise problem in time `T`**: on every input `z` (oracle
`∅`, auxiliary, guess and randomness tapes empty) the machine halts within `T(|z|)` steps; it
outputs `1` on every `z ∈ YES` and `0` on every `z ∈ NO`. -/
def DetDecidesWithin (M : Machine) (T : ℕ → ℕ) (P : PromiseProblem) : Prop :=
  ∀ z : List Bool,
    (M.run ∅ ⟨z, [], [], []⟩ (T z.length)).state = M.halt ∧
    (z ∈ P.yes → M.HaltsWith ∅ ⟨z, [], [], []⟩ (T z.length) (bitOut true)) ∧
    (z ∈ P.no → M.HaltsWith ∅ ⟨z, [], [], []⟩ (T z.length) (bitOut false))

/-- **`prP`** (Goldberg, Hu, Lu, Lyu, Oliveira, *The Gap Between Average-Case and Worst-Case
Complexity*, arXiv:2610.19162, version of October 30, 2026, §2.3, p.14 and Theorem 4.1, p.34:
"`Gap-MINKT^O ∈ P`" for a promise problem): some deterministic machine decides the promise problem
within `p(n)` steps for a polynomial `p`.

**Formalization Note.** The machine model is the published `NKtLB.Machine` of the base mission,
run with oracle `∅` and empty auxiliary, guess and randomness tapes. A language `L` is in `P`
(`InP`) when the promise problem `(L, Lᶜ)` is in `prP`, exactly as the base defines `BPP` from
`prBPP`. `PH = P` and `NP = P` are equalities of classes of languages; the inclusions `P ⊆ NP ⊆ PH`
are part of the stated equalities, not assumed. -/
def InPrP (P : PromiseProblem) : Prop :=
  ∃ (p : Polynomial ℕ) (M : Machine), DetDecidesWithin M (fun n => p.eval n) P

/-- **`P`** (for a language `L`): the promise problem `(L, Lᶜ)` is in `prP`. -/
def InP (L : Set (List Bool)) : Prop := InPrP ⟨L, Lᶜ⟩

/-- **`PH = P`** (Theorem 4.1, p.34): a language is in `PH` if and only if it is in `P`. -/
def PHEqP : Prop := ∀ L : Set (List Bool), InPH L ↔ InP L

/-- **`NP = P`** (Theorem 4.3, p.34): a language is in `NP` if and only if it is in `P`. -/
def NPEqP : Prop := ∀ L : Set (List Bool), InNP L ↔ InP L

end AvgWorstGap.Supplement


