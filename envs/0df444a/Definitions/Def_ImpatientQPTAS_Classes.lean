-- Prove2me | Definitions.Def_ImpatientQPTAS_Classes
-- name    : ImpatientQPTAS_Classes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:35.765207+00:00
-- url     : https://prove2.me/theorems/af9f2ed6-43fa-4611-b3bd-959ba74fb0b2
-- title:
--   §2.1, p.7 — stickers, quitters, average customers, and class-ordered policies
-- statement:
--   Given $\epsilon\in(0,\tfrac14)$, customer $i$ is a **sticker** when $p_i<\epsilon/n^2$, a **quitter** when $p_i>1-\epsilon/n$, and **average** when $p_i\in[\epsilon/n^2,\,1-\epsilon/n]$. The sets are $C_{\mathrm{stick}}$, $C_{\mathrm{quit}}$, $C_{\mathrm{average}}$.
--
--   An extended policy is **class-ordered** when (1) quitters can only be served at stage $1$, and (2) stickers are served only in stages $n+1,\dots,2n$, by picking the highest-reward sticker who is still available in each stage.
--
--   This classification is the first step of the reduction to average customers.
--
--   **Formalization Note** Condition 2 is written in two parts: a sticker is served only in those stages, and in those stages, whenever $A$ holds a sticker, a sticker of $A$ of the largest reward is served.
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, §2.1, p.7

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model

namespace ImpatientQPTAS

/-- The stickers `C_stick`: customers with `p_i < ε/n²`. Segev, arXiv:2209.13878v1, §2.1, p.7. -/
noncomputable def Cstick {n : ℕ} (ε : ℝ) (I : Instance n) : Finset (Fin n) :=
  Finset.univ.filter fun i => I.p i < ε / (n : ℝ) ^ 2

/-- The quitters `C_quit`: customers with `p_i > 1 − ε/n`. Segev, arXiv:2209.13878v1, §2.1, p.7. -/
noncomputable def Cquit {n : ℕ} (ε : ℝ) (I : Instance n) : Finset (Fin n) :=
  Finset.univ.filter fun i => 1 - ε / (n : ℝ) < I.p i

/-- The average customers `C_average`: customers with `p_i ∈ [ε/n², 1 − ε/n]`. Segev,
arXiv:2209.13878v1, §2.1, p.7. -/
noncomputable def Caverage {n : ℕ} (ε : ℝ) (I : Instance n) : Finset (Fin n) :=
  Finset.univ.filter fun i => ε / (n : ℝ) ^ 2 ≤ I.p i ∧ I.p i ≤ 1 - ε / (n : ℝ)

/-- Class-ordered policies. Segev, arXiv:2209.13878v1, §2.1, p.7: "1. Quitters can only be served at
stage 1. 2. Stickers are served only in stages n + 1, . . . , 2n, by picking the highest-reward sticker
who is still available in each stage."

**Formalization Note.** Condition 2 has two parts: a sticker is served only in those stages, and in
those stages, when `A` holds a sticker, the policy serves a sticker of `A` of the largest reward. -/
def ClassOrdered {n : ℕ} (ε : ℝ) (I : Instance n) (T : Policy n) : Prop :=
  (∀ t A i, T t A = some i → i ∈ Cquit ε I → t = 1) ∧
  (∀ t A i, T t A = some i → i ∈ Cstick ε I → n + 1 ≤ t ∧ t ≤ 2 * n) ∧
  (∀ t A, n + 1 ≤ t → t ≤ 2 * n → (A ∩ Cstick ε I).Nonempty →
    ∃ i ∈ A ∩ Cstick ε I, T t A = some i ∧ ∀ j ∈ A ∩ Cstick ε I, I.r j ≤ I.r i)

end ImpatientQPTAS


