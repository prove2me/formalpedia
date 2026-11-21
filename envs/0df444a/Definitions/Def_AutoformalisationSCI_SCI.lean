-- Prove2me | Definitions.Def_AutoformalisationSCI_SCI
-- name    : AutoformalisationSCI_SCI
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T14:47:16.856187+00:00
-- url     : https://prove2.me/theorems/9cc59ced-b3c0-4e3c-a636-59a9ce4bab39
-- title:
--   SCI hierarchy for decision problems via arithmetic towers
-- statement:
--   This file defines the **Solvability Complexity Index (SCI)** for decision problems via arithmetic (computable) towers, as in Appendix A.2 of the paper.
--
--   The input space is $\mathbb N$ and the output space is $\{0,1\}$ with the discrete metric, so a sequence converges iff it is eventually constant. `IterLimit h g b` says the iterated limit $\lim_{s_1}\cdots\lim_{s_h} g(s_1,\dots,s_h)$ equals $b$, with every successive limit existing (for each fixed choice of the outer indices). A **tower of height $h$** for $\Xi:\mathbb N\to\{0,1\}$ is a computable $\Gamma:\mathbb N\times\mathbb N^h\to\{0,1\}$ whose iterated limit equals $\Xi(e)$ for every $e$; a height-zero tower is a computable function equal to $\Xi$. `SCI_A Ξ` is the least height of a tower for $\Xi$, and $+\infty$ (represented by `⊤` in `WithTop ℕ`) if no finite tower exists. `DeltaA h Ξ` expresses $\mathrm{SCI}_A(\Xi)\le h$, i.e. $\Xi\in\Delta^A_{h+1}$. `setProblem A` is the decision problem of a set $A\subseteq\mathbb N$.
--
--   **Formalization Note.** $\mathbb N^h$ is represented as `Fin h → ℕ`. The definition of `SCI_A` uses `Nat.find` on the (classically decidable) existence of a tower, hence is noncomputable.
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), Appendix A (pp. 17–23); https://arxiv.org/abs/2610.08144. Standard background: R. I. Soare, Turing Computability, Springer 2016, Ch. 4. See also M. J. Colbrook, A. C. Hansen, JEMS 25(12) 2022, Definitions 5.2–5.6.

import Mathlib.Computability.Partrec
import Mathlib.Data.ENat.Basic

open Encodable
open scoped Classical

namespace AutoformalisationSCI

def IterLimit : (h : ℕ) → ((Fin h → ℕ) → Bool) → Bool → Prop
  | 0, g, b => g Fin.elim0 = b
  | h + 1, g, b =>
      (∀ s₁, ∃ b', IterLimit h (fun ss => g (Fin.cons s₁ ss)) b') ∧
      (∃ N, ∀ s₁ ≥ N, IterLimit h (fun ss => g (Fin.cons s₁ ss)) b)

def IsTower (Ξ : ℕ → Bool) (h : ℕ) : Prop :=
  ∃ Γ : ℕ × (Fin h → ℕ) → Bool, Computable Γ ∧ ∀ e, IterLimit h (fun ss => Γ (e, ss)) (Ξ e)

noncomputable def SCI_A (Ξ : ℕ → Bool) : WithTop ℕ :=
  if h : ∃ h : ℕ, IsTower Ξ h then (Nat.find h : WithTop ℕ) else ⊤

def DeltaA (h : ℕ) (Ξ : ℕ → Bool) : Prop := SCI_A Ξ ≤ (h : WithTop ℕ)

noncomputable def setProblem (A : Set ℕ) : ℕ → Bool := fun n => if n ∈ A then true else false

end AutoformalisationSCI


