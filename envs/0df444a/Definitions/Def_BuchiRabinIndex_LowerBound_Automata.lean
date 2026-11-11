-- Prove2me | Definitions.Def_BuchiRabinIndex_LowerBound_Automata
-- name    : BuchiRabinIndex_LowerBound_Automata
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:12.579449+00:00
-- url     : https://prove2.me/theorems/96f16ec4-8154-4f2c-91cb-1ead31e7ab65
-- title:
--   Büchi runs, languages, and the full Büchi automaton
-- statement:
--   A nondeterministic Büchi automaton has initial states $Q_0$, a transition map $\delta:Q\times\Sigma\to2^Q$, and accepting states $\lambda$. A run $\rho$ on a word $\alpha:\mathbb N\to\Sigma$ begins in $Q_0$ and satisfies $\rho(i+1)\in\delta(\rho(i),\alpha(i))$. Write $\operatorname{Inf}(\rho)$ for the states recurring arbitrarily late. Its language is
--   $$L(B)=\{\alpha:\exists\rho\text{ a run on }\alpha,\ \operatorname{Inf}(\rho)\cap\lambda\ne\varnothing\}.$$
--
--   For $n\ge1$, the full automaton $F_n$ has all binary relations on its $n$ states as letters, initial state $q_1$, and accepting state $q_n$. A letter contains exactly the permitted one-step transitions. States use $\mathrm{Fin}\,n$, with $q_i$ encoded by $i-1$; letters and state subsets use finite sets.
--
--   The general NBW object is separate from the paper-specific full automaton. The language is defined through runs, with no reference to history trees. Finiteness and nonemptiness of the carrier are imposed at theorems requiring the paper’s setting.
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Definition 1, pp. 4–5; Definition 28 and the F_n paragraph, p. 22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Mathlib

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound
noncomputable section
open scoped Classical

/-- General NBW data; finiteness/nonemptiness belong to the ambient types. -/
structure NBW (Q Sigma : Type) where
  initial : Finset Q
  delta : Q → Sigma → Finset Q
  accepting : Finset Q

/-- Inf of a sequence, on arbitrary carriers. -/
def infSet {X : Type} (f : ℕ → X) : Set X := {x | ∀ N, ∃ i ≥ N, f i = x}

def IsRun {Q Sigma : Type} (B : NBW Q Sigma) (α : ℕ → Sigma) (ρ : ℕ → Q) : Prop :=
  ρ 0 ∈ B.initial ∧ ∀ i, ρ (i + 1) ∈ B.delta (ρ i) (α i)

/-- Language defined only through Büchi runs, independently of history trees. -/
def language {Q Sigma : Type} (B : NBW Q Sigma) : Set (ℕ → Sigma) :=
  {α | ∃ ρ, IsRun B α ρ ∧ ∃ q ∈ B.accepting, q ∈ infSet ρ}

abbrev Letter (n : ℕ) := Finset (Fin n × Fin n)

def fullBuchi (n : ℕ) (hn : 1 ≤ n) : NBW (Fin n) (Letter n) where
  initial := {⟨0, by omega⟩}
  delta p σ := Finset.univ.filter fun q => (p, q) ∈ σ
  accepting := {⟨n - 1, by omega⟩}

end
end BuchiRabinIndex.LowerBound


