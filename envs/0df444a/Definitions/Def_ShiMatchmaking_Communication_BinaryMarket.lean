-- Prove2me | Definitions.Def_ShiMatchmaking_Communication_BinaryMarket
-- name    : ShiMatchmaking_Communication_BinaryMarket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:47:20.003989+00:00
-- url     : https://prove2.me/theorems/9ab5fa0f-c689-44b6-b45b-da35186b05a0
-- title:
--   Independent binary assignment market and private observations
-- statement:
--   The market $M(n,d^I,d^J)$ has $n$ customers and $n$ providers. Agents form a tagged disjoint union of two copies of $\{0,\ldots,n-1\}$. A profile has two Boolean $n\times n$ matrices. A true customer flag gives benefit $99/100$ and a false one benefit zero; a true provider flag gives cost $1/100$ and a false one cost one. Each flag is independent of every other flag, with customer probability $d^I$ and provider probability $d^J$. The profile mass is the product of these Bernoulli coordinate masses. Its support consists exactly of profiles of positive mass.
--
--   Customer $i$ observes only row $i$ of the benefit flags; provider $j$ observes only column $j$ of the cost flags. Flags are bijective encodings of the two possible real preference values. They reveal no extra information. A good pair has both flags true. A perfect pair is good and has no other good edge incident to either endpoint. These predicates are the indicators $G_{ij}$ and $P_{ij}$ in (D.27)–(D.28). The binary game builds on the separate assignment definition; the law builds on the separate Bernoulli product definition.
-- source:
--   Peng Shi (2023), Optimal Matchmaking Strategy in Two-Sided Marketplaces, Management Science, DOI 10.1287/mnsc.2022.4444, supplied published 65-page artifact; §§2.1–2.3, pp. 7–9; Proposition 12, p. 26, equations (33)–(34); Appendix D.5, p. 40, (D.27)–(D.28).

import Definitions.Def_ShiMatchmaking_Communication_Assignment
import Definitions.Def_ShiMatchmaking_Communication_FiniteInformation

noncomputable section

namespace ShiMatchmaking.Communication

abbrev Agents (n : ℕ) := Sum (Fin n) (Fin n)
abbrev Profile (n : ℕ) := (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool)
abbrev Outcome (n : ℕ) := Transaction (Fin n) (Fin n)

/-- Equations (33)--(34). The second flag is true for LOW cost. -/
def binaryGame {n : ℕ} (ω : Profile n) : AssignmentGame (Fin n) (Fin n) :=
  { benefit := fun i j => if ω.1 i j then 99 / 100 else 0
    cost := fun i j => if ω.2 i j then 1 / 100 else 1 }

/-- Independence across all pairs and both sides, with no conditioning or truncation. -/
def marketMass (n : ℕ) (dI dJ : ℝ) (ω : Profile n) : ℝ :=
  bernoulliProduct (fun _ : Fin n × Fin n => dI) (fun ij => ω.1 ij.1 ij.2) *
  bernoulliProduct (fun _ : Fin n × Fin n => dJ) (fun ij => ω.2 ij.1 ij.2)

def marketSupport (n : ℕ) (dI dJ : ℝ) : Finset (Profile n) := by
  classical
  exact Finset.univ.filter (fun ω => 0 < marketMass n dI dJ ω)

/-- Local input is a benefit row for a customer, a cost column for a provider.
The flag representation is bijective to the two possible real-valued preferences. -/
def privateInput {n : ℕ} (ω : Profile n) : Agents n → (Fin n → Bool)
  | .inl i => ω.1 i
  | .inr j => fun i => ω.2 i j

/-- Good and perfect pairs, (D.27)--(D.28). -/
def Good {n : ℕ} (ω : Profile n) (i j : Fin n) : Prop :=
  ω.1 i j = true ∧ ω.2 i j = true

def Perfect {n : ℕ} (ω : Profile n) (i j : Fin n) : Prop :=
  Good ω i j ∧ (∀ k, k ≠ j → ¬ Good ω i k) ∧
    (∀ k, k ≠ i → ¬ Good ω k j)

end ShiMatchmaking.Communication


