-- Prove2me | Definitions.Def_TreeEquivalenceHORS_Equivalence_Languages
-- name    : TreeEquivalenceHORS_Equivalence_Languages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:14.334574+00:00
-- url     : https://prove2.me/theorems/ed8af7bf-67df-41e8-a12f-d81035dad7be
-- title:
--   The four tree-equivalence languages of Section 3 and $\Pi^0_1$-completeness under total computable many-one reductions
-- statement:
--   Pairs of schemes are coded by natural numbers $\langle G,H\rangle$; codes that do not decode are malformed and lie in none of the languages. $\mathrm{Valid}(G,H)$ means that both schemes are well formed and share a common ranked alphabet $\Sigma$.
--
--   1. $\mathrm{Eq}_{\mathrm{HORS}}=\{\langle G,H\rangle:\mathrm{Valid}(G,H)\wedge\mathrm{BT}(G)=\mathrm{BT}(H)\}$, with arbitrary alphabets (including the empty one) and arbitrary finite orders;
--   2. $\mathrm{Eq}_{4,\Sigma_2}=\{\langle G,H\rangle\in\mathrm{Eq}_{\mathrm{HORS}}:\Sigma=\Sigma_2\wedge\max\{\operatorname{ord}G,\operatorname{ord}H\}\le4\}$;
--   3. $\mathrm{Eq}^{\mathrm{prod}}_{4,\Sigma_2}=\{\langle G,H\rangle\in\mathrm{Eq}_{4,\Sigma_2}:\mathrm{Prod}(G)\wedge\mathrm{Prod}(H)\}$;
--   4. $\mathrm{Eq}^{\mathrm{safe,prod}}_{4,\Sigma_2}=\{\langle G,H\rangle\in\mathrm{Eq}^{\mathrm{prod}}_{4,\Sigma_2}:\mathrm{Safe}(G)\wedge\mathrm{Safe}(H)\}$.
--
--   Productivity is part of membership, not a promise on the input. Tree equality includes $\bot$ nodes.
--
--   A predicate $P$ on $\mathbb N$ is **co-c.e.** ($\Pi^0_1$) if its complement is recursively enumerable. It is **$\Pi^0_1$-complete under total computable many-one reductions** if it is co-c.e. and for every co-c.e. $A\subseteq\mathbb N$ there is a total computable $f$ with $A(n)\iff P(f(n))$ for all $n$.
--
--   **Formalization Note** Codes are those of the derived `Encodable (HORS × HORS)` instance. Recursive enumerability, computability and many-one reducibility are Mathlib's `REPred`, `Computable` and `ManyOneReducible`.
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Section 3 "Inputs", printed p. 11 / PDF p. 13; Theorem 1.1, printed p. 1 / PDF p. 3

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Semantics

namespace TreeEquivalenceHORS.Equivalence

/-! # The tree-equivalence languages and co-c.e.-completeness (Section 3, PDF p. 13 / printed p. 11)

Pairs of schemes are coded by natural numbers through the fixed `Encodable (HORS × HORS)`
encoding; a code that does not decode is malformed and belongs to no language. -/

/-- `Valid(G, H)`: both schemes are well formed and use a common ranked alphabet. -/
def ValidPair (G H : HORS) : Prop := G.Valid ∧ H.Valid ∧ G.alphabet = H.alphabet

/-- `Eq_HORS = {⟨G, H⟩ : Valid(G, H) ∧ BT(G) = BT(H)}`. -/
def EqHORS (n : ℕ) : Prop :=
  ∃ G H : HORS, Encodable.decode n = some (G, H) ∧ ValidPair G H ∧ G.BT = H.BT

/-- `Eq_{4,Σ₂} = {⟨G, H⟩ ∈ Eq_HORS : Σ = Σ₂ ∧ max{ord(G), ord(H)} ≤ 4}`. -/
def Eq4Sigma2 (n : ℕ) : Prop :=
  ∃ G H : HORS, Encodable.decode n = some (G, H) ∧ ValidPair G H ∧ G.BT = H.BT ∧
    G.alphabet = sigma2 ∧ G.order ≤ 4 ∧ H.order ≤ 4

/-- `Eq^prod_{4,Σ₂} = {⟨G, H⟩ ∈ Eq_{4,Σ₂} : Prod(G) ∧ Prod(H)}`. -/
def Eq4Sigma2Prod (n : ℕ) : Prop :=
  ∃ G H : HORS, Encodable.decode n = some (G, H) ∧ ValidPair G H ∧ G.BT = H.BT ∧
    G.alphabet = sigma2 ∧ G.order ≤ 4 ∧ H.order ≤ 4 ∧ G.Prod ∧ H.Prod

/-- `Eq^{safe,prod}_{4,Σ₂} = {⟨G, H⟩ ∈ Eq^prod_{4,Σ₂} : Safe(G) ∧ Safe(H)}`. -/
def Eq4Sigma2SafeProd (n : ℕ) : Prop :=
  ∃ G H : HORS, Encodable.decode n = some (G, H) ∧ ValidPair G H ∧ G.BT = H.BT ∧
    G.alphabet = sigma2 ∧ G.order ≤ 4 ∧ H.order ≤ 4 ∧ G.Prod ∧ H.Prod ∧ G.Safe ∧ H.Safe

/-- A predicate on `ℕ` is co-c.e. (`Π⁰₁`) when its complement is recursively enumerable. -/
def CoCE (P : ℕ → Prop) : Prop := REPred fun n => ¬ P n

/-- `Π⁰₁`-completeness (co-c.e.-completeness) under total computable many-one reductions: `P` is
co-c.e., and every co-c.e. predicate `A` on `ℕ` many-one reduces to it by a total computable
function (`A ≤₀ P`, i.e. `∃ f, Computable f ∧ ∀ n, A n ↔ P (f n)`). -/
def CoCEComplete (P : ℕ → Prop) : Prop :=
  CoCE P ∧ ∀ A : ℕ → Prop, CoCE A → ManyOneReducible A P

end TreeEquivalenceHORS.Equivalence


