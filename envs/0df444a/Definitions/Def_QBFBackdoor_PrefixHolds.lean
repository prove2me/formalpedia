-- Prove2me | Definitions.Def_QBFBackdoor_PrefixHolds
-- name    : QBFBackdoor_PrefixHolds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:31:16.9637+00:00
-- url     : https://prove2.me/theorems/e9ce2bae-f7a9-45f8-8db9-afcaa6de5615
-- title:
--   Truth of a quantified Boolean formula with an arbitrary matrix
-- statement:
--   Let $Q = Q_1x_1\cdots Q_nx_n$ be a quantifier prefix, $Q_i\in\{\forall,\exists\}$, and let $F$ be a matrix, i.e. a predicate on total assignments $x\in\{0,1\}^n$. The truth of the closed formula $Q.F$ is defined recursively on the first quantifier:
--
--   $$
--   Q.F \text{ is true iff } \begin{cases} F \text{ is true}, & n = 0,\\ Q'.F[x_1=0] \text{ or } Q'.F[x_1=1] \text{ is true}, & Q_1=\exists,\\ Q'.F[x_1=0] \text{ and } Q'.F[x_1=1] \text{ are true}, & Q_1=\forall,\end{cases}
--   $$
--
--   where $Q' = Q_2x_2\cdots Q_nx_n$. Equivalently, it is the outcome of the game in which the two players assign the variables in prefix order and the existential player wins if $F$ holds at the end.
--
--   This one notion of truth serves every matrix type of the mission: CNF, disjunctions of $\Gamma_{\mathrm{AFF}}$ formulas, and conjunctions of guarded affine atoms.
--
--   **Formalization Note** Variables are `Fin n`, quantified in index order; the prefix is a map `q : Fin n → Bool` with `true` meaning $\exists$. The recursion copies that of the published `MDPComplexity.PartiallyObserved.QBF.holdsFrom`; a verification file proves that the two agree on CNF matrices.
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), §3.2, p.15

import Mathlib

namespace QBFBackdoor

/-- **The quantifier game from variable `k` on**, for an arbitrary matrix. Eriksson, Lagerkvist,
Ordyniak, Osipov, Panolan, Rychlicki, *Backdoors for Quantified Boolean Formulas*,
arXiv:2604.15927 (held version, sha256 3ea1662e…), §3.2, p.15: "The truth value of a QBF Q.ϕ is
defined recursively. Let Q = Q₁x₁ … Qₙxₙ and Q′ = Q₂x₂ … Qₙxₙ. Then Q.ϕ is true if ϕ is a true
Boolean expression, or Q₁ = ∃ and Q′.ϕ[x₁ = 0] or Q′.ϕ[x₁ = 1] is true, or Q₁ = ∀ and
Q′.ϕ[x₁ = 0] and Q′.ϕ[x₁ = 1] are true."

The variables are `Fin n`, quantified in index order; `q j = true` means `∃`, `q j = false`
means `∀`. The values of the variables before `k` are those of `x`; variable `k` is then given a
value by the player `q k`, and so on; after the last variable the matrix `F` must hold.

**Formalization Note** This is the recursion of the published
`MDPComplexity.PartiallyObserved.QBF.holdsFrom`, with the CNF matrix replaced by an arbitrary
predicate `F` on total assignments, so that the same notion of truth serves disjunctive and
guarded-affine matrices. Restriction `ϕ[x₁ = b]` is modelled by updating the assignment. -/
def prefixHoldsFrom {n : ℕ} (q : Fin n → Bool) (F : (Fin n → Bool) → Prop) (k : ℕ)
    (x : Fin n → Bool) : Prop :=
  if h : k < n then
    if q ⟨k, h⟩ then ∃ b : Bool, prefixHoldsFrom q F (k + 1) (Function.update x ⟨k, h⟩ b)
    else ∀ b : Bool, prefixHoldsFrom q F (k + 1) (Function.update x ⟨k, h⟩ b)
  else F x
termination_by n - k

/-- **Truth of the closed QBF `Q.F`** with prefix `q` (§3.2, p.15). The starting assignment is
irrelevant, since every variable is overwritten before `F` is evaluated. -/
def PrefixHolds {n : ℕ} (q : Fin n → Bool) (F : (Fin n → Bool) → Prop) : Prop :=
  prefixHoldsFrom q F 0 (fun _ => false)

end QBFBackdoor


