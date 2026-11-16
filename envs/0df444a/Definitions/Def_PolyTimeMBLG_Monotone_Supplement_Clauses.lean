-- Prove2me | Definitions.Def_PolyTimeMBLG_Monotone_Supplement_Clauses
-- name    : PolyTimeMBLG_Monotone_Supplement_Clauses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:32:30.492628+00:00
-- url     : https://prove2.me/theorems/91b300d1-8038-41c5-ac72-029976462ee9
-- title:
--   Theorem 3 and Lemma 13 — disjunctions of 3 literals and 3-CNFs as language families
-- statement:
--   For a Boolean variable $x_i$ and $\alpha\in\{0,1\}$, the **literal** $x_i^\alpha$ is $x_i$ if $\alpha=1$ and $\neg x_i$ if $\alpha=0$; it is true at a word $x\in\{0,1\}^n$ exactly when $x_i=\alpha$.
--
--   A **disjunction of 3 literals** over $x_1,\dots,x_n$ is a formula
--   $$D=x_{i_1}^{\alpha_1}\vee x_{i_2}^{\alpha_2}\vee x_{i_3}^{\alpha_3},\qquad i_1,i_2,i_3\in\{1,\dots,n\},\ \alpha_1,\alpha_2,\alpha_3\in\{0,1\},$$
--   and its language is the set of words $x\in\{0,1\}^n$ that satisfy it. In the **family of disjunctions of 3 literals** the three variables are pairwise distinct: $F_n$ is the set of languages of all such $D$ with $i_1,i_2,i_3$ pairwise distinct ($F_n=\emptyset$ for $n<3$).
--
--   A **3-CNF** is a conjunction $\varphi=D_1\wedge\cdots\wedge D_m$ of any finite number $m\ge0$ of clauses $D_j$ of the displayed form, now with indices allowed to coincide (clauses of at most three literals; $m=0$ gives the whole cube), and its language is the set of words satisfying every $D_j$. The **family of 3-CNFs** has as $F_n$ the set of languages of all 3-CNFs over $x_1,\dots,x_n$.
--
--   These are the families of Theorem 3 and Lemma 13. The first has at most $(2n)^3$ members. For $n\ge3$ a clause with a repeated variable is a conjunction of clauses on three distinct variables (e.g. $a\vee b=(a\vee b\vee c)\wedge(a\vee b\vee\neg c)$), so the 3-CNF languages are exactly the intersections of finitely many members of $F_n$ (with the cube).
--
--   **Formalization Note** A clause is a function `Fin 3 → Fin n × Bool` (index and polarity of each slot); `disj3Family` requires the three indices to be pairwise distinct (`Function.Injective`), the stronger of the two readings of "disjunction of 3 literals" for Theorem 3; a 3-CNF is a list of clauses with indices allowed to repeat. Both families are values of the base mission's `FamilySeq` (a set of `Finset`s of words `Fin n → Bool` for each $n$). The number of clauses of a 3-CNF is not capped.
-- source:
--   Héctor Jimenez, Alexander Kozachinskiy, Vicente Opazo, STOC 2027 submission #402 (October 2026), Theorem 3 and §2.3, p. 4 (disjunctions of 3 literals); literal notation x_i^α, §4, p. 6; Lemma 13 and its proof, p. 9 (3-CNFs ϕ = D1 ∧ … ∧ Dm). PDF SHA-256 2e6ec485290626cb762f55f7c45588eeb0047572a27748b20af18d34ebad7511, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/402.pdf

import Mathlib
import Definitions.Def_PolyTimeMBLG_Monotone_Generation

namespace PolyTimeMBLG.Monotone.Supplement

/-- A clause of at most 3 literals over the variables `x₁, …, xₙ` (literal notation `x_i^α`,
§4, p. 6): three literal slots `ℓ_j = x_{i_j}^{α_j}`, each a variable index `i_j : Fin n` and a
polarity `α_j : Bool` (`x^1 = x`, `x^0 = ¬x`). Indices may repeat here, so this type also holds
the clauses with fewer than three distinct literals that occur in 3-CNFs; the family of
disjunctions of 3 literals (`disj3Family`) keeps only the clauses on three distinct variables. -/
abbrev Clause3 (n : ℕ) : Type := Fin 3 → Fin n × Bool

/-- A word `x ∈ {0,1}ⁿ` satisfies the clause `ℓ₁ ∨ ℓ₂ ∨ ℓ₃` when some literal is true:
the literal `x_i^α` is true at `x` exactly when `x_i = α`. -/
def Clause3.Sat {n : ℕ} (D : Clause3 n) (x : Fin n → Bool) : Prop :=
  ∃ j : Fin 3, x (D j).1 = (D j).2

instance {n : ℕ} (D : Clause3 n) : DecidablePred D.Sat := fun x =>
  inferInstanceAs (Decidable (∃ j : Fin 3, x (D j).1 = (D j).2))

/-- The language of a disjunction of 3 literals: the words that satisfy it. -/
def Clause3.language {n : ℕ} (D : Clause3 n) : Finset (Fin n → Bool) :=
  Finset.univ.filter D.Sat

/-- The family of disjunctions of 3 literals (Theorem 3, p. 4): `Fₙ` is the set of languages of
all disjunctions `x_{i₁}^{α₁} ∨ x_{i₂}^{α₂} ∨ x_{i₃}^{α₃}` of literals on three pairwise distinct
variables `x_{i₁}, x_{i₂}, x_{i₃}` (empty for `n < 3`). This is the stronger reading for Theorem 3:
the family is contained in the one allowing repeated indices. -/
def disj3Family : FamilySeq := fun n =>
  {L | ∃ D : Clause3 n, Function.Injective (fun j => (D j).1) ∧ L = D.language}

/-- The language of the 3-CNF `D₁ ∧ ⋯ ∧ D_m` given by the list of clauses `[D₁, …, D_m]`, each
of at most 3 literals (`m = 0` gives the whole cube). For `n ≥ 3` every clause with a repeated
variable is a conjunction of clauses on three distinct variables, so the languages are those of
conjunctions of disjunctions of 3 literals. -/
def cnf3Language {n : ℕ} (Ds : List (Clause3 n)) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun x => ∀ D ∈ Ds, D.Sat x)

/-- The family of 3-CNFs (Lemma 13, p. 9): `Fₙ` is the set of languages of all conjunctions
`D₁ ∧ ⋯ ∧ D_m` of any finite number `m ≥ 0` of clauses of at most 3 literals over `x₁, …, xₙ`. -/
def cnf3Family : FamilySeq := fun n => {L | ∃ Ds : List (Clause3 n), L = cnf3Language Ds}

end PolyTimeMBLG.Monotone.Supplement


