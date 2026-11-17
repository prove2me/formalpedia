-- Prove2me | Definitions.Def_ReplParity_Supplement_IsRobustDescription
-- name    : ReplParity_Supplement_IsRobustDescription
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:57:10.840991+00:00
-- url     : https://prove2.me/theorems/75d4c45f-789b-4529-95a0-13bd06d6399a
-- title:
--   Definition 2.4 — robust finite-bit description of a $(\gamma,A)$-IAT
-- statement:
--   Let $\{S_a\}_{a\in L}$ be a $(\gamma,A)$-IAT of $\mathbb R^N$. A **robust description** of it is a finite-bit membership program together with a positive rational robustness radius $\eta^*$. The program accepts dyadic query vectors $q$ (rational coordinates whose denominators are powers of $2$), uses uniform random bits, and outputs canonically encoded rational labels. It satisfies:
--
--   1. (membership) for every covered dyadic query $q\in\bigcup_a S_a$, with probability at least $2/3$ it returns the label $a$ of a tile $S_a$ containing $q$;
--   2. (robustness) there is a Lebesgue-null set $E$ such that for every $a$, every $x\in S_a\setminus E$, and every dyadic $q$ with $\lfloor q\rfloor=\lfloor x\rfloor$ (coordinatewise) and $\|q-x\|_\infty\le\eta^*$, with probability at least $2/3$ the program on input $q$ returns $a$. The query $q$ need not be covered.
--
--   In this formalization the description is a bit string $d$ run by a query program that belongs to the generator; the program also receives the generator's parameters $N,\gamma,\zeta$.
--
--   **Formalization Note** Probabilities are over the program's uniform random bits, whose number is polynomial in the generator's parameters and the query length (Definition 2.5). A label $a\in\mathbb R^N$ is returned when the output is a list of $N$ rationals with the coordinates of $a$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Definition 2.4 and the paragraph after it, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ReplParity_Supplement_IAT
import Definitions.Def_ReplParity_Supplement_genEncoding

set_option autoImplicit false

namespace ReplParity

namespace Supplement

open MeasureTheory

open Classical in
/-- `bitProb ℓ P` is the probability that a uniform string `r` of `ℓ` unbiased bits satisfies `P`. -/
noncomputable def bitProb (ℓ : ℕ) (P : (Fin ℓ → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / 2 ^ ℓ

/-- A dyadic query vector of `ℝ^N`: `N` rationals whose denominators are powers of two. -/
def IsDyadicQuery (N : ℕ) (q : List ℚ) : Prop :=
  q.length = N ∧ ∀ x ∈ q, ∃ k : ℕ, x.den = 2 ^ k

/-- The point of `ℝ^N` named by a list of rationals (coordinate `i` is the `i`-th entry). -/
noncomputable def queryPoint (N : ℕ) (q : List ℚ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun i : Fin N => ((q.getD i 0 : ℚ) : ℝ))

/-- The program's answer is the canonically encoded rational label `a`: a list of `N` rationals
whose coordinates are those of `a`. -/
def LabelIs (N : ℕ) (ans : Option (List ℚ)) (a : EuclideanSpace ℝ (Fin N)) : Prop :=
  ∃ l : List ℚ, ans = some l ∧ l.length = N ∧ ∀ i : Fin N, ((l.getD i 0 : ℚ) : ℝ) = a i

/-- **Definition 2.4 (Robust finite-bit IAT description).** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), Definition 2.4, p.12 (PDF p.14): "A robust description of a (γ, A)-IAT consists
of a finite-bit membership program and a positive rational robustness radius η∗. The program
accepts dyadic query vectors and outputs canonically encoded rational labels, and it satisfies two
conditions. (i) (membership) On every covered dyadic query, the program returns the label of a tile
containing it with probability at least 2/3. (ii) (robustness) Let x ∈ S_a be a covered point
outside an exceptional null set, and let q be dyadic with ⌊q⌋ = ⌊x⌋ and ‖q − x‖∞ ≤ η∗. Then the
program on input q returns the label a with probability at least 2/3. … the floor is taken
coordinatewise." and "the perturbed query q in (ii) need not be covered."

`IsRobustDescription Q qbits N γ ζ d η L T`: the description bits `d` and the radius `η = η∗`, run by
the query program `Q` (which receives the generator parameters `N, γ, ζ`, the description `d`, the
query `q` and `qbits N γ ζ (qSize q)` uniform random bits), form a robust description of the tiling
with labels `L` and tiles `T`:
1. `0 < η∗`;
2. (membership) for every covered dyadic `q`, with probability at least `2/3` the answer is the
   label `a ∈ L` of a tile `T a` containing `q`;
3. (robustness) there is a Lebesgue-null set `E` such that for every `a ∈ L`, every `x ∈ T a \ E`
   and every dyadic `q` with `⌊q_i⌋ = ⌊x_i⌋` for all `i` and `‖q − x‖∞ ≤ η∗`, with probability at
   least `2/3` the answer is `a`.

**Formalization Note.** The program's probabilities are over its own uniform random bits. Its
running time and the length of its labels are constrained in `IsUniformIATGenerator`
(Definition 2.5). -/
def IsRobustDescription (Q : QInput → Option (List ℚ)) (qbits : ℕ → ℚ → ℚ → ℕ → ℕ) (N : ℕ)
    (γ ζ : ℚ) (d : List Bool) (η : ℚ) (L : Set (EuclideanSpace ℝ (Fin N)))
    (T : EuclideanSpace ℝ (Fin N) → Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  0 < η ∧
  (∀ q : List ℚ, IsDyadicQuery N q → queryPoint N q ∈ ⋃ a ∈ L, T a →
    2 / 3 ≤ bitProb (qbits N γ ζ (qSize q)) (fun r =>
      ∃ a ∈ L, queryPoint N q ∈ T a ∧ LabelIs N (Q (N, γ, ζ, d, q, List.ofFn r)) a)) ∧
  (∃ E : Set (EuclideanSpace ℝ (Fin N)), volume E = 0 ∧
    ∀ a ∈ L, ∀ x ∈ T a, x ∉ E → ∀ q : List ℚ, IsDyadicQuery N q →
      (∀ i : Fin N, ⌊((q.getD i 0 : ℚ) : ℝ)⌋ = ⌊x i⌋) →
      (∀ i : Fin N, |((q.getD i 0 : ℚ) : ℝ) - x i| ≤ (η : ℝ)) →
      2 / 3 ≤ bitProb (qbits N γ ζ (qSize q)) (fun r =>
        LabelIs N (Q (N, γ, ζ, d, q, List.ofFn r)) a))

end Supplement

end ReplParity


