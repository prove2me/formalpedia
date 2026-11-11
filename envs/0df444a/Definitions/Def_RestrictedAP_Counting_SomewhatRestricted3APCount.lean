-- Prove2me | Definitions.Def_RestrictedAP_Counting_SomewhatRestricted3APCount
-- name    : RestrictedAP_Counting_SomewhatRestricted3APCount
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:19:08.691533+00:00
-- url     : https://prove2.me/theorems/d501b345-91bf-46ee-9b69-3e824f1d25bb
-- title:
--   Somewhat restricted 3-APs in $\mathbb F_p^n$ and their counting probability
-- statement:
--   Fix a prime $p \ge 3$ and $n \in \mathbb N$, and write $\mathbb F_p^n$ for the vectors $x = (x_1,\dots,x_n)$ over $\mathbb F_p = \mathbb Z/p\mathbb Z$. A **somewhat restricted 3-AP** is a triple $(x, x+a, x+2a)$ with $x \in \mathbb F_p^n$ and a difference $a \in \{0,1,2\}^n$, the entries $0,1,2$ being read in $\mathbb F_p$. For $A \subseteq \mathbb F_p^n$ the **counting probability** is
--   $$\Pr_{x\in\mathbb F_p^n,\ a\in\{0,1,2\}^n}\big[x,\ x+a,\ x+2a \in A\big] = \frac{\#\{(x,a) \in \mathbb F_p^n\times\{0,1,2\}^n : x \in A,\ x+a\in A,\ x+2a \in A\}}{p^n\,3^n},$$
--   with $x$ and $a$ independent and uniform; the zero difference $a = 0$ is included (as in Theorem 1.2; Definition 1.1 excludes it from the patterns themselves). The **density** of $A$ is $|A|/p^n$.
--
--   **Formalization Note.** $\mathbb F_p^n$ is `Fin n → ZMod p`, a difference is `a : Fin n → Fin 3`, cast coordinatewise by `castDiff` (the value $j\in\{0,1,2\}$ becomes $(j : \mathbb F_p)$); `somewhatRestricted3APCount` is the count and `somewhatRestricted3APProb` the count divided by $p^n 3^n$.
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 2, Definition 1.1; p. 3, Theorem 1.2

import Mathlib

namespace RestrictedAP.Counting

/-!
# Somewhat restricted 3-APs in `F_p^n` and their counting probability

Bhangale, Khot, Liu, Minzer, *A Counting Lemma for Somewhat Restricted 3-APs*,
arXiv:2608.17365 (copy sha256 de0b96c1…), p. 2, Definition 1.1, and p. 3, Theorem 1.2.

* `F_p^n` is `Fin n → ZMod p` (coordinates indexed by `Fin n`).
* A difference vector `a ∈ {0,1,2}^n` is `a : Fin n → Fin 3`; it is cast coordinatewise into
  `ZMod p` by `castDiff` (the value `j ∈ {0,1,2}` becomes `(j : ZMod p)`).
* `somewhatRestricted3APCount p n A` counts the pairs `(x, a) ∈ F_p^n × {0,1,2}^n` with
  `x, x + a, x + 2a ∈ A`; the zero vector `a = 0` is included, as in Theorem 1.2.
* `somewhatRestricted3APProb p n A` is that count divided by `p^n · 3^n`: the probability, over
  independent uniform `x ∈ F_p^n` and `a ∈ {0,1,2}^n`, that `x, x + a, x + 2a ∈ A`.
-/

/-- The coordinatewise cast of `a ∈ {0,1,2}^n` into `(ZMod p)^n`. -/
def castDiff {p n : ℕ} (a : Fin n → Fin 3) : Fin n → ZMod p :=
  fun i => (((a i : ℕ)) : ZMod p)

/-- The number of pairs `(x, a) ∈ (ZMod p)^n × {0,1,2}^n` with `x ∈ A`, `x + a ∈ A` and
`x + 2a ∈ A` (`a = 0` included). -/
def somewhatRestricted3APCount (p n : ℕ) [NeZero p] (A : Finset (Fin n → ZMod p)) : ℕ :=
  ((Finset.univ : Finset ((Fin n → ZMod p) × (Fin n → Fin 3))).filter
    (fun xa => xa.1 ∈ A ∧ xa.1 + castDiff xa.2 ∈ A ∧ xa.1 + 2 • castDiff xa.2 ∈ A)).card

/-- `Pr_{x ∈ F_p^n, a ∈ {0,1,2}^n} [x, x + a, x + 2a ∈ A]`, with `x` and `a` independent and
uniform: the count above divided by `p^n · 3^n`. -/
noncomputable def somewhatRestricted3APProb (p n : ℕ) [NeZero p]
    (A : Finset (Fin n → ZMod p)) : ℝ :=
  (somewhatRestricted3APCount p n A : ℝ) / ((p : ℝ) ^ n * (3 : ℝ) ^ n)

end RestrictedAP.Counting


