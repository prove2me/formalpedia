-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_InRoABP
-- name    : BorderDiffEq_Supplement_InRoABP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:49:53.779997+00:00
-- url     : https://prove2.me/theorems/726bdd89-8fcc-4e6e-b685-9ec62ab6cf81
-- title:
--   The class $\mathrm{roABP}_\pi(w,R)$
-- statement:
--   For a permutation $\pi$ of $[n]$, $\mathrm{roABP}_\pi(w,R)\subseteq K[x_1,\dots,x_n]$ is the set of polynomials computed by a read-once oblivious ABP over $K$ that reads the variables in the order $x_{\pi(1)},\dots,x_{\pi(n)}$, has width at most $w$ and individual degree at most $R$.
--
--   The **any-order** class $\text{ao-roABP}(w,R)$ of Definition 4.12 consists of the polynomials lying in $\mathrm{roABP}_\pi(w,R)$ for every permutation $\pi$. These are the bases of the common-order and any-order rows of Theorems 2.5, 2.6, 6.1 and the hard class of Theorem 2.9.
--
--   **Formalization Note** For the bases of a border presentation the ring is $F((\epsilon))$, so the roABP is over $F((\epsilon))$, as in §2.2 and §9.2.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Definition 4.11 and the notation after it, p.28; Definition 4.12, p.28; §9.2, p.71

import Mathlib
import Definitions.Def_BorderDiffEq_Supplement_RoABP

namespace BorderDiffEq.Supplement

/-- **The class `roABP_π(w, R)`** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of
Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027 submission),
Definition 4.11 and the notation after it, p.28; §9.2, p.71): the polynomials in
`K[x₁, …, xₙ]` computed by a read-once oblivious ABP over `K` reading the variables in the order
`x_{π(1)}, …, x_{π(n)}`, of width at most `w` and individual degree at most `R`.

**Formalization Note.** The any-order class `ao-roABP(w, R)` (Definition 4.12) is
`∀ π, InRoABP K n π w R p`. For the bases of a border presentation `K` is `F((ε))`. -/
def InRoABP (K : Type) [CommRing K] (n : ℕ) (π : Equiv.Perm (Fin n)) (w R : ℕ)
    (p : MvPolynomial (Fin n) K) : Prop :=
  ∃ A : RoABP K n, A.width ≤ w ∧ A.IndivDegLe R ∧ A.eval π = p

end BorderDiffEq.Supplement


