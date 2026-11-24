-- Prove2me | Definitions.Def_VpVnp_Classes
-- name    : VpVnp_Classes
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T23:37:23.734879+00:00
-- url     : https://prove2.me/theorems/033897ef-17e4-4c74-8cd5-a7ce1e14ee26
-- title:
--   Polynomial families and Valiant's classes $\mathrm{VP}$, $\overline{\mathrm{VP}}$, $\mathrm{VNP}$
-- statement:
--   Valiant's classes, over a commutative semiring $F$ (a field for the closure). A **family** consists of, for each $n \in \mathbb N$, a finite set $V_n$ of variable labels and a polynomial $f_n \in F[V_n]$.
--
--   - $\mathrm{VP}$ is the set of families for which there is a single $a \in \mathbb N$ such that for every $n$,
--   $$|V_n| \leq n^a + a, \qquad \deg f_n \leq n^a + a, \qquad f_n \text{ has a circuit with at most } n^a + a \text{ gates.}$$
--   - $\mathrm{VNP}$ is the set of families $f$ for which there are a function $r : \mathbb N \to \mathbb N$ and polynomials $g_n \in F[V_n \sqcup \{1,\dots,r(n)\}]$ such that the family $(g_n)$, with variables $V_n \sqcup \{1,\dots,r(n)\}$, lies in $\mathrm{VP}$ and
--   $$f_n(x) = \sum_{e \in \{0,1\}^{r(n)}} g_n(x,e)$$
--   holds identically as polynomials for every $n$: the extra variables are substituted by the bits of $e$ and the results are summed.
--   - $\overline{\mathrm{VP}}$ is defined exactly like $\mathrm{VP}$, with approximating circuits in place of circuits; it requires a field, since the approximation is over formal Laurent series.
--
--   These are the classes whose separation is the mission's subject: $\mathrm{VP} \subseteq \mathrm{VNP}$ always, and Valiant's conjecture is that the inclusion is proper. The source's Corollary 1.2 asserts $\mathrm{VP} \subsetneq \mathrm{VNP}$ over every field, and the second assertion of its Theorem 1.4 asserts $\mathrm{VNP} \not\subseteq \overline{\mathrm{VP}}$ over every field.
--
--   **Formalization Note.** "Polynomially bounded" is normalized to the single bound $n^a + a$, imposed simultaneously on the number of variables, the total degree and the gate count; any polynomial bound is dominated by such a bound, and conversely. The variable sets are types with `Fintype` instances rather than a fixed ambient type, so a family may change its variables with $n$. The Boolean sum is a finite sum over `Fin (r n) → Bool`, with the substitution performed by `aeval`; the identity is between polynomials, not between functions on $F$-points. $\mathrm{VP}$ and $\mathrm{VNP}$ are defined over commutative semirings, as the source's Appendix Q records; the separation statements are over fields.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf §1.3, p. 4 (Valiant's classes) and Definition 1.3, p. 2 (the closure); Lean vp-vnp/Statement.lean, structure Statement.Family and defs Statement.VP, Statement.VPBar, Statement.VNP

import Mathlib
import Definitions.Def_VpVnp_Circuit
import Definitions.Def_VpVnp_Approximates

open MvPolynomial

universe u

namespace VpVnp

/-- A family of polynomials, with finitely many variables for every `n`. -/
structure Family (F : Type u) [CommSemiring F] where
  /-- the variables of the `n`-th polynomial -/
  vars : ℕ → Type
  /-- finitely many -/
  [fin : ∀ n, Fintype (vars n)]
  /-- the `n`-th polynomial -/
  poly : ∀ n, MvPolynomial (vars n) F

attribute [instance] Family.fin

/-- VP: the number of variables, the degree and the circuit size are polynomially bounded in `n`. -/
def VP (F : Type u) [CommSemiring F] : Set (Family F) :=
  {f | ∃ a : ℕ, ∀ n, Fintype.card (f.vars n) ≤ n ^ a + a ∧ (f.poly n).totalDegree ≤ n ^ a + a ∧
    Computes (f.poly n) (n ^ a + a)}

/-- The closure of VP: the same with approximating circuits. -/
def VPBar (F : Type u) [Field F] : Set (Family F) :=
  {f | ∃ a : ℕ, ∀ n, Fintype.card (f.vars n) ≤ n ^ a + a ∧ (f.poly n).totalDegree ≤ n ^ a + a ∧
    Approximates (f.poly n) (n ^ a + a)}

/-- VNP: the families `f n = ∑ g n (x, e)`, as polynomials, the sum over all vectors `e` of `r n` bits,
for some family `g` in VP. -/
def VNP (F : Type u) [CommSemiring F] : Set (Family F) :=
  {f | ∃ (r : ℕ → ℕ) (g : ∀ n, MvPolynomial (f.vars n ⊕ Fin (r n)) F),
    ({ vars := fun n => f.vars n ⊕ Fin (r n), poly := g } : Family F) ∈ VP F ∧
      ∀ n, f.poly n = ∑ e : Fin (r n) → Bool, aeval (Sum.elim X fun i => if e i then 1 else 0) (g n)}

end VpVnp


