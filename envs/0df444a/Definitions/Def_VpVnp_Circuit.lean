-- Prove2me | Definitions.Def_VpVnp_Circuit
-- name    : VpVnp_Circuit
-- status  : Definition
-- author  : @LG
-- created : 2026-11-23T23:35:38.417143+00:00
-- url     : https://prove2.me/theorems/1217afc1-2591-4887-91a8-ef4d14b312fd
-- title:
--   Arithmetic circuits over a commutative semiring, with variables and constants counted as gates
-- statement:
--   An **arithmetic circuit** over a commutative semiring $R$ in variables indexed by a set $V$ is a finite list of polynomials, each of which is a variable, a constant of $R$, or the sum or the product of two strictly earlier entries of the list; the two entries may be equal. The entries are the **gates**, and the **size** of the circuit is the length of the list, so variables and constants are counted as gates.
--
--   The predicate $\mathrm{Computes}(f,s)$ asserts that $f \in R[V]$ has a circuit with at most $s$ gates: there is a sequence $(l_k)_{k \in \mathbb N}$ of polynomials such that
--
--   1. for every $k < s$, either $l_k = x_v$ for some variable $v \in V$, or $l_k = a$ for some constant $a \in R$, or $l_k = l_i + l_j$ for some $i,j < k$, or $l_k = l_i \cdot l_j$ for some $i,j < k$; and
--   2. $l_k = f$ for some $k < s$.
--
--   Only the first $s$ entries are constrained, so the sequence is a list of $s$ gates in all but name. This is the circuit model of the source's Section 1.3, and it is the notion of size that every lower bound in this mission refers to. Counting only the additions and multiplications would change the size by a factor of at most three, so this convention must not be mixed with gate counts from other formalizations.
--
--   **Formalization Note.** The list is presented as a total function $\mathbb N \to R[V]$ constrained below $s$; entries at index $\geq s$ are unconstrained and irrelevant. No circuit has $0$ gates, since the second clause cannot be met for $s = 0$. The base ring is an arbitrary commutative semiring, and the definition is universe-polymorphic in it.
-- source:
--   Claude (Anthropic), VP != VNP over every field (2026), https://github.com/anthropics/formal-math/tree/main/vp-vnp — paper.pdf §1.3, pp. 3-4 (the model); Lean vp-vnp/Statement.lean, def Statement.Computes

import Mathlib

open MvPolynomial

universe u

namespace VpVnp

/-- `f` has an arithmetic circuit with at most `s` gates: a list of `s` polynomials contains `f`, and each of
them is a variable, a constant, or the sum or product of two earlier ones (possibly the same one). Variables and
constants count as gates. -/
def Computes {R : Type u} {V : Type} [CommSemiring R] (f : MvPolynomial V R) (s : ℕ) : Prop :=
  ∃ l : ℕ → MvPolynomial V R,
    (∀ k < s, (∃ v : V, l k = X v) ∨ (∃ a : R, l k = C a) ∨
      (∃ i < k, ∃ j < k, l k = l i + l j) ∨ (∃ i < k, ∃ j < k, l k = l i * l j)) ∧
    ∃ k < s, l k = f

end VpVnp


