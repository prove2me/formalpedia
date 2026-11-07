-- Prove2me | Definitions.Def_PCNonBool_IsDerivation
-- name    : PCNonBool_IsDerivation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:02.243236+00:00
-- url     : https://prove2.me/theorems/0229942f-1efc-430f-8df9-f7d505e346cb
-- title:
--   Polynomial calculus derivation (lines in the reduced quotient ring)
-- statement:
--   Let $\mathbb F$ be a field, $P$ a set of polynomials (the axioms), and $\mathrm{red}$ the reduction modulo the range axioms. A **polynomial calculus derivation** from $P$ is a finite sequence of polynomials $\pi=(p_1,\dots,p_\tau)$ such that each line $p_k$ is obtained in one of three ways:
--
--   1. **axiom**: $p_k=c\cdot\mathrm{red}(a)$ for some $a\in P$ and $c\in\mathbb F$;
--   2. **linear combination** (3a): $p_k=\alpha p_i+\beta p_j$ with $i,j<k$ and $\alpha,\beta\in\mathbb F$;
--   3. **multiplication** (3b): $p_k=\mathrm{red}(x\,p_i)$ with $i<k$ and $x$ any variable.
--
--   Lines are thus kept in the quotient ring $\mathbb F[x]/\langle\text{range axioms}\rangle$, represented by their multilinear normal forms, as the paper does for all its lower bounds.
--
--   **Formalization Note** The paper's axiom rule takes $c=1$; scalar multiples ($c=0$ included) are allowed here. This only enlarges the proof system, so lower bounds in this model imply the paper's: every standard derivation maps under $\mathrm{red}$ to one of these of no larger size. The paper's own splitting and restriction steps (Lemmas 5.9 and 5.13) produce scaled axiom lines. Linear combinations have fan-in $2$.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, rules (3a)–(3b) and the quotient-ring convention, p.11 (PDF p.14)

import Mathlib

namespace PCNonBool

/-- A polynomial calculus derivation from the axiom set `P`, with lines represented modulo the
range axioms through the reduction `red` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.4, (3a)–(3b), p.11 (PDF p.14)). Every
line `π[k]` is

* an axiom line: `c • red a` for some `a ∈ P` and `c ∈ F`;
* a linear combination (3a) of fan-in 2: `α • π[i] + β • π[j]` with `i, j < k`; or
* a multiplication (3b): `red (x_v · π[i])` with `i < k` and `v` any variable.

**Formalization Note** (1) Lines are the reduced representatives in the quotient ring, as in the
paper's convention ("we always think of the lines … as represented in the quotient ring", p.11);
the multiplication rule reduces its result. (2) An axiom line may be any scalar multiple of a
(reduced) axiom, `c = 0` included. This generalizes the paper's rule (`c = 1`); the paper's own
Lemmas 5.9 and 5.13 produce such lines when splitting and restricting. Every standard derivation
maps under `red` to a derivation in this sense of no larger size. (3) Fan-in is 2; `i = j` is
allowed. -/
def IsDerivation {σ F : Type*} [Field F] (red : MvPolynomial σ F →ₗ[F] MvPolynomial σ F)
    (P : Set (MvPolynomial σ F)) (π : List (MvPolynomial σ F)) : Prop :=
  ∀ (k : ℕ) (hk : k < π.length),
    (∃ a ∈ P, ∃ c : F, π[k] = c • red a) ∨
    (∃ (i j : ℕ) (hi : i < k) (hj : j < k) (α β : F),
      π[k] = α • π[i]'(hi.trans hk) + β • π[j]'(hj.trans hk)) ∨
    (∃ (i : ℕ) (hi : i < k) (v : σ), π[k] = red (MvPolynomial.X v * π[i]'(hi.trans hk)))

end PCNonBool


