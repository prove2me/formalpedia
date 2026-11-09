-- Prove2me | Definitions.Def_SemAC02_PCDegreeAtLeast
-- name    : SemAC02_PCDegreeAtLeast
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:32.304872+00:00
-- url     : https://prove2.me/theorems/2c0e5dba-0d26-40a7-bec2-8fd9a22ef706
-- title:
--   Polynomial Calculus refutations of a CNF have degree at least $\Delta$
-- statement:
--   Let $F$ be a CNF in $z_1,\dots,z_n$, encoded by its clause polynomials $[\![C]\!]=\prod_{i\in P}(1-z_i)\prod_{i\in N}z_i$, the indicators of the assignments falsifying the clauses $C=\bigvee_{i\in P}z_i\vee\bigvee_{i\in N}\neg z_i$ of $F$. A **Polynomial Calculus (PC) derivation** from $F$ is a sequence of elements of $\mathcal B_n$ each of which is an axiom $[\![C]\!]$ or follows from earlier lines by
--   $$
--   \frac{p\quad q}{\alpha p+\beta q}\ (\alpha,\beta\in\mathbb F_2),\qquad \frac{p}{x_i p}\ (i\in[n]).
--   $$
--   A refutation is a derivation of $1$; its degree is the largest degree of its lines. We say $\deg_{\mathrm{PC}}(F)\ge\Delta$ if every PC refutation of $F$ has a line of degree at least $\Delta$.
--
--   **Formalization Note** Refutations are the published `PCNonBool.IsRefutation` (a `PCNonBool.IsDerivation` containing the line $1$) with reduction `AC02Frege.ML` (lines are multilinear representatives, so all equalities are in $\mathcal B_n$), axioms the published `AC02Frege.clauseCompl C` (which over $\mathbb F_2$ is $[\![C]\!]$). Its axiom rule also allows the multiple $0\cdot[\![C]\!]$, which adds only zero lines.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §2.1, pp.14–15; Theorem 8.1, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_PCNonBool_IsDerivation
import Definitions.Def_PCNonBool_IsRefutation
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_PC

namespace SemAC02

open MvPolynomial

/-- The polynomial encoding of a CNF (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard
Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), §2.1, p.14): the
clause polynomials `⟦C⟧ = ∏_{i∈P}(1 − x_i) ∏_{i∈N} x_i`, `C ∈ F`, the indicators of the
assignments falsifying `C`.

**Formalization Note** `⟦C⟧` is the published `AC02Frege.clauseCompl C = ∏_{l ∈ C} (1 + λ_l)`,
which over `𝔽₂` is the paper's `⟦C⟧` (`1 + x = 1 − x`). -/
def pcAxioms {n : ℕ} (F : LiftSAParity.CNF (Fin n)) : Set (MvPolynomial (Fin n) (ZMod 2)) :=
  {p | ∃ C ∈ F, p = AC02Frege.clauseCompl C}

/-- `degPC(F) ≥ Δ` (p.15; used in Theorem 8.1, p.62 and Lemma 8.4, p.64): every Polynomial
Calculus refutation of `F` over `𝔽₂` has a line of degree at least `Δ`. A PC derivation is a
sequence of elements of `B_n` each of which is an axiom or follows from earlier lines by a linear
combination `αp + βq` or a multiplication `x_i p`; a refutation is a derivation of `1`; its degree
is the largest degree of a line.

**Formalization Note** Refutations are the published `PCNonBool.IsRefutation` (a
`PCNonBool.IsDerivation` containing the line `1`) with reduction `AC02Frege.ML`, so every line is
kept as its multilinear representative in `B_n` (all equalities of the rules are in `B_n`, p.15),
and the degree of a line is the total degree of that representative. The axiom rule allows scalar
multiples of an axiom (only the line `0` is new). -/
def PCDegreeAtLeast {n : ℕ} (F : LiftSAParity.CNF (Fin n)) (Δ : ℕ) : Prop :=
  ∀ π : List (MvPolynomial (Fin n) (ZMod 2)),
    PCNonBool.IsRefutation AC02Frege.ML (pcAxioms F) π → ∃ p ∈ π, Δ ≤ p.totalDegree

end SemAC02


