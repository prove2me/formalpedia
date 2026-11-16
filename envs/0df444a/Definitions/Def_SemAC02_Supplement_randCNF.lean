-- Prove2me | Definitions.Def_SemAC02_Supplement_randCNF
-- name    : SemAC02_Supplement_randCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:44:03.916946+00:00
-- url     : https://prove2.me/theorems/0add1cbc-ab05-465e-b2cb-723689b7909a
-- title:
--   Random width-ℓ CNFs and the uniform probability
-- statement:
--   For $n,\ell$, let $\mathcal W_{n,\ell}$ be the set of clauses of width exactly $\ell$ on $\ell$ distinct variables among $x_1,\dots,x_n$; it has $2^\ell\binom n\ell$ elements. A random CNF with $m$ clauses drawn **independently and uniformly, with repetition**, is a uniformly random sequence $(C_1,\dots,C_m)\in\mathcal W_{n,\ell}^m$, and the formula is $C_1\wedge\dots\wedge C_m$.
--
--   * $F_{n,\alpha}$ (§6.1): $\ell=3$, $m=\lfloor\alpha n\rfloor$.
--   * $F_n$ (§7.1): $\ell=\lceil\log_2 n\rceil$, $m=n2^\ell$.
--
--   The probability of an event is the number of sequences in it divided by $|\mathcal W_{n,\ell}|^m$.
--
--   These are the random formulas of Theorems 6.5, 7.2 and 7.12.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), §6.1, p.41 (PDF p.43); §7.1, p.50 (PDF p.52)

import Mathlib
import Definitions.Def_LiftSAParity_CNF

namespace SemAC02.Supplement

open LiftSAParity

/-- The clauses of width exactly `ℓ` on `ℓ` distinct variables among `x₁, …, x_n` (Alekseev–
Gryaznov–Itsykson–Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*,
manuscript (STOC 2027 submission), §6.1, p.41 and §7.1, p.50): there are `2^ℓ C(n, ℓ)` of them
(`8 C(n,3)` for `ℓ = 3`). -/
abbrev WClause (n ℓ : ℕ) : Type :=
  {C : Clause (Fin n) // C.card = ℓ ∧ (C.image Prod.fst).card = ℓ}

/-- The CNF formula `C₁ ∧ ⋯ ∧ C_m` of a sequence of clauses (repeated clauses give the same
clause set). -/
def seqCNF {n ℓ m : ℕ} (ω : Fin m → WClause n ℓ) : CNF (Fin n) :=
  Finset.univ.image (fun j => (ω j).1)

/-- The **uniform probability** of an event on a finite sample space: the number of outcomes in
the event divided by the number of outcomes. The random formulas of §6.1 (`F_{n,α}`, p.41) and
§7.1 (`F_n`, p.50) are sequences of clauses drawn "independently and uniformly, with
repetition", i.e. uniform elements of `Fin m → WClause n ℓ`. -/
noncomputable def uprob {Ω : Type} [Fintype Ω] (E : Ω → Prop) : ℝ :=
  open Classical in ((Finset.univ.filter E).card : ℝ) / (Fintype.card Ω : ℝ)

end SemAC02.Supplement


