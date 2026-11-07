-- Prove2me | Definitions.Def_CompNonlocal_Certificate
-- name    : CompNonlocal_Certificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:28.519476+00:00
-- url     : https://prove2.me/theorems/347fbd89-26b0-4940-bdd1-47a64513c27e
-- title:
--   One-round single-copy certification games
-- statement:
--   A single-copy nonlocal game consists of four algorithms: the verifier's question generation $Q(1^\kappa)\to(x,y,\mathrm{td})$ ("jointly generates classical questions $x,y$ and a private register td, which may be quantum"), Alice's algorithm $A(x,\omega_A)\to a$, Bob's algorithm $B(y,\omega_B)\to b$, and the verifier's decision $\mathrm{Val}(a,b,x,y;\mathrm{td})$, with the lengths of $x$, $a$ and $b$.
--
--   Derived quantities: the verifier's unnormalized register after producing the questions $o=x\Vert y$, the effect of "Val accepts" on that register, and the probability of producing $o$ and then accepting given answers.
--
--   **Formalization Note** Val accepts when its first output bit is $1$: this is Definition 11's event "$v_1<0$; a discarded round is rejected". Answers are read at their fixed lengths.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definitions 8, 9, 11, pp.23–25

import Mathlib
import Definitions.Def_CompNonlocal_Family
import Definitions.Def_CompNonlocal_ICirc_effectOn
import Definitions.Def_CompNonlocal_ICirc_branchOn
import Definitions.Def_CompNonlocal_fit

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- A one-round, single-copy nonlocal certification game. Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), Definition 8, pp.23–24 and Definition 9, pp.24–25 with `k = 1` (Definition 11, p.25):
the verifier's question generation `Q(1^κ) → (x, y, td)` ("jointly generates classical questions
x, y and a private register td, which may be quantum"), Alice's algorithm `A(x, ω_A) → a`, Bob's
algorithm `B(y, ω_B) → b`, and the verifier's score `Val(a, b, x, y; td)`.

The derived functions in this module: `td κ o`, the unnormalized private register of the verifier
after its question circuit produced the classical output `o = x ++ y` (its trace is `Pr[o]`);
`valEffect κ a b o`, the effect on `td` of "Val accepts on answers `a, b` and questions `o`"; and
`valAccept κ a b o = Re Tr(valEffect · td)`, the probability of producing `o` and then accepting.

**Formalization Note** `Qg` has no input; its classical output `o` is split as `x = o.take (lx κ)`,
`y = o.drop (lx κ)`, and its quantum output is `td`. `A` and `B` read their question classically
and their qubit on their first quantum-input wire. `Val` reads `fit (la κ) a ++ fit (lb κ) b ++ x ++ y`
(answers of fixed lengths `la κ`, `lb κ`) and `td`, and accepts when its first output bit is `1`
(Reading 3: Definition 11's acceptance event `v₁ < 0`, a discarded round rejected). -/
structure Certificate where
  /-- The verifier's question generation `Q`. -/
  Qg : Family
  /-- Alice's honest algorithm `A`. -/
  A : Family
  /-- Bob's honest algorithm `B`. -/
  B : Family
  /-- The verifier's decision `Val`. -/
  Val : Family
  /-- The length of Alice's question `x` inside `Q`'s classical output `x ++ y`. -/
  lx : ℕ → ℕ
  /-- The length of Alice's answer. -/
  la : ℕ → ℕ
  /-- The length of Bob's answer. -/
  lb : ℕ → ℕ

namespace Certificate

/-- The verifier's unnormalized private register after producing the questions `o = x ++ y`. -/
noncomputable def td (c : Certificate) (κ : ℕ) (o : Str) :
    Matrix (Bits (c.Qg κ).outQ.length) (Bits (c.Qg κ).outQ.length) ℂ :=
  (c.Qg κ).branchOn 0 [] 1 (fun t => decide (t = o))

/-- The effect on the verifier's register of "Val accepts on answers `a, b` and questions `o`". -/
noncomputable def valEffect (c : Certificate) (κ : ℕ) (a b o : Str) :
    Matrix (Bits (c.Qg κ).outQ.length) (Bits (c.Qg κ).outQ.length) ℂ :=
  (c.Val κ).effectOn (c.Qg κ).outQ.length (fit (c.la κ) a ++ fit (c.lb κ) b ++ o)
    (fun t => t.headD false)

/-- The probability that the questions are `o` and that Val then accepts answers `a, b`. -/
noncomputable def valAccept (c : Certificate) (κ : ℕ) (a b o : Str) : ℝ :=
  (c.valEffect κ a b o * c.td κ o).trace.re

end Certificate

end CompNonlocal


