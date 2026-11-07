-- Prove2me | Definitions.Def_CallCountPOPBR_IsCompletion
-- name    : CallCountPOPBR_IsCompletion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:05:18.727196+00:00
-- url     : https://prove2.me/theorems/e60341fa-ab8f-4296-baf2-818bbffef3a1
-- title:
--   Completion of an instance under a rule
-- statement:
--   A sequence $C_0,\dots,C_N$ is a **completion** of the instance $(N,d,p,\mathrm{Obs})$ under the rule $(a_r,b_r)_{r<p}$ when
--   $$
--   C_n=1\quad(0\le n<d),\qquad C_n=1+C_{n-a_{n\bmod p}}+C_{n-b_{n\bmod p}}\quad(d\le n\le N),
--   $$
--   and $C_n=\mathrm{Obs}(n)$ at every observed index $n\le N$. These are equations (2) and (3) of the paper.
--
--   **Formalization Note** $C$ is a function $\mathbb N\to\mathbb N$ constrained on $0,\dots,N$ only; natural-number values are exact since (2)–(3) force $C_n\ge1$. The subtraction $n-a$ is truncated, which never matters for an admissible rule because $a\le d\le n$.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Definition 2.1, Eqs. (2)–(3), p.4

import Definitions.Def_CallCountPOPBR_Instance

set_option autoImplicit false

namespace CallCountPOPBR

/-- **Completion of an instance under a rule** (Definition 2.1, Eqs. (2)–(3)). Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…),
Definition 2.1, p.4: "We seek a sequence C_0, …, C_N … such that C_n = 1 (0 ≤ n < d), (2)
C_n = 1 + C_{n − a_{n mod p}} + C_{n − b_{n mod p}} (d ≤ n ≤ N), (3) … and C_n = Obs(n) at
every observed index n."

**Formalization Note.** `C : ℕ → ℕ` is constrained only on `0, …, N`. Natural-number values are
exact: (2)–(3) force `C_n ≥ 1`. The subtraction `n − a` is truncated, which is harmless for an
admissible rule since `1 ≤ a ≤ b ≤ d ≤ n` (`IsAdmissibleRule`). -/
def IsCompletion (I : Instance) (rule : ℕ → ℕ × ℕ) (C : ℕ → ℕ) : Prop :=
  (∀ n, n < I.d → C n = 1) ∧
  (∀ n, I.d ≤ n → n ≤ I.N →
    C n = 1 + C (n - (rule (n % I.p)).1) + C (n - (rule (n % I.p)).2)) ∧
  (∀ n, n ≤ I.N → ∀ v, I.obs.getD n none = some v → C n = v)

end CallCountPOPBR


