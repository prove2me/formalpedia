-- Prove2me | Definitions.Def_GeoSemialgCSP_Inst_val
-- name    : GeoSemialgCSP_Inst_val
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:15.56978+00:00
-- url     : https://prove2.me/theorems/b2dfd936-99d1-4e59-9d21-5de3ca622be9
-- title:
--   Value of an assignment on an instance
-- statement:
--   For an instance $I$ with variables $[n]$ and constraint list $C$, a predicate $P$ with accepting set $S$, and an assignment $\phi:[n]\to\mathbb R^d$, the **value** is the fraction of constraints satisfied:
--   $$\mathrm{val}(\phi,I_P)=\frac{\#\{c\in C:\ P(\phi(c_1),\dots,\phi(c_k))=1\}}{|C|},$$
--   counted with multiplicity.
--
--   **Formalization Note** For an empty constraint list the value is $0$; the promise sets of the hardness theorems exclude this case.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_Inst

namespace GeoSemialgCSP

open Classical in
/-- **Value of an assignment.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, printed p.7 (PDF p.8):
`val(ϕ, I_P) = E_{(i₁,…,i_k) ∼ I} P(ϕ(i₁), …, ϕ(i_k))`, the fraction of constraints satisfied by
`ϕ : [n] → ℝ^d`.

**Formalization Note.** The fraction is the count of satisfied constraints (with multiplicity)
divided by their number; it is `0` for the empty list, which the promise sets exclude. -/
noncomputable def Inst.val {k d : ℕ} (S : Set (Fin k → E d)) (I : Inst k) (ϕ : Fin I.n → E d) : ℝ :=
  ((I.cons.countP (fun c => decide (ϕ ∘ c ∈ S)) : ℕ) : ℝ) / (I.cons.length : ℝ)

end GeoSemialgCSP


