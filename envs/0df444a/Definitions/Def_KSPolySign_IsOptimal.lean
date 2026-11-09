-- Prove2me | Definitions.Def_KSPolySign_IsOptimal
-- name    : KSPolySign_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:57.396751+00:00
-- url     : https://prove2.me/theorems/33b2ed3a-252c-468e-b4a9-ac73e7ec857c
-- title:
--   Optimizers of the matrix potential program
-- statement:
--   A feasible triple $(b,U,V)$ at $y$ is an **optimizer** when its objective value attains the potential:
--   $$b+\rho\,\mathrm{tr}[U+V] = P(y).$$
--   Lemma 3.7(a) shows that the optimizer exists and is unique.
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(a), p.19 (PDF p.19)

import Mathlib
import Definitions.Def_KSPolySign_pot
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Optimizers of the potential program.** `(b, U, V)` is an optimizer at `y` when it is feasible and
its objective value `b + ρ tr[U + V]` equals `P(y)`.
Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma 3.7(a), p.19 (PDF p.19): "The program in Definition 3.3 has a unique optimizer (b, U, V)". -/
def IsOptimal {n k : ℕ} (C : Fin k → Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ)
    (ρ : ℝ) (y : Fin k → ℝ) (b : ℝ) (U V : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Feasible C F y b U V ∧ b + ρ * (U + V).trace.re = pot C F ρ y

end KSPolySign


