-- Prove2me | Definitions.Def_AvoidPlast_ZoS
-- name    : AvoidPlast_ZoS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:26.302754+00:00
-- url     : https://prove2.me/theorems/9a03cba6-754a-4c31-82d5-23d72924695c
-- title:
--   The set ZoS$(F,m,d,H)$
-- statement:
--   For a finite field $F$, positive integers $m,d$ and $H\subseteq F$, $\mathrm{ZoS}(F,m,d,H)$ is the set of functions $F^m\to F$ given by a polynomial of total degree at most $d$ that vanish on the subcube $H^m$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 4.4, p.18

import Mathlib

namespace AvoidPlast

/-- The set `ZoS(F, m, d, H)` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 4.4, p.18): the functions `F^m → F` given by a
polynomial of total degree at most `d` that vanish on the subcube `H^m`. -/
def ZoS (F : Type) [Field F] (m d : ℕ) (H : Set F) : Set ((Fin m → F) → F) :=
  {f | (∃ p : MvPolynomial (Fin m) F, p.totalDegree ≤ d ∧ ∀ a, f a = MvPolynomial.eval a p) ∧
    ∀ a : Fin m → F, (∀ i, a i ∈ H) → f a = 0}

end AvoidPlast


