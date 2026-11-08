-- Prove2me | Definitions.Def_AvoidPlast_IsPairNTimeVerifier
-- name    : AvoidPlast_IsPairNTimeVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:47:57.321633+00:00
-- url     : https://prove2.me/theorems/6d94b1f0-12a2-48a0-8686-f676a37e99b6
-- title:
--   $L\in\mathrm{NTIME}[T(m)]$ for pair languages
-- statement:
--   A pair language $L$ is in $\mathrm{NTIME}[T(m)]$, $m=|x|+|y|$, witnessed by a multitape Turing machine $V_0$ (no jumps): on $(\langle x,y\rangle,w)$ the machine halts within $C\,T(m)$ steps, and $(x,y)\in L$ if and only if some witness of length at most $C\,T(m)$ is accepted.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.2 and footnote 17, p.17

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_IsSequential
import Definitions.Def_UniqueOptScores_pair

namespace AvoidPlast

/-- `L ∈ NTIME[T(m)]` for a pair language (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 4.2 and footnote 17, p.17), witnessed by a
*multitape Turing machine* `V₀` (a machine with no jumps) on `(⟨x, y⟩, w)`, with `m = |x| + |y|`: it
halts within `C · T(m)` steps, and `(x, y) ∈ L` iff some witness of length at most `C · T(m)` is
accepted. -/
def IsPairNTimeVerifier (V₀ : Machine 2) (L : List Bool → List Bool → Prop) (T : ℕ → ℕ) (C : ℕ) :
    Prop :=
  IsSequential V₀ ∧
    (∀ x y w : List Bool, HaltsWithin V₀ ![UniqueOptScores.pair x y, w] (C * T (x.length + y.length))) ∧
    ∀ x y : List Bool, L x y ↔
      ∃ w : List Bool, w.length ≤ C * T (x.length + y.length) ∧ Accepts V₀ ![UniqueOptScores.pair x y, w]

end AvoidPlast


