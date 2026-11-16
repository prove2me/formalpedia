-- Prove2me | Definitions.Def_XORFullTilt_Hardness_Supplement_TracialModel
-- name    : XORFullTilt_Hardness_Supplement_TracialModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:23:47.101257+00:00
-- url     : https://prove2.me/theorems/85dba564-ec2b-490d-903f-0de6b43066a4
-- title:
--   Tracial and oracularisable strategies and values
-- statement:
--   For every positive integer $d$, let $P^x_a,Q^y_b$ be two families of PVMs on the same space $\mathbb C^d$. Their tracial probabilities are
--   $$p(a,b\mid x,y)=\operatorname{Re}\operatorname{tr}_d(P^x_aQ^y_b),\qquad\operatorname{tr}_d(M)=\operatorname{Tr}(M)/d.$$
--   The tracial value is the supremum of the corresponding winning probabilities over every $d>0$ and every pair of PVM families. Oracularisable strategies additionally require $[P^x_a,Q^y_b]=0$ for every $a,b$ whenever $\pi(x,y)>0$; the oracularisable value is the supremum over precisely this subset. No commutation condition is imposed on zero-law question pairs, and none is imposed in the tracial class. Both values evaluate the original game, with its original predicate and law.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), pp.36,39, Definitions 6.8 and 6.13

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_QuantumModel

namespace XORFullTilt.Hardness.Supplement

/-- The normalized trace on the common complex matrix space. -/
noncomputable def normalizedTrace {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) : ℂ :=
  Matrix.trace M / (d : ℂ)

/-- Two independent PVM families on one common positive finite dimension. -/
structure TracialStrategy (X Y A B : Type) [Fintype A] [Fintype B] (d : ℕ) where
  dimension_pos : 0 < d
  alice : X → Measurement A d
  bob : Y → Measurement B d
  alice_projective : ∀ x, IsPVM (alice x)
  bob_projective : ∀ y, IsPVM (bob y)

noncomputable def tracialStrategyValue {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B] {d : ℕ}
    (G : MIPRE.Game X Y A B) (S : TracialStrategy X Y A B d) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, G.μ x y * (if G.D x y a b then 1 else 0) *
    (normalizedTrace (effect (S.alice x) a * effect (S.bob y) b)).re

/-- Only pairs in the support of the law must commute. -/
def IsOracularisable {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] {d : ℕ} (G : MIPRE.Game X Y A B)
    (S : TracialStrategy X Y A B d) : Prop :=
  ∀ x y, 0 < G.μ x y → ∀ a b,
    effect (S.alice x) a * effect (S.bob y) b =
      effect (S.bob y) b * effect (S.alice x) a

noncomputable def tracialValue {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : MIPRE.Game X Y A B) : ℝ :=
  sSup {v | ∃ d : ℕ, ∃ S : TracialStrategy X Y A B d, v = tracialStrategyValue G S}

noncomputable def oracularisableValue {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (G : MIPRE.Game X Y A B) : ℝ :=
  sSup {v | ∃ d : ℕ, ∃ S : TracialStrategy X Y A B d,
    IsOracularisable G S ∧ v = tracialStrategyValue G S}
end XORFullTilt.Hardness.Supplement


