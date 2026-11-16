-- Prove2me | Definitions.Def_XORFullTilt_Hardness_Supplement_SingleTest
-- name    : XORFullTilt_Hardness_Supplement_SingleTest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:24:31.591626+00:00
-- url     : https://prove2.me/theorems/99f23bbe-5444-4bca-93ca-2ae5cfe403df
-- title:
--   The half-XOR, half-single-test construction
-- statement:
--   For a tilted XOR game $G$ with distinguished Alice question $\bot$, form $T(G)$ with Alice's original questions and Bob's questions augmented by a fresh symbol $\star$. With probability $1/2$, play the XOR relaxation of $G$; with probability $1/2$, ask $(\bot,\star)$ and accept exactly when Alice answers zero. Thus
--   $$\pi_T(x,y)=\pi_G(x,y)/2\quad(y\ne\star),\qquad\pi_T(\bot,\star)=1/2.$$
--   All other pairs with $\star$ have zero probability. The tested Alice label is the same $\bot$ already used by the XOR component. The sole supported non-XOR pair ignores Bob's answer. The value on an integer input code is the full finite-dimensional quantum value of $T(G)$ for the base encoded game $G$. No soundness or completeness property is part of the definition.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), pp.30–31, proof of Theorem 6.1

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_EffectiveGames

namespace XORFullTilt.Hardness.Supplement

/-- The source's concrete half-XOR, half-one-bit-test game. Alice's tested
    question is the very same bottom label used in the XOR component. Only Bob
    receives a fresh label (`none`), so there is exactly one supported non-XOR pair. -/
noncomputable def singleTestGame {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (G : TiltedGame X Y) : MIPRE.Game X (Option Y) Bool Bool where
  μ x y := match y with
    | none => if x = G.bottom then 1/2 else 0
    | some y => G.game.μ x y / 2
  μ_nonneg x y := by
    cases y with
    | none => split_ifs <;> norm_num
    | some y => exact div_nonneg (G.game.μ_nonneg x y) (by norm_num)
  μ_sum_one := by
    classical
    simp only [Fintype.sum_option, Finset.sum_add_distrib, ← Finset.sum_div]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [G.game.μ_sum_one]
    norm_num
  D x y a b := match y with
    | none => !a
    | some y => decide (Bool.xor a b = G.f x y)

noncomputable def singleTestValue (n : ℕ) : ℝ :=
  quantumValue (singleTestGame (explicitGame n))
end XORFullTilt.Hardness.Supplement


