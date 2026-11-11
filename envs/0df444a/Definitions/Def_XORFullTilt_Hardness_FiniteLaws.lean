-- Prove2me | Definitions.Def_XORFullTilt_Hardness_FiniteLaws
-- name    : XORFullTilt_Hardness_FiniteLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:52:30.785482+00:00
-- url     : https://prove2.me/theorems/4382f40f-e683-44ff-b1a8-de4e347ff39b
-- title:
--   Finite probability-law transport into games
-- statement:
--   A finite probability mass function $p$ on question pairs gives the real question law
--   $$\pi(x,y)=p(x,y).$$
--   Its nonnegativity and unit total mass are proved structurally when converting to the published general-game type. A Boolean predicate then determines a game. The tilted specialization builds its acceptance predicate from a distinguished question and a Boolean table.
--
--   Finite PMFs and arbitrary nonnegative real laws of total mass one describe the same distributions, including laws with zero weights. This conversion is reused by semantic E3-LIN games and by effective game descriptions.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), pp.8–9, Definitions 2.1, 2.3; p.28, cube sampling

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_TiltedGame

namespace XORFullTilt.Hardness

noncomputable def gameOfPMF {X Y A B : Type} [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (p : PMF (X × Y)) (D : X → Y → A → B → Bool) :
    MIPRE.Game X Y A B where
  μ x y := (p (x,y)).toReal
  μ_nonneg x y := ENNReal.toReal_nonneg
  μ_sum_one := by
    rw [← Fintype.sum_prod_type (fun xy : X × Y => (p xy).toReal), ← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
    have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    simp [h]
  D := D

noncomputable def tiltedOfPMF {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (p : PMF (X × Y)) (bottom : X) (f : X → Y → Bool) : TiltedGame X Y where
  game := gameOfPMF p (fun x y a b => decide ((if x = bottom then b else Bool.xor a b) = f x y))
  bottom := bottom
  f := f
  rule := by intros; rfl

end XORFullTilt.Hardness


