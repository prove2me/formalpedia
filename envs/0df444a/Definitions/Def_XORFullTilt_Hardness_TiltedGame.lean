-- Prove2me | Definitions.Def_XORFullTilt_Hardness_TiltedGame
-- name    : XORFullTilt_Hardness_TiltedGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:51:48.78103+00:00
-- url     : https://prove2.me/theorems/a29400e9-7852-431e-86bd-700f54b41e35
-- title:
--   Tilted XOR games, XOR relaxation and the cube
-- statement:
--   A tilted XOR game has a finite question law, a distinguished Alice question $\bot$ and a Boolean table $f$. Its acceptance rule is
--   $$a\oplus b=f(x,y)\quad(x\ne\bot),\qquad b=f(\bot,y)\quad(x=\bot).$$
--   Alice's output at $\bot$ is ignored. The XOR relaxation retains the law and table and tests $a\oplus b=f(x,y)$ everywhere.
--
--   For the cube, the even vertices are ordered $000,011,101,110$ and the odd vertices $111,100,010,001$. Every pair has probability $1/16$. The required XOR is zero for complements and one otherwise. Tilting distinguishes $000$. A three-bit answer has parity given by exclusive-or. Given an eight-outcome measurement $\Pi$ and three binary measurements $P^u$, the relation score is
--   $$\frac13\sum_{a:\,a_1\oplus a_2\oplus a_3=0}\langle\psi|\Pi_a\otimes(P^{011}_{a_1}+P^{101}_{a_2}+P^{110}_{a_3})|\psi\rangle.$$
--   The zero measurement extends these three measurements to the distinguished vertex. This supplies the exact games and the shared consistency expression for the rounding lemmas.
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), pp.14, 16–18, Definitions 2.11, 3.1, 3.2, 3.5; Eq.(9)

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_QuantumModel

namespace XORFullTilt.Hardness


structure XORGame (X Y : Type) [Fintype X] [Fintype Y] where
  game : MIPRE.Game X Y Bool Bool
  f : X → Y → Bool
  rule : ∀ x y a b, game.D x y a b = decide (Bool.xor a b = f x y)

structure TiltedGame (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] where
  game : MIPRE.Game X Y Bool Bool
  bottom : X
  f : X → Y → Bool
  rule : ∀ x y a b, game.D x y a b =
    decide ((if x = bottom then b else Bool.xor a b) = f x y)

noncomputable def xorRelaxation {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (G : TiltedGame X Y) : XORGame X Y where
  game := { μ := G.game.μ
            μ_nonneg := G.game.μ_nonneg
            μ_sum_one := G.game.μ_sum_one
            D := fun x y a b => decide (Bool.xor a b = G.f x y) }
  f := G.f
  rule := by intros; rfl

/-- Even vertices are 000,011,101,110; odd vertices are 111,100,010,001.
    Equal coordinate indices are complementary bit strings. -/
noncomputable def cube : XORGame (Fin 4) (Fin 4) where
  game := { μ := fun _ _ => 1/16
            μ_nonneg := by
              intros
              norm_num
            μ_sum_one := by
              norm_num [Fin.sum_univ_succ]
            D := fun x y a b => decide (Bool.xor a b = decide (x ≠ y)) }
  f x y := decide (x ≠ y)
  rule := by intros; rfl

noncomputable def tiltedCube : TiltedGame (Fin 4) (Fin 4) where
  game := { μ := cube.game.μ
            μ_nonneg := cube.game.μ_nonneg
            μ_sum_one := cube.game.μ_sum_one
            D := fun x y a b => decide ((if x = 0 then b else Bool.xor a b) = cube.f x y) }
  bottom := 0
  f := cube.f
  rule := by intros; rfl

abbrev Triple := Fin 3 → Bool

def parity (a : Triple) : Bool := Bool.xor (Bool.xor (a 0) (a 1)) (a 2)

def fourParity (g : Fin 4 → Bool) : Bool :=
  Bool.xor (Bool.xor (g 0) (g 1)) (Bool.xor (g 2) (g 3))

/-- Insert the ignored output at 000 while retaining the three given measurements. -/
def extendMeasurements {d : ℕ} (P : Fin 3 → Measurement Bool d) : Fin 4 → Measurement Bool d :=
  fun x => if h : x = 0 then zeroMeasurement d else P ⟨x.val - 1, by omega⟩

noncomputable def relationScore {d e : ℕ} (ψ : State d e)
    (Pi : Measurement Triple d) (P : Fin 3 → Measurement Bool e) : ℝ :=
  (1/3 : ℝ) * ∑ a : Triple, if parity a = false then
    born ψ (effect Pi a) (effect (P 0) (a 0) + effect (P 1) (a 1) + effect (P 2) (a 2)) else 0

end XORFullTilt.Hardness


