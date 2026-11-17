-- Prove2me | Definitions.Def_N25_ExplicitF2
-- name    : N25_ExplicitF2
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:46.79321+00:00
-- url     : https://prove2.me/theorems/a744e380-1733-48cf-978f-82fcc6f3bb54
-- title:
--   Executable polynomial-basis arithmetic for $𝔽_4$
-- statement:
--   The file takes $𝔽_2=ℤ/2ℤ$ and represents $𝔽_4$ as pairs in the basis $1,α$ with $α^2=α+1$. It defines zero, one, addition, negation, multiplication, subtraction, squaring, and inversion, with $a^{-1}=a^2$ on the nonzero multiplicative group of order three. This is the smallest explicit extension-field table used in the characteristic-two point counts.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_NormalizedPointPredicates
/-! Polynomial-basis operations for the characteristic-two extension fields. -/
namespace MazurProof.RationalPointsN25QuotientF2

attribute [local instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

/-- The prime field of characteristic two. -/
abbrev F2 := ZMod 2

abbrev F4 := F2 × F2

def f4Zero : F4 := (0, 0)
def f4One : F4 := (1, 0)

def f4Add (a b : F4) : F4 :=
  (a.1 + b.1, a.2 + b.2)

def f4Neg (a : F4) : F4 :=
  (-a.1, -a.2)

/-- Multiplication in the basis `1, alpha`, using `alpha^2 = alpha + 1` in
characteristic two. -/
def f4Mul (a b : F4) : F4 :=
  (a.1 * b.1 + a.2 * b.2,
    a.1 * b.2 + a.2 * b.1 + a.2 * b.2)

def f4Sub (a b : F4) : F4 :=
  f4Add a (f4Neg b)

def f4Sq (a : F4) : F4 :=
  f4Mul a a

/-- In the multiplicative group of order three, inversion is squaring. -/
def f4Inv (a : F4) : F4 :=
  f4Sq a

end MazurProof.RationalPointsN25QuotientF2


