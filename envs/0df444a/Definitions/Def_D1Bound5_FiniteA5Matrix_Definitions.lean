-- Prove2me | Definitions.Def_D1Bound5_FiniteA5Matrix_Definitions
-- name    : D1Bound5_FiniteA5Matrix_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T22:32:12.622649+00:00
-- url     : https://prove2.me/theorems/fc042a0e-3a66-46f4-ad34-a9f6315dc1d1
-- title:
--   Finite A5Matrix
-- statement:
--   Definitions for finite a5matrix in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `finiteA5Constant`, `finiteA5LeftRow0`, `finiteA5LeftRow1`, `finiteA5LeftRow2`, `finiteA5Left`, `finiteA5RightRow0`, `finiteA5RightRow1`, `finiteA5RightRow2` and 4 further declarations.
-- source:
--   D1Bound5/FiniteA5Matrix.lean, lines 9-10, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 12-13, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 15-16, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 18-19, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 21-22, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 24-25, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 27-28, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 30-31, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 33-34, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 36-37, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 39-40, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e; D1Bound5/FiniteA5Matrix.lean, lines 42-42, SHA-256 95c6b1fcfb97cfa9725e1e807d76cad25c2ef212a9fdb17d7ac1625b237edc1e. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

section
namespace D1Bound5
variable {R : Type*} [CommRing R]

def finiteA5Constant (x y c : R) : Fin 3 → R :=
  ![(x-y)^9*c^1*(17920*x^4*c^4 + 44800*x^3*y*c^4 + 49280*x^3*c^3 + 57600*x^2*y^2*c^4 + 105600*x^2*y*c^3 + 47520*x^2*c^2 + 44800*x*y^3*c^4 + 105600*x*y^2*c^3 + 79200*x*y*c^2 + 18480*x*c + 17920*y^4*c^4 + 49280*y^3*c^3 + 47520*y^2*c^2 + 18480*y*c + 2310),(x-y)^10*c^2*(-14336*x^3*c^3 - 26880*x^2*y*c^3 - 29568*x^2*c^2 - 23040*x*y^2*c^3 - 42240*x*y*c^2 - 19008*x*c - 8960*y^3*c^3 - 21120*y^2*c^2 - 15840*y*c - 3696),(x-y)^10*c^2*(-8960*x^3*c^3 - 23040*x^2*y*c^3 - 21120*x^2*c^2 - 26880*x*y^2*c^3 - 42240*x*y*c^2 - 15840*x*c - 14336*y^3*c^3 - 29568*y^2*c^2 - 19008*y*c - 3696)]

@[simp]  def finiteA5LeftRow0 (x y c : R) : R :=
  -17920*x^12*c^5 + 116480*x^11*y*c^5 - 40320*x^11*c^4 - 299520*x^10*y^2*c^5 + 279680*x^10*y*c^4 - 29600*x^10*c^3 + 366080*x^9*y^3*c^5 - 779520*x^9*y^2*c^4 + 223200*x^9*y*c^3 - 7600*x^9*c^2 - 183040*x^8*y^4*c^5 + 1056000*x^8*y^3*c^4 - 693120*x^8*y^2*c^3 + 63920*x^8*y*c^2 - 390*x^8*c - 605440*x^7*y^4*c^4 + 1085920*x^7*y^3*c^3 - 231120*x^7*y^2*c^2 + 3800*x^7*y*c + 10*x^7 - 765600*x^6*y^4*c^3 + 453200*x^6*y^3*c^2 - 17220*x^6*y^2*c - 120*x^6*y - 457600*x^5*y^4*c^2 + 51480*x^5*y^3*c + 780*x^5*y^2 - 127270*x^4*y^4*c - 5720*x^4*y^3 - 12870*x^3*y^4

@[simp]  def finiteA5LeftRow1 (x y c : R) : R :=
  14336*x^12*c^5 - 116480*x^11*y*c^5 + 22400*x^11*c^4 + 399360*x^10*y^2*c^5 - 195200*x^10*y*c^4 + 9600*x^10*c^3 - 732160*x^9*y^3*c^5 + 729600*x^9*y^2*c^4 - 91200*x^9*y*c^3 + 800*x^9*c^2 + 732160*x^8*y^4*c^5 - 1492480*x^8*y^3*c^4 + 382080*x^8*y^2*c^3 - 8480*x^8*y*c^2 - 40*x^8*c - 329472*x^7*y^5*c^5 + 1724800*x^7*y^4*c^4 - 913440*x^7*y^3*c^3 + 41520*x^7*y^2*c^2 + 490*x^7*y*c + 3*x^7 - 950400*x^6*y^5*c^4 + 1320000*x^6*y^4*c^3 - 127600*x^6*y^3*c^2 - 3000*x^6*y^2*c - 45*x^6*y - 1029600*x^5*y^5*c^3 + 286000*x^5*y^4*c^2 + 14300*x^5*y^3*c + 390*x^5*y^2 - 514800*x^4*y^5*c^2 - 57200*x^4*y^4*c - 4290*x^4*y^3 - 115830*x^3*y^5*c - 19305*x^3*y^4 - 9009*x^2*y^5

@[simp]  def finiteA5LeftRow2 (x y c : R) : R :=
  8960*x^12*c^5 - 66560*x^11*y*c^5 + 16640*x^11*c^4 + 199680*x^10*y^2*c^5 - 135680*x^10*y*c^4 + 8640*x^10*c^3 - 292864*x^9*y^3*c^5 + 457728*x^9*y^2*c^4 - 79872*x^9*y*c^3 + 896*x^9*c^2 + 183040*x^8*y^4*c^5 - 782848*x^8*y^3*c^4 + 318816*x^8*y^2*c^3 - 9824*x^8*y*c^2 - 58*x^8*c + 605440*x^7*y^4*c^4 - 690624*x^7*y^3*c^3 + 51648*x^7*y^2*c^2 + 808*x^7*y*c + 6*x^7 + 765600*x^6*y^4*c^3 - 177760*x^6*y^3*c^2 - 6780*x^6*y^2*c - 120*x^6*y + 457600*x^5*y^4*c^2 + 40040*x^5*y^3*c + 2340*x^5*y^2 + 127270*x^4*y^4*c + 17160*x^4*y^3 + 12870*x^3*y^4

def finiteA5Left (x y c : R) : Fin 3 → R :=
  ![finiteA5LeftRow0 x y c,finiteA5LeftRow1 x y c,finiteA5LeftRow2 x y c]

@[simp]  def finiteA5RightRow0 (x y c : R) : R :=
  183040*x^4*y^8*c^5 + 605440*x^4*y^7*c^4 + 765600*x^4*y^6*c^3 + 457600*x^4*y^5*c^2 + 127270*x^4*y^4*c + 12870*x^4*y^3 - 366080*x^3*y^9*c^5 - 1056000*x^3*y^8*c^4 - 1085920*x^3*y^7*c^3 - 453200*x^3*y^6*c^2 - 51480*x^3*y^5*c + 5720*x^3*y^4 + 299520*x^2*y^10*c^5 + 779520*x^2*y^9*c^4 + 693120*x^2*y^8*c^3 + 231120*x^2*y^7*c^2 + 17220*x^2*y^6*c - 780*x^2*y^5 - 116480*x*y^11*c^5 - 279680*x*y^10*c^4 - 223200*x*y^9*c^3 - 63920*x*y^8*c^2 - 3800*x*y^7*c + 120*x*y^6 + 17920*y^12*c^5 + 40320*y^11*c^4 + 29600*y^10*c^3 + 7600*y^9*c^2 + 390*y^8*c - 10*y^7

@[simp]  def finiteA5RightRow1 (x y c : R) : R :=
  183040*x^4*y^8*c^5 + 605440*x^4*y^7*c^4 + 765600*x^4*y^6*c^3 + 457600*x^4*y^5*c^2 + 127270*x^4*y^4*c + 12870*x^4*y^3 - 292864*x^3*y^9*c^5 - 782848*x^3*y^8*c^4 - 690624*x^3*y^7*c^3 - 177760*x^3*y^6*c^2 + 40040*x^3*y^5*c + 17160*x^3*y^4 + 199680*x^2*y^10*c^5 + 457728*x^2*y^9*c^4 + 318816*x^2*y^8*c^3 + 51648*x^2*y^7*c^2 - 6780*x^2*y^6*c + 2340*x^2*y^5 - 66560*x*y^11*c^5 - 135680*x*y^10*c^4 - 79872*x*y^9*c^3 - 9824*x*y^8*c^2 + 808*x*y^7*c - 120*x*y^6 + 8960*y^12*c^5 + 16640*y^11*c^4 + 8640*y^10*c^3 + 896*y^9*c^2 - 58*y^8*c + 6*y^7

@[simp]  def finiteA5RightRow2 (x y c : R) : R :=
  -329472*x^5*y^7*c^5 - 950400*x^5*y^6*c^4 - 1029600*x^5*y^5*c^3 - 514800*x^5*y^4*c^2 - 115830*x^5*y^3*c - 9009*x^5*y^2 + 732160*x^4*y^8*c^5 + 1724800*x^4*y^7*c^4 + 1320000*x^4*y^6*c^3 + 286000*x^4*y^5*c^2 - 57200*x^4*y^4*c - 19305*x^4*y^3 - 732160*x^3*y^9*c^5 - 1492480*x^3*y^8*c^4 - 913440*x^3*y^7*c^3 - 127600*x^3*y^6*c^2 + 14300*x^3*y^5*c - 4290*x^3*y^4 + 399360*x^2*y^10*c^5 + 729600*x^2*y^9*c^4 + 382080*x^2*y^8*c^3 + 41520*x^2*y^7*c^2 - 3000*x^2*y^6*c + 390*x^2*y^5 - 116480*x*y^11*c^5 - 195200*x*y^10*c^4 - 91200*x*y^9*c^3 - 8480*x*y^8*c^2 + 490*x*y^7*c - 45*x*y^6 + 14336*y^12*c^5 + 22400*y^11*c^4 + 9600*y^10*c^3 + 800*y^9*c^2 - 40*y^8*c + 3*y^7

def finiteA5Right (x y c : R) : Fin 3 → R :=
  ![finiteA5RightRow0 x y c,finiteA5RightRow1 x y c,finiteA5RightRow2 x y c]

def finiteA5DividedMatrix (x y c : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => ![finiteA5Constant x y c i,finiteA5Left x y c i,finiteA5Right x y c i] j

def finiteA5Matrix (x y c : R) : Matrix (Fin 3) (Fin 3) R :=
  finiteA5DividedMatrix x y c * Matrix.diagonal ![1,x,y]

def finiteA5RowFactor (x y : R) : Fin 3 → R := ![x-y,x,y]











end D1Bound5
end


