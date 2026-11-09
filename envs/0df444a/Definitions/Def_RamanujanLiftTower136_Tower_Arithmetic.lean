-- Prove2me | Definitions.Def_RamanujanLiftTower136_Tower_Arithmetic
-- name    : RamanujanLiftTower136_Tower_Arithmetic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:26:54.080208+00:00
-- url     : https://prove2.me/theorems/0d4f37d3-684b-455a-9b19-a03f81011395
-- title:
--   The fixed quadratic field, quaternion algebra, and order lattices
-- statement:
--   The fixed field is $F=\mathbb Q(r)$, with $r^2=17$ and real embeddings $\tau_\pm(r)=\pm\sqrt{17}$. Put $\omega=(1+r)/2$, $\eta=\omega+2$, $\rho=3-\omega$, and $O_F$ equal to the ring of integers of $F$.
--
--   The quaternion algebra $D=(-1,-3)_F$ has basis $1,i,j,k$, with $i^2=-1$, $j^2=-3$, and $ij=-ji=k$. Its reduced norm and trace are
--   $$\operatorname{nrd}(x)=x_0^2+x_1^2+3x_2^2+3x_3^2,\qquad \operatorname{trd}(x)=2x_0.$$
--   Conjugation negates the last three coordinates. Define $u=(1+j)/2$, $v=(i-r)/2+(k+rj)/6$, the $O_F$-lattices $O=\langle1,i,u,v\rangle$ and $E_0=\langle1,\eta i,\eta u,v\rangle$, and the ordered integer basis $(1,\omega,\eta i,\omega\eta i,\eta u,\omega\eta u,v,\omega v)$.
--
--   These are the common arithmetic data for all levels and primes. Maximality and arithmetic class-number properties are not part of these definitions.
--
--   **Formalization Note** $F$ is Mathlib's concrete quadratic algebra with parameters $(17,0)$; its field and number-field instances use the nonsquareness of $17$. The ring of integers is Mathlib's integral closure, not an assumed presentation.
-- source:
--   Olga Kharlampovich, Igor Pak, Alina Vdovina, STOC 2027 submission #136 (October 2026), source.pdf SHA-256 27d691a82d8af863e511e7e6b00cee95779d914645846d2974f876836db8f83b, p.8 (PDF p.9), §3.1, (3.1); §3.4, (3.5)–(3.7); §3.5, (3.10); §7.1, (7.3). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/136.pdf

import Mathlib

noncomputable section

namespace RamanujanLiftTower136.Tower
open scoped Quaternion

instance nonsquare17 : Fact (∀ q : ℚ, q ^ 2 ≠ (17 : ℚ) + 0 * q) := ⟨by
  intro q h
  have hn : ¬ IsSquare (17 : ℚ) := by norm_num
  apply hn
  exact ⟨q, by simpa [pow_two] using h.symm⟩⟩

abbrev F := QuadraticAlgebra ℚ 17 0
instance : NumberField F := NumberField.of_module_finite ℚ F
abbrev OF := NumberField.RingOfIntegers F
abbrev D := ℍ[F, -1, -3]
def r : F := ⟨0, 1⟩
def omega : F := (1 + r) / 2
def eta : F := omega + 2
def rho : F := 3 - omega
def tauPlus (x : F) : ℝ := x.re + x.im * Real.sqrt 17
def tauMinus (x : F) : ℝ := x.re - x.im * Real.sqrt 17
def totallyPositive (x : F) : Prop := 0 < tauPlus x ∧ 0 < tauMinus x

def scalar (x : F) : D := algebraMap F D x
def qi : D := ⟨0, 1, 0, 0⟩
def qj : D := ⟨0, 0, 1, 0⟩
def qk : D := ⟨0, 0, 0, 1⟩
def qu : D := (1 / 2 : F) • (1 + qj)
def qv : D := (1 / 2 : F) • (qi - scalar r) + (1 / 6 : F) • (qk + r • qj)
def conjugate (x : D) : D := ⟨x.re, -x.imI, -x.imJ, -x.imK⟩
def nrd (x : D) : F := x.re^2 + x.imI^2 + 3*x.imJ^2 + 3*x.imK^2
def trd (x : D) : F := 2*x.re

def orderBasis : Fin 4 → D := ![1, qi, qu, qv]
def baseBasis : Fin 4 → D := ![1, eta • qi, eta • qu, qv]
def orderLattice : Submodule OF D := Submodule.span OF (Set.range orderBasis)
def baseLattice : Submodule OF D := Submodule.span OF (Set.range baseBasis)
def integerBasis : Fin 8 → D := ![1, omega • (1 : D), eta • qi,
  (omega*eta) • qi, eta • qu, (omega*eta) • qu, qv, omega • qv]
def fromCoordinates (m : Fin 8 → ℤ) : D := ∑ s, (m s : F) • integerBasis s

end RamanujanLiftTower136.Tower


