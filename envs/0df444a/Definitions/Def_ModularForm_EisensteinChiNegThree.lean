-- Prove2me | Definitions.Def_ModularForm_EisensteinChiNegThree
-- name    : ModularForm_EisensteinChiNegThree
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/adc43756-9cf5-5205-863c-fe07d61abdf1
-- title:
--   Weight-one level-three Eisenstein series: q-expansion and modularity
-- statement:
--   The module fixes a concrete model for the weight-one Eisenstein series attached to the non-trivial Dirichlet character modulo $3$, working entirely with $q$-expansions. `chiNegThree : ℕ → ℤ` is that character written out by hand on residues: it sends $n$ to $1$ if $n \equiv 1 \pmod 3$, to $-1$ if $n \equiv 2 \pmod 3$, and to $0$ if $3 \mid n$; thus it is the Kronecker symbol $\left(\frac{-3}{\cdot}\right)$ as a function of natural numbers. `sigmaChi n` is the twisted divisor sum $\sum_{d \mid n} \chi_{-3}(d)$, the sum being over Mathlib's `Nat.divisors` (so `sigmaChi 0 = 0`, the divisor set of $0$ being empty). `e1Chi3 : PowerSeries ℤ` is then the formal power series whose $0$-th coefficient is $1$ and whose $n$-th coefficient for $n \ge 1$ is $6\,\sigma_{\chi}(n)$, i.e. $1 + 6\sum_{n \ge 1}\bigl(\sum_{d\mid n}\chi_{-3}(d)\bigr)q^n$; all coefficients beyond the constant term are divisible by $6$, in particular by $3$. For a commutative ring $R$, `e1Chi3In R` is the image of this series in $R[\![q]\!]$ under coefficientwise application of `Int.castRingHom R`.
--
--   Finally `E1Chi3IsModular` is not a theorem but a `Prop`-valued definition, a named statement: it asserts the existence of a modular form $f$ of weight $1$ on the congruence subgroup $\Gamma_1(3)$ such that for every point $z$ of the upper half-plane, $f(z)$ equals the sum $\sum_{n \ge 0} c_n e^{2\pi i n z}$, where $c_n$ is the $n$-th coefficient of `e1Chi3` pushed into $\mathbb{C}$. The sum is an unconditional `tsum` over $n : ℕ$, with no summability hypothesis recorded in the statement; the predicate thus says exactly that the formal series `e1Chi3` is realised as the $q$-expansion of some weight-one form on $\Gamma_1(3)$, and it is stated here as a hypothesis to be supplied elsewhere rather than proved in this module.
--
--   **Relation to Mathlib.** The ambient notions `PowerSeries`, `ModularForm` and `CongruenceSubgroup.Gamma1` are Mathlib's; the character is not Mathlib's `DirichletCharacter` but a hand-written function `ℕ → ℤ` given by residues modulo $3$, and the Eisenstein series itself is introduced only through its integral $q$-expansion, with modularity packaged as the project's own proposition `E1Chi3IsModular`.
--
--   **Where it is used.** Because every non-constant coefficient of `e1Chi3` is divisible by $3$, this series is congruent to $1$ modulo $3$, and multiplication by it is the weight-one-to-weight-two shift used in the Langlands–Tunnell part of the argument: a weight-one form is replaced by a weight-two form with the same mod-$3$ Hecke eigensystem. The definitions here are imported by the modules that set up that congruence.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularForm_EisensteinChiNegThree.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace EisensteinWeightOne

def chiNegThree (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

def sigmaChi (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, chiNegThree d

def e1Chi3 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 6 * sigmaChi n

noncomputable def e1Chi3In (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.map (Int.castRingHom R) e1Chi3

open CongruenceSubgroup in

def E1Chi3IsModular : Prop :=
  ∃ f : ModularForm (Gamma1 3) 1, ∀ z : UpperHalfPlane,
    f z = ∑' n : ℕ,
      ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ))

end EisensteinWeightOne


