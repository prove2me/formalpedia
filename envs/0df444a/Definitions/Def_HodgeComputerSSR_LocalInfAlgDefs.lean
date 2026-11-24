-- Prove2me | Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs
-- name    : HodgeComputerSSR_LocalInfAlgDefs
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T15:42:15.894504+00:00
-- url     : https://prove2.me/theorems/9419071b-27fc-4d29-8ec5-3b75ff73fa52
-- title:
--   Pure-field $U = \infty$ polynomial definitions and algebraic identity specs
-- statement:
--   Pure-field leaf defining the $U$-degree decompositions `minor_U3..minor_U0`, `numM_Uk`, `A0V_Uk`, `AX_Uk`, the leading-jet polynomials `P44_fn`, `M01_q_fn`, `A32_*_q_fn`, the `W1_inf` dual weight expressions, and the specs `LocalInfLead3AlgSpec` and `LocalInfWeightsAlgSpec`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInfAlg.lean#L1-L558

import Definitions.Def_HodgeComputerFormal_LaurentJets
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SymmetricSexticResidual.LocalResidueInfAlg
open Polynomial QuadraticCovers

def P44_fn {R : Type*} [Field R] (S Q T : R) : R :=
    (20510415 : R) +
    (-45278190 : R) * T +
    (-135184545 : R) * T ^ 2 +
    (-13243230 : R) * T ^ 3 +
    (-496300770 : R) * Q +
    (1002263220 : R) * Q * T +
    (1619567460 : R) * Q * T ^ 2 +
    (61801740 : R) * Q * T ^ 3 +
    (1510998300 : R) * Q ^ 2 +
    (-9227925000 : R) * Q ^ 2 * T +
    (-4613962500 : R) * Q ^ 2 * T ^ 2 +
    (4883417910 : R) * Q ^ 3 +
    (25838190000 : R) * Q ^ 3 * T +
    (-20513855880 : R) * Q ^ 4 +
    (141076404 : R) * S +
    (-302433264 : R) * S * T +
    (-657628902 : R) * S * T ^ 2 +
    (-22660638 : R) * S * T ^ 3 +
    (-1013761980 : R) * S * Q +
    (6278958000 : R) * S * Q * T +
    (3978922500 : R) * S * Q * T ^ 2 +
    (-4586695470 : R) * S * Q ^ 2 +
    (-28116396000 : R) * S * Q ^ 2 * T +
    (-1389150000 : R) * S * Q ^ 2 * T ^ 2 +
    (28084223286 : R) * S * Q ^ 3 +
    (2593080000 : R) * S * Q ^ 3 * T +
    (161280315 : R) * S ^ 2 +
    (-1055687850 : R) * S ^ 2 * T +
    (-843577875 : R) * S ^ 2 * T ^ 2 +
    (1449439110 : R) * S ^ 2 * Q +
    (10141721100 : R) * S ^ 2 * Q * T +
    (1065015000 : R) * S ^ 2 * Q * T ^ 2 +
    (-14449808646 : R) * S ^ 2 * Q ^ 2 +
    (-2722734000 : R) * S ^ 2 * Q ^ 2 * T +
    (-108045000 : R) * S ^ 2 * Q ^ 2 * T ^ 2 +
    (-155306970 : R) * S ^ 3 +
    (-1212264900 : R) * S ^ 3 * T +
    (-203742000 : R) * S ^ 3 * T ^ 2 +
    (3313480842 : R) * S ^ 3 * Q +
    (950796000 : R) * S ^ 3 * Q * T +
    (79233000 : R) * S ^ 3 * Q * T ^ 2 +
    (-285894273 : R) * S ^ 4 +
    (-110397980 : R) * S ^ 4 * T +
    (-14526050 : R) * S ^ 4 * T ^ 2

def M01_q_fn {R : Type*} [Field R] (S Q T : R) : R :=
    (-2238759810 : R) * Q +
    (5237503740 : R) * Q * T +
    (-3040030980 : R) * Q * T ^ 2 +
    (525029505 : R) * Q * T ^ 3 +
    (7683624765 : R) * Q ^ 2 +
    (-372008700 : R) * Q ^ 2 * T +
    (10237067550 : R) * Q ^ 3 +
    (1928934000 : R) * Q ^ 3 * T +
    (4197469815 : R) * Q ^ 4 +
    (746253270 : R) * S +
    (-1745834580 : R) * S * T +
    (1013343660 : R) * S * T ^ 2 +
    (-175009835 : R) * S * T ^ 3 +
    (-4575240450 : R) * S * Q +
    (275562000 : R) * S * Q * T +
    (-8309917980 : R) * S * Q ^ 2 +
    (-2057529600 : R) * S * Q ^ 2 * T +
    (-7561149120 : R) * S * Q ^ 3 +
    (671344065 : R) * S ^ 2 +
    (-50519700 : R) * S ^ 2 * T +
    (2244102813 : R) * S ^ 2 * Q +
    (730851660 : R) * S ^ 2 * Q * T +
    (4310935335 : R) * S ^ 2 * Q ^ 2 +
    (-203860701 : R) * S ^ 3 +
    (-86444820 : R) * S ^ 3 * T +
    (-968078160 : R) * S ^ 3 * Q +
    (71921850 : R) * S ^ 4

def A32_2_q_fn {R : Type*} [Field R] (S Q T : R) : R :=
    (3000564 : R) * Q +
    (78318540 : R) * Q * T +
    (-197659350 : R) * Q ^ 2 +
    (-1000188 : R) * S +
    (-26106180 : R) * S * T +
    (124429830 : R) * S * Q +
    (18357675 : R) * S * Q * T +
    (-19514460 : R) * S ^ 2 +
    (-6119225 : R) * S ^ 2 * T

def A32_1_q_fn {R : Type*} [Field R] (S Q T : R) : R :=
    (482717070 : R) * Q +
    (-275562000 : R) * Q * T +
    (-1157172750 : R) * Q * T ^ 2 +
    (1567877310 : R) * Q ^ 2 +
    (-1841555250 : R) * Q ^ 2 * T +
    (-160905690 : R) * S +
    (91854000 : R) * S * T +
    (385724250 : R) * S * T ^ 2 +
    (-1036249848 : R) * S * Q +
    (1656892800 : R) * S * Q * T +
    (-783185400 : R) * S * Q * T ^ 2 +
    (-1185956100 : R) * S * Q ^ 2 +
    (1976593500 : R) * S * Q ^ 2 * T +
    (171208026 : R) * S ^ 2 +
    (-347680350 : R) * S ^ 2 * T +
    (261061800 : R) * S ^ 2 * T ^ 2 +
    (779622795 : R) * S ^ 2 * Q +
    (-1244298300 : R) * S ^ 2 * Q * T +
    (-91788375 : R) * S ^ 2 * Q * T ^ 2 +
    (-128101365 : R) * S ^ 3 +
    (195144600 : R) * S ^ 3 * T +
    (30596125 : R) * S ^ 3 * T ^ 2

def Q5_c5 {R : Type*} [Field R] (S Q : R) : R :=
    (80 / 567 : R) * Q ^ 4 +
    (-160 / 243 : R) * Q ^ 5 +
    (-320 / 1701 : R) * S * Q ^ 3 +
    (272 / 243 : R) * S * Q ^ 4 +
    (160 / 1701 : R) * S ^ 2 * Q ^ 2 +
    (-1664 / 2187 : R) * S ^ 2 * Q ^ 3 +
    (-320 / 15309 : R) * S ^ 3 * Q +
    (1696 / 6561 : R) * S ^ 3 * Q ^ 2 +
    (80 / 45927 : R) * S ^ 4 +
    (-32 / 729 : R) * S ^ 4 * Q +
    (176 / 59049 : R) * S ^ 5

def Q5_c4 {R : Type*} [Field R] (S Q : R) : R :=
    (400 / 1323 : R) * Q +
    (800 / 1323 : R) * Q ^ 2 +
    (-4400 / 3969 : R) * Q ^ 3 +
    (-320 / 63 : R) * Q ^ 4 +
    (-80 / 81 : R) * Q ^ 5 +
    (-400 / 3969 : R) * S +
    (-800 / 3969 : R) * S * Q +
    (3520 / 3969 : R) * S * Q ^ 2 +
    (4400 / 567 : R) * S * Q ^ 3 +
    (-992 / 243 : R) * S * Q ^ 4 +
    (-880 / 5103 : R) * S ^ 2 * Q +
    (-2600 / 567 : R) * S ^ 2 * Q ^ 2 +
    (15584 / 2187 : R) * S ^ 2 * Q ^ 3 +
    (18800 / 15309 : R) * S ^ 3 * Q +
    (-26656 / 6561 : R) * S ^ 3 * Q ^ 2 +
    (-5720 / 45927 : R) * S ^ 4 +
    (6556 / 6561 : R) * S ^ 4 * Q +
    (-5380 / 59049 : R) * S ^ 5

def p21_c3 {R : Type*} [Field R] (S Q : R) : R :=
    (80 / 63 : R) * Q +
    (40 / 63 : R) * Q ^ 2 +
    (-80 / 189 : R) * S +
    (-80 / 81 : R) * S * Q ^ 2 +
    (-40 / 567 : R) * S ^ 2 +
    (56 / 81 : R) * S ^ 2 * Q +
    (-88 / 729 : R) * S ^ 3

def p21_c2 {R : Type*} [Field R] (S Q : R) : R :=
    (-1040 / 63 : R) * Q +
    (-520 / 63 : R) * Q ^ 2 +
    (1840 / 189 : R) * S +
    (-560 / 81 : R) * S * Q ^ 2 +
    (1430 / 567 : R) * S ^ 2 +
    (292 / 81 : R) * S ^ 2 * Q +
    (-152 / 243 : R) * S ^ 3

def Q7_c7 {R : Type*} [Field R] (S Q : R) : R :=
    (64 / 6561 : R) * Q ^ 6 +
    (-128 / 6561 : R) * S * Q ^ 5 +
    (320 / 19683 : R) * S ^ 2 * Q ^ 4 +
    (-1280 / 177147 : R) * S ^ 3 * Q ^ 3 +
    (320 / 177147 : R) * S ^ 4 * Q ^ 2 +
    (-128 / 531441 : R) * S ^ 5 * Q +
    (64 / 4782969 : R) * S ^ 6

def Q7_c6 {R : Type*} [Field R] (S Q : R) : R :=
    (1760 / 5103 : R) * Q ^ 4 +
    (1760 / 5103 : R) * Q ^ 5 +
    (6944 / 6561 : R) * Q ^ 6 +
    (-7040 / 15309 : R) * S * Q ^ 3 +
    (-7040 / 15309 : R) * S * Q ^ 4 +
    (-1792 / 729 : R) * S * Q ^ 5 +
    (3520 / 15309 : R) * S ^ 2 * Q ^ 2 +
    (3520 / 15309 : R) * S ^ 2 * Q ^ 3 +
    (45920 / 19683 : R) * S ^ 2 * Q ^ 4 +
    (-7040 / 137781 : R) * S ^ 3 * Q +
    (-7040 / 137781 : R) * S ^ 3 * Q ^ 2 +
    (-206080 / 177147 : R) * S ^ 3 * Q ^ 3 +
    (1760 / 413343 : R) * S ^ 4 +
    (1760 / 413343 : R) * S ^ 4 * Q +
    (19040 / 59049 : R) * S ^ 4 * Q ^ 2 +
    (-25088 / 531441 : R) * S ^ 5 * Q +
    (13664 / 4782969 : R) * S ^ 6

def p32_c5 {R : Type*} [Field R] (S Q : R) : R :=
    (160 / 243 : R) * Q ^ 4 +
    (-640 / 729 : R) * S * Q ^ 3 +
    (320 / 729 : R) * S ^ 2 * Q ^ 2 +
    (-640 / 6561 : R) * S ^ 3 * Q +
    (160 / 19683 : R) * S ^ 4

def p32_c4 {R : Type*} [Field R] (S Q : R) : R :=
    (-400 / 1323 : R) +
    (-800 / 1323 : R) * Q +
    (4400 / 3969 : R) * Q ^ 2 +
    (800 / 567 : R) * Q ^ 3 +
    (80 / 81 : R) * Q ^ 4 +
    (1280 / 243 : R) * S * Q ^ 3 +
    (-880 / 5103 : R) * S ^ 2 +
    (-880 / 5103 : R) * S ^ 2 * Q +
    (-5120 / 729 : R) * S ^ 2 * Q ^ 2 +
    (18400 / 6561 : R) * S ^ 3 * Q +
    (-7124 / 19683 : R) * S ^ 4

def p31_c3 {R : Type*} [Field R] (S Q : R) : R :=
    (-40 / 63 : R) +
    (-40 / 63 : R) * Q +
    (80 / 81 : R) * S * Q +
    (-28 / 81 : R) * S ^ 2

def p31_c2 {R : Type*} [Field R] (S Q : R) : R :=
    (520 / 63 : R) +
    (520 / 63 : R) * Q +
    (560 / 81 : R) * S * Q +
    (-146 / 81 : R) * S ^ 2



def dHS_2 {R : Type*} [Field R] (s q : R) : R := -(4 / 81 : R) * (s - 3 * q) ^ 2
def dHS_1 {R : Type*} [Field R] (s q : R) : R := (143 / 81 : R) * s ^ 2 - (184 / 27) * s * q + (52 / 9) * q ^ 2
def dHS_0 {R : Type*} [Field R] (s q : R) : R := -(25 / 243 : R) * (5 * s - 9 * q) * (15 * s - 9 * q)
def dHQ_1 {R : Type*} [Field R] (s q v : R) : R :=
  -(92 / 27 : R) * s ^ 2 + (104 / 9) * s * q - (22 / 3) * q ^ 2 + (10 / 7) * q * v + (10 / 7) * v ^ 2
def dHQ_0 {R : Type*} [Field R] (s q : R) : R := (50 / 27 : R) * s * (5 * s - 9 * q)

def minor_U3 {R : Type*} [Field R] (s1 q1 v1 s2 q2 v2 : R) : R :=
  dHS_2 s1 q1 * (dHQ_1 s2 q2 v2 + 3 * dHS_1 s2 q2) - dHS_2 s2 q2 * (dHQ_1 s1 q1 v1 + 3 * dHS_1 s1 q1)

def minor_U2 {R : Type*} [Field R] (s1 q1 v1 s2 q2 v2 : R) : R :=
  dHS_2 s1 q1 * (dHQ_0 s2 q2 + 3 * dHS_0 s2 q2) - dHS_2 s2 q2 * (dHQ_0 s1 q1 + 3 * dHS_0 s1 q1) +
  dHS_1 s1 q1 * dHQ_1 s2 q2 v2 - dHS_1 s2 q2 * dHQ_1 s1 q1 v1

def minor_U1 {R : Type*} [Field R] (s1 q1 v1 s2 q2 v2 : R) : R :=
  dHS_1 s1 q1 * dHQ_0 s2 q2 - dHS_1 s2 q2 * dHQ_0 s1 q1 +
  dHS_0 s1 q1 * dHQ_1 s2 q2 v2 - dHS_0 s2 q2 * dHQ_1 s1 q1 v1

def minor_U0 {R : Type*} [Field R] (s1 q1 s2 q2 : R) : R :=
  dHS_0 s1 q1 * dHQ_0 s2 q2 - dHS_0 s2 q2 * dHQ_0 s1 q1


def d20_U3 {R : Type*} [Field R] (a b xS xQ : R) : R := minor_U3 a b 0 xS xQ 1
def d20_U2 {R : Type*} [Field R] (a b xS xQ : R) : R := minor_U2 a b 0 xS xQ 1
def d20_U1 {R : Type*} [Field R] (a b xS xQ : R) : R := minor_U1 a b 0 xS xQ 1
def d20_U0 {R : Type*} [Field R] (a b xS xQ : R) : R := minor_U0 a b xS xQ

def d21_U3 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U3 a b 0 (a + xS) (b + xQ) 0 - minor_U3 a b 0 xS xQ 0 + (10 / 7 : R) * b * dHS_2 a b
def d21_U2 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U2 a b 0 (a + xS) (b + xQ) 0 - minor_U2 a b 0 xS xQ 0 + (10 / 7 : R) * b * dHS_1 a b
def d21_U1 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U1 a b 0 (a + xS) (b + xQ) 0 - minor_U1 a b 0 xS xQ 0 + (10 / 7 : R) * b * dHS_0 a b
def d21_U0 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U0 a b (a + xS) (b + xQ) - minor_U0 a b xS xQ

def d10_U3 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U3 (a + xS) (b + xQ) 0 xS xQ 1 - minor_U3 a b 0 xS xQ 1 - minor_U3 xS xQ 0 xS xQ 1 -
    (10 / 7 : R) * b * dHS_2 xS xQ
def d10_U2 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U2 (a + xS) (b + xQ) 0 xS xQ 1 - minor_U2 a b 0 xS xQ 1 - minor_U2 xS xQ 0 xS xQ 1 -
    (10 / 7 : R) * b * dHS_1 xS xQ
def d10_U1 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U1 (a + xS) (b + xQ) 0 xS xQ 1 - minor_U1 a b 0 xS xQ 1 - minor_U1 xS xQ 0 xS xQ 1 -
    (10 / 7 : R) * b * dHS_0 xS xQ
def d10_U0 {R : Type*} [Field R] (a b xS xQ : R) : R :=
  minor_U0 (a + xS) (b + xQ) xS xQ - minor_U0 a b xS xQ - minor_U0 xS xQ xS xQ

def numM_Uk {R : Type*} [Field R] (k : Fin 4) (mi : Fin 10) (a b xS xQ : R) : R :=
  let (d10, d20, d21) : R × R × R := match k with
    | 0 => (d10_U0 a b xS xQ, d20_U0 a b xS xQ, d21_U0 a b xS xQ)
    | 1 => (d10_U1 a b xS xQ, d20_U1 a b xS xQ, d21_U1 a b xS xQ)
    | 2 => (d10_U2 a b xS xQ, d20_U2 a b xS xQ, d21_U2 a b xS xQ)
    | 3 => (d10_U3 a b xS xQ, d20_U3 a b xS xQ, d21_U3 a b xS xQ)
  let (m2, m1, m0) : R × R × R := match mi with
    | 0 => (a ^ 2, 2 * a * xS, xS ^ 2)
    | 1 => (a * b, a * xQ + b * xS, xS * xQ)
    | 2 => (b ^ 2, 2 * b * xQ, xQ ^ 2)
    | 3 => (a, xS, 0)
    | 4 => (0, a, xS)
    | 5 => (b, xQ, 0)
    | 6 => (0, b, xQ)
    | 7 => (1, 0, 0)
    | 8 => (0, 1, 0)
    | 9 => (0, 0, 1)
  (1 / 16 : R) * (m2 * d10 - m1 * d20 + m0 * d21)


def A0V_Uk {R : Type*} [Field R] (k : Fin 4) (a b xS xQ : R) : R :=
  -(892 / 3645 : R) * (5 * numM_Uk k 3 a b xS xQ - 9 * numM_Uk k 4 a b xS xQ) +
   (40 / 81) * (5 * numM_Uk k 5 a b xS xQ - 9 * numM_Uk k 6 a b xS xQ) -
   (112 / 2395) * (5 * numM_Uk k 7 a b xS xQ - 9 * numM_Uk k 8 a b xS xQ) +
   (392 / 11975) * (5 * numM_Uk k 8 a b xS xQ - 9 * numM_Uk k 9 a b xS xQ)

def AX_Uk {R : Type*} [Field R] (k : Fin 4) (a b xS xQ : R) : R :=
  -(8 / 405 : R) * (5 * numM_Uk k 3 a b xS xQ - 9 * numM_Uk k 4 a b xS xQ) -
   (476 / 7185) * (5 * numM_Uk k 7 a b xS xQ - 9 * numM_Uk k 8 a b xS xQ) +
   (6916 / 35925) * (5 * numM_Uk k 8 a b xS xQ - 9 * numM_Uk k 9 a b xS xQ)


def A0V_U3_lead3_fn {R : Type*} [Field R] (S Q T aa ab : R) : R :=
  -(1 / 4949782425 : R) * (5 * T - 9) *
    (-7728665 * Q ^ 2 * aa ^ 3 - 1746360 * Q * T * aa ^ 3 + 15457330 * S * Q * aa ^ 2 * ab +
     21962150 * Q ^ 2 * aa ^ 2 * ab + 1746360 * S * T * aa ^ 2 * ab + 10001880 * Q * T * aa ^ 2 * ab -
     7728665 * S ^ 2 * aa * ab ^ 2 - 43924300 * S * Q * aa * ab ^ 2 - 10001880 * S * T * aa * ab ^ 2 -
     14288400 * Q * T * aa * ab ^ 2 + 21962150 * S ^ 2 * ab ^ 3 + 14288400 * S * T * ab ^ 3 +
     6563302 * Q * aa ^ 3 - 6563302 * S * aa ^ 2 * ab - 39046416 * Q * aa ^ 2 * ab -
     1020600 * T * aa ^ 2 * ab + 39046416 * S * aa * ab ^ 2 + 58069530 * Q * aa * ab ^ 2 +
     6123600 * T * aa * ab ^ 2 - 58069530 * S * ab ^ 3 - 9185400 * T * ab ^ 3 +
     5340850 * aa ^ 3 - 42108180 * aa ^ 2 * ab + 108446130 * aa * ab ^ 2 - 90567720 * ab ^ 3)


lemma dual_div_eq_iff {R : Type*} [Field R] (a b c : Dual R) (hb : b.val ≠ 0) :
    a * ⟨b.val⁻¹, -b.eps / b.val ^ 2⟩ = c ↔ a = b * c := by
  constructor
  · intro h; rw [← h]
    ext
    · simp only [Dual.mul_val]; field_simp [hb]
    · simp only [Dual.mul_val, Dual.mul_eps]; field_simp [hb]; ring
  · intro h; rw [h]
    ext
    · simp only [Dual.mul_val]; field_simp [hb]
    · simp only [Dual.mul_val, Dual.mul_eps]; field_simp [hb]; ring

-- Purely symbolic log-derivative identity for `W1_inf_weights_alg` (no unfolding of concrete polynomials!):

lemma ofNat_ne_zero {R : Type*} [Field R] [CharZero R] (n : ℕ) [n.AtLeastTwo] :
    (no_index (OfNat.ofNat n) : R) ≠ 0 := by
  rw [← Nat.cast_ofNat (R := R) (n := n)]
  exact Nat.cast_ne_zero.mpr (NeZero.ne n)


lemma ring_regroup8 {R : Type*} [Field R] (a b c1 c2 d1 d2 e f g h : R) :
    a + b - c1 / c2 - d1 / d2 - e - f - g + h =
      (a + b + (-c1 / c2) + (-d1 / d2)) + (-e - f - g + h) := by ring

def w1_Bv2 {R : Type*} [Field R] (S Q : R) : R := -(4 / 243 : R) * (S - 3 * Q) ^ 3
def w1_Bv1 {R : Type*} [Field R] (S Q T : R) : R :=
  (143 / 243 : R) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3 +
  (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 + (52 / 9) * T - (22 / 9) + (5 / 7) * Q ^ 2 + (10 / 7) * Q
def w1_Cv0 {R : Type*} [Field R] (T : R) : R := -(25 / 243 : R) * T * (5 * T - 9) ^ 2
def w1_w0 {R : Type*} [Field R] (S Q T : R) : R := -w1_Cv0 T / w1_Bv2 S Q
def w1_w1 {R : Type*} [Field R] (S Q T : R) : R := w1_Cv0 T * w1_Bv1 S Q T / w1_Bv2 S Q ^ 2
def w1_WD {R : Type*} [Field R] (S Q T : R) : Dual R := ⟨w1_w0 S Q T, w1_w1 S Q T⟩
def w1_cbD {R : Type*} [Field R] (S Q : R) : Dual R :=
  ⟨(4 / 27 : R) * (S - 3 * Q) ^ 2, -(92 / 27 : R) * S ^ 2 + (104 / 9) * S * Q - (22 / 3) * Q ^ 2 + (10 / 7) * Q + (10 / 7)⟩
def w1_c0_0 {R : Type*} [Field R] (T : R) : R := -(25 / 81 : R) * (5 * T - 9) * (5 * T - 3)
def w1_k2_0 {R : Type*} [Field R] (T : R) : R := -(125 / 81 : R) * (5 * T - 6)
def w1_k3_0 (R : Type*) [Field R] : R := -(625 / 243 : R)
def w1_D22 {R : Type*} [Field R] (S Q : R) : Dual R := ⟨Q5_c5 S Q, Q5_c4 S Q⟩
def w1_D21_v {R : Type*} [Field R] (S Q T : R) : R := p21_c3 S Q * w1_c0_0 T
def w1_D20_v {R : Type*} [Field R] (S Q T : R) : R :=
  (-(4 / 9 : R) * S + (4 / 3) * Q) * w1_c0_0 T ^ 2 + (w1_cbD S Q).val ^ 2 * (w1_w0 S Q T * w1_k2_0 T)
def w1_D20 {R : Type*} [Field R] (S Q T d20e : R) : Dual R := ⟨w1_D20_v S Q T, d20e⟩
def w1_D33 {R : Type*} [Field R] (S Q : R) : Dual R := ⟨Q7_c7 S Q, Q7_c6 S Q⟩
def w1_D32_v {R : Type*} [Field R] (S Q T : R) : R := p32_c5 S Q * w1_c0_0 T
def w1_D31_v {R : Type*} [Field R] (S Q T : R) : R := p31_c3 S Q * w1_c0_0 T ^ 2
def w1_D30_v {R : Type*} [Field R] (S Q T : R) : R :=
  -(4 / 9 : R) * w1_c0_0 T ^ 3 + (w1_cbD S Q).val ^ 3 * (w1_w0 S Q T ^ 2 * w1_k3_0 R)
def w1_diff12_v {R : Type*} [Field R] (S Q T : R) : R :=
  (w1_D22 S Q).val * w1_D32_v S Q T - w1_D21_v S Q T * (w1_D33 S Q).val
def w1_d1_main {R : Type*} [Field R] (S Q T d20e : R) : Dual R := -(w1_D22 S Q * w1_D20 S Q T d20e * w1_D33 S Q)
def w1_d1_sub_v {R : Type*} [Field R] (S Q T : R) : R :=
  (w1_D22 S Q).val ^ 2 * w1_D31_v S Q T - w1_D21_v S Q T * w1_diff12_v S Q T
def w1_d1_D {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  ⟨(w1_d1_main S Q T d20e).val, (w1_d1_main S Q T d20e).eps + w1_d1_sub_v S Q T⟩
def w1_d0_v {R : Type*} [Field R] (S Q T : R) : R :=
  (w1_D22 S Q).val ^ 2 * w1_D30_v S Q T - w1_D20_v S Q T * w1_diff12_v S Q T
def w1_res_main {R : Type*} [Field R] (S Q T d20e : R) : Dual R := w1_D20 S Q T d20e ^ 3 * w1_D33 S Q ^ 2
def w1_res_sub_v {R : Type*} [Field R] (S Q T : R) : R :=
  -w1_D21_v S Q T * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val * w1_D32_v S Q T +
  (w1_D22 S Q).val * w1_D20_v S Q T ^ 2 * w1_D32_v S Q T ^ 2 -
  2 * (w1_D22 S Q).val * w1_D20_v S Q T ^ 2 * (w1_D33 S Q).val * w1_D31_v S Q T +
  3 * (w1_D22 S Q).val * w1_D21_v S Q T * w1_D20_v S Q T * (w1_D33 S Q).val * w1_D30_v S Q T -
  2 * (w1_D22 S Q).val ^ 2 * w1_D20_v S Q T * w1_D32_v S Q T * w1_D30_v S Q T +
  (w1_D22 S Q).val ^ 3 * w1_D30_v S Q T ^ 2
def w1_res_D {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  ⟨(w1_res_main S Q T d20e).val, (w1_res_main S Q T d20e).eps + w1_res_sub_v S Q T⟩
def w1_num_pref {R : Type*} [Field R] (S Q T : R) : Dual R := -(w1_WD S Q T * w1_cbD S Q ^ 4)
def w1_den_pref {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  Dual.C (81 : R) * ⟨w1_Bv2 S Q, w1_Bv1 S Q T⟩ * w1_D22 S Q ^ 3 * w1_res_D S Q T d20e
def w1_P0_4_D {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  ⟨(w1_D22 S Q * w1_D20 S Q T d20e ^ 2).val,
   (w1_D22 S Q * w1_D20 S Q T d20e ^ 2).eps - w1_D21_v S Q T ^ 2 * w1_D20_v S Q T⟩
def w1_P1_4_v {R : Type*} [Field R] (S Q T : R) : R :=
  2 * (w1_D22 S Q).val * w1_D21_v S Q T * w1_D20_v S Q T
def w1_C4_D {R : Type*} [Field R] (S Q T d20e : R) : Dual R :=
  ⟨(-(w1_P0_4_D S Q T d20e * w1_d1_D S Q T d20e)).val,
   (-(w1_P0_4_D S Q T d20e * w1_d1_D S Q T d20e)).eps + w1_P1_4_v S Q T * w1_d0_v S Q T⟩
def w1_C3_v {R : Type*} [Field R] (S Q T d20e : R) : R :=
  (-(w1_D22 S Q).val ^ 2 * w1_D20_v S Q T) * w1_d0_v S Q T -
  ((w1_D22 S Q).val * w1_D21_v S Q T * w1_D20_v S Q T) * (w1_d1_main S Q T d20e).val
def w1_C2_v {R : Type*} [Field R] (S Q T d20e : R) : R :=
  ((w1_D22 S Q).val ^ 2 * w1_D20_v S Q T) * (w1_d1_main S Q T d20e).val
def w1_A4_3 {R : Type*} [Field R] (S Q T : R) : R :=
  -(279006525 / 64 : R) * T * (5 * T - 9) ^ 2 / ((S - 3 * Q) ^ 8 * (77 * S - 210 * Q + 45))
def w1_A4_4 {R : Type*} [Field R] (S Q T : R) : R :=
  (13286025 / 12544 : R) * T * (5 * T - 9) ^ 2 * P44_fn S Q T / ((S - 3 * Q) ^ 11 * (77 * S - 210 * Q + 45) ^ 2)
def w1_A3_4 {R : Type*} [Field R] (S Q T : R) : R :=
  (531441 / 448 : R) * T * (5 * T - 9) * (35 * S * T + 133 * S - 420 * Q + 225 * T - 45) / (S - 3 * Q) ^ 8
def w1_A2_4 {R : Type*} [Field R] (S Q T : R) : R :=
  -(177147 / 400 : R) * T / (S - 3 * Q) ^ 5


/-- Bundled pure-field leading-degree-3 and dual-jet identities for `U = ∞`. -/
structure LocalInfLead3AlgSpec : Prop where
  A0V_U3_poly : ∀ {R : Type} [Field R] [CharZero R] (S Q T u : R),
    T ≠ 0 → 5 * T - 9 ≠ 0 →
    let β : R := -(S - 3 * Q) * (5 * T - 3) / (3 * T * (5 * T - 9))
    A0V_Uk 3 u (u / 3 + β) (S - u * T) (Q - (u / 3 + β) * T) =
      ((73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2) * u ^ 3 +
      (A32_2_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (14849347275 * (3 * T * (5 * T - 9)))) * u ^ 2 +
      (A32_1_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / (4949782425 * (3 * T * (5 * T - 9)) ^ 2)) * u +
      A0V_Uk 3 0 β S (Q - β * T)
  A0V_U3_lead3_eq : ∀ {R : Type} [Field R] [CharZero R] (S Q T aa ab b0 : R),
    let f := fun z : R => A0V_Uk 3 (aa * z) (ab * z + b0) (S - aa * z * T) (Q - (ab * z + b0) * T)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 = A0V_U3_lead3_fn S Q T aa ab
  A0V_U2_lead3_at_third : ∀ {R : Type} [Field R] [CharZero R] (S Q T aa b0 : R),
    let f := fun z : R => A0V_Uk 2 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      aa ^ 3 * ((1 / 53457650190 : R) * (5 * T - 9) *
        (-50137409 * S ^ 2 + 300824454 * S * Q - 451236681 * Q ^ 2 - 10001880 * S * T +
         30005640 * Q * T - 45873099 * S + 137619297 * Q - 10103940 * T + 58998753))
  AX_U3_lead3_at_third : ∀ {R : Type} [Field R] [CharZero R] (S Q T aa b0 : R),
    let f := fun z : R => AX_Uk 3 (aa * z) ((aa / 3) * z + b0) (S - aa * z * T) (Q - ((aa / 3) * z + b0) * T)
    (f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6 =
      aa ^ 3 * ((2 / 885735 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2)
  M01_dual_combine : ∀ {R : Type} [Field R] [CharZero R] (S Q T : R),
    let Bv1 : R := (143 / 243 : R) * S ^ 3 - (92 / 27) * S ^ 2 * Q + (52 / 9) * S * Q ^ 2 - (22 / 9) * Q ^ 3 +
      (143 / 243) * T ^ 3 - (92 / 27) * T ^ 2 + (52 / 9) * T - (22 / 9) + (5 / 7) * Q ^ 2 + (10 / 7) * Q
    let w1w0_sc : R := (243 / 4 : R) * Bv1
    let rb_sc : R := -(3 / 28 : R) * (S - 3 * Q) * (119 * S ^ 2 - 560 * S * Q + 630 * Q ^ 2 + 90 * Q + 90)
    let c0 : R := (73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2
    let dc0 : R := -(2 / 2121335325 : R) * (5 * T - 9) * (-464630 * S + 1568725 * Q + 34020 * T - 23814) * (-S + 3 * Q)
    let c2 : R := (1 / 53457650190 : R) * (5 * T - 9) *
      (-50137409 * S ^ 2 + 300824454 * S * Q - 451236681 * Q ^ 2 - 10001880 * S * T +
       30005640 * Q * T - 45873099 * S + 137619297 * Q - 10103940 * T + 58998753);
    -2 * w1w0_sc * c0 + (rb_sc / 3) * dc0 + (S - 3 * Q) ^ 3 * c2 =
      M01_q_fn S Q T * (5 * T - 9) * (S - 3 * Q) / 267288250950
  A0V_U3_lead3_dual : ∀ {R : Type} [Field R] [CharZero R] (S Q T r1 : R),
    let c0 : R := (73 / 7971615 : R) * (5 * T - 9) * (S - 3 * Q) ^ 2
    let dc0 : R := -(2 / 2121335325 : R) * (5 * T - 9) * (-464630 * S + 1568725 * Q + 34020 * T - 23814) * (-S + 3 * Q)
    (-(1 / 4949782425 : R) * (5 * T - 9) *
      (-7728665 * Q ^ 2 - 1746360 * Q * T + 15457330 * S * Q * (1 / 3 : R) +
       21962150 * Q ^ 2 * (1 / 3) + 1746360 * S * T * (1 / 3) + 10001880 * Q * T * (1 / 3) -
       7728665 * S ^ 2 * (1 / 3) ^ 2 - 43924300 * S * Q * (1 / 3) ^ 2 - 10001880 * S * T * (1 / 3) ^ 2 -
       14288400 * Q * T * (1 / 3) ^ 2 + 21962150 * S ^ 2 * (1 / 3) ^ 3 + 14288400 * S * T * (1 / 3) ^ 3 +
       6563302 * Q - 6563302 * S * (1 / 3) - 39046416 * Q * (1 / 3) -
       1020600 * T * (1 / 3) + 39046416 * S * (1 / 3) ^ 2 + 58069530 * Q * (1 / 3) ^ 2 +
       6123600 * T * (1 / 3) ^ 2 - 58069530 * S * (1 / 3) ^ 3 - 9185400 * T * (1 / 3) ^ 3 +
       5340850 - 42108180 * (1 / 3) + 108446130 * (1 / 3) ^ 2 - 90567720 * (1 / 3) ^ 3) = c0) ∧
    (-(1 / 4949782425 : R) * (5 * T - 9) *
      ((15457330 * S * Q + 21962150 * Q ^ 2 + 1746360 * S * T + 10001880 * Q * T -
        6563302 * S - 39046416 * Q - 1020600 * T - 42108180) +
       2 * (-7728665 * S ^ 2 - 43924300 * S * Q - 10001880 * S * T - 14288400 * Q * T +
        39046416 * S + 58069530 * Q + 6123600 * T + 108446130) * (1 / 3 : R) +
       3 * (21962150 * S ^ 2 + 14288400 * S * T - 58069530 * S - 9185400 * T - 90567720) * (1 / 3 : R) ^ 2) * r1 =
      dc0 * r1)

/-- Bundled pure-field `W1_inf` dual-weight identities. -/
structure LocalInfWeightsAlgSpec : Prop where
  W1_inf_weights_alg : ∀ {R : Type} [Field R] [CharZero R] (S Q T d20e : R),
    S - 3 * Q ≠ 0 → 77 * S - 210 * Q + 45 ≠ 0 → 5 * T - 9 ≠ 0 →
    (w1_res_D S Q T d20e).val =
      -(64000000000000 / 6461081889226673298932241 : R) * (5 * T - 9) ^ 6 * (S - 3 * Q) ^ 15 ∧
    (w1_den_pref S Q T d20e).val ≠ 0 ∧
    w1_num_pref S Q T * w1_C4_D S Q T d20e =
      w1_den_pref S Q T d20e * ⟨w1_A4_3 S Q T, w1_A4_4 S Q T⟩ ∧
    (w1_num_pref S Q T).val * w1_C3_v S Q T d20e =
      (w1_den_pref S Q T d20e).val * w1_A3_4 S Q T ∧
    (w1_num_pref S Q T).val * w1_C2_v S Q T d20e =
      (w1_den_pref S Q T d20e).val * w1_A2_4 S Q T

end SymmetricSexticResidual.LocalResidueInfAlg


