-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TableDegreeElevenProduct
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_TableDegreeElevenProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:12.277258+00:00
-- url     : https://prove2.me/theorems/804dab00-3341-4271-bb06-bbb5736ec35b
-- title:
--   Table Degree Eleven Product
-- statement:
--   Definitions and structural lemmas for Table Degree Eleven Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TableDegreeElevenProduct.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.OT
def lse (x : ℝ) : ℝ := Real.log (Real.exp x + 1)
def xl (x : ℝ) : ℝ := x * Real.log (max 1 x)
def lf (n : ℕ) : ℝ := Real.log (n.factorial : ℝ)
structure Num where
  D : ℕ
  DX : ℕ
  f : ℝ
  r : ℝ
  m : ℝ
  L : ℝ
  j : ℝ
  nW : ℝ
  Np : ℝ
  lrd : ℝ
  LL : ℝ
  lM : ℝ
  lg : ℝ
  lg1 : ℝ
  lp : ℝ
  ld : ℝ
  l4 : ℝ
  l2q : ℝ
  lx : ℝ
  llx : ℝ
  n : ℝ
  w : ℝ
  a : ℝ
  ka : ℝ
  u1 : ℝ
  DF : ℝ
  DFs : ℝ
  RTc : ℝ
  lh : ℝ
  lNc : ℝ
  lpi : ℝ
  lmu : ℝ
  lmu1 : ℝ
  V : ℝ
  hb : ℝ
  logGenusConstant : ℝ
  dS : ℝ
  rS : ℝ
  dP : ℝ
  rP : ℝ
  lNA : ℝ
  Om : ℝ
  nu : ℝ
  lc : ℝ
  leE : ℝ
  ln0 : ℝ
  c1 : ℝ
  sc1 : ℝ
  G1 : ℝ
  CL : ℝ
  lR : ℝ
  rho : ℝ
  dp : ℝ
  gC : ℝ
namespace Num
variable (N : Num)
def Z : ℝ := N.f * N.r * N.L
def b : ℝ := Real.exp N.L
def r2 : ℝ := N.r ^ 2 - 1
def mono (a b c d : ℕ) : ℝ := N.f ^ a * N.r ^ b * N.m ^ c * N.L ^ d
structure H0 : Prop where
  f_ge : 8 ≤ N.f
  r_ge : 9 ≤ N.r
  m_ge : 2 ≤ N.m
  L_ge : 10 ≤ N.L
  fourth_power_le_degree : N.m ^ 4 ≤ N.f
  f_le : N.f ≤ N.r
  zBase_pow_twelve_le : N.Z ^ 12 ≤ N.b
  j_ge : 0 ≤ N.j
  j_le : N.j ≤ N.m
  D_ge : 4 / 9 * N.f * N.r ^ 2 ≤ (N.D : ℝ)
  D_le : (N.D : ℝ) ≤ N.f * N.r ^ 2 / 2
  DX_le : (N.DX : ℝ) ≤ N.f * N.r * N.m
  nW_ge : 40 ≤ N.nW
  nW_le : N.nW ≤ 11 * (N.f * N.r + N.f ^ 2 * N.r ^ 4 * N.L ^ 2 / N.m)
  Np_ge : 0 ≤ N.Np
  Np_le : N.Np ≤ 3 * N.f * N.r ^ 2
  lrd_ge : 1 ≤ N.lrd
  lrd_mem : 0 ≤ N.lrd ∧ N.lrd ≤ 30 * N.L
  LL_mem : 0 ≤ N.LL ∧ N.LL ≤ 30 * N.L
  lM_mem : 0 ≤ N.lM ∧ N.lM ≤ 30 * N.L
  lg_mem : 0 ≤ N.lg ∧ N.lg ≤ 30 * N.L
  genus_log_bound : 0 ≤ N.lg1 ∧ N.lg1 ≤ 30 * N.L
  lp_mem : 0 ≤ N.lp ∧ N.lp ≤ 30 * N.L
  ld_mem : 0 ≤ N.ld ∧ N.ld ≤ 30 * N.L
  fourth_log_bound : 0 ≤ N.l4 ∧ N.l4 ≤ 30 * N.L
  second_log_bound : 0 ≤ N.l2q ∧ N.l2q ≤ 30 * N.L
  lx_mem : 0 ≤ N.lx ∧ N.lx ≤ 30 * N.L
  llx_mem : 0 ≤ N.llx ∧ N.llx ≤ 30 * N.L
  n_mem : 1 ≤ N.n ∧ N.n ≤ N.b ^ 3
  w_mem : 1 ≤ N.w ∧ N.w ≤ N.b ^ 3
  ka_mem : 1 ≤ N.ka ∧ N.ka ≤ N.b ^ 3
  first_unit_bound : 1 ≤ N.u1 ∧ N.u1 ≤ N.b ^ 3
  DFs_mem : 1 ≤ N.DFs ∧ N.DFs ≤ N.b ^ 3
  a_mem : 0 ≤ N.a ∧ N.a ≤ N.b ^ 3
  DF_mem : 0 ≤ N.DF ∧ N.DF ≤ N.b ^ 3
  RTc_mem : 0 ≤ N.RTc ∧ N.RTc ≤ N.b ^ 3
  RTc_le : 2 * N.f ^ 2 * N.m ^ 3 * N.RTc ≤ N.b ^ 2
def hHat : ℝ := N.f * N.lrd + 2 * N.f * Real.log (1 + N.f * N.lrd)
def muHat : ℝ := Real.log 2 + N.hHat + 2 * N.f * (N.r ^ 2 + 1) * N.lM + N.f * (N.r ^ 2 - 1) / 2 * N.lrd
def ncHat : ℝ := max (N.hHat + 2 * N.f * N.lM) (N.muHat + N.f * N.r ^ 2 / 2 * Real.log N.r)
def dsHat : ℝ := 19 * N.f * N.r ^ 2 * N.L + 62 * N.f ^ 2 * N.L
def rsHat : ℝ := 19 * N.f * N.r ^ 2 * N.L + 198 * N.f * N.L
def omHat : ℝ := 2.42 + N.lrd + N.LL
def muLow : ℝ := -(N.f * N.r * Real.log 2) - N.f * N.r ^ 2 / 2 * Real.log N.r
def hat : Num :=
  { N with
    lh := N.hHat
    lNc := N.ncHat
    lpi := N.ncHat
    lmu := N.muHat
    lmu1 := max (N.f * N.r ^ 2 * N.lM + N.f * N.r ^ 2 / 2 * N.lrd + 2 * N.f) N.muHat
    V := 38 * N.f * N.r ^ 2 * N.L
    hb := N.f * N.r ^ 2 * N.lM
    logGenusConstant := 20 * N.f * N.r ^ 2 * N.L
    dS := N.dsHat
    rS := N.rsHat
    dP := N.dsHat + 60 * N.f * N.L + 1.4 * N.r + 1.4
    rP := N.rsHat + 30 * N.L
    lNA := 2 * N.lrd
    Om := N.omHat
    nu := 2 * N.L
    lc := 0
    leE := 2 * N.f * N.lrd
    ln0 := 4 * N.f * N.r ^ 2 * Real.log 5
    c1 := N.r / 2 * N.omHat
    sc1 := N.f * N.r / 2 * N.omHat
    G1 := 1009 * N.Z
    CL := N.Z
    lR := 40 * N.Z
    rho := N.m
    dp := 2 * N.f * N.m
    gC := N.f * N.m * N.r }
structure LetLow : Prop where
  lh : 0 ≤ N.lh
  lNc : 0 ≤ N.lNc
  lpi : 0 ≤ N.lpi
  lmu : N.muLow ≤ N.lmu
  lmu1 : N.muLow ≤ N.lmu1
  V : 0 ≤ N.V
  hb : 0 ≤ N.hb
  logGenusConstant : 0 ≤ N.logGenusConstant
  dS : 0 ≤ N.dS
  rS : 0 ≤ N.rS
  dP : 0 ≤ N.dP
  rP : 0 ≤ N.rP
  lNA : 0 ≤ N.lNA
  Om : 0 ≤ N.Om
  nu : 0 ≤ N.nu
  lc : 0 ≤ N.lc
  leE : 0 ≤ N.leE
  ln0 : 0 ≤ N.ln0
  c1 : 0 ≤ N.c1
  sc1 : 0 ≤ N.sc1
  G1 : 0 ≤ N.G1
  CL : 0 ≤ N.CL
  lR : 0 ≤ N.lR
  rho : 0 ≤ N.rho
  dp : 0 ≤ N.dp
  gC : 0 ≤ N.gC
structure LetLe (N N' : Num) : Prop where
  D : N.D = N'.D
  DX : N.DX = N'.DX
  f : N.f = N'.f
  r : N.r = N'.r
  m : N.m = N'.m
  L : N.L = N'.L
  j : N.j = N'.j
  nW : N.nW = N'.nW
  Np : N.Np = N'.Np
  lrd : N.lrd = N'.lrd
  LL : N.LL = N'.LL
  lM : N.lM = N'.lM
  lg : N.lg = N'.lg
  lg1 : N.lg1 = N'.lg1
  lp : N.lp = N'.lp
  ld : N.ld = N'.ld
  l4 : N.l4 = N'.l4
  l2q : N.l2q = N'.l2q
  lx : N.lx = N'.lx
  llx : N.llx = N'.llx
  n : N.n = N'.n
  w : N.w = N'.w
  a : N.a = N'.a
  ka : N.ka = N'.ka
  u1 : N.u1 = N'.u1
  DF : N.DF = N'.DF
  DFs : N.DFs = N'.DFs
  RTc : N.RTc = N'.RTc
  lh : N.lh ≤ N'.lh
  lNc : N.lNc ≤ N'.lNc
  lpi : N.lpi ≤ N'.lpi
  lmu : N.lmu ≤ N'.lmu
  lmu1 : N.lmu1 ≤ N'.lmu1
  V : N.V ≤ N'.V
  hb : N.hb ≤ N'.hb
  logGenusConstant : N.logGenusConstant ≤ N'.logGenusConstant
  dS : N.dS ≤ N'.dS
  rS : N.rS ≤ N'.rS
  dP : N.dP ≤ N'.dP
  rP : N.rP ≤ N'.rP
  lNA : N.lNA ≤ N'.lNA
  Om : N.Om ≤ N'.Om
  nu : N.nu ≤ N'.nu
  lc : N.lc ≤ N'.lc
  leE : N.leE ≤ N'.leE
  ln0 : N.ln0 ≤ N'.ln0
  c1 : N.c1 ≤ N'.c1
  sc1 : N.sc1 ≤ N'.sc1
  G1 : N.G1 ≤ N'.G1
  CL : N.CL ≤ N'.CL
  lR : N.lR ≤ N'.lR
  rho : N.rho ≤ N'.rho
  dp : N.dp ≤ N'.dp
  gC : N.gC ≤ N'.gC
structure admitted : Prop where
  h0 : N.H0
  low : N.LetLow
  le : LetLe N N.hat
def frM : ℝ := N.f * N.r * N.lM
def lrho0 : ℝ := Real.log (2 * N.f) / 2 + Real.log (N.n) + N.lrd
def X2 : ℝ := (max (0) (N.lM + Real.log (N.f * N.w) + N.ld / 2 + Real.log (1.77)))
def B : ℝ := N.lM + N.nu + N.lrd + Real.log (N.f * N.r * N.n * N.w * (N.a + 2))
def PLam : ℝ := N.f * N.r * (24 * N.B + 1.04)
def AO : ℝ := (max (N.dS + N.rS) (N.dP + N.rP))
def o : ℝ := N.dP + N.rP
def Ls : ℝ := N.lg + N.l4
def Lp : ℝ := N.Ls + 2 * N.lp
def Lp9 : ℝ := (max (9 * N.Lp) (1 + N.Ls))
def G : ℝ := N.G1 + 3 * N.L + 2 * N.AO + 2 * N.f * N.r * N.Lp + 31 * N.f * N.r * N.L
def lrw : ℝ := N.f * N.r * N.nW * (N.lM + 1 + 1.5 * Real.log (1 + N.DF)) + (max (N.dS) (N.dP)) + Real.log (2)
def muM : ℝ := Real.log (2) + N.lh + 2 * N.f * (N.r * N.r + 1) * N.lM + N.f * N.r2 * N.lrd / 2
def P7 : ℝ := 2 + (N.D : ℝ) * Real.log (510 * N.r * N.r) + 4 * N.f * N.f * N.r * N.r * (Real.log (5 * N.f * N.r) + 1.5 * N.lrd + (max (0) (N.lM + Real.log (8 * N.f * N.w) + N.ld / 2))) + N.muM
def MU : ℝ := Real.log (2) + N.f * N.lrd + 2 * N.f * Real.log (1 + N.f * N.lrd) + 2 * N.f * (N.r * N.r + 1) * N.lM + N.f * N.r2 * N.lrd / 2 + N.f * N.r * N.r * Real.log (N.r) / 2
def tableDegreeTwoSeven : ℝ := 2 + lf N.DX + (N.DX : ℝ) * Real.log ((max (4) (16 * N.f * N.r * N.w))) + 4 * N.f * N.f * N.r * N.r * (Real.log (7 * N.f * N.r) + 1.5 * N.lrd + (max (0) (N.lM + Real.log (8 * N.f * N.w) + N.ld / 2 + Real.log (1.77)))) + N.MU + N.f * N.r * N.r * Real.log (1 + 16 * N.w)
def Psk : ℝ := N.P7 + lf N.D + (N.D : ℝ) * Real.log (3.51 * N.r * (N.ka + 2 * N.r * N.f))
def sizeConstantAtParamsWeight : ℝ := (max (90 * (N.f * N.r + 1)) (max (360 * N.f * N.m ^ 3) (max (2 * (3 * N.r + 3 + N.r * Real.log (N.r))) (max (N.nW) (max (1250 * N.r) (max (N.f * N.r * N.r + 6) (11)))))))
def XB : ℝ := (2 * N.f * N.m) ^ 4 * N.nW + 2 * (2 * N.f * N.m) ^ 3
def PairingSeriesLinearForm : ℝ := (2 * N.f * N.m) ^ 4 / 4 + 2 * (2 * N.f * N.m) ^ 3
def flipOneThree : ℝ := (max (50894 * N.nW * N.m ^ 4 * (2 * N.f * N.m) ^ 4) (max (N.XB) (N.r * (2 * N.f * N.m) ^ 3)))
def tableLineDegreeFive : ℝ := (N.f * N.r * N.nW * N.lM + N.nW * (Real.log (24) + N.f * N.m * Real.log (4 * N.f * N.m)) + (N.r + 2) * Real.log (2) + Real.log (3.15)) / 2
def tableDegreeFiveBound : ℝ := N.tableLineDegreeFive + N.f * N.r * N.nW
def PR : ℝ := 390 * (1 + N.f * N.r * N.nW) * N.L
def p1 : ℝ := 1 + N.f * N.r * (Real.log (7) + (Real.log (N.f * N.r) + N.lM) / 2)
def p2 : ℝ := 1 + xl (3 * N.dp) / 3
def p3 : ℝ := N.r * (N.p1 + N.p2 + N.dp)
def p4 : ℝ := N.lNc + 2 * N.f * N.r * N.r * Real.log (5)
def tableDegreeTwoSixteen : ℝ := xl (312.5 * N.r * N.dp) + 312.5 * N.r * N.dp * (Real.log (4) + 7 * N.lrd + 2 * Real.log ((max (1) (N.dp))))
def tableLineDegreeTwo : ℝ := 1250 * (N.p3 + N.p4) + N.tableDegreeTwoSixteen
def Ap : ℝ := (max (1) (N.r * N.dp / 4))
def P0 : ℝ := N.p3 + N.Ap * (Real.log (2500 * N.Ap) + 7 * N.lrd + 2 * Real.log ((max (1) (N.dp))))
def Pet : ℝ := 1250 * (N.P0 + N.p4)
def tableDegreeTwoUpper : ℝ := 5 * N.PLam + 2 * N.lNc / (N.D : ℝ)
def PI4 : ℝ := 5 * (N.PLam + N.Ls) + 2 * N.lNc / (N.D : ℝ)
def M0 : ℝ := 2 * Real.sqrt (N.dp)
def PU : ℝ := N.f * N.r * (2 * N.lrd + 2 * Real.log (N.f * N.r) + 3)
def tableDegreeOneUnipotent : ℝ := 2 * N.f * N.r * (2 * N.lrd + 2 * Real.log (2 * N.f * N.r) + 3)
def primePairSetFirst : ℝ := 2 * N.PU + Real.log (2 * N.m) + N.lc
def N1 : ℝ := 2 * N.f * N.rho * N.rho
def tableDegreeOneSquareM : ℝ := 2 * N.f * N.m * N.m
def cnt : ℝ := N.lM + 2 * N.lrd + N.primePairSetFirst + 1
def P6 : ℝ := 2 * N.PU + 2 * N.lNA + 2 * N.lc + Real.log (3)
def tableLogDegreeOne : ℝ := N.lM + 4 * N.f * N.lrd
def lA : ℝ := lse (Real.log (2) + N.tableLogDegreeOne + Real.log (1 + N.RTc * N.dp * N.dp * N.rho / 2) + N.P6)
def RSt : ℝ := xl (N.N1) + N.N1 * N.lA + 2
def aar : ℝ := 12.57 * N.f * N.rho
def Par : ℝ := N.lR / 2 + N.lc + N.lrd + 2 * Real.log (2 * N.f * N.r)
def Pex : ℝ := xl (N.gC) + N.gC * (2 * N.lM + (4 * N.f + 3) * N.lrd + 3 * N.lc + 2 * Real.log (2 * N.f * N.r))
def Pbe : ℝ := N.lrd + N.lc + 3 * N.lg1 + N.Pex / 2 + N.gC * N.lR / 2
def Pdeg : ℝ := (1 + N.Om + N.lrd) / 2
def tableDegreeThreeBase : ℝ := 3 * N.lrd + 12.57 * (xl (4 * N.tableDegreeOneSquareM) / 4 + N.tableDegreeOneSquareM * N.cnt + 4) + N.primePairSetFirst + 2 * Real.log (2 * N.f * N.r) + 1 + N.Pdeg
def tableDegreeThreeTripled : ℝ := 3 * N.tableDegreeThreeBase + 3 * N.lrd + 3
def r49 : ℝ := 3 * N.lrd + 3
def tableDegreeThreeScaled : ℝ := 3 * N.tableDegreeThreeBase + N.f * N.r * N.L
def T7 : ℝ := N.tableDegreeThreeBase + 2 * N.tableDegreeTwoSeven + 10 * (N.D : ℝ) * N.L + (max (N.rS) (N.rP)) / 2
def PO : ℝ := 19 * N.f * N.r * N.r * N.L + 198 * N.f * N.f * N.L
def Prw : ℝ := 38 * N.L + N.PO
def PN : ℝ := 2 * N.L + N.Ls + 4
def lbad : ℝ := N.l2q + N.lg + Real.log (15) + 2 * N.lp
def g0n : ℝ := 1250 * N.r
def n0 : ℝ := N.r + 2 * N.g0n * ((N.DX : ℝ) + 1)
def DivisibilityWeightConstant : ℝ := 45000 * (N.D : ℝ) * (N.D : ℝ) * N.f * N.f * N.r * N.r * N.m ^ 4
def Pd : ℝ := N.P7 + 8 * N.f * N.r * N.r * N.L
def PD : ℝ := 2 * N.G + N.Prw + N.tableDegreeThreeBase + 1.5 * (N.Pd + N.PO)
def PQ : ℝ := N.Pd / 2 + 12.57 * N.f * N.r + N.Par + N.G + N.Pdeg + N.Pbe
def PH : ℝ := N.tableDegreeThreeBase + N.PN + N.tableLineDegreeFive + (max (N.tableLineDegreeTwo) (N.Pet)) + N.PI4 + N.Prw
def P1 : ℝ := 60 * N.G + 180 * N.PH + 40 * N.PD
def P2 : ℝ := 5 * N.G * N.f * N.r * N.r + N.Pd
def P3 : ℝ := N.Pet / 2
def tableDegreeNineSquare : ℝ := (N.D : ℝ) * (N.D : ℝ) * N.P1
def tableDegreeElevenProduct : ℝ := N.Lp * N.DivisibilityWeightConstant
def c0 : ℝ := (N.DX : ℝ) * ((N.DX : ℝ) + 1) / 2
def s1 : ℝ := N.r + N.c0 + 2
def c0p : ℝ := (max (N.s1) (8 * N.f * N.r + 4)) + 7
def ESH : ℝ := 16 * N.f ^ 4 * N.r ^ 6 * N.m * N.m
def fr5 : ℝ := 5 * N.f * N.r * N.r
def ldg : ℝ := N.hb + N.lpi
def g0 : ℝ := N.f * N.r * N.c0p
def tableDegreeFiveTheta : ℝ := N.g0 * (1.5 * N.lM + 2 * Real.log (N.g0) + 6 * N.f * N.lrd + 4)
def Iq : ℝ := N.g0 * N.lM
def Ifr : ℝ := N.g0 * N.lrd + 2 * N.lrd
def c1s : ℝ := N.r * (3 + N.lrd + N.LL) / 2 + 3 * N.r * N.lrd
def Bbad : ℝ := 2 * N.lrd + Real.log (15) + N.lg
def MK : ℝ := N.f * N.c0p * (N.c1s + N.r * N.lrd) / 2 + N.Bbad + N.rP / 2
def rts : ℝ := 0.46 * N.g0
def TH : ℝ := N.tableDegreeFiveTheta + N.Iq + N.Ifr + N.MK + N.rts
def U0 : ℝ := N.TH + 2 * N.ldg
def tableDegreeFiveShifted : ℝ := N.U0 + N.rts
def PPh : ℝ := 1.5 * N.hb + N.U0
def tableLogDegreeOneTwelve : ℝ := Real.log (10000) + N.leE + N.f * N.lrd + 2 * Real.log (2 * N.f * N.m)
def cubicPeriodConstant : ℝ := 2 * (N.f * N.m * N.r + 8 * N.f ^ 3 * N.m * N.m * N.tableLogDegreeOneTwelve + xl (8 * N.f ^ 3 * N.m * N.m) + 3) + N.ln0
def PPA : ℝ := 3 * (N.D : ℝ) + 3 * N.cubicPeriodConstant
def Xde : ℝ := N.lmu + N.f * N.r * N.r * (1 + Real.log (N.r) / 2) + 3 * (N.D : ℝ) * N.L
def Xdel : ℝ := N.lmu1 + (N.D : ℝ) * Real.log ((N.D : ℝ) * N.u1)
def lr0 : ℝ := 2 * N.f * N.r * N.r * Real.log (5)
def Psup : ℝ := N.lr0 / 2 + N.P0 + 2 * N.f * N.r * N.r
def Xg : ℝ := 2 * N.Psup
def Pt0 : ℝ := N.lr0 / 2 + lse (N.Xde) + N.Psup
def LL0 : ℝ := (N.L + N.lrd) * N.llx + N.LL + N.lx
def Ac : ℝ := 1.5 * N.f * N.r ^ 4 * N.L
def Afr : ℝ := (N.f * N.r * N.r + 3) * N.f * N.r * N.lrd + 3 * N.l2q
def Aun : ℝ := 3 * N.lg + Real.log (15)
def PPe : ℝ := N.Ac + N.Afr + N.Aun
def X1 : ℝ := N.c0p * N.f * N.j + 4 * N.f * N.r * N.r
def Xe : ℝ := 200 * N.LL0 * N.X1
def PPeT : ℝ := N.PPe + N.Xe
def XW : ℝ := 66 * N.L + N.Np * N.f * N.r * N.lrd
def XSg : ℝ := 1200 * N.LL0 * N.f * N.r * N.r + N.PPe + N.XW + 1
def x28 : ℝ := 28 * N.logGenusConstant + 1
def xd3 : ℝ := (max (N.r * N.dp ^ 3 / 50) (2 * (2 * N.f * N.m) ^ 3))
def gG : ℝ := 20 * N.f * N.r * N.r * N.L
def cC : ℝ := Real.log (4 * N.f * N.f * N.r * N.r * (N.ka + 1)) + N.lrd
def lbe : ℝ := N.P7 + 2 * (N.D : ℝ) * Real.log ((N.D : ℝ) * N.ka) + N.V
def Xbe : ℝ := N.P7 + (N.DX : ℝ) * Real.log (N.f * N.r * N.r)
def lMs : ℝ := N.dP / 2 + N.rP
def Ath : ℝ := N.G + 31 * N.f * N.r * N.L
def Afl : ℝ := N.c1 + N.j * N.lrd
def Bfl : ℝ := 35 * N.L + N.rP / 2
def B7 : ℝ := N.P7 + 6 * (N.D : ℝ) * N.L
def Bt : ℝ := N.B7 + N.V
def product_zeroth_terms : ℝ := N.B7 / 2
def Gka : ℝ := 3 * N.G
def B0 : ℝ := N.Bfl + 1.5 * N.dP + N.rP + N.B7
def Xn : ℝ := N.dP + N.B7
def rtN : ℝ := 0.46 * N.f * N.r * N.Np
def rt8 : ℝ := 0.46 * N.f * N.r * 24 * ((N.D : ℝ) + 3) * N.r
def A1 : ℝ := (N.r + 1) * N.Ath + N.Afl
def tableDegreeThreeBase' : ℝ := N.A1 + 1
def B1 : ℝ := N.Ath * (N.f * N.r * (N.Np + 1) + N.Np) + N.Afl * N.f * (N.Np + 1) + N.B0 + N.rtN
def B2 : ℝ := (3 * (N.D : ℝ) + 13) * N.f * N.r * N.r * N.A1 + N.B1 + N.Xn + lse (N.Xde)
def Xt : ℝ := N.PPA / 2 + 1.5 * (N.lr0 + 2 * N.Xde + 2 + N.Xg) + 1.5 * N.r * N.sc1 + 4.5 * N.f * N.r * N.j * N.lrd + 1.5 * N.f * N.r * N.r * (1 + N.lrd)
def XJ : ℝ := N.lM + 2 * (N.l2q + N.lM) + 3 * N.lrd
def JJ : ℝ := (N.D : ℝ) * N.XJ
def aJ : ℝ := (((N.D : ℝ) + 4) * N.A1 + ((N.D : ℝ) + 3) * (400 * N.LL0 + 0.5)) / (N.D : ℝ)
def tJ : ℝ := 6 * N.f * N.r * N.r * N.A1
def cJ : ℝ := N.XSg + N.Xt + (2 * N.B1 + N.B2 + N.Bfl + N.JJ + 101 * (N.D : ℝ) * N.L + (N.Xde + N.lbe) / 2) / ((N.D : ℝ) + 3)
def x33 : ℝ := (3 * (N.D : ℝ) + 10) * 33 * N.L
def x3j : ℝ := 3 * N.j * N.f * (N.Np + 2)
def x4 : ℝ := N.Np * (N.sc1 + N.f * N.j * N.lrd) / 2
def x6 : ℝ := N.r * (N.sc1 + N.f * N.j * N.lrd) + 35 * N.L
def xfr : ℝ := 4.5 * N.f * N.r * N.m * N.lrd + 1.5 * N.f * N.r * N.c1
def r58 : ℝ := 12 * ((N.D : ℝ) + 3) * N.r * N.sc1 / (N.D : ℝ) + 6 * N.f * N.r * N.r * N.L
def xint : ℝ := 30 * N.f * N.r * N.L + N.lrd + N.l2q
def xk : ℝ := N.ld / 2 + N.lc + Real.log (2) + N.lrd
def xla : ℝ := 2 * N.lrho0 + Real.log (2 * N.f)
def xCd : ℝ := 2 * N.f * N.f * Real.sqrt (N.f) * N.rho * N.rho
def ldE : ℝ := 2 * N.f * N.lrd
def lDF : ℝ := Real.log (N.DFs)
def E0 : ℝ := N.f * N.r * (N.c0p + 4 * N.r)
def CLE : ℝ := N.CL * N.LL0 * N.E0
def tableDegreeThreeSecondValue : ℝ := 2 * (1 + N.r) * N.G + N.c1 + N.m * N.lrd
def A0 : ℝ := (2 * N.r * N.G + N.c1 + N.m * N.lrd) * N.f * (N.Np + 1 + 3 * N.r) + 2 * N.G * N.Np + 35 * N.L + 3 * N.o + N.B7 + N.rtN
def PPp : ℝ := 10 * ((N.tableDegreeThreeSecondValue + N.CL * N.LL0) * (1 + N.E0) + N.A0 + N.Gka + 3 * N.tableDegreeThreeBase + N.f * N.r * N.L + N.B7 + N.hb + N.gG)
def PPp1 : ℝ := N.PPp + 1 + N.lrd
def al : ℝ := 26 * (N.o + 2 * N.B7 + 4 * N.L + N.tableDegreeThreeSecondValue + N.A0)
def Pa : ℝ := 4.5 * N.f * N.r * N.m + 1.5 * N.f * N.r * N.r + 12 * N.f * N.m * (N.Np + 1)
def Pinf : ℝ := 2 * N.Pt0 + N.PPA + 2 * N.f * N.r * N.c1 + 7 * N.f * N.r * N.r + 2 * N.lNc
def Pfl : ℝ := 3 * N.f * N.r * (N.c1 + 3 * N.m * N.lrd) + 35 * N.L
def xn : ℝ := ((N.D : ℝ) + 1) * (N.o + N.B7 + 1) + 6
def xA : ℝ := 1352 * (N.L + Real.log (1352)) + 4
def QJ : ℝ := 4 * N.tableDegreeThreeSecondValue * N.f * N.r * N.r + 3 * N.A0 + 4 * N.B7 + N.V + N.o + 40 * N.L + N.PPe + N.PPA + 3 * N.Pt0 + 12 * N.f * N.r * (N.c1 + N.m * N.lrd) + 1.5 * N.f * N.r * N.r * N.lrd
def Qc : ℝ := N.PPe + N.XW + 104 * N.L * N.Pa + 3 * N.Pinf
def QH : ℝ := N.xA + 26 * (N.al + N.L) + 2 * N.Bt + N.xn + 1 + N.al + N.Bt / 2 + N.Pfl
def Q6 : ℝ := 1.5 * N.hb + N.U0 + N.o + N.gG + N.V
def PPpp : ℝ := 32 * N.PPp + N.QJ + N.Qc + N.QH + N.Q6
def tableDegreeSevenMax : ℝ := (max (N.sizeConstantAtParamsWeight) (max (N.flipOneThree) (max (N.tableLineDegreeFive) (max (N.tableLineDegreeTwo) (max (N.Pet) (max (N.G * (1 + N.Np)) (N.o + N.B7)))))))
def P4 : ℝ := N.DivisibilityWeightConstant * (N.PD + N.PQ)
end Num
def Bd (X M : Num → ℝ) : Prop := ∃ C : ℝ, ∀ N : Num, N.admitted → 0 ≤ X N ∧ X N ≤ C * M N
def MonoLet (X : Num → ℝ) : Prop := ∀ N N' : Num, N.H0 → N.LetLow → Num.LetLe N N' → X N ≤ X N'
def lineRows : List ((Num → ℝ) × ℕ) :=
  [(Num.frM, 1), (Num.lrho0, 1), (Num.X2, 1), (Num.B, 1), (Num.PLam, 1), (Num.AO, 2), (Num.o, 2), (Num.Ls, 1), (Num.Lp, 1), (Num.Lp9, 1), (Num.G, 2), (Num.lrw, 5), (Num.muM, 2), (Num.P7, 2), (Num.MU, 2), (Num.tableDegreeTwoSeven, 2), (Num.Psk, 2), (Num.sizeConstantAtParamsWeight, 4), (Num.XB, 7), (Num.PairingSeriesLinearForm, 4), (Num.flipOneThree, 7), (Num.tableLineDegreeFive, 5), (Num.tableDegreeFiveBound, 5), (Num.PR, 5), (Num.p1, 1), (Num.p2, 1), (Num.p3, 2), (Num.p4, 2), (Num.tableDegreeTwoSixteen, 2), (Num.tableLineDegreeTwo, 2), (Num.Ap, 2), (Num.P0, 2), (Num.Pet, 2), (Num.tableDegreeTwoUpper, 2), (Num.PI4, 2), (Num.M0, 1), (Num.PU, 1), (Num.tableDegreeOneUnipotent, 1), (Num.primePairSetFirst, 1), (Num.N1, 1), (Num.tableDegreeOneSquareM, 1), (Num.cnt, 1), (Num.P6, 1), (Num.tableLogDegreeOne, 1), (Num.lA, 1), (Num.RSt, 2), (Num.aar, 1), (Num.Par, 1), (Num.Pex, 2), (Num.Pbe, 3), (Num.Pdeg, 1), (Num.tableDegreeThreeBase, 3), (Num.tableDegreeThreeTripled, 3), (Num.r49, 1), (Num.tableDegreeThreeScaled, 3), (Num.T7, 3), (Num.PO, 2), (Num.Prw, 2), (Num.PN, 1), (Num.lbad, 1), (Num.g0n, 1), (Num.n0, 3), (Num.DivisibilityWeightConstant, 10), (Num.Pd, 2), (Num.PD, 3), (Num.PQ, 3), (Num.PH, 5), (Num.P1, 5), (Num.P2, 4), (Num.P3, 2), (Num.tableDegreeNineSquare, 9), (Num.tableDegreeElevenProduct, 11), (Num.c0, 4), (Num.s1, 4), (Num.c0p, 4), (Num.ESH, 8), (Num.fr5, 2), (Num.ldg, 2), (Num.g0, 5), (Num.tableDegreeFiveTheta, 5), (Num.Iq, 5), (Num.Ifr, 5), (Num.c1s, 1), (Num.Bbad, 1), (Num.MK, 5), (Num.rts, 5), (Num.TH, 5), (Num.U0, 5), (Num.tableDegreeFiveShifted, 5), (Num.PPh, 5), (Num.tableLogDegreeOneTwelve, 1), (Num.cubicPeriodConstant, 4), (Num.PPA, 4), (Num.Xde, 2), (Num.Xdel, 2), (Num.lr0, 2), (Num.Psup, 2), (Num.Xg, 2), (Num.Pt0, 2), (Num.LL0, 2), (Num.Ac, 4), (Num.Afr, 4), (Num.Aun, 1), (Num.PPe, 4), (Num.X1, 5), (Num.Xe, 5), (Num.PPeT, 5), (Num.XW, 3), (Num.XSg, 4), (Num.x28, 2), (Num.xd3, 3), (Num.gG, 2), (Num.cC, 1), (Num.lbe, 2), (Num.Xbe, 2), (Num.lMs, 2), (Num.Ath, 2), (Num.Afl, 1), (Num.Bfl, 2), (Num.B7, 2), (Num.Bt, 2), (Num.product_zeroth_terms, 2), (Num.Gka, 2), (Num.B0, 2), (Num.Xn, 2), (Num.rtN, 3), (Num.rt8, 4), (Num.A1, 3), (Num.tableDegreeThreeBase', 3), (Num.B1, 5), (Num.B2, 7), (Num.Xt, 4), (Num.XJ, 1), (Num.JJ, 2), (Num.aJ, 3), (Num.tJ, 5), (Num.cJ, 5), (Num.x33, 2), (Num.x3j, 3), (Num.x4, 3), (Num.x6, 2), (Num.xfr, 2), (Num.r58, 2), (Num.xint, 1), (Num.xk, 1), (Num.xla, 1), (Num.xCd, 2), (Num.ldE, 1), (Num.lDF, 1), (Num.E0, 5), (Num.CLE, 8), (Num.tableDegreeThreeSecondValue, 3), (Num.A0, 5), (Num.PPp, 8), (Num.PPp1, 8), (Num.al, 5), (Num.Pa, 3), (Num.Pinf, 4), (Num.Pfl, 2), (Num.xn, 4), (Num.xA, 1), (Num.QJ, 5), (Num.Qc, 4), (Num.QH, 5), (Num.Q6, 5), (Num.PPpp, 8), (Num.tableDegreeSevenMax, 7)]
def letterRows : List ((Num → ℝ) × ℕ) :=
  [(Num.lh, 1), (Num.lNc, 2), (Num.lpi, 2), (fun N => max 0 N.lmu, 2), (fun N => max 0 N.lmu1, 2), (Num.V, 2), (Num.hb, 2), (Num.logGenusConstant, 2), (Num.dS, 2), (Num.rS, 2), (Num.dP, 2), (Num.rP, 2), (Num.lNA, 1), (Num.Om, 1), (Num.nu, 1), (Num.lc, 1), (Num.leE, 1), (Num.ln0, 2), (Num.c1, 1), (Num.sc1, 1), (Num.G1, 1), (Num.CL, 1), (Num.lR, 1), (Num.rho, 1), (Num.dp, 1), (Num.gC, 2),
   (Num.nW, 4), (Num.Np, 2), (fun N => (N.D : ℝ), 2), (Num.lM, 1)]
def Dom (CP : ℝ) (N : Num) : Prop := ∀ p ∈ lineRows ++ letterRows, p.1 N ≤ CP * N.Z ^ p.2
end GlobalTheory.OT


