-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMoment380kModel
-- name    : row23_rh_supp_RHLocalMoment380kModel
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:02:59.572204+00:00
-- url     : https://prove2.me/theorems/c52a7aba-0567-46c0-ad76-66205ec84edc
-- title:
--   Row 23 RH support: RHLocalMoment380kModel
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreRationalRowModel
set_option autoImplicit false
namespace DusartLegendreSmoothing.Moment380k
open RationalRows
 def piLower : ℚ := 314159265358979323846/10^20
 def piUpper : ℚ := 314159265358979323847/10^20
 def lowHeight : ℚ := 1000
 def highHeight : ℚ := 380000
structure Data where
  S : ℚ
  L0 : ℚ
  U0 : ℚ
  V0 : ℚ
  LT : ℚ
  UT : ℚ
  VT : ℚ
  LH : ℚ
  UH : ℚ
  VH : ℚ
 def slopeLower (a U : ℚ) : ℚ := 1/(2*piUpper)+9/(a*U)
 def slopeUpper (a L : ℚ) : ℚ := 1/(2*piLower)+9/(a*L)
 def primitive (m : ℕ) (a L : ℚ) : ℚ := (1+(m:ℚ)*L)/((m:ℚ)^2*a^m)
 def lowUpper (p : Parameters) (d : Data) : ℚ :=
  2*(d.S+2*(9*d.V0+79)/lowHeight+
    (slopeUpper lowHeight d.L0*d.UT^2-slopeLower lowHeight d.U0*d.L0^2)/2)
 def bandUpper (p : Parameters) (d : Data) : ℚ :=
  2*(2*(9*d.VT+79)/(p.T:ℚ)^(p.m+1)+
    slopeUpper p.T d.LT*primitive p.m p.T d.UT-
    slopeLower p.T d.UT*primitive p.m highHeight d.LH)
 def tailUpper (p : Parameters) (d : Data) : ℚ :=
  2*(2*(9*d.VH+79)/highHeight^(p.m+1)+
    slopeUpper highHeight d.LH*primitive p.m highHeight d.UH)
 def checks (p : Parameters) (d : Data) : Prop :=
  2 ≤ p.m ∧ lowHeight ≤ (p.T:ℚ) ∧ (p.T:ℚ) ≤ highHeight ∧
  0 < d.L0 ∧ d.L0 ≤ d.U0 ∧ 0 < d.LT ∧ d.LT ≤ d.UT ∧
  0 < d.LH ∧ d.LH ≤ d.UH ∧
  lowUpper p d ≤ p.B₁ ∧ bandUpper p d ≤ p.B₂ ∧ tailUpper p d ≤ p.B₃
end DusartLegendreSmoothing.Moment380k


