-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_ChainV2
-- name    : CK_CKLaneM07_CE_ChainV2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:17:57.375092+00:00
-- url     : https://prove2.me/theorems/bf476db8-0a5a-4e81-b61e-7de508178994
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.ChainV2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.ChainV2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.ChainV2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.ChainV2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/ChainV2.lean)

import Definitions.Def_CK_CKLaneM07_CE_Chain

-- ===== source module CKLaneM07.CE.ChainV2 =====
section

/-!
# Lane M07 / CE-stat: flat cell checker (chain v2, executable)

Cell: `A = (A0 + hA x)/2^PB`, `t_C = (T0 + hT y)/2^PB`, `(x, y) ∈ [-1,1]²`.

Every series call (logarithm / reciprocal) of the chart chain is a witness item carrying its
series length, (for logs) a Lane D certificate of the centre, and its claimed output Taylor model.
Each item is checked by an independent Boolean conjunct `logOK` / `recOK` (recompute and compare),
so the stage checks `chkA … chkUE` and the final check are independent and can be decided in
separate kernel runs.  Implicit chart variables (`t_A, t_B, a, b, t_D, u_E`) are candidate
polynomials with radii (`Site`), accepted by strict opposite residual signs at `P ± ρ` and the band
condition `P + ρ < 1/2`.  In `edge` mode the lower side of `a` is replaced by `P - ρ ≤ 0`.

`mode`: `0` positivity of the pure-gap Taylor model; `1` `b > t_C` (excluded by `chart_order`);
`2` `a + c ≤ 1/10000` (excluded by the retained cutoff); `3` `λ ≥ 1` (excluded by `λ = f/(e+f)`).

Mirrored exactly by `M07/work/cestat/chainv2.py`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open CKLaneD

deriving instance DecidableEq for TMI

/-- one logarithm call: series length, centre certificate, claimed output -/
structure LogI where
  n : ℕ
  c : LogCert
  out : TMI

/-- one reciprocal call: series length, claimed output -/
structure RecI where
  n : ℕ
  out : TMI

def logOK (K : ℕ) (u : TMI) (it : LogI) : Bool :=
  checkLogCert ((pC00 u.p : ℚ) / (ONE : ℚ)) it.c &&
    decide (TMI.log K it.n u it.c.lo it.c.hi = some it.out)

def recOK (K : ℕ) (u : TMI) (it : RecI) : Bool :=
  decide (TMI.recip K it.n u = some it.out)

namespace Fns

/-- `1 - 2u` -/
def den (F : Fns) : TMI := oneT.sub (TMI.mulC TWOk F.u)

/-- `Ln = 2 Hn / (1 - 2u)` given the reciprocal `rd` of `1 - 2u` -/
def LnW (K : ℕ) (F : Fns) (rd : TMI) : TMI := TMI.mulC TWOk (TMI.mul K (F.Hn K) rd)

/-- `-(u (1-u) (log u + log (1-u)))` -/
def qarg (K : ℕ) (F : Fns) : TMI := (TMI.mul K (TMI.mul K F.u (oneT.sub F.u)) (F.lu.add F.l1u)).neg

/-- `Υn = Jn + Hn (1 - 2u) / qarg` given the reciprocal `rq` of `qarg` -/
def UpsW (K : ℕ) (F : Fns) (rq : TMI) : TMI := F.Jn.add (TMI.mul K (TMI.mul K (F.Hn K) F.den) rq)

end Fns

/-- an implicit chart variable: candidate, radius, and the series items at `P ± ρ` -/
structure Site where
  P : PolI
  rho : ℕ
  lp : LogI
  l1p : LogI
  lm : LogI
  l1m : LogI
  rp : RecI
  rm : RecI

namespace Site

def up (s : Site) : TMI := shiftP s.P s.rho
def dn (s : Site) : TMI := shiftP s.P (-(s.rho : ℤ))
def Fp (s : Site) : Fns := ⟨s.up, s.lp.out, s.l1p.out⟩
def Fm (s : Site) : Fns := ⟨s.dn, s.lm.out, s.l1m.out⟩
def z (s : Site) : TMI := ⟨s.P, s.rho⟩
def F (s : Site) : Fns := ⟨s.z, hull s.lm.out s.lp.out, hull s.l1p.out s.l1m.out⟩
def logsP (K : ℕ) (s : Site) : Bool := logOK K s.up s.lp && logOK K (oneT.sub s.up) s.l1p
def logsM (K : ℕ) (s : Site) : Bool := logOK K s.dn s.lm && logOK K (oneT.sub s.dn) s.l1m
def band (s : Site) : Bool := decide (2 * s.up.hi < ONE)

end Site

def incrOK (Rp Rm : TMI) : Bool := decide (0 < Rp.lo) && decide (Rm.hi < 0)
def decrOK (Rp Rm : TMI) : Bool := decide (Rp.hi < 0) && decide (0 < Rm.lo)

structure CellV where
  A0 : ℤ
  hA : ℤ
  T0 : ℤ
  hT : ℤ
  deriving Repr

def CellV.A (cl : CellV) : TMI := ⟨[[cl.A0], [cl.hA]], 0⟩
def CellV.tC (cl : CellV) : TMI := ⟨[[cl.T0, cl.hT]], 0⟩

def ln2T : TMI := TMI.const (qfl ((L0 + L1) / 2)) (qcl ((L1 - L0) / 2) + 1)

structure WitV where
  sA : Site
  lC : LogI
  l1C : LogI
  rUA : RecI
  rUC : RecI
  sB : Site
  rLB : RecI
  rB : RecI
  rLC : RecI
  rl : RecI
  sa : Site
  edge : Bool
  rAB : RecI
  sb : Site
  sD : Site
  sU : Site

namespace V2

variable (K : ℕ) (cl : CellV) (w : WitV)

def FC : Fns := ⟨cl.tC, w.lC.out, w.l1C.out⟩
def UAC : TMI := (w.sA.F.UpsW K w.rUA.out).add ((FC cl w).UpsW K w.rUC.out)
def LB : TMI := w.sB.F.LnW K w.rLB.out
def B : TMI := TMI.mul K ln2T w.rB.out
def LnC : TMI := (FC cl w).LnW K w.rLC.out
def lam : TMI := TMI.mul K (TMI.mul K ((B K w).sub cl.A) (LnC K cl w)) (TMI.mulC HALFk w.rl.out)
def AB : TMI := cl.A.add (B K w)
def rhsA : TMI := TMI.mul K (TMI.mulC TWOk (oneT.sub (lam K cl w))) ln2T
def E : TMI := TMI.mul K (oneT.sub (TMI.mulC TWOk w.sa.z)) w.rAB.out
def lamEln2 : TMI := TMI.mul K (TMI.mul K (lam K cl w) (E K w)) ln2T
def cT : TMI := TMI.mulC HALFk (oneT.sub (TMI.mul K (E K w) ((B K w).sub cl.A)))
def bma : TMI := w.sb.z.sub w.sa.z
def Eln2 : TMI := TMI.mul K (E K w) ln2T
def hEln2 : TMI := TMI.mulC HALFk (Eln2 K w)

/-! residuals -/
def resA (F : Fns) (rd : TMI) : TMI := (TMI.mul K cl.A (F.LnW K rd)).sub ln2T
def resB (F : Fns) (rq : TMI) : TMI := (F.UpsW K rq).sub (UAC K cl w)
def resa (F : Fns) (rd : TMI) : TMI := (TMI.mul K (F.LnW K rd) (AB K cl w)).sub (rhsA K cl w)
def resb (F : Fns) : TMI := (F.Hn K).sub (lamEln2 K cl w)
def resD (F : Fns) (rd : TMI) : TMI := (TMI.mul K (bma w) (F.LnW K rd)).sub (Eln2 K w)
def resU (F : Fns) : TMI := (F.Hn K).sub (hEln2 K w)

/-! stage checks -/
def chk0 : Bool := decide (0 < cl.hA) && decide (0 < cl.hT)

def chkA : Bool :=
  w.sA.logsP K && w.sA.logsM K && w.sA.band &&
    recOK K w.sA.Fp.den w.sA.rp && recOK K w.sA.Fm.den w.sA.rm &&
    incrOK (resA K cl w.sA.Fp w.sA.rp.out) (resA K cl w.sA.Fm w.sA.rm.out)

def chkC : Bool := logOK K cl.tC w.lC && logOK K (oneT.sub cl.tC) w.l1C

def chkU : Bool := recOK K (w.sA.F.qarg K) w.rUA && recOK K ((FC cl w).qarg K) w.rUC

def chkB : Bool :=
  w.sB.logsP K && w.sB.logsM K && w.sB.band &&
    recOK K (w.sB.Fp.qarg K) w.sB.rp && recOK K (w.sB.Fm.qarg K) w.sB.rm &&
    decrOK (resB K cl w w.sB.Fp w.sB.rp.out) (resB K cl w w.sB.Fm w.sB.rm.out)

def chkL : Bool :=
  recOK K w.sB.F.den w.rLB && recOK K (LB K w) w.rB && recOK K (FC cl w).den w.rLC && recOK K ln2T w.rl

def chka : Bool :=
  w.sa.logsP K && w.sa.band && recOK K w.sa.Fp.den w.sa.rp &&
    decide (0 < (resa K cl w w.sa.Fp w.sa.rp.out).lo) &&
    (if w.edge then decide (w.sa.dn.hi ≤ 0)
     else w.sa.logsM K && recOK K w.sa.Fm.den w.sa.rm &&
       decide ((resa K cl w w.sa.Fm w.sa.rm.out).hi < 0))

def chkE : Bool := recOK K (AB K cl w) w.rAB

def chkb : Bool :=
  w.sb.logsP K && w.sb.logsM K && w.sb.band &&
    incrOK (resb K cl w w.sb.Fp) (resb K cl w w.sb.Fm)

def chkD : Bool :=
  w.sD.logsP K && w.sD.logsM K && w.sD.band &&
    recOK K w.sD.Fp.den w.sD.rp && recOK K w.sD.Fm.den w.sD.rm &&
    incrOK (resD K w w.sD.Fp w.sD.rp.out) (resD K w w.sD.Fm w.sD.rm.out)

def chkUE : Bool :=
  w.sU.logsP K && w.sU.logsM K && w.sU.band &&
    incrOK (resU K w w.sU.Fp) (resU K w w.sU.Fm)

/-! the pure gap (natural-log units); the `a`-logarithm enters through `Jn(P_a + ρ_a) ≤ Jn(a)` -/
def t1 : TMI := (TMI.mul K (bma w) w.sD.F.Jn).neg
def t2 : TMI := TMI.mulC HALFk (TMI.mul K (bma w).neg (w.sb.F.Jn.sub w.sa.Fp.Jn))
def t3 : TMI := (TMI.mul K (oneT.sub (TMI.mulC TWOk w.sU.z)) w.sU.F.Jn).neg
def t4 : TMI := TMI.mulC HALFk (TMI.mul K (oneT.sub (TMI.mulC TWOk w.sb.z)) w.sb.F.Jn)
def t5 : TMI := TMI.mul K ((cT K cl w).sub w.sa.z) w.sA.F.Jn
def t6 : TMI := TMI.mul K ((oneT.sub w.sa.z).sub (cT K cl w)) w.sB.F.Jn
def t7 : TMI := (TMI.mulC HALFk (TMI.mul K (oneT.sub (TMI.mulC TWOk (cT K cl w))) (FC cl w).Jn)).neg

def Gt : TMI :=
  ((((((t1 K w).add (t2 K w)).add (t3 K w)).add (t4 K w)).add (t5 K cl w)).add (t6 K cl w)).add
    (t7 K cl w)

/-! final checks -/
def finG : Bool := decide (0 < (Gt K cl w).lo)
def finE : Bool := decide (0 < (w.sb.z.sub cl.tC).lo)
def finF : Bool := decide (10000 * (w.sa.z.add (cT K cl w)).hi ≤ ONE)
def finL : Bool := decide (ONE ≤ (lam K cl w).lo)

end V2

end CKLaneM07.CE

end


