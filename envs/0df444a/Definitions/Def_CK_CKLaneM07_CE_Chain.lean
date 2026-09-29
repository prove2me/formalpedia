-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_Chain
-- name    : CK_CKLaneM07_CE_Chain
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:09:03.424407+00:00
-- url     : https://prove2.me/theorems/fb1c5450-f082-4ab4-8e2c-86d1b416bbe8
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.Chain` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.Chain` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.Chain` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.Chain (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/Chain.lean)

import Definitions.Def_CK_CKLaneM07_CE_TMI

-- ===== source module CKLaneM07.CE.Chain =====
section

/-!
# Lane M07 / CE-stat: the stationary Case-E chart as a Taylor-model chain (executable)

Cell: `A = A0 + hA x`, `t_C = T0 + hT y`, `(x, y) ∈ [-1,1]²`.  Implicit chart variables
`t_A, t_B, a, b, t_D, u_E` are given as candidate polynomials `P` with radii `ρ`; each is accepted when
its monotone residual has opposite strict signs at `P + ρ` and `P - ρ` over the whole cell.
Natural-log units (`Hn = H·ln2`, `Jn = J·ln2`, `Ln = L·ln2`, `Upsn = Υ·ln2`, `Gn = g·ln2`).
Series lengths and Lane D certificates for every log centre are consumed from a witness stream.
Mirrored exactly by `M07/work/cestat/chainint.py`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open CKLaneD

/-- One series call of the witness stream: length and (for logs) the centre certificate. -/
structure Item where
  n : ℕ
  c : LogCert
  deriving Repr

abbrev M := StateT (List Item) Option

def pop : M Item := do
  match (← get) with
  | it :: rest => set rest; pure it
  | [] => failure

def mlog (K : ℕ) (u : TMI) : M TMI := do
  let it ← pop
  let u0q : ℚ := (pC00 u.p : ℚ) / (ONE : ℚ)
  if checkLogCert u0q it.c then
    match TMI.log K it.n u it.c.lo it.c.hi with
    | some t => pure t
    | none => failure
  else failure

def mrecip (K : ℕ) (u : TMI) : M TMI := do
  let it ← pop
  match TMI.recip K it.n u with
  | some t => pure t
  | none => failure

def oneT : TMI := TMI.const ONE

/-- `2^PB · 2 = 2` as a fixed-point multiplier, `2^PB / 2 = 1/2` -/
def TWOk : ℤ := 2 * ONE
def HALFk : ℤ := ONE / 2

/-- entropy-function bundle of an argument `u ∈ (0, 1/2)` with its two logarithms -/
structure Fns where
  u : TMI
  lu : TMI
  l1u : TMI

def Fns.Hn (K : ℕ) (F : Fns) : TMI :=
  ((TMI.mul K F.u F.lu).add (TMI.mul K (oneT.sub F.u) F.l1u)).neg

def Fns.Jn (F : Fns) : TMI := F.l1u.sub F.lu

def Fns.Ln (K : ℕ) (F : Fns) : M TMI := do
  let rd ← mrecip K (oneT.sub (TMI.mulC TWOk F.u))
  pure (TMI.mulC TWOk (TMI.mul K (F.Hn K) rd))

def Fns.Upsn (K : ℕ) (F : Fns) : M TMI := do
  let s := TMI.mul K F.u (oneT.sub F.u)
  let ls := F.lu.add F.l1u
  let d := oneT.sub (TMI.mulC TWOk F.u)
  let rq ← mrecip K (TMI.mul K s ls).neg
  pure (F.Jn.add (TMI.mul K (TMI.mul K (F.Hn K) d) rq))

def mkFns (K : ℕ) (u : TMI) : M Fns := do
  let lu ← mlog K u
  let l1u ← mlog K (oneT.sub u)
  pure ⟨u, lu, l1u⟩

/-- pointwise hull: encloses any value between the values enclosed by `a` and `b` -/
def hull (a b : TMI) : TMI :=
  let avg := (pAdd a.p b.p).map (List.map (fun z => z / 2))
  ⟨avg, cdiv (pAbs (pAdd b.p (pNeg a.p))) 2 + a.r + b.r + pCount avg⟩

def shiftP (P : PolI) (d : ℤ) : TMI := ⟨pAdd P [[d]], 0⟩

/-- accept an implicit variable with candidate `P`, radius `ρ` and monotone residual `R` -/
def implicit (K : ℕ) (P : PolI) (rho : ℕ) (R : Fns → M TMI) (incr : Bool) : M (TMI × Fns) := do
  let Fp ← mkFns K (shiftP P rho)
  let Fm ← mkFns K (shiftP P (-(rho : ℤ)))
  let Rp ← R Fp
  let Rm ← R Fm
  let ok := if incr then decide (0 < Rp.lo ∧ Rm.hi < 0) else decide (Rp.hi < 0 ∧ 0 < Rm.lo)
  if ok then
    let z : TMI := ⟨P, rho⟩
    pure (z, ⟨z, hull Fm.lu Fp.lu, hull Fp.l1u Fm.l1u⟩)
  else failure

structure Cell where
  A0 : ℚ
  hA : ℚ
  T0 : ℚ
  hT : ℚ
  deriving Repr

structure Wit where
  PtA : PolI
  rtA : ℕ
  PtB : PolI
  rtB : ℕ
  Pa : PolI
  ra : ℕ
  Pb : PolI
  rb : ℕ
  PtD : PolI
  rtD : ℕ
  PuE : PolI
  ruE : ℕ
  items : List Item
  deriving Repr

/-- the chart chain; returns the Taylor model of `Gn = g · ln 2` -/
def chainG (K : ℕ) (cl : Cell) (w : Wit) : M TMI := do
  let A : TMI := ⟨[[qfl cl.A0], [qfl cl.hA]], 0⟩
  let tC : TMI := ⟨[[qfl cl.T0, qfl cl.hT]], 0⟩
  let ln2 : TMI := TMI.const (qfl ((L0 + L1) / 2)) (qcl ((L1 - L0) / 2) + 1)
  let (_, FA) ← implicit K w.PtA w.rtA (fun F => do
      let l ← F.Ln K
      pure ((TMI.mul K A l).sub ln2)) true
  let FC ← mkFns K tC
  let UA ← FA.Upsn K
  let UC ← FC.Upsn K
  let UAC := UA.add UC
  let (_, FB) ← implicit K w.PtB w.rtB (fun F => do
      let U ← F.Upsn K
      pure (U.sub UAC)) false
  let LB ← FB.Ln K
  let rLB ← mrecip K LB
  let B := TMI.mul K ln2 rLB
  let LnC ← FC.Ln K
  let rl ← mrecip K ln2
  let lam := TMI.mul K (TMI.mul K (B.sub A) LnC) (TMI.mulC HALFk rl)
  let AB := A.add B
  let rhsA := TMI.mul K (TMI.mulC TWOk (oneT.sub lam)) ln2
  let (a, Fa) ← implicit K w.Pa w.ra (fun F => do
      let l ← F.Ln K
      pure ((TMI.mul K l AB).sub rhsA)) true
  let rAB ← mrecip K AB
  let E := TMI.mul K (oneT.sub (TMI.mulC TWOk a)) rAB
  let lamEln2 := TMI.mul K (TMI.mul K lam E) ln2
  let (b, Fb) ← implicit K w.Pb w.rb (fun F => pure ((F.Hn K).sub lamEln2)) true
  let c := TMI.mulC HALFk (oneT.sub (TMI.mul K E (B.sub A)))
  let bma := b.sub a
  let Eln2 := TMI.mul K E ln2
  let (_, FD) ← implicit K w.PtD w.rtD (fun F => do
      let l ← F.Ln K
      pure ((TMI.mul K bma l).sub Eln2)) true
  let hEln2 := TMI.mulC HALFk Eln2
  let (uE, FU) ← implicit K w.PuE w.ruE (fun F => pure ((F.Hn K).sub hEln2)) true
  let t1 := (TMI.mul K bma FD.Jn).neg
  let t2 := TMI.mulC HALFk (TMI.mul K bma.neg (Fb.Jn.sub Fa.Jn))
  let t3 := (TMI.mul K (oneT.sub (TMI.mulC TWOk uE)) FU.Jn).neg
  let t4 := TMI.mulC HALFk (TMI.mul K (oneT.sub (TMI.mulC TWOk b)) Fb.Jn)
  let t5 := TMI.mul K (c.sub a) FA.Jn
  let t6 := TMI.mul K ((oneT.sub a).sub c) FB.Jn
  let t7 := (TMI.mulC HALFk (TMI.mul K (oneT.sub (TMI.mulC TWOk c)) FC.Jn)).neg
  pure (((((t1.add t2).add t3).add t4).add t5).add t6 |>.add t7)

/-- Boolean cell check: every implicit acceptance, certificate and series side condition holds and the
Taylor model of `Gn` is strictly positive on the cell. -/
def checkCell (K : ℕ) (cl : Cell) (w : Wit) : Bool :=
  match (chainG K cl w).run w.items with
  | some (G, _) => decide (0 < G.lo)
  | none => false

end CKLaneM07.CE

end


