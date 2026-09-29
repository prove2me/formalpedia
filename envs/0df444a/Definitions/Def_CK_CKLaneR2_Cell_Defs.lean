-- Prove2me | Definitions.Def_CK_CKLaneR2_Cell_Defs
-- name    : CK_CKLaneR2_Cell_Defs
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:20:13.590558+00:00
-- url     : https://prove2.me/theorems/d6ee945c-6cb7-420a-94fd-178fc0661caa
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Cell.Defs` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Cell.Defs` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Cell.Defs` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Cell.Defs (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Cell/Defs.lean)

import Definitions.Def_CK_CKLaneR2_TM3_Fun

-- ===== source module CKLaneR2.Cell.Defs =====
section

/-!
# Lane C, RA-stat interior: the rayGamma cell checker (computational definitions)

This is the Lean mirror of `C/tools/rscell.py`, which is a cleaned copy of R1's `rg_cell.cell_gamma`
running on tm3c.

**Cell.**
* The TM variables are `b = (bc + bh x)/one`, `t = (tc + th y)/one` and `σ = (sc + sh z)/one`,
  with `x, y, z ∈ [-1,1]`.
* Derived quantities are `u = bσ` and `d = b - u`.

**Implicit quantities.** The certificate supplies a polynomial `V` and a radius `ρ` for each of them:
* four contacts `δ_k = 1 - 2 radialContact(Z_k, 1)`;
* one entropy inverse `δ_m = 1 - 2 entropyInverse(E)`.

These are verified by two-sided residual signs.
-/

namespace CKLaneR2.Cell

open CKLaneR2.TM3

abbrev P : ℕ := 64
abbrev N : ℕ := 4
def one : ℕ := 2 ^ P

noncomputable def ONEi : Int := (one : Int)
noncomputable def half : Int := ((one / 2 : ℕ) : Int)

noncomputable def mul (A B : TM) : TM := TM.mul one N A B
noncomputable def mulc (A : TM) (c : Int) : TM := TM.mulc one A c
noncomputable def recip (A : TM) : TM := TM.recip one N A
noncomputable def log (A : TM) : TM := TM.log P N A

/-- `log 2` and `1 / log 2` as constant TMs (tm3c `Ctx`). -/
noncomputable def Lc : TM := TM.const (LN2 P) (LN2E P)
noncomputable def invLc : TM := TM.const (((one * one : ℕ) : Int) / LN2 P) (1 + 3 * LN2E P)

/-- `h(δ) = 1 - ((1+δ) lp + (1-δ) lm) · invL / 2`. -/
noncomputable def hOfLogs (D lp lm : TM) : TM :=
  TM.addc (TM.neg (mulc (mul (TM.add (mul (TM.addc D ONEi) lp) (mul (TM.addc (TM.neg D) ONEi) lm)) invLc)
    half)) ONEi

noncomputable def jOfLogs (lp lm : TM) : TM := mul (TM.sub lp lm) invLc

structure Impl where
  D : TM
  lp : TM
  lm : TM

/-- Two-sided residual check (tm3c/rg_cell `check_implicit`). `contact = true`: residual `Z h - V`;
`contact = false`: residual `h - Z` (entropy, with `Z = E`). -/
noncomputable def checkImplicit (contact : Bool) (Z : TM) (V : Poly) (rho : ℕ) : Impl :=
  let Vt : TM := ⟨V, 0, true⟩
  let Vm := TM.addc Vt (-(rho : Int))
  let Vp := TM.addc Vt (rho : Int)
  let lpm := log (TM.addc Vm ONEi)
  let lmm := log (TM.addc (TM.neg Vm) ONEi)
  let lpp := log (TM.addc Vp ONEi)
  let lmp := log (TM.addc (TM.neg Vp) ONEi)
  let hm := hOfLogs Vm lpm lmm
  let hp := hOfLogs Vp lpp lmp
  let Rm := if contact then TM.sub (mul Z hm) Vm else TM.sub hm Z
  let Rp := if contact then TM.sub (mul Z hp) Vp else TM.sub hp Z
  let okc := Z.ok && Rm.ok && Rp.ok && decide (Vp.upper < ONEi) && decide (-ONEi < Vm.lower)
    && decide (0 < Rm.lower) && decide (Rp.upper < 0)
  let lp := TM.average lpm lpp
  let lm := TM.average lmp lmm
  ⟨⟨V, rho, okc⟩, ⟨lp.p, lp.r, lp.ok && okc⟩, ⟨lm.p, lm.r, lm.ok && okc⟩⟩

structure CF where
  F0 : TM
  F1 : TM
  F2 : TM

/-- `F0 = z J(v)`, `F1 = radialSlope v`, `F2 = F''` (corpus closed form), with `v = (1-δ)/2`. -/
noncomputable def contactFuncs (Z : TM) (I : Impl) : CF :=
  let J := jOfLogs I.lp I.lm
  let hnv := TM.add Lc (TM.neg (mulc (TM.add (mul (TM.addc I.D ONEi) I.lp)
    (mul (TM.addc (TM.neg I.D) ONEi) I.lm)) half))
  let kap := TM.add Lc (TM.neg (mulc (TM.add I.lp I.lm) half))
  let omd2 := TM.addc (TM.neg (mul I.D I.D)) ONEi
  let ik := recip kap
  let iom := recip omd2
  let F0 := mul Z J
  let F1 := TM.add J (TM.scaleInt (mul (mul (mul I.D hnv) (mul iom ik)) invLc) 2)
  let izj := recip (TM.addc (mul Z J) (2 * ONEi))
  let num := mul (mul hnv hnv) (TM.sub (TM.scaleInt kap 2) (mul I.D I.D))
  let deninv := mul (mul (mul iom iom) (mul ik ik)) izj
  let F2 := TM.scaleInt (mul (mul num deninv) (mul invLc invLc)) 4
  ⟨F0, F1, F2⟩

/-- `((ds - Z de)^2 / e) F2 + (-Z dde) F1 + dde F0` with `iE = 1/e`. -/
noncomputable def raysec (Z iE ds de dde : TM) (F : CF) : TM :=
  let a := TM.sub ds (mul Z de)
  TM.add (TM.add (mul (mul (mul a a) iE) F.F2) (TM.neg (mul (mul Z dde) F.F1))) (mul dde F.F0)

structure Cell where
  bc : Int
  bh : Int
  tc : Int
  th : Int
  sc : Int
  sh : Int

structure Cert where
  V0 : Poly
  r0 : ℕ
  V1 : Poly
  r1 : ℕ
  V2 : Poly
  r2 : ℕ
  V3 : Poly
  r3 : ℕ
  Vm : Poly
  rm : ℕ

/-- Base quantities of a cell. -/
structure Base where
  B : TM
  T : TM
  U : TM
  Dd : TM
  Hu : TM
  E : TM
  Ju : TM
  Jd1 : TM
  term0 : TM
  iE : TM
  iHu : TM
  TD : TM
  r12b : TM

noncomputable def base (c : Cell) : Base :=
  let B := TM.lin c.bc c.bh 0 0
  let T := TM.lin c.tc 0 c.th 0
  let Sg := TM.lin c.sc 0 0 c.sh
  let U := mul B Sg
  let Dd := TM.sub B U
  let logB := log B
  let log1mB := log (TM.addc (TM.neg B) ONEi)
  let logS := log Sg
  let logU := TM.add logB logS
  let log1mU := log (TM.addc (TM.neg U) ONEi)
  let HuL := TM.neg (TM.add (mul U logU) (mul (TM.addc (TM.neg U) ONEi) log1mU))
  let HbL := TM.neg (TM.add (mul B logB) (mul (TM.addc (TM.neg B) ONEi) log1mB))
  let Hu := mul HuL invLc
  let Hb := mul HbL invLc
  let E := mulc (TM.add Hu Hb) half
  let Ju := mul (TM.sub log1mU logU) invLc
  let iB := recip B
  let iS := recip Sg
  let iU := mul iB iS
  let i1mU := recip (TM.addc (TM.neg U) ONEi)
  let iUU := mul iU i1mU
  let Jd1 := TM.neg (mul iUU invLc)
  let Jd2 := mul (mul (TM.addc (TM.scaleInt U (-2)) ONEi) (mul iUU iUU)) invLc
  let r12b := TM.addc (TM.scaleInt B (-2)) ONEi
  let term0 := TM.add (TM.scaleInt Jd1 (-3)) (mul (mulc (TM.add r12b (TM.scaleInt Dd 3)) half) Jd2)
  let iE := recip E
  let iHu := recip Hu
  let TD := mul T Dd
  ⟨B, T, U, Dd, Hu, E, Ju, Jd1, term0, iE, iHu, TD, r12b⟩

/-- The eta block `-(etaCurvature E · de^2 + etaSlope E · dde)`. -/
noncomputable def etaBlock (E de dde : TM) (Im : Impl) : TM :=
  let Dm := Im.D
  let Jm := jOfLogs Im.lp Im.lm
  let om := TM.addc (TM.neg (mul Dm Dm)) ONEi
  let iom := recip om
  let iJm := recip Jm
  let etaSlope := TM.addc (TM.neg (TM.scaleInt (mul (mul Dm (mul iom iJm)) invLc) 4)) (-2 * ONEi)
  let cn := TM.sub (mulc (mul (TM.addc (mul Dm Dm) ONEi) (mul Lc Jm)) half) Dm
  let etaCurv := TM.scaleInt (mul (mul cn (mul (mul iom iom) (mul (mul iJm iJm) iJm))) (mul invLc invLc)) 16
  TM.neg (TM.add (mul etaCurv (mul de de)) (mul etaSlope dde))

/-- The rayGamma TM of a cell (mirror of `rscell.cell_gamma(cert=...)`). -/
noncomputable def cellG (c : Cell) (q : Cert) : TM :=
  let b := base c
  let Z0 := mul b.TD b.iE
  let Z1 := mul b.Dd b.iE
  let Z2 := mul (TM.add b.r12b b.TD) b.iE
  let Z3 := mul (TM.add b.r12b (TM.scaleInt b.TD 2)) b.iHu
  let de := mulc (TM.neg b.Ju) half
  let dde := mulc b.Jd1 half
  let t1 := raysec Z0 b.iE b.T de dde (contactFuncs Z0 (checkImplicit true Z0 q.V0 q.r0))
  let t2 := TM.neg (raysec Z1 b.iE (TM.const ONEi 0) de dde (contactFuncs Z1 (checkImplicit true Z1 q.V1 q.r1)))
  let t3 := raysec Z2 b.iE b.T de dde (contactFuncs Z2 (checkImplicit true Z2 q.V2 q.r2))
  let t4 := etaBlock b.E de dde (checkImplicit false b.E q.Vm q.rm)
  let t5 := TM.neg (mulc (raysec Z3 b.iHu (TM.scaleInt b.T 2) (TM.neg b.Ju) b.Jd1
    (contactFuncs Z3 (checkImplicit true Z3 q.V3 q.r3))) half)
  TM.add (TM.add (TM.add (TM.add (TM.add b.term0 t1) t2) t3) t4) t5

/-- The Boolean cell check that is decided by the kernel. -/
noncomputable def cellCheck (c : Cell) (q : Cert) : Bool :=
  (cellG c q).ok && decide (0 < (cellG c q).lower)

end CKLaneR2.Cell

end


