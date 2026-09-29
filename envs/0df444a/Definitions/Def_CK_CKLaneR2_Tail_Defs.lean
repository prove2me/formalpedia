-- Prove2me | Definitions.Def_CK_CKLaneR2_Tail_Defs
-- name    : CK_CKLaneR2_Tail_Defs
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:27:00.460343+00:00
-- url     : https://prove2.me/theorems/83a024b4-704d-4cb4-bdea-01ae3e8c94a9
-- title:
--   Courtade–Kumar proof module `CKLaneR2.Tail.Defs` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.Tail.Defs` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.Tail.Defs` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.Tail.Defs (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/Tail/Defs.lean)

import Definitions.Def_CK_CKLaneR2_Cell_Defs

-- ===== source module CKLaneR2.Tail.Defs =====
section

/-!
# Lane R2 — RA-stat u-tail: the tail cell checker (computational definitions)

Bit-exact Lean mirror of `R2/tools/tailcell.py`. The certified quantity is `u² · rayGamma b t (b - u)`.

**Charts.**
* S-cells: `b = (bc + bh x)/one`, `t = (tc + th y)/one`, `σ = (sc/one) · exp(-sh z)` with `sh = shN/shD`;
  `u = b σ`, `ℓ = ln(1/u) = -ln b - ln(sc/one) + sh z`.
* L-cells (limit layer): `b`, `t` as above, `λ = 1/ln(1/u) = (lh + lh z)/one ∈ [0, lam1/one]`;
  `u`, `u ℓ`, `-ln(1-u)` and `g1 u` enter as noise constants.

**Assembly.** `G = u2T0 + t1 + t2 + t3 + t4 + u2T5`, where `t1..t4` are Lane C's contact/eta blocks with the
scaled derivative inputs `(u·ds, u·de, u²·dde)` and `u2T5` is either the ρ-representation of the fifth
`raySec` block (mode R: `ρ = v/u`, `v = radialContact (s3/H u) 1`) or its universal lower bound (mode S).
-/

namespace CKLaneR2.Tail

open CKLaneR2.TM3 CKLaneR2.Cell

/-! ## Exp polynomial (S-chart) -/

/-- Coefficient `⌊sc (-shN)^k / (shD^k k!)⌋` of `σ = (sc/one) exp(-(shN/shD) z)`. -/
noncomputable def expCoef (sc : Int) (shN shD k : Nat) : Int :=
  (sc * (-(shN : Int)) ^ k) / ((shD ^ k * Nat.factorial k : Nat) : Int)

/-- Remainder `5 + ⌈sc shN^5 / (100 shD^5)⌉` (Real.exp_bound with n = 5 plus coefficient rounding). -/
noncomputable def expRem (sc : Int) (shN shD : Nat) : Nat :=
  5 + cdiv (sc.toNat * shN ^ 5) (100 * shD ^ 5)

/-- `(sc/one) exp(-(shN/shD) z)` as a TM in `z`. -/
noncomputable def expPolyTM (sc : Int) (shN shD : Nat) : TM :=
  ⟨[[[expCoef sc shN shD 0]], [[expCoef sc shN shD 1]], [[expCoef sc shN shD 2]], [[expCoef sc shN shD 3]],
    [[expCoef sc shN shD 4]]], expRem sc shN shD, true⟩

/-- `(bc/one) exp(-(bN/bD) x)` as a TM in `x`. -/
noncomputable def expPolyTMx (bc : Int) (bN bD : Nat) : TM :=
  ⟨[[[expCoef bc bN bD 0]], [[], [expCoef bc bN bD 1]], [[], [], [expCoef bc bN bD 2]],
    [[], [], [], [expCoef bc bN bD 3]], [[], [], [], [], [expCoef bc bN bD 4]]], expRem bc bN bD, true⟩

/-! ## `g1(u) = -(1-u) ln(1-u)/u` by its series (valid for `0 ≤ u ≤ 1/8`) -/

noncomputable def g1Step (U S : TM) (c : Int) : TM :=
  let M := mul U S
  ⟨(TM.addc M c).p, M.r + 1, M.ok⟩

noncomputable def g1Horner (U : TM) : TM :=
  let S6 := TM.const ((one / 7 : ℕ) : Int) 1
  let S5 := g1Step U S6 ((one / 6 : ℕ) : Int)
  let S4 := g1Step U S5 ((one / 5 : ℕ) : Int)
  let S3 := g1Step U S4 ((one / 4 : ℕ) : Int)
  let S2 := g1Step U S3 ((one / 3 : ℕ) : Int)
  let S1 := g1Step U S2 ((one / 2 : ℕ) : Int)
  g1Step U S1 ((one / 1 : ℕ) : Int)

noncomputable def g1Series (U omU : TM) : TM :=
  let G := mul omU (g1Horner U)
  ⟨G.p, G.r + (cdiv (U.upper.toNat ^ 7) (one ^ 6) + 1),
    G.ok && decide (0 < U.upper) && decide (U.upper ≤ ((one / 8 : ℕ) : Int))⟩

/-! ## Front ends -/

structure Front where
  B : TM
  T : TM
  logB : TM
  U : TM
  Lam : TM
  W : TM
  omU : TM
  Cq : TM
  G1 : TM
  lim : Bool

/-- The `b`-chart: exponential (`bexp`: `b = (bc/one) exp(-(bN/bD) x)`) or linear (`b = (bc + bh x)/one`). -/
structure BChart where
  bexp : Bool
  bc : Int
  bh : Int
  bN : Nat
  bD : Nat

structure SCell where
  bch : BChart
  tc : Int
  th : Int
  sc : Int
  shN : Nat
  shD : Nat

structure LCell where
  bch : BChart
  tc : Int
  th : Int
  lam1 : Nat
  u1 : Nat
  w1 : Nat

/-- `rate · one` for a rate `n/d` (exact when `d ∣ n · one`, which the domain check verifies). -/
noncomputable def rateI (n d : Nat) : Int := ((n * one / d : ℕ) : Int)

/-- `(B, log B)` for a `b`-chart. -/
noncomputable def frontB (c : BChart) : TM × TM :=
  if c.bexp then
    let Lb := logScalar P c.bc.toNat
    (expPolyTMx c.bc c.bN c.bD, TM.add (TM.const Lb.1 Lb.2) (TM.lin 0 (-(rateI c.bN c.bD)) 0 0))
  else (TM.lin c.bc c.bh 0 0, log (TM.lin c.bc c.bh 0 0))

noncomputable def frontS (c : SCell) : Front :=
  let B := (frontB c.bch).1
  let logB := (frontB c.bch).2
  let T := TM.lin c.tc 0 c.th 0
  let Sg := expPolyTM c.sc c.shN c.shD
  let Lk := logScalar P c.sc.toNat
  let ell := TM.add (TM.add (TM.neg logB) (TM.const (-Lk.1) Lk.2)) (TM.lin 0 0 0 (rateI c.shN c.shD))
  let U := mul B Sg
  let Lam := recip ell
  let W := mul U ell
  let omU := TM.addc (TM.neg U) ONEi
  let Cq := TM.neg (log omU)
  let G1 := g1Series U omU
  ⟨B, T, logB, U, Lam, W, omU, Cq, G1, false⟩

noncomputable def frontL (c : LCell) : Front :=
  let B := (frontB c.bch).1
  let logB := (frontB c.bch).2
  let T := TM.lin c.tc 0 c.th 0
  let lh : Int := (((c.lam1 + 1) / 2 : ℕ) : Int)
  let Lam := TM.lin lh 0 0 lh
  let uh : ℕ := (c.u1 + 1) / 2
  let U := TM.const (uh : Int) uh
  let wh : ℕ := (c.w1 + 1) / 2
  let W := TM.const (wh : Int) wh
  let Cq := TM.const (c.u1 : Int) c.u1
  let G1 := TM.const (ONEi - uh) uh
  let omU := TM.addc (TM.neg U) ONEi
  ⟨B, T, logB, U, Lam, W, omU, Cq, G1, true⟩

/-! ## The fifth raySec block -/

/-- `g1(v)`: noise in the limit layer, series for `v ≤ 1/8`, closed form otherwise. -/
noncomputable def g1Of (F : Front) (v omv cv : TM) : TM :=
  if F.lim then
    let h : Int := (v.upper + 1) / 2
    ⟨[[[ONEi - h]]], h.toNat, v.ok && decide (v.upper < ((one / 2 : ℕ) : Int))⟩
  else if decide (v.upper ≤ ((one / 8 : ℕ) : Int)) then g1Series v omv
  else mul (mul omv cv) (recip v)

structure T5Parts where
  R : TM
  eta : TM
  cv : TM
  v : TM

/-- Residual `s3 ρ (1 - Λ ln ρ + Λ g1(uρ)) - (1 - 2uρ)(1 + Λ g1(u))` (increasing in `ρ`). -/
noncomputable def t5Resid (F : Front) (s3 rhoT : TM) : T5Parts :=
  let eta := log rhoT
  let v := mul F.U rhoT
  let omv := TM.addc (TM.neg v) ONEi
  let cv := TM.neg (log omv)
  let g1v := g1Of F v omv cv
  let X := TM.addc (TM.sub (mul F.Lam g1v) (mul F.Lam eta)) ONEi
  let R := TM.sub (mul (mul s3 rhoT) X) (mul (TM.addc (TM.scaleInt v (-2)) ONEi) (TM.addc (mul F.Lam F.G1) ONEi))
  ⟨R, eta, cv, v⟩

/-- Mode R: the ρ-representation of `u² · (-raySec5/2)` with a two-sided residual certificate `(P, r)`. -/
noncomputable def t5R (F : Front) (s3 : TM) (Pc : Poly) (r : ℕ) : TM :=
  let rm := TM.addc ⟨Pc, 0, true⟩ (-(r : Int))
  let rp := TM.addc ⟨Pc, 0, true⟩ (r : Int)
  let Qm := t5Resid F s3 rm
  let Qp := t5Resid F s3 rp
  let okc := decide (0 < rm.lower) && Qm.R.ok && Qp.R.ok && decide (Qm.R.upper < 0) && decide (0 < Qp.R.lower)
    && Qp.v.ok && decide (Qp.v.upper < ONEi)
  let rho : TM := ⟨Pc, r, okc⟩
  let etaA := TM.average Qm.eta Qp.eta
  let cvA := TM.average Qm.cv Qp.cv
  let eta : TM := ⟨etaA.p, etaA.r, etaA.ok && okc⟩
  let cv : TM := ⟨cvA.p, cvA.r, cvA.ok && okc⟩
  let v := mul F.U rho
  let omv := TM.addc (TM.neg v) ONEi
  let g1v := g1Of F v omv cv
  let LG1 := TM.addc (mul F.Lam F.G1) ONEi
  let X := TM.addc (TM.sub (mul F.Lam g1v) (mul F.Lam eta)) ONEi
  let Yc := TM.addc (TM.sub (mul F.Lam cv) (mul F.Lam eta)) ONEi
  let om2v := TM.addc (TM.scaleInt v (-2)) ONEi
  let Yd := TM.sub Yc (mul F.Lam (mul om2v om2v))
  let iLG1 := recip LG1
  let omega := mul (TM.addc (TM.neg (mul F.Lam F.Cq)) ONEi) iLG1
  let iYc := recip Yc
  let iomv := recip omv
  let Yt := mul (mul (mul X X) Yd) (mul (mul iomv iomv) (mul (mul iYc iYc) iYc))
  let q := TM.add (TM.scaleInt (mul F.T F.U) 2) (mul s3 omega)
  let A1 := mul (mul (mul (mul q q) rho) (mul X Yt)) (mul invLc iLG1)
  let A2 := mul (mul (mul s3 om2v) (mul X F.Lam)) (mul invLc (mul (mul (recip F.omU) iomv) (mul iYc iLG1)))
  TM.neg (mulc (TM.add A1 A2) half)

/-- Mode S: universal lower bound for `u² · (-raySec5/2)` (`Ỹ ≤ 4`, `X/Yc ≤ 2(1-v)`, `4t²u²/s3 ≤ 2tu²/d`). -/
noncomputable def t5S (F : Front) (s3 Dd : TM) : TM :=
  let omega := mul (TM.addc (TM.neg (mul F.Lam F.Cq)) ONEi) (recip (TM.addc (mul F.Lam F.G1) ONEi))
  let TU := mul F.T F.U
  let a := TM.scaleInt (mul (mul TU F.U) (recip Dd)) 2
  let b := TM.scaleInt (mul TU omega) 4
  let c := mul s3 (mul omega omega)
  let UB1 := TM.scaleInt (mul (TM.add (TM.add a b) c) invLc) 4
  let UB2 := mul (TM.scaleInt (mul s3 F.Lam) 2) (mul invLc (recip F.omU))
  TM.neg (mulc (TM.add UB1 UB2) half)

/-! ## Cell assembly -/

/-- Factored contact block `((ds - Z de)^2 / e) F2 + dde (F0 - Z F1)` (same value as Lane C's `raysec`). -/
noncomputable def raysecF (Z iE ds de dde : TM) (F : CF) : TM :=
  let a := TM.sub ds (mul Z de)
  TM.add (mul (mul (mul a a) iE) F.F2) (mul dde (TM.sub F.F0 (mul Z F.F1)))

structure TCert where
  V0 : Poly
  r0 : ℕ
  V1 : Poly
  r1 : ℕ
  V2 : Poly
  r2 : ℕ
  Vm : Poly
  rm : ℕ
  rhoP : Poly
  rhoR : ℕ

structure Base where
  E : TM
  iE : TM
  Dd : TM
  s3 : TM
  Z0 : TM
  Z1 : TM
  Z2 : TM
  ude : TM
  u2dde : TM
  uT : TM
  u2T0 : TM

noncomputable def base (F : Front) : Base :=
  let log1mB := log (TM.addc (TM.neg F.B) ONEi)
  let Hb := mul (TM.neg (TM.add (mul F.B F.logB) (mul (TM.addc (TM.neg F.B) ONEi) log1mB))) invLc
  let Hu := mul (TM.add F.W (mul F.omU F.Cq)) invLc
  let E := mulc (TM.add Hu Hb) half
  let iE := recip E
  let Dd := TM.sub F.B F.U
  let TD := mul F.T Dd
  let r12b := TM.addc (TM.scaleInt F.B (-2)) ONEi
  let s3 := TM.add r12b (TM.scaleInt TD 2)
  let Z0 := mul TD iE
  let Z1 := mul Dd iE
  let Z2 := mul (TM.add r12b TD) iE
  let uJ := mul (TM.sub F.W (mul F.U F.Cq)) invLc
  let ude := mulc (TM.neg uJ) half
  let iomU := recip F.omU
  let u2Jd1 := TM.neg (mul (mul F.U iomU) invLc)
  let u2dde := mulc u2Jd1 half
  let uT := mul F.U F.T
  let a0 := TM.scaleInt (mul F.U iomU) 3
  let a1 := mulc (mul (mul (TM.add (TM.addc F.B ONEi) (TM.scaleInt F.U (-3))) (TM.addc (TM.scaleInt F.U (-2)) ONEi))
    (mul iomU iomU)) half
  let u2T0 := mul (TM.add a0 a1) invLc
  ⟨E, iE, Dd, s3, Z0, Z1, Z2, ude, u2dde, uT, u2T0⟩

/-- The certified TM of `u² · rayGamma` (mode S if `sMode`). -/
noncomputable def cellG (F : Front) (q : TCert) (sMode : Bool) : TM :=
  let b := base F
  let t1 := raysecF b.Z0 b.iE b.uT b.ude b.u2dde (contactFuncs b.Z0 (checkImplicit true b.Z0 q.V0 q.r0))
  let t2 := TM.neg (raysecF b.Z1 b.iE F.U b.ude b.u2dde (contactFuncs b.Z1 (checkImplicit true b.Z1 q.V1 q.r1)))
  let t3 := raysecF b.Z2 b.iE b.uT b.ude b.u2dde (contactFuncs b.Z2 (checkImplicit true b.Z2 q.V2 q.r2))
  let t4 := etaBlock b.E b.ude b.u2dde (checkImplicit false b.E q.Vm q.rm)
  let u2T5 := if sMode then t5S F b.s3 b.Dd else t5R F b.s3 q.rhoP q.rhoR
  TM.add (TM.add (TM.add (TM.add (TM.add b.u2T0 t1) t2) t3) t4) u2T5

/-- The Boolean cell check (besides the chart-domain checks). -/
noncomputable def tailCheck (F : Front) (q : TCert) (sMode : Bool) : Bool :=
  (cellG F q sMode).ok && decide (0 < (cellG F q sMode).lower) && (base F).Dd.ok && decide (0 < (base F).Dd.lower)

end CKLaneR2.Tail

end


