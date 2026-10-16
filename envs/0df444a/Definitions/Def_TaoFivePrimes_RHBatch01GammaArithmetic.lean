-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01GammaArithmetic
-- name    : TaoFivePrimes_RHBatch01GammaArithmetic
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T15:39:36.325401+00:00
-- url     : https://prove2.me/theorems/56ba9803-9f2a-42df-9dce-136bf517f371
-- title:
--   Exact integer gamma-sample algorithm at height 3.29 billion
-- statement:
--   Transparent integer algorithm and record/guard types for the 16384 gamma samples in the 128-unit high-height evaluator. Defines 40-term logarithm Horner arithmetic, 32-term exponential arithmetic, and dyadic rounding. Contains no analytic Gamma enclosure or RH assertion.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198, gamma-sampling architecture; ordinary integer Taylor/logarithm certificates. Surrounding attribution: sometik179, c9908072-d99a-4431-aad8-a72c6352619a, Gabewhigham.

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHBatch01HomogeneousHorner
noncomputable def hom : List Nat→Nat→Nat→Nat
  | [],_,_ => 0
  | c::cs,x,y => c*y^cs.length+x*hom cs x y
end RHBatch01HomogeneousHorner
namespace RHBatch01LogData
open RHBatch01HomogeneousHorner
noncomputable def F : Nat := 506779050856155982994105817275475
noncomputable def coefficients : List Nat := [506779050856155982994105817275475, 168926350285385327664701939091825, 101355810171231196598821163455095, 72397007265165140427729402467925, 56308783428461775888233979697275, 46070822805105089363100528843225, 38983003912011998691854293636575, 33785270057077065532940387818365, 29810532403303293117300342192675, 26672581624008209631268727225025, 24132335755055046809243134155975, 22033871776354607956265470316325, 20271162034246239319764232691019, 18769594476153925296077993232425, 17475139684695033896348476457775, 16347711317940515580455026363725, 15356940935035029787700176281075, 14479401453033028085545880493585, 13696731104220431972813670737175, 12994334637337332897284764545525, 12360464655028194707173312616475, 11785559322236185651025716680825, 11261756685692355177646795939455, 10782532996939488999874591856925, 10342429609309305775389914638275, 9936844134434431039100114064225, 9561868884078414773473694665575, 9214164561021017872620105768645, 8890860541336069877089575741675, 8589475438239931915154335886025, 8307853292723868573673865856975, 8044111918351682269747711385325, 7796600782402399738370858727315, 7563866430688895268568743541425, 7344623925451535985421823438775, 7137733110650084267522617144725, 6942178778851451821837065990075, 6757054011415413106588077563673, 6581546115015012766157218406175, 6414924694381721303722858446525]
noncomputable def numerator (p q : Nat) : Nat := 2*p*q*hom coefficients (p^2) (q^2)
noncomputable def denominator (q : Nat) : Nat := q^80*F
noncomputable def rounded (p q D : Nat) : Nat := numerator p q*D/denominator q
noncomputable def D : Nat := 2^128
noncomputable def log2 : Nat := 235865763225513294137944142764154484399
noncomputable def log2pi : Nat := 625397158267482887231032432550145572935
end RHBatch01LogData
namespace RHBatch01GenericExpHorner
noncomputable def horner (cs : List Nat) (x : Nat) : Nat := cs.foldr (fun c p => c+x*p) 0
noncomputable def cp (D : Nat) : List Nat := [8222838654177922817725562880000000*D^31,342618277257413450738565120000000*D^27,203939450748460387344384000000*D^23,17166620433372086476800000*D^19,393008709555221760000*D^15,3379847863392000*D^11,13253058000*D^7,26970*D^3]
noncomputable def cn (D : Nat) : List Nat := [4111419327088961408862781440000000*D^29,11420609241913781691285504000000*D^25,2265993897205115414937600000*D^21,94322090293253222400000*D^17,1284342188088960000*D^13,7315688016000*D^9,20389320*D^5,31*D^1]
noncomputable def sp (D : Nat) : List Nat := [8222838654177922817725562880000000*D^30,68523655451482690147713024000000*D^26,22659938972051154149376000000*D^22,1320509264105545113600000*D^18,23118159385601280000*D^14,160945136352000*D^10,530122320*D^6,930*D^2]
noncomputable def sn (D : Nat) : List Nat := [1370473109029653802954260480000000*D^28,1631515605987683098755072000000*D^24,205999445200465037721600000*D^20,6288139352883548160000*D^16,67596957267840000*D^12,318073392000*D^8,755160*D^4,1*D^0]
end RHBatch01GenericExpHorner
namespace RHBatch01NegativeExp
open RHBatch01GenericExpHorner
noncomputable def ep (D : Nat) : List Nat := [8222838654177922817725562880000000*D^31,4111419327088961408862781440000000*D^29,342618277257413450738565120000000*D^27,11420609241913781691285504000000*D^25,203939450748460387344384000000*D^23,2265993897205115414937600000*D^21,17166620433372086476800000*D^19,94322090293253222400000*D^17,393008709555221760000*D^15,1284342188088960000*D^13,3379847863392000*D^11,7315688016000*D^9,13253058000*D^7,20389320*D^5,26970*D^3,31*D^1]
noncomputable def en (D : Nat) : List Nat := [8222838654177922817725562880000000*D^30,1370473109029653802954260480000000*D^28,68523655451482690147713024000000*D^26,1631515605987683098755072000000*D^24,22659938972051154149376000000*D^22,205999445200465037721600000*D^20,1320509264105545113600000*D^18,6288139352883548160000*D^16,23118159385601280000*D^14,67596957267840000*D^12,160945136352000*D^10,318073392000*D^8,530122320*D^6,755160*D^4,930*D^2,1*D^0]
noncomputable def numerator (D d : Nat) : Nat := horner (ep D) (d^2)-d*horner (en D) (d^2)
noncomputable def denominator (D : Nat) : Nat := D^31*(31).factorial
noncomputable def seed (D d : Nat) : Nat := numerator D d*D/denominator D
end RHBatch01NegativeExp
namespace RHBatch01GammaArithmetic
open RHBatch01LogData RHBatch01GenericExpHorner
abbrev Frac := Int×Nat
noncomputable def add (a b : Frac) : Frac := (a.1*(b.2:Int)+b.1*(a.2:Int),a.2*b.2)
noncomputable def sum (xs : List Frac) : Frac := xs.foldr add (0,1)
noncomputable def round (a : Frac) : Int := a.1*(D:Int)/(a.2:Int)
noncomputable def log2pi : Nat := 625397158267482887231032432550145572935
noncomputable def P : Nat := 314159265358979323846264338327950288419716939937510
noncomputable def square (a : Int×Int) : Int×Int := (a.1*a.1-a.2*a.2,2*a.1*a.2)
noncomputable def phaseCS (d : Nat) : Nat×Nat :=
  let Q:=D^31*8222838654177922817725562880000000
  ((horner (cp D) (d^4)-d^2*horner (cn D) (d^4))*D/Q,
   d*(horner (sp D) (d^4)-d^2*horner (sn D) (d^4))*D/Q)
structure Record where
  logu : Nat
  realPart : Int
  phase : Int
  period : Int
  phaseInput : Nat
  negative : Bool
  expInput : Nat
  cos : Nat
  sin : Nat
  expSeed : Nat
  amplitude : Nat
  gammaRe : Int
  gammaIm : Int
  deriving DecidableEq,BEq
noncomputable def compute (i : Nat) : Record :=
  let n : Int := (i:Int)-8192
  let bn : Nat := (3289999808*32+n).toNat
  let lu := rounded (bn-2^36) (bn+2^36) D
  let lb : Int := 30*(log2:Int)+(lu:Int)
  let rr:=round (sum [(-lb+2*(log2pi:Int),4*D),(-160,3*bn^2),
    (256,3*(bn^2+256)),(-n*n,819200)])
  let ii:=round (sum [((bn:Int)*(lb-(D:Int)),64*D),(-(P:Int),8*10^50),
    (6,bn),(-1024,3*bn^3),(-16*(bn:Int),3*(bn^2+256))])
  let k : Int := (ii*10^50+(P:Int)*(D:Int))/(2*(P:Int)*(D:Int))
  let residual:=ii*10^50-2*(P:Int)*k*(D:Int)
  let dp:=residual.natAbs/(8*10^50)
  let da:=(-rr).toNat/256
  let cs:=phaseCS dp
  let w:=square (square (square ((cs.1:Int),(cs.2:Int))))
  let wi:=if residual<0 then -w.2 else w.2
  let ea:=RHBatch01NegativeExp.seed D da
  let a:=(List.range 8).foldl (fun z _ => z*z/D) ea
  ⟨lu,rr,ii,k,dp,decide (residual<0),da,cs.1,cs.2,ea,a,
    (a:Int)*w.1*(2:Int)^80/(D:Int)^9,(a:Int)*wi*(2:Int)^80/(D:Int)^9⟩
end RHBatch01GammaArithmetic
namespace RHBatch01GammaGuards
open RHBatch01GammaArithmetic RHBatch01LogData
noncomputable def guard (v : Record) : Bool := decide (
  v.realPart≤0 ∧ -(100*(D:Int))≤v.realPart ∧
  v.period.natAbs≤10000000000 ∧ 2*v.phaseInput≤D ∧ 2*v.expInput≤D ∧
  0<v.cos ∧ (v.phaseInput=0 ∨ 0<v.sin) ∧ 0<v.expSeed ∧ v.expSeed≤D ∧ v.amplitude≤D)
end RHBatch01GammaGuards
noncomputable def TaoFivePrimes_RHBatch01GammaArithmetic : Nat := 16384


