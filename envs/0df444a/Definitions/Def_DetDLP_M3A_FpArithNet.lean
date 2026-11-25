-- Prove2me | Definitions.Def_DetDLP_M3A_FpArithNet
-- name    : DetDLP_M3A_FpArithNet
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:23:49.397183+00:00
-- url     : https://prove2.me/theorems/843db072-e347-4c93-8105-f06029ca63fa
-- title:
--   Concrete bounded prime-field chains and lookup bus
-- statement:
--   Two linked modular product chains share their final remainder, compare each stage output with p, pin the residue prefix, reject oversized prefixes, and expose distinct hash bus wires to 4m degree-k lookups. Includes the linear incidence bound.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3A_FpSlotTile
import Definitions.Def_DetDLP_M3B_ECLayout

set_option autoImplicit false
namespace DetDLP.M3A.FpArithNet
open S8C S8J S8G.FpMoment S8L.FpPair S8L.FpPair.Stage.Links FpSlotTile w4_M5PortTensor
attribute [-simp] Fin.natAdd_eq_addNat

variable {d m k : ℕ} (hd : 1 ≤ d)

/-- The extra d+1 columns enforce the strict bound on each stage output. -/
def stageBase := join (Stage.Links.layout hd) (AddLayout.layout (d+1))
def stageOut (i : Fin d) : Fin (stageBase hd).nb := Fin.natAdd _ (AddLayout.reg i.castSucc 0)
def stageTie (i : Fin d) : Fin (stageBase hd).nb := Fin.castAdd _ (addr hd ⟨i.val,by omega⟩ 1)
def boundedStage := links (stageBase hd) (stageOut hd) (stageTie hd)
def operand (a : Bool) (i : Fin d) : Fin (boundedStage hd).nb := Fin.castAdd _ (mul1 hd (inPos a i))

private noncomputable def rangeTest (d p : ℕ) : w3_factorTest (AddLayout.layout (d+1)) :=
  atPins (atPins (AddLayout.test (d:=d+1) true) (fun j => AddLayout.reg j 2) (fun j => p.testBit j.val))
    (fun _ : Fin 1 => AddLayout.reg (Fin.last d) 0) (fun _ => false)

noncomputable def stageTest (p : ℕ) := linksTest (stageOut hd) (stageTie hd)
  (joinTest (atPins (atPins (linkedTests hd) (fun i => mul2 hd (inPos true i)) (fun i => p.testBit i.val))
    (fun i : Fin d => addr hd ⟨d+i.val,by omega⟩ 1) (fun _ => false)) (rangeTest d p))

private abbrev bank (m : ℕ) := tiles (2*m) (boundedStage hd)
def base (m k : ℕ) := join (tiles (4*m) (slotLayout d k hd)) (join (bank hd m) (bank hd m))

def slotPort (s : Fin (4*m)) (i : Fin (slotLayout d k hd).nb) : Fin (base hd m k).nb :=
  Fin.castAdd _ (finProdFinEquiv (s,i))

def stagePort (side : Bool) (s : Fin (2*m)) (i : Fin (boundedStage hd).nb) : Fin (base hd m k).nb :=
  Fin.natAdd _ (if side then Fin.natAdd (bank hd m).nb (finProdFinEquiv (s,i)) else Fin.castAdd _ (finProdFinEquiv (s,i)))

def slotNumber (side : Bool) (s : Fin (2*m)) : Fin (4*m) :=
  ⟨if side then 2*m+s.val else s.val,by split <;> omega⟩

def whichSide (s : Fin (4*m)) := decide (2*m ≤ s.val)
def whichStep (s : Fin (4*m)) : Fin (2*m) := ⟨s.val%(2*m),Nat.mod_lt _ (by clear * - s; have := s.isLt; omega)⟩

def factorTie (u : Fin ((4*m)*d)) : Fin (base hd m k).nb × Fin (base hd m k).nb :=
  let (s,j) := finProdFinEquiv.symm u
  (slotPort hd s (xBits hd j),stagePort hd (whichSide s) (whichStep s) (operand hd true j))

/-- Row zero ties the two final remainders; other rows route the previous remainder to the current left operand. -/
def chainTie (u : Fin ((4*m)*d)) : Fin (base hd m k).nb × Fin (base hd m k).nb :=
  let (s,j) := finProdFinEquiv.symm u
  let n := whichStep s
  let a := whichSide s
  if n.val = 0 then
    let last : Fin (2*m) := ⟨2*m-1,by have := n.isLt; omega⟩
    (stagePort hd a last (stageOut hd j),stagePort hd (!a) last (stageOut hd j))
  else (stagePort hd a ⟨n.val-1,by have := n.isLt; omega⟩ (stageOut hd j),stagePort hd a n (operand hd false j))

def ties : Fin ((4*m)*d+(4*m)*d) → Fin (base hd m k).nb × Fin (base hd m k).nb :=
  Fin.addCases (factorTie hd) (chainTie hd)

def chains (m k : ℕ) := links (base hd m k) (fun u => (ties hd u).1) (fun u => (ties hd u).2)

private noncomputable def firstStageTest (p start : ℕ) (j : Fin (2*m)) : w3_factorTest (boundedStage hd) :=
  if j.val = 0 then atPins (stageTest hd p) (operand hd false) (fun i => start.testBit i.val) else stageTest hd p

def blockIndex (s : Fin (4*m)) : Fin m := ⟨s.val%m,Nat.mod_lt _ (by clear * - s; have := s.isLt; omega)⟩

noncomputable def chainTest (p T P : ℕ) (seed : FpSeed p m) : w3_factorTest (chains hd m k) :=
  linksTest (fun u => (ties hd u).1) (fun u => (ties hd u).2)
    (joinTest (tileTests fun s => slotTest hd p T (seed (blockIndex s)).1.val (seed (blockIndex s)).2.val)
      (joinTest (tileTests (firstStageTest hd p P)) (tileTests (firstStageTest hd p 1))))

/-- Word order is side, block, coordinate, bit; stage order is side, coordinate, block. -/
def prefixPort (u : Fin ((4*m)*d)) : Fin (chains hd m k).nb :=
  let v : Fin (4*m) × Fin d := finProdFinEquiv.symm u
  let a := v.1.val / (2*m)
  let i := (v.1.val/2)%m
  let j := v.1.val%2
  let s : Fin (4*m) := ⟨(a*(2*m)+j*m+i)%(4*m),Nat.mod_lt _ (by have := v.1.isLt; omega)⟩
  slotPort hd s (xBits hd v.2)

private abbrev rows (n : ℕ) := S8H0.AnchoredLayout.anchors n
private def nPins (m d : ℕ) (pre : List Bool) := min pre.length (4*m*d)
def pinBase (m k : ℕ) (pre : List Bool) := join (chains hd m k) (rows (nPins m d pre + 1))

def lhs (pre : List Bool) (i : Fin (nPins m d pre)) : Fin (pinBase hd m k pre).nb :=
  Fin.castAdd _ (prefixPort hd (Fin.castLE (min_le_right ..) i))

def rhs (pre : List Bool) (i : Fin (nPins m d pre)) : Fin (pinBase hd m k pre).nb :=
  Fin.natAdd _ i.castSucc

def arith (m k : ℕ) (pre : List Bool) := links (pinBase hd m k pre) (lhs hd pre) (rhs hd pre)

private def pins (m d : ℕ) (pre : List Bool) : w3_factorTest (rows (nPins m d pre+1)) := fun g x =>
  if g.val < nPins m d pre then decide (x ⟨g,rfl⟩ = pre[g.val]?.getD false)
  else decide (pre.length ≤ 4*m*d ∧ x ⟨g,rfl⟩ = false)

noncomputable def arithTest (p T P : ℕ) (seed : FpSeed p m) (pre : List Bool) : w3_factorTest (arith hd m k pre) :=
  linksTest (lhs hd pre) (rhs hd pre) (joinTest (chainTest hd p T P seed) (pins m d pre))

def bus (pre : List Bool) (s : Fin (4*m)) (j : Fin k) : Fin (arith hd m k pre).nb :=
  Fin.castAdd _ (slotPort hd s (zBits hd j))

def layout (m k : ℕ) (pre : List Bool) := M3B.ECLayout.layout (arith hd m k pre) (bus hd pre)
noncomputable def test (p T P : ℕ) (seed : FpSeed p m) (pre : List Bool) : w3_factorTest (layout hd m k pre) :=
  M3B.ECLayout.test _ _ (arithTest hd p T P seed pre)

theorem lookup_degree (pre : List Bool) (s : Fin (4*m)) :
    (w3_factorGraph (layout hd m k pre)).deg (M3B.ECLayout.vertex (arith hd m k pre) (bus hd pre) s) = k :=
  M3B.ECLayout.lookup_degree _ _ _

theorem oversized {p T P : ℕ} {seed : FpSeed p m} {pre : List Bool} (h : 4*m*d < pre.length)
    (x : Fin (layout hd m k pre).nb → Bool) : ¬ Accept _ (test hd p T P seed pre) x := by
  intro ha
  have h₁ := (M3B.ECLayout.accept_iff _ _ _ _).mp ha
  have h₂ := ((links_iff _ _ _ _).mp h₁).1
  have h₃ := ((join_iff _ _ _).mp h₂).2 (Fin.last (nPins m d pre))
  simpa [pins,Nat.not_le.mpr h] using h₃

theorem bus_injective (pre : List Bool) : Function.Injective (fun t : Fin (4*m) × Fin k => bus hd pre t.1 t.2) := by
  rintro ⟨s,i⟩ ⟨t,j⟩ h
  have h₁ := Fin.castAdd_injective _ _ h
  have h₂ := Fin.castAdd_injective _ _ h₁
  have h₃ := finProdFinEquiv.injective h₂
  obtain ⟨hst,hij⟩ := Prod.mk.inj h₃
  exact Prod.ext hst (z_injective hd hij)

theorem stage_edges : (boundedStage hd).ne < 5100*(d+2) := by
  have h := Stage.Links.edges hd
  change (Stage.Links.layout hd).ne+(d+1)*5+(d+d) < _
  omega

theorem edge_budget (pre : List Bool) : (layout hd m k pre).ne ≤ 70000*m*(d+3)+16*m*k+1 := by
  have hs := Nat.mul_le_mul_left (4*m) (FpSlotTile.edges (k:=k) hd).le
  have ht := Nat.mul_le_mul_left (2*m) (stage_edges hd).le
  have hn : nPins m d pre ≤ 4*m*d := min_le_right ..
  change 4*m*(slotLayout d k hd).ne + (2*m*(boundedStage hd).ne + 2*m*(boundedStage hd).ne) +
    ((4*m*d+4*m*d)+(4*m*d+4*m*d)) + (nPins m d pre+1) + (nPins m d pre+nPins m d pre) + (4*m)*k ≤ _
  nlinarith only [hs,ht,hn]

theorem lookup_read {p T P : ℕ} {seed : FpSeed p m} {pre : List Bool}
    (x : {x // (w3_factorGraph (layout hd m k pre)).Satisfies (w3_factorChecks _ (test hd p T P seed pre)) x})
    (s : Fin (4*m)) (j : Fin k) :
    w3_wireLocal _ (M3B.ECLayout.vertex _ (bus hd pre) s) x.val (M3B.ECLayout.port _ (bus hd pre) s j) =
      (w3_factorEquiv _ _ x).val (bus hd pre s j) := M3B.ECLayout.read_accepted _ _ _ x s j

end DetDLP.M3A.FpArithNet
abbrev DetDLP_M3A_FpArithNet := @DetDLP.M3A.FpArithNet.layout


