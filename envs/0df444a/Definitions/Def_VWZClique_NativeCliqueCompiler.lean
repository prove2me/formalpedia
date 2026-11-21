-- Prove2me | Definitions.Def_VWZClique_NativeCliqueCompiler
-- name    : VWZClique_NativeCliqueCompiler
-- status  : Definition
-- author  : @orz
-- created : 2026-11-20T13:57:08.189633+00:00
-- url     : https://prove2.me/theorems/31bb2b8a-68e6-4beb-a134-85f16a8f5136
-- title:
--   Word-RAM programs and bounds for the clique counting compiler
-- statement:
--   The compiler uses one finite program for each fixed clique size. Each recursive frame stores the weighted nine-vertex pattern, the position of its compacted masks and spectral labels, and the integer value passed back to its caller. The projected contraction precomputes support tables, materializes three dense matrices, and packs them into square tiles for multiplication. This module defines these programs, their matrix layouts, the memory predicates that connect stored integers to matrix entries, and the instruction-count bounds used in the recursion. Its interface also specifies when the resulting finite program realizes the asymptotic counting bound for every graph size.
-- source:
--   V. Vassilevska Williams and O. Zamir, The k-Clique hypothesis is dead, for good, Theorem 1.1 and Appendix A, pp. 21–22. The Lean data structures and interfaces specify the recursive program, projected products, and the transfer to the uniform word RAM. https://zamir.prof/kclq.pdf

import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega
import Definitions.Def_VWZClique_Contraction
import Definitions.Def_VWZClique_Count
import Definitions.Def_VWZClique_FoldedSum
import Definitions.Def_VWZClique_Operators
import Definitions.Def_VWZClique_Weighted
import Mathlib
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring

import Definitions.Def_VWZClique_NativeProjectionContract

/- CliqueVM -/
section

/-! Simulation of bounded integer arithmetic, indirect addressing and branches on
    the fixed-width instruction interpreter used for clique counting. -/

namespace VWZClique.IntegerRAM
open TrulySubcubicAPSP






def input (ws : List ℤ) : Memory := fun a => if a < 0 then 0 else ws.getD a.toNat 0








end VWZClique.IntegerRAM

end

/- CliqueReduction -/
section

/-! Exact reduction from unordered cliques to a single weighted nine-vertex instance.
    A fixed vertex fills unused slots, and order constraints choose one increasing
    enumeration of each clique. The extra slots allow all clique sizes. -/

namespace VWZClique
namespace BlockReduction

open Finset
open scoped BigOperators
noncomputable section
open Classical



/-- Group and coordinate of one padded slot, with row-major numbering. -/
def slot {t : ℕ} (i : V) (p : Fin t) : Fin (9*t) := finProdFinEquiv (i,p)

/-- Value in an encoded block. -/
def digit {n t : ℕ} (a : Fin (n^t)) : Fin t → Fin n := finFunctionFinEquiv.symm a







/-- A pair of active slots holds adjacent vertices in the order fixed by its positions. -/
def compatible {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (r s : Fin (9*t)) (u v : Fin n) : Prop :=
  r.val < k → s.val < k →
    (r < s → u < v ∧ G.Adj u v) ∧ (s < r → v < u ∧ G.Adj v u)


/-- Unary constraints enforce internal pairs and a unique padding value. -/
def unaryOK {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (pad : Fin n) (i : V) (a : Fin (n^t)) : Prop :=
  (∀ p, k ≤ (slot i p).val → digit a p = pad) ∧
  ∀ p q, compatible G k (slot i p) (slot i q) (digit a p) (digit a q)

/-- An edge constraint checks all pairs crossing the two blocks. -/
def edgeOK {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (i j : V)
    (a b : Fin (n^t)) : Prop :=
  ∀ p q, compatible G k (slot i p) (slot j q) (digit a p) (digit b q)






/-- Initial values use only zero and one in the weighted nine-vertex instance. -/
def weights {F : Type*} [Field F] {n t : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ)
    (pad : Fin n) : WeightKey (n^t) → F
  | .inl (i, a) => if unaryOK G k pad i a then 1 else 0
  | .inr (i, j, a, b) => if edgeOK G k i j a b then 1 else 0




end
end BlockReduction
end VWZClique

end

/- CliqueStructured -/
section

/-! Composition of fixed, bounded integer loops for the published clique VM. -/

namespace VWZClique.IntegerRAM.Structured
open TrulySubcubicAPSP

/-- Advance a counter and test whether the next iteration is still below the limit. -/
def tick (i one limit test : ℤ) : Command :=
  .seq (.atom (.add i i one)) (.atom (.sub test i limit))

def nextMemory (m : Memory) (i test : ℤ) (q N : ℕ) : Memory :=
  update (update m i ((q:ℤ)+1)) test (((q:ℤ)+1)-N)

theorem tick_runs {W : ℕ} {i one limit test : ℤ} {q N : ℕ} {m : Memory}
    (hneq : limit ≠ i) (hi : m i = (q:ℤ)) (h1 : m one = 1) (hn : m limit = (N:ℤ)) :
    Runs W (tick i one limit test) m 2 (nextMemory m i test q N) := by
  have hs := Runs.seq (Runs.atom (Step.add (W := W) m i i one))
    (Runs.atom (Step.sub (W := W) (update m i (m i+m one)) test i limit))
  simpa only [tick,nextMemory,hi,h1,update,if_pos rfl,if_true,if_neg hneq,hn] using hs

/-- A fixed ascending for-loop. The caller initializes the counter and the input limit. -/
def repeatN (body : Command) (i one limit test : ℤ) : Command :=
  .repeatWhileNegative (.seq body (tick i one limit test)) test

/-- With a per-iteration body bound `B`, the compiled loop uses at most
    `N(B+3)` instructions, charging the two counter updates and the backward test. -/
theorem repeatN_runs {W N B : ℕ} (hN : 0 < N) (body : Command) {i one limit test : ℤ}
    (hneq : limit ≠ i) (inv : ℕ → Memory → Prop)
    (fits : ∀ q : ℕ, q ≤ N → Fits W ((q:ℤ)-N))
    (step : ∀ q : ℕ, q < N → ∀ m : Memory, inv q m →
      ∃ t : ℕ, t ≤ B ∧ ∃ x : Memory, Runs W body m t x ∧
        x i = (q:ℤ) ∧ x one = 1 ∧ x limit = (N:ℤ) ∧ inv (q+1) (nextMemory x i test q N))
    {m : Memory} (hm : inv 0 m) :
    ∃ t : ℕ, t ≤ N*(B+3) ∧ ∃ out, Runs W (repeatN body i one limit test) m t out ∧ inv N out := by
  have go (r q : ℕ) (he : q+r=N) (hr : 0<r) (m : Memory) (hin : inv q m) :
      ∃ t : ℕ, t ≤ r*(B+3) ∧ ∃ out,
        Runs W (repeatN body i one limit test) m t out ∧ inv N out := by
    induction r generalizing q m with
    | zero => omega
    | succ r ih =>
      obtain ⟨s,hs,x,hx,hxi,hx1,hxN,hin'⟩ := step q (by omega) m hin
      let y := nextMemory x i test q N
      have run : Runs W (.seq body (tick i one limit test)) m (s+2) y :=
        Runs.seq hx (tick_runs hneq hxi hx1 hxN)
      have htest : y test = ((q:ℤ)+1)-N := by simp [y,nextMemory,update]
      have hfit : Fits W (y test) := by
        rw [htest]
        exact_mod_cast fits (q+1) (by omega)
      by_cases hz : r=0
      · subst r
        have hqn : q+1=N := by omega
        refine ⟨(s+2)+1,by omega,y,Runs.loop_done run hfit ?_,hqn ▸ hin'⟩
        rw [htest]
        exact_mod_cast (show ¬ ((q:ℤ)+1-(N:ℤ))<0 by omega)
      · obtain ⟨t,ht,out,ho,final⟩ := ih (q+1) (by omega) (by omega) y hin'
        refine ⟨(s+2)+1+t,?_,out,Runs.loop_again run hfit ?_ ho,final⟩
        · rw [Nat.succ_mul]
          omega
        · rw [htest]
          omega
  exact go N 0 (by omega) hN m hm

end VWZClique.IntegerRAM.Structured

namespace VWZClique.BlockReduction
open IntegerRAM IntegerRAM.Structured




end VWZClique.BlockReduction

end

/- WordButterfly -/
section

/-! A fixed native signed-word program for one product-basis digit.
    Four contiguous input stripes are streamed into one contiguous output array.
    Each output quartet has the order 00, 11, 01+10, 01−10. -/

namespace VWZClique.IntegerRAM.Butterfly
open Structured TrulySubcubicAPSP

namespace Reg
abbrev p0 : ℤ := -1
abbrev p1 : ℤ := -2
abbrev p2 : ℤ := -3
abbrev p3 : ℤ := -4
abbrev dest : ℤ := -5
abbrev x0 : ℤ := -6
abbrev x1 : ℤ := -7
abbrev x2 : ℤ := -8
abbrev x3 : ℤ := -9
abbrev sum : ℤ := -10
abbrev diff : ℤ := -11
abbrev count : ℤ := -12
abbrev srcBase : ℤ := -13
abbrev dstBase : ℤ := -14
abbrev stride : ℤ := -15
abbrev one : ℤ := -16
abbrev zero : ℤ := -17
abbrev stages : ℤ := -18
abbrev swap : ℤ := -19
end Reg

/-- Straight-line commands, with one native instruction per list entry. -/
def line : List Atom → Command
  | [] => .skip
  | a :: as => .seq (.atom a) (line as)





def prepare : List Atom := [
  .one Reg.one, .sub Reg.zero Reg.one Reg.one,
  .add Reg.p0 Reg.srcBase Reg.zero, .add Reg.p1 Reg.p0 Reg.stride,
  .add Reg.p2 Reg.p1 Reg.stride, .add Reg.p3 Reg.p2 Reg.stride,
  .add Reg.dest Reg.dstBase Reg.zero, .sub Reg.count Reg.zero Reg.stride]

def readInputs : List Atom := [
  .load Reg.x0 Reg.p0, .load Reg.x1 Reg.p1, .load Reg.x2 Reg.p2, .load Reg.x3 Reg.p3,
  .add Reg.sum Reg.x2 Reg.x3, .sub Reg.diff Reg.x2 Reg.x3]

def writeOne (r : ℤ) : Command := line [.store Reg.dest r,.add Reg.dest Reg.dest Reg.one]

def writeOutputs : Command := .seq (writeOne Reg.x0) (.seq (writeOne Reg.x1)
    (.seq (writeOne Reg.sum) (writeOne Reg.diff)))

def advance : List Atom := [
  .add Reg.p0 Reg.p0 Reg.one, .add Reg.p1 Reg.p1 Reg.one,
  .add Reg.p2 Reg.p2 Reg.one, .add Reg.p3 Reg.p3 Reg.one,
  .add Reg.count Reg.count Reg.one]

def body : Command := .seq (line readInputs) (.seq writeOutputs (line advance))
def sweep : Command := .repeatWhileNegative body Reg.count
def stage : Command := .seq (line prepare) sweep














set_option maxHeartbeats 1600000


attribute [local simp] Reg.p0 Reg.p1 Reg.p2 Reg.p3 Reg.dest Reg.x0 Reg.x1 Reg.x2 Reg.x3
  Reg.sum Reg.diff Reg.count Reg.srcBase Reg.dstBase Reg.stride Reg.one Reg.zero Reg.stages Reg.swap
















end VWZClique.IntegerRAM.Butterfly

end

/- NativeMaskScan -/
section

/-! Uniform stable compaction for mask and projected-label records. -/
namespace VWZClique.IntegerRAM.MaskScan
open Structured Butterfly

abbrev idx : ℤ := -200
abbrev lim : ℤ := -201
abbrev unit : ℤ := -5
abbrev test : ℤ := -202
abbrev outC : ℤ := -203
abbrev outV : ℤ := -204
abbrev flag : ℤ := -205
abbrev value : ℤ := -206

/-- One output record consists of its original numeric code and its signed value. -/
def appendRow : List Atom := [.store outC idx, .store outV value,
  .add outC outC unit, .add outV outV unit]
def scanBody (classify : Command) := Command.seq classify (.whenNonnegative flag (line appendRow))
def scan (classify : Command) := repeatN (scanBody classify) idx unit lim test









end VWZClique.IntegerRAM.MaskScan

end

/- WordGraphDivide -/
section

/-! Repeated subtraction for radix decoding. It uses one graph-order cell and
four negative cells, with a time linear in the quotient. A blocked input table
can afford linear work per packed key. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction

namespace Division
abbrev num : ℤ := -1
abbrev quot : ℤ := -2
abbrev test : ℤ := -3
abbrev one : ℤ := -5

def body : Command :=
  .seq (.atom (.sub num num 0))
  (.seq (.atom (.add quot quot one))
  (.seq (.atom (.sub test 0 num))
        (.atom (.sub test test one))))

def loop : Command := .repeatWhileNegative body test

def command : Command :=
  .seq (.atom (.sub quot quot quot))
  (.seq (.atom (.sub test num 0))
        (.whenNonnegative test loop))









theorem Room.fits {W M : ℕ} (cap : Room W M) {v : ℤ} (lo : -(M:ℤ) ≤ v)
    (hi : v ≤ (M:ℤ)) : Fits W v := ⟨(neg_le_neg cap.le).trans lo, hi.trans_lt cap⟩



end Division
end VWZClique.IntegerRAM.Graph

end

/- WordGraphDigits -/
section

/-! Radix-n unpacking of a blocked vertex label by the native word machine. -/

namespace VWZClique.IntegerRAM.Graph
open Structured BlockReduction

namespace Digits
open Division

def step (r : ℤ) : Command :=
  .seq command (.seq (.atom (.mul r num one)) (.atom (.mul num quot one)))








end Digits
end VWZClique.IntegerRAM.Graph

end

/- NativeMaskScanClass -/
section

namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph
abbrev digit : ℤ := -6
abbrev amount : ℤ := -207
abbrev sign : ℤ := -208
abbrev countFrom : ℤ := -209
abbrev signFrom : ℤ := -210
abbrev remSteps : ℤ := -211
abbrev len : ℤ := -212
abbrev zero : ℤ := -213
abbrev cmp : ℤ := -214



def mark (h dst : ℤ) (act : Atom) : Command :=
  .seq (.atom (.sub cmp digit h)) (.whenNonnegative cmp (.atom act))




def oneDigit : Command := .seq (Graph.Digits.step digit)
  (.seq (mark countFrom amount (.add amount amount unit))
  (.seq (mark signFrom sign (.sub sign zero sign)) (.atom (.add remSteps remSteps unit))))



end VWZClique.IntegerRAM.MaskScan

end

/- NativeMaskScanDigits -/
section

namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph
open Division (num)


def beginDigits : List Atom := [.sub zero unit unit,.sub amount unit unit,.one sign,
  .mul num idx unit,.sub remSteps zero len,.sub cmp len unit]
def allDigits : Command := .seq (Butterfly.line beginDigits)
  (.whenNonnegative cmp (.repeatWhileNegative oneDigit remSteps))




end VWZClique.IntegerRAM.MaskScan

end

/- NativeMaskScanTable -/
section

namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph Butterfly
abbrev leftCut : ℤ := -215
abbrev rightCut : ℤ := -216
abbrev coef : ℤ := -217
abbrev ptr : ℤ := -218

def writeValue : List Atom := [.add ptr coef amount,.load value ptr,.mul value value sign,
  .sub flag amount rightCut,.sub cmp leftCut amount]
def post : Command := .seq (line writeValue) (.whenNonnegative cmp (.atom (.one flag)))
def classifier : Command := .seq allDigits post










end VWZClique.IntegerRAM.MaskScan

end

/- FoldKernel -/
section

open VWZClique
namespace VWZClique.FoldProof

abbrev Quad := Bool × Bool × Bool × Bool

def pin {L : ℕ} (m : Option (Mask L)) (read : Quad → Bool) (u : Bits L) : Prop :=
  match m with
  | none => True
  | some mask => ∀ i r, mask i = some r → u i = read r

def restore {L : ℕ} (m : Mask L) (read : Quad → Bool) (u : Bits L) : Bits L :=
  fun i => (m i).elim (u i) read


open Classical in
noncomputable def flag {F : Type*} [Field F] {L : ℕ} (m : Option (Mask L)) (read : Quad → Bool)
    (u : Bits L) : F := if pin m read u then 1 else 0




end VWZClique.FoldProof

end

/- FoldRouting -/
section

open VWZClique
namespace VWZClique.FoldProof

def perm {L : ℕ} (m : Option (Mask L)) (i : Fin 3) : Fin 3 :=
  if m.isSome then ![1,0,2] i else i

def adjust {L : ℕ} (m : Option (Mask L)) (i : Fin 3) (s : Bits L) : Bits L :=
  match m with
  | none => s
  | some m => ![restore m (fun r => r.2.2.1) s, restore m (fun r => r.2.2.2) s,s] i

def route {L : ℕ} (a b : Option (Mask L)) (h : Fin 3) : Slot → V × (Bits L → Bits L)
  | .inl i => if h=1 then (site h (perm b i),adjust b i) else (site h i,id)
  | .inr i => if h=2 then (site (next h) (perm a i),adjust a i) else (site (next h) i,id)













end VWZClique.FoldProof

end

/- GraphWeights -/
section

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.FoldProof


abbrev Kind := V ⊕ V × V

def kind (p : V × V) : Kind :=
  if p.1=p.2 then .inl p.1 else if p.1<p.2 then .inr p else .inr (p.2,p.1)

def shape {n : ℕ} : WeightKey n → Kind
  | .inl (i,_) => .inl i
  | .inr (i,j,_,_) => .inr (i,j)

def addressValue {n : ℕ} : WeightKey n → V → Fin n
  | .inl (_,x), _ => x
  | .inr (i,_,x,y), k => if k=i then x else y




def collect {F I T : Type*} [Field F] [Fintype T] {n : ℕ} (ep : T → V × V)
    (f : T → Fin n → Fin n → (I → F) → F) (k : WeightKey n) (w : I → F) : F :=
  ∏ t ∈ Finset.univ.filter (fun t => kind (ep t) = shape k),
    f t (addressValue k (ep t).1) (addressValue k (ep t).2) w


end VWZClique.FoldProof

end

/- FoldFactors -/
section

open VWZClique
namespace VWZClique.FoldProof

abbrev FoldToken (E : Finset EdgeSlot) := Fin 4 ⊕ (Fin 3 × Slot) ⊕ ↥E

def pinSite (i : Fin 4) : V := ![site 0 0,site 0 1,site 1 0,site 1 1] i

noncomputable def pinWeight {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L))
    (i : Fin 4) (s : Bits L) : F :=
  ![flag a Prod.fst s,flag a (fun r => r.2.1) s,flag b Prod.fst s,flag b (fun r => r.2.1) s] i

def ends {L : ℕ} (a b : Option (Mask L)) {E : Finset EdgeSlot} : FoldToken E → V × V
  | .inl i => (pinSite i,pinSite i)
  | .inr (.inl (h,s)) => ((route a b h s).1,(route a b h s).1)
  | .inr (.inr e) => ((route a b e.val.1 e.val.2.1).1,(route a b e.val.1 e.val.2.2).1)

noncomputable def weight {F : Type*} [Field F] {L : ℕ} (a b : Option (Mask L)) {E : Finset EdgeSlot} :
    FoldToken E → Bits L → Bits L → (ChannelKey L → F) → F
  | .inl i, s, _, _ => pinWeight a b i s
  | .inr (.inl (h,i)), s, _, w => w (h,.inl (i,(route a b h i).2 s))
  | .inr (.inr e), s,t,w => w (e.val.1,.inr (e.val.2.1,e.val.2.2,
      (route a b e.val.1 e.val.2.1).2 s,(route a b e.val.1 e.val.2.2).2 t))






end VWZClique.FoldProof

end

/- FoldEdges -/
section

open VWZClique
namespace VWZClique.FoldProof

def epPair {L : ℕ} (a b : Option (Mask L)) (e : EdgeSlot) : V × V :=
  ((route a b e.1 e.2.1).1, (route a b e.1 e.2.2).1)

def edgeImage {L : ℕ} (a b : Option (Mask L)) (e : EdgeSlot) : Sym2 V :=
  s((epPair a b e).1, (epPair a b e).2)

def foldedGraph {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet ↑(E.image (edgeImage a b))


theorem image_drop {α β : Type*} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (x y : α) (hy : y ∈ T) (hyx : y ≠ x) (h : f x = f y) :
    T.image f = (T.erase x).image f := by
  apply Finset.Subset.antisymm _ (Finset.image_mono f (Finset.erase_subset _ _))
  intro z hz
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
  by_cases heq : u = x
  · subst u
    exact Finset.mem_image.mpr ⟨y, Finset.mem_erase.mpr ⟨hyx,hy⟩, h.symm⟩
  · exact Finset.mem_image_of_mem f (Finset.mem_erase.mpr ⟨heq,hu⟩)

def leftEdge (h : Fin 3) : EdgeSlot := (h, .inl 0, .inl 2)
def rightEdge (h : Fin 3) : EdgeSlot := (h, .inr 1, .inr 2)

theorem folded_count {L : ℕ} (a b : Option (Mask L)) (E : Finset EdgeSlot)
    (ha : a.isSome = true → wedgePlaced E 0 2)
    (hb : b.isSome = true → wedgePlaced E 1 0) :
    Nat.card (foldedGraph a b E).edgeSet + a.isSome.toNat + b.isSome.toNat ≤ E.card := by
  have graphBound : Nat.card (foldedGraph a b E).edgeSet ≤ (E.image (edgeImage a b)).card := by
    rw [Nat.card_coe_set_eq, foldedGraph, SimpleGraph.edgeSet_fromEdgeSet, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard Set.sdiff_subset
  obtain ⟨T,hImage,hCard,hb'⟩ : ∃ T : Finset EdgeSlot,
      E.image (edgeImage a b) = T.image (edgeImage a b) ∧
      T.card + a.isSome.toNat = E.card ∧
      (b.isSome = true → wedgePlaced T 1 0) := by
    cases a with
    | none => exact ⟨E,rfl,by simp,hb⟩
    | some m =>
      have hA := ha rfl
      refine ⟨E.erase (leftEdge 0), ?_, Finset.card_erase_add_one hA.1, ?_⟩
      · exact image_drop E (edgeImage (some m) b) (leftEdge 0) (rightEdge 2) hA.2 (by decide) rfl
      · intro h
        exact ⟨Finset.mem_erase.mpr ⟨by decide,(hb h).1⟩,
          Finset.mem_erase.mpr ⟨by decide,(hb h).2⟩⟩
  have countT : (T.image (edgeImage a b)).card + b.isSome.toNat ≤ T.card := by
    cases b with
    | none => simpa using (Finset.card_image_le (s := T) (f := edgeImage a none))
    | some m =>
      have hB := hb' rfl
      rw [image_drop T (edgeImage a (some m)) (leftEdge 1) (rightEdge 0) hB.2 (by decide) rfl]
      have hErase : (T.erase (leftEdge 1)).card + 1 = T.card := Finset.card_erase_add_one hB.1
      have hBound := Finset.card_image_le (s := T.erase (leftEdge 1)) (f := edgeImage a (some m))
      change _ + 1 ≤ _
      omega
  rw [hImage] at graphBound
  omega

end VWZClique.FoldProof

end

/- WeightedPlacement -/
section

open VWZClique VWZClique.FoldProof OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof








theorem pairs_card (H : SimpleGraph V) : (pairs H).card ≤ Nat.card H.edgeSet := by
  classical
  let mapEdge : ↥(pairs H) → H.edgeSet := fun p =>
    ⟨s(p.val.1,p.val.2),(Finset.mem_filter.mp p.property).2.2⟩
  have hinj : Function.Injective mapEdge := by
    intro p q hpq
    obtain ⟨p,hp⟩ := p
    obtain ⟨q,hq⟩ := q
    apply Subtype.ext
    obtain ⟨hp,_⟩ := (Finset.mem_filter.mp hp).2
    obtain ⟨hq,_⟩ := (Finset.mem_filter.mp hq).2
    have huv : s(p.1,p.2) = s(q.1,q.2) := congrArg Subtype.val hpq
    rcases Sym2.eq_iff.mp huv with huv|huv
    · exact Prod.ext huv.1 huv.2
    · exact (not_lt_of_ge hq.le (by simpa only [huv.1,huv.2] using hp)).elim
  simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective mapEdge hinj



theorem slots_card (π : Equiv.Perm V) (H : SimpleGraph V) :
    (slots π H).card ≤ Nat.card H.edgeSet := Finset.card_image_le.trans (pairs_card H)

theorem slots_adj (π : Equiv.Perm V) (H : SimpleGraph V) {u v : V} (hlt : u<v)
    (h : H.Adj (π u) (π v)) : locate u v ∈ slots π H := by
  classical
  have ne : π u ≠ π v := π.injective.ne hlt.ne
  rcases lt_or_gt_of_ne ne with hnum|hnum
  · exact Finset.mem_image.mpr ⟨(π u,π v),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnum,h⟩,
      by simp [chosen,min_eq_left hlt.le,max_eq_right hlt.le]⟩
  · exact Finset.mem_image.mpr ⟨(π v,π u),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hnum,h.symm⟩,
      by simp [chosen,min_eq_right hlt.le,max_eq_left hlt.le]⟩

theorem place_wedges (H : SimpleGraph V) (f g : Fin 3 → V)
    (hf : wedge H f) (hg : wedge H g) (hfg : ∀ i j, f i ≠ g j) :
    ∃ π : Equiv.Perm V, wedgePlaced (slots π H) 0 2 ∧ wedgePlaced (slots π H) 1 0 := by
  let sites : Slot → V := Sum.elim ![0,2,1] ![3,5,4]
  let verts := Sum.elim f g
  have hs : Function.Injective sites := by decide
  have hv : Function.Injective verts := by
    intro v w h
    rcases v with i|i <;> rcases w with j|j
    · exact congrArg Sum.inl (hf.1 h)
    · exact (hfg _ _ h).elim
    · exact (hfg _ _ h.symm).elim
    · exact congrArg Sum.inr (hg.1 h)
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair sites verts hs hv
  have A (i : Fin 3) : π (![0,2,1] i) = f i := hπ (.inl i)
  have B (i : Fin 3) : π (![3,5,4] i) = g i := hπ (.inr i)
  refine ⟨π,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact slots_adj π H (u:=0) (v:=2) (by decide) (by simpa [← A 0,← A 1] using hf.2.1)
  · exact slots_adj π H (u:=1) (v:=2) (by decide) (by simpa [← A 2,← A 1] using hf.2.2.symm)
  · exact slots_adj π H (u:=3) (v:=5) (by decide) (by simpa [← B 0,← B 1] using hg.2.1)
  · exact slots_adj π H (u:=4) (v:=5) (by decide) (by simpa [← B 2,← B 1] using hg.2.2.symm)

end VWZClique.WeightedProof

end

/- WeightedPadding -/
section

open VWZClique OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.WeightedProof

variable {F I J : Type*} [Field F]







def padTag {n N : ℕ} : WeightKey N → WeightKey n ⊕ F
  | .inl (i,x) => if h : x.val < n then .inl (.inl (i,⟨x,h⟩)) else .inr 0
  | .inr (i,j,x,y) => if h : x.val < n ∧ y.val < n then .inl (.inr (i,j,⟨x,h.1⟩,⟨y,h.2⟩)) else .inr 0





end VWZClique.WeightedProof

end

/- UniformFoldWeights -/
section

open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds







/-- The literal product of all unary, edge and pin factors routed to this table entry. -/
noncomputable def updated {F : Type*} [Field F] {L : ℕ} (E : Finset EdgeSlot)
    (a b : Option (Mask L)) (w : ChannelKey L → F) (k : WeightKey (2^L)) : F :=
  collect (ends (E:=E) a b)
    (fun t x y => weight a b t ((wordIndex L).symm x) ((wordIndex L).symm y)) k w














end VWZClique.UniformFolds

end

/- NativeMaskScanScale -/
section

namespace VWZClique.IntegerRAM.MaskScan
open Structured Graph Butterfly

abbrev powBase : ℤ := -219

def scaleFinish : List Atom := [.add ptr powBase amount,.load ptr ptr,.mul value value ptr,.add countFrom countFrom unit]
def scaleClass : Command := .seq classifier (.seq (.atom (.add countFrom unit unit)) (.seq allDigits (line scaleFinish)))


end VWZClique.IntegerRAM.MaskScan

end

/- NativeMaskScanForward -/
section

/-! A contiguous convolution triangle realizes every coefficient (shift^[s] c) 0
with one pass in O((L+1)^2) native instructions. -/
namespace VWZClique.IntegerRAM.MaskScan.Forward
open Structured Butterfly
abbrev rd : ℤ := -240
abbrev wr : ℤ := -241
abbrev other : ℤ := -242
abbrev ireg : ℤ := -243
abbrev maxI : ℤ := -244
abbrev check : ℤ := -245
abbrev va : ℤ := -246
abbrev vb : ℤ := -247
abbrev unit : ℤ := -5

def block : List Atom := [.add other rd unit, .load va rd, .load vb other, .add vb vb vb,
  .sub va va vb,.store wr va,.add rd rd unit,.add wr wr unit]
def forward : Command := repeatN (line block) ireg unit maxI check





end VWZClique.IntegerRAM.MaskScan.Forward

end

/- NativeMaskScanResidual -/
section

namespace VWZClique.IntegerRAM.MaskScan.Forward
open Structured Butterfly
abbrev resWr : ℤ := -249
abbrev powWr : ℤ := -250
abbrev stride : ℤ := -251
abbrev parity : ℤ := -252
abbrev power : ℤ := -253
abbrev nilReg : ℤ := -254

def gatherBlock : List Atom := [.load va rd,.mul va parity va,.sub va unit va,
  .store resWr va,.store powWr power,.add rd rd stride,.add resWr resWr unit,
  .sub powWr powWr unit,.sub parity nilReg parity,.add power power power]
def gather : Command := repeatN (line gatherBlock) ireg unit maxI check




end VWZClique.IntegerRAM.MaskScan.Forward

end

/- NativeMaskScanPrecompute -/
section

namespace VWZClique.IntegerRAM.MaskScan.Forward
open Structured Butterfly

/-- A caller places four runtime words in this fixed header. The coefficients
occupy the first row of the triangular buffer. The two answers are contiguous
arrays with arbitrary disjoint base addresses beyond the triangle. -/
abbrev inLen : ℤ := 300
abbrev inTriangle : ℤ := 301
abbrev inResidual : ℤ := 302
abbrev inPowers : ℤ := 303
def startF : List Atom := [.one unit,.sub ireg unit unit,.mul rd inTriangle unit,.add stride inLen unit,
  .add wr rd stride,.mul maxI inLen stride,.sub check inLen unit]
def startG : List Atom := [.one unit,.sub ireg unit unit,.sub nilReg unit unit,.mul rd inTriangle unit,
  .mul resWr inResidual unit,.add powWr inPowers inLen,.add stride inLen unit,.add maxI stride nilReg,
  .one parity,.one power]
def precompute : Command := .seq (line startF) (.seq (.whenNonnegative check forward) (.seq (line startG) gather))





end VWZClique.IntegerRAM.MaskScan.Forward

end

/- NativeMaskScanPower -/
section

namespace VWZClique.IntegerRAM.MaskScan.Pow
open Structured Butterfly
abbrev base : ℤ := -264
abbrev bound : ℤ := -265
abbrev x : ℤ := -266
abbrev ireg : ℤ := -267
abbrev flag : ℤ := -268
abbrev one : ℤ := -269

def setup := [Atom.one one,.sub ireg one one,.one x,.sub flag bound one]
def command := Command.seq (line setup) (.whenNonnegative flag
  (repeatN (.atom (.mul x x base)) ireg one bound flag))


end VWZClique.IntegerRAM.MaskScan.Pow

end

/- NativeMaskScanArena -/
section

namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Butterfly
abbrev Lr : ℤ := 300
abbrev Cr : ℤ := 301
abbrev Rr : ℤ := 302
abbrev Pr : ℤ := 303
abbrev Ar : ℤ := 304
abbrev Dr : ℤ := 305
abbrev MC : ℤ := 306
abbrev MV : ℤ := 307
abbrev LC : ℤ := 308
abbrev LV : ℤ := 309
abbrev counts : ℤ := 310
abbrev originalN : ℤ := 311
abbrev maskN : ℤ := 312
abbrev slab : ℤ := 313
abbrev labelN : ℤ := 314
abbrev inputLen : ℤ := 320
abbrev scratch : ℤ := -275

def layout (w : ℤ) : List Atom := [.one unit,.mul originalN 0 unit,.mul Lr inputLen unit,
  .mul labelN 0 0,.mul slab labelN 0,.add scratch 0 0,.add scratch scratch scratch,.add scratch scratch scratch,
  .add scratch scratch 0,.mul Cr scratch scratch,.add Cr Cr scratch,.add Cr Cr w,
  .add Rr Cr slab,.add Pr Rr slab,.add MC Pr slab,.add MV MC slab,.add LC MV slab,.add LV LC slab,
  .add counts LV slab,.mul (-2) Cr unit,.mul (-12) Lr unit]



end VWZClique.IntegerRAM.MaskScan.Arena

end

/- NativeMaskScanStart -/
section

namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Butterfly

def maskInit : List Atom := [.one unit,.sub idx unit unit,.add 0 unit unit,.add 0 0 0,.add 0 0 unit,
  .mul len Lr unit,.one countFrom,.add signFrom unit unit,.add signFrom signFrom unit,.mul coef Cr unit,
  .mul leftCut Dr unit,.add rightCut Lr unit,.mul outC MC unit,.mul outV MV unit,.mul lim maskN unit]
def labelInit : List Atom := [.one unit,.sub idx unit unit,.add 0 unit unit,.add 0 0 0,
  .mul len Lr unit,.sub countFrom 0 unit,.mul signFrom 0 unit,.mul coef Rr unit,.mul powBase Pr unit,
  .sub leftCut Ar unit,.add rightCut Ar Dr,.add rightCut rightCut unit,.mul outC LC unit,.mul outV LV unit,.mul lim labelN unit]

def radixSetup : List Atom := [.one unit,.mul Pow.bound Lr unit,.add Pow.base unit unit,.add Pow.base Pow.base Pow.base,
  .add Pow.base Pow.base unit]
def radixCommand := Command.seq (line radixSetup) (.seq Pow.command (.atom (.mul maskN Pow.x unit)))




end VWZClique.IntegerRAM.MaskScan.Arena

end

/- NativeMaskScanSave -/
section

namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Butterfly

def saveMask := [Atom.sub scratch outC MC,.store counts scratch]
def saveLabel := [Atom.sub scratch outC LC,.add ptr counts unit,.store ptr scratch,.mul 0 originalN unit]



end VWZClique.IntegerRAM.MaskScan.Arena

end

/- NativeMaskScanBoth -/
section

namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Graph RankSwap RankSwap.MaskEnumeration UniformFolds Butterfly

def compact := Command.seq (line maskInit) (.seq (scan classifier) (.seq (line saveMask)
  (.seq (line labelInit) (.seq (scan scaleClass) (line saveLabel)))))





end VWZClique.IntegerRAM.MaskScan.Arena

end

/- NativeSignedDivision -/
section

/-! Exact signed division on the published add/subtract/multiply word machine.
The divisor is positive. A fixed scan takes one quotient bit per iteration. -/
namespace VWZClique.IntegerRAM.SignedDivision
open Structured
abbrev value : ℤ := -100
abbrev divisor : ℤ := -101
abbrev length : ℤ := -102
abbrev remn : ℤ := -103
abbrev result : ℤ := -104
abbrev threshold : ℤ := -105
abbrev index : ℤ := -106
abbrev unit : ℤ := -107
abbrev flag : ℤ := -108
abbrev signReg : ℤ := -109


def grow : Command := .atom (.add threshold threshold threshold)
def scale : Command := repeatN grow index unit length flag
def save : Command := .seq (.atom (.sub remn remn threshold)) (.atom (.add result result unit))
def digit : Command :=
  .seq (.atom (.add result result result))
  (.seq (.atom (.add remn remn remn))
  (.seq (.atom (.sub flag remn threshold)) (.whenNonnegative flag save)))
def scan : Command := repeatN digit index unit length flag







def initCode : Command :=
  .seq (.atom (.one unit))
  (.seq (.atom (.sub index index index))
  (.seq (.atom (.sub result result result))
  (.seq (.atom (.mul threshold divisor unit))
  (.seq (.atom (.sub remn result value))
  (.seq (.atom (.sub signReg result unit))
       (.whenNonnegative value (.seq (.atom (.mul remn value unit)) (.atom (.one signReg)))))))))


def command : Command :=
  .seq initCode (.seq scale (.seq (.atom (.sub index index index)) (.seq scan (.atom (.mul result result signReg)))))





end VWZClique.IntegerRAM.SignedDivision

end

/- NativeWindowInit -/
section

namespace VWZClique.IntegerRAM.WindowInit
open Structured SignedDivision

/-- L remains in the register produced by the graph-size preparation. -/
abbrev Lreg : ℤ := -12
abbrev loReg : ℤ := -15
abbrev hiReg : ℤ := -16
abbrev degreeReg : ℤ := -7
abbrev negLower : ℤ := -8

def constant (dest : ℤ) : ℕ → Command
  | 0 => .atom (.sub dest dest dest)
  | n+1 => .seq (constant dest n) (.atom (.add dest dest unit))


def setup (c r : ℕ) : Command :=
  .seq (.atom (.one unit)) (.seq (constant value c) (.seq (constant divisor r)
    (.seq (.atom (.mul value value Lreg)) (.atom (.add length Lreg unit)))))


def ratio (c r : ℕ) : Command := .seq (setup c r) command


/-- Copy a register without assuming a resident constant. -/
def copy (dst src : ℤ) : Command := .seq (.atom (.one unit)) (.atom (.mul dst src unit))

def window (K : ℕ) := Command.seq (ratio (K-4) (4*K))
  (.seq (copy loReg result) (.seq (ratio (K+4) (4*K)) (.seq (copy hiReg result)
    (.seq (.atom (.sub degreeReg hiReg loReg)) (.seq (.atom (.sub negLower negLower negLower))
     (.atom (.sub negLower negLower loReg)))))))


end VWZClique.IntegerRAM.WindowInit

end

/- NativeFoldBits -/
section

namespace VWZClique.IntegerRAM.FoldBits
open Structured







def code : List Atom → Command
  | [] => .skip
  | h :: t => .seq (.atom h) (code t)











end VWZClique.IntegerRAM.FoldBits

end

/- NativeWindowSeed -/
section

namespace VWZClique.IntegerRAM.WindowSeed
open Structured FoldBits

abbrev idx : ℤ := -21
abbrev lim : ℤ := -22
abbrev test : ℤ := -23
abbrev sign : ℤ := -24
abbrev zero : ℤ := -25
abbrev one : ℤ := -6
abbrev ptr : ℤ := -26
abbrev term : ℤ := -27
abbrev cut : ℤ := -28
abbrev base : ℤ := -2


def paritySetup : List Atom := [.one one,.sub zero one one,.sub sign zero one,
  .sub idx one one,.sub lim one WindowInit.negLower]
def parityLoop : Command := repeatN (.atom (.sub sign zero sign)) idx one lim test
def parity : Command := .seq (code paritySetup) parityLoop


def fillSetup : List Atom := [.sub idx one one,.add lim WindowInit.Lreg one,.mul ptr base one]
def before : List Atom := [.sub cut WindowInit.degreeReg idx,.sub term one one]
def writeCell : List Atom := [.store ptr term,.add ptr ptr one]
def fillOne : Command := .seq (code before) (.seq (.whenNonnegative cut (.atom (.mul term sign one))) (code writeCell))
def fill : Command := .seq (code fillSetup) (repeatN fillOne idx one lim test)


end VWZClique.IntegerRAM.WindowSeed

end

/- WordWindow -/
section

namespace VWZClique.IntegerRAM.WindowSweep
open Structured
namespace Reg
abbrev ptr : ℤ := -1
abbrev base : ℤ := -2
abbrev carry : ℤ := -3
abbrev val : ℤ := -4
abbrev test : ℤ := -5
abbrev one : ℤ := -6
end Reg

/-- Update a coefficient by c[h] + 2b[h+1], write it back, and move one entry left. -/
def body : Command :=
  .seq (.atom (.load Reg.val Reg.ptr))
  (.seq (.atom (.add Reg.carry Reg.carry Reg.carry))
  (.seq (.atom (.add Reg.carry Reg.val Reg.carry))
  (.seq (.atom (.store Reg.ptr Reg.carry))
  (.seq (.atom (.sub Reg.test Reg.base Reg.ptr))
        (.atom (.sub Reg.ptr Reg.ptr Reg.one))))))

def command : Command := .repeatWhileNegative body Reg.test








end VWZClique.IntegerRAM.WindowSweep

end

/- WordWindowTable -/
section

namespace VWZClique.IntegerRAM.WindowSweep
open Structured
open VWZClique.RankSwap.Window

abbrev degrees : ℤ := -7
abbrev counter : ℤ := -8

/-- Reset the pointer and carry before each backward sweep. -/
def reset : Command :=
  .seq (.atom (.add Reg.ptr Reg.base degrees)) (.atom (.sub Reg.carry Reg.one Reg.one))



def outerBody : Command :=
  .seq reset (.seq command (.atom (.add counter counter Reg.one)))

def tableCommand : Command := .repeatWhileNegative outerBody counter




def guardSetup : Command :=
  .seq (.atom (.sub Reg.test Reg.one Reg.one))
  (.seq (.atom (.sub Reg.test Reg.test Reg.one)) (.atom (.sub Reg.test Reg.test counter)))



def generateCommand : Command := .seq guardSetup (.whenNonnegative Reg.test tableCommand)


end VWZClique.IntegerRAM.WindowSweep

end

/- NativeWindowTables -/
section

namespace VWZClique.IntegerRAM.WindowSweep
open Structured VWZClique.RankSwap.Window


end VWZClique.IntegerRAM.WindowSweep

namespace VWZClique.IntegerRAM.WindowSeed
open Structured UniformFolds VWZClique.RankSwap.Window


def coefficients (K : ℕ) := Command.seq (WindowInit.window K) (.seq parity (.seq fill WindowSweep.generateCommand))


end VWZClique.IntegerRAM.WindowSeed

end

/- NativeMaskScanLocal -/
section

namespace VWZClique.IntegerRAM.MaskScan.Arena
open Structured Graph RankSwap UniformFolds Butterfly

def reloadLength := [Atom.one unit,.mul WindowInit.Lreg Lr unit]
def stashCuts := [Atom.one unit,.mul Ar WindowInit.loReg unit,.mul Dr WindowInit.degreeReg unit]
def prepare (K : ℕ) (source : ℤ) := Command.seq (line (layout source)) (.seq (WindowSeed.coefficients K)
  (.seq (line reloadLength) (.seq (WindowInit.window K) (.seq (line stashCuts) (.seq Forward.precompute radixCommand)))))
def buildMaskMetadata (K : ℕ) (source : ℤ) := Command.seq (prepare K source) compact









end VWZClique.IntegerRAM.MaskScan.Arena

end

/- CliqueBlockMM -/
section

/-! Fixed integer-coefficient bilinear schemes recursively multiply arbitrary
    tensor powers of their base dimension. Clearing the base coefficients'
    denominators introduces just one fixed scale factor per level. -/

namespace VWZClique.BlockMM
open scoped BigOperators

abbrev Square (I : Type*) := Matrix I I ℤ

def linear {b : ℕ} (L A : Square (Fin b)) : ℤ := ∑ i, ∑ j, L i j * A i j

/-- An integer bilinear multiplication scheme, possibly representing a rational
    scheme whose fixed denominators have been cleared. -/
structure Scheme (b r : ℕ) where
  left : Fin r → Square (Fin b)
  right : Fin r → Square (Fin b)
  out : Fin b → Fin b → Fin r → ℤ
  scale : ℤ
  correct : ∀ (A B : Square (Fin b)) (i j : Fin b),
    (∑ s, out i j s * (linear (left s) A * linear (right s) B)) = scale * (A*B) i j













end VWZClique.BlockMM

end

/- MMUniform -/
section

namespace VWZClique.BlockMM

/-- Least upper-power padding is unnecessary: this explicit depth pads by at most a factor b. -/
def depth (b n : ℕ) : ℕ := Nat.log b n + 1














end VWZClique.BlockMM

end

/- NativeFrame -/
section

namespace VWZClique.IntegerRAM.NativeFrame
open Structured




theorem reg_positive (d : ℕ) (f : Field) : 0 < reg d f := by
  cases f <;> simp [reg,Field.offset] <;> omega

theorem reg_below {d : ℕ} (hd : d ≤ 36) (f : Field) : reg d f < 297 := by
  cases f <;> simp [reg,Field.offset] <;> omega


theorem separate {a b : ℕ} (h : a<b) (f g : Field) : reg a f < reg b g := by
  cases f <;> cases g <;> simp [reg,Field.offset] <;> omega






/-- Restoring an accumulator from any source register, independent of its current value. -/
def copy (dst src : ℤ) : Command :=
  .seq (.atom (.one dst)) (.atom (.mul dst dst src))

theorem copy_runs (W : ℕ) (dst src : ℤ) (hd : src≠dst) (m : Memory) :
    Runs W (copy dst src) m 2 (update m dst (m src)) := by
  let a := update m dst 1
  have first : Runs W (.atom (.one dst)) m 1 a := .atom (.one _ _)
  have second := Runs.atom (Step.mul (W:=W) a dst dst src)
  have eq : update a dst (a dst*a src) = update m dst (m src) := by
    funext i; by_cases hi : i=dst <;> simp [a,update,hd,hi]
  rw [eq] at second
  exact first.seq second

end VWZClique.IntegerRAM.NativeFrame

end

/- UniformFolds -/
section

open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds


def representative : Bool → Option (Mask 0)
  | false => none
  | true => some Fin.elim0

def first : Branch → Bool
  | .right => false
  | _ => true

def second : Branch → Bool
  | .left => false
  | _ => true

/-- A branch's graph is fixed before the size of the assignment domain is known. -/
def child (E : Finset EdgeSlot) (d : Branch) : SimpleGraph V :=
  foldedGraph (representative (first d)) (representative (second d)) E



def HasWedges (H : SimpleGraph V) : Prop :=
  ∃ f g : Fin 3 → V, wedge H f ∧ wedge H g ∧ ∀ i j, f i ≠ g j

theorem placeable (H : SimpleGraph V) (h : HasWedges H) :
    ∃ π : Equiv.Perm V, wedgePlaced (slots π H) 0 2 ∧ wedgePlaced (slots π H) 1 0 := by
  obtain ⟨f,g,hf,hg,hd⟩ := h
  exact place_wedges H f g hf hg hd

theorem branch_smaller (H : SimpleGraph V) (π : Equiv.Perm V)
    (h : wedgePlaced (slots π H) 0 2 ∧ wedgePlaced (slots π H) 1 0) (d : Branch) :
    Nat.card (child (slots π H) d).edgeSet < Nat.card H.edgeSet := by
  let E := slots π H
  have bound := folded_count (representative (first d)) (representative (second d)) E
    (fun _ => h.1) (fun _ => h.2)
  have hE : E.card ≤ Nat.card H.edgeSet := slots_card π H
  change Nat.card (foldedGraph _ _ E).edgeSet < Nat.card H.edgeSet
  cases d <;> simp [representative,first,second] at bound hE ⊢ <;> omega

/-- A finite table of placements and graph branches can be fixed for each initial pattern.
    A split's three children may be used repeatedly for different masks and sizes. -/
inductive Plan : SimpleGraph V → Type where
  | leaf (H : SimpleGraph V) (h : ¬ HasWedges H) : Plan H
  | split (H : SimpleGraph V) (π : Equiv.Perm V)
      (h : wedgePlaced (slots π H) 0 2 ∧ wedgePlaced (slots π H) 1 0)
      (children : (d : Branch) → Plan (child (slots π H) d)) : Plan H

noncomputable def compile : (k : ℕ) → (H : SimpleGraph V) → Nat.card H.edgeSet < k → Plan H
  | 0, _, h => (Nat.not_lt_zero _ h).elim
  | k+1, H, hk => by
    classical
    by_cases hw : HasWedges H
    · let π := Classical.choose (placeable H hw)
      have hp := Classical.choose_spec (placeable H hw)
      exact .split H π hp (fun d => compile k (child (slots π H) d)
        (by have hdec := branch_smaller H π hp d; omega))
    · exact .leaf H hw

theorem edge_limit (H : SimpleGraph V) : Nat.card H.edgeSet ≤ 36 := by
  classical
  rw [Nat.card_eq_fintype_card,← SimpleGraph.edgeFinset_card]
  exact (SimpleGraph.card_edgeFinset_le_card_choose_two (G:=H)).trans_eq (by decide)

/-- This finite object depends on the nine-vertex pattern alone. -/
noncomputable def fixed (H : SimpleGraph V) : Plan H :=
  compile 37 H (by have := edge_limit H; omega)




end VWZClique.UniformFolds

end

/- UniformFoldPaths -/
section

open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds



noncomputable def Round.apply {L : ℕ} (r : Round L) (w : WeightKey (2^L) → ℚ) : WeightKey (2^L) → ℚ :=
  updated (slots r.π r.H) r.a r.b (r.inputs w)











end VWZClique.UniformFolds

end

/- SparsePartition -/
section

open VWZClique
namespace VWZClique.SparseProof

theorem make_wedge {H : SimpleGraph V} {u i v : V} (hu : H.Adj i u) (hv : H.Adj i v)
    (hne : u ≠ v) : wedge H ![u,i,v] := by
  have hui := hu.ne
  have hiv := hv.ne
  refine ⟨?_,hu.symm,hv⟩
  intro x y he
  fin_cases x <;> fin_cases y <;> simp_all

theorem hitting_set (H : SimpleGraph V)
    (hh : ¬ ∃ f g : Fin 3 → V, wedge H f ∧ wedge H g ∧ ∀ i j, f i ≠ g j) :
    ∃ S : Finset V, S.card ≤ 3 ∧
      ∀ i u v : V, i ∉ S → u ∉ S → v ∉ S → H.Adj i u → H.Adj i v → u = v := by
  classical
  have hit : ∃ S : Finset V, S.card ≤ 3 ∧ ∀ g, wedge H g → ∃ k, g k ∈ S := by
    by_cases h : ∃ f, wedge H f
    · obtain ⟨f,hf⟩ := h
      refine ⟨Finset.univ.image f, Finset.card_image_le.trans (by simp), ?_⟩
      intro g hg
      by_contra! hd
      apply hh
      exact ⟨f,g,hf,hg,fun i j hij => hd j (hij ▸ Finset.mem_image_of_mem f (Finset.mem_univ i))⟩
    · exact ⟨∅,by simp,fun g hg => (h ⟨g,hg⟩).elim⟩
  obtain ⟨S,hs,hhit⟩ := hit
  refine ⟨S,hs,?_⟩
  intro i u v hi hu hv heu hev
  by_contra hne
  obtain ⟨k,hk⟩ := hhit _ (make_wedge heu hev hne)
  fin_cases k <;> simp_all

abbrev Bag := Finset V
abbrev Bucket := Option Bag
abbrev Fiber (key : V → Bucket) (b : Bucket) := {i : V // key i = b}

theorem matching_partition (H : SimpleGraph V)
    (hh : ¬ ∃ f g : Fin 3 → V, wedge H f ∧ wedge H g ∧ ∀ i j, f i ≠ g j) :
    ∃ key : V → Bucket, Fintype.card (Fiber key none) ≤ 3 ∧
      (∀ b : Bag, Fintype.card (Fiber key (some b)) ≤ 2) ∧
      ∀ i j, H.Adj i j → key i = none ∨ key j = none ∨ key i = key j := by
  classical
  obtain ⟨S,hs,hm⟩ := hitting_set H hh
  let bag := fun i : V => Finset.univ.filter fun v : V => v ∉ S ∧ (v = i ∨ H.Adj i v)
  let key := fun i : V => if i ∈ S then (none : Bucket) else some (bag i)
  have mem_self (i : V) (hi : i ∉ S) : i ∈ bag i := by simp [bag,hi]
  have bag_size (i : V) (hi : i ∉ S) : (bag i).card ≤ 2 := by
    by_cases h : ∃ v, v ∉ S ∧ H.Adj i v
    · obtain ⟨v,hv,he⟩ := h
      apply (Finset.card_le_card (t := {i,v}) ?_).trans Finset.card_le_two
      intro x hx
      obtain ⟨hx,hxi|hedge⟩ := (Finset.mem_filter.mp hx).2
      · simp [hxi]
      · simp [hm i x v hi hx hv hedge he]
    · have sub : bag i ⊆ {i} := by
        intro x hx
        obtain ⟨hx,hxi|he⟩ := (Finset.mem_filter.mp hx).2
        · simp [hxi]
        · exact (h ⟨x,hx,he⟩).elim
      exact (Finset.card_le_card sub).trans (by simp)
  have same {i j : V} (hi : i ∉ S) (hj : j ∉ S) (he : H.Adj i j) : bag i ⊆ bag j := by
    intro x hx
    obtain ⟨hx,hxi|he'⟩ := (Finset.mem_filter.mp hx).2
    · subst x; simp [bag,hi,he.symm]
    · have := hm i x j hi hx hj he' he
      subst x; exact mem_self _ hj
  refine ⟨key,?_,?_,?_⟩
  · have : Finset.univ.filter (fun i => key i = none) = S := by ext i; simp [key]
    simpa only [Fiber, Fintype.card_subtype, this] using hs
  · intro b
    have hcard : Fintype.card (Fiber key (some b)) =
        (Finset.univ.filter (fun i => key i = some b)).card := Fintype.card_subtype _
    rw [hcard]
    let T := Finset.univ.filter (fun i => key i = some b)
    change T.card ≤ 2
    by_cases h : T.Nonempty
    · obtain ⟨i,hi⟩ := h
      have read (x : V) (hx : x ∈ T) : x ∉ S ∧ bag x = b := by
        have hh := (Finset.mem_filter.mp hx).2
        by_cases hm : x ∈ S <;> simp_all [key]
      have ⟨hn, he⟩ := read i hi
      apply (Finset.card_le_card (t := b) ?_).trans (he ▸ bag_size i hn)
      intro x hx
      have ⟨hn', he'⟩ := read x hx
      exact he' ▸ mem_self x hn'
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]
  · intro i j he
    by_cases hi : i ∈ S
    · simp [key,hi]
    by_cases hj : j ∈ S
    · simp [key,hj]
    exact Or.inr (Or.inr (by simp [key,hi,hj,Finset.Subset.antisymm (same hi hj he) (same hj hi he.symm)]))

end VWZClique.SparseProof

end

/- SparseFactor -/
section

open VWZClique
namespace VWZClique.SparseProof

abbrev Token := V ⊕ V × V
abbrev Assignment (key : V → Bucket) (n : ℕ) (b : Bucket) := Fiber key b → Fin n

open Classical in
noncomputable def factor {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V)
    (w : WeightKey n → F) (x : V → Fin n) : Token → F
  | .inl i => w (.inl (i,x i))
  | .inr (i,j) => if i < j ∧ H.Adj i j then w (.inr (i,j,x i,x j)) else 1

def owner (key : V → Bucket) : Token → Bag
  | .inl i => (key i).getD ∅
  | .inr (i,j) => (key i).getD ((key j).getD ∅)

def localAssignment {n : ℕ} (key : V → Bucket) (zero : Fin n) (z : Assignment key n none)
    (k : Bag) (y : Assignment key n (some k)) (i : V) : Fin n :=
  if h : key i = none then z ⟨i,h⟩ else if h' : key i = some k then y ⟨i,h'⟩ else zero

noncomputable def piece {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V) (key : V → Bucket)
    (zero : Fin n) (z : Assignment key n none) (k : Bag) (y : Assignment key n (some k))
    (w : WeightKey n → F) : F :=
  ∏ t ∈ Finset.univ.filter (fun t => owner key t = k), factor H w (localAssignment key zero z k y) t

def assignmentEquiv (key : V → Bucket) (n : ℕ) :
    (V → Fin n) ≃ Assignment key n none × ((k : Bag) → Assignment key n (some k)) :=
  (Equiv.piCongrFiberwise (f := key) (γ₁ := fun _ => Fin n)
    (fun b => Equiv.refl (Assignment key n b))).trans Equiv.piOptionEquivProd

theorem local_matches {n : ℕ} (key : V → Bucket) (zero : Fin n)
    (x : V → Fin n) (k : Bag) (i : V) (hi : key i = none ∨ key i = some k) :
    localAssignment key zero (fun u => x u.val) k (fun u => x u.val) i = x i := by
  rcases hi with h | h <;> simp [localAssignment,h]

theorem restrict_factor {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V) (key : V → Bucket)
    (hedge : ∀ i j, H.Adj i j → key i = none ∨ key j = none ∨ key i = key j)
    (zero : Fin n) (x : V → Fin n) (t : Token) (w : WeightKey n → F) :
    let k := owner key t
    factor H w (localAssignment key zero (fun u => x u.val) k (fun u => x u.val)) t =
    factor H w x t := by
  classical
  cases t with
  | inl i =>
    change w (.inl (_,localAssignment _ _ _ _ _ i)) = w (.inl (_,x i))
    rw [local_matches]
    cases h : key i <;> simp [owner,h]
  | inr v =>
    obtain ⟨i,j⟩ := v
    by_cases he : i < j ∧ H.Adj i j
    · simp only [factor, if_pos he]
      have h := hedge i j he.2
      have hi : key i = none ∨ key i = some (owner key (.inr (i,j))) := by
        cases hi : key i <;> simp [owner,hi]
      have hj : key j = none ∨ key j = some (owner key (.inr (i,j))) := by
        cases hi : key i <;> cases hj : key j <;> simp_all [owner]
      rw [local_matches _ _ _ _ _ hi, local_matches _ _ _ _ _ hj]
    · simp [factor,he]

theorem factorization {F : Type*} [Field F] {n : ℕ} (H : SimpleGraph V) (key : V → Bucket)
    (hedge : ∀ i j, H.Adj i j → key i = none ∨ key j = none ∨ key i = key j)
    (zero : Fin n) (w : WeightKey n → F) :
    weightedSum H w = ∑ z : Assignment key n none, ∏ k : Bag,
      ∑ y : Assignment key n (some k), piece H key zero z k y w := by
  classical
  have localProd (x : V → Fin n) :
      (∏ t : Token, factor H w x t) =
      ∏ k : Bag, piece H key zero (fun u => x u.val) k (fun u => x u.val) w := by
    rw [← Finset.prod_fiberwise Finset.univ (owner key)]
    apply Finset.prod_congr rfl
    intro k _
    apply Finset.prod_congr rfl
    intro t ht
    have hk := (Finset.mem_filter.mp ht).2
    subst k
    exact (restrict_factor H key hedge zero x t w).symm
  let e := assignmentEquiv key n
  calc
    weightedSum H w = ∑ x : V → Fin n, ∏ t : Token, factor H w x t := by
      simp [weightedSum, Fintype.prod_sum_type, Fintype.prod_prod_type, factor]
    _ = ∑ x : V → Fin n, ∏ k : Bag, piece H key zero ((e x).1) k ((e x).2 k) w :=
      Finset.sum_congr rfl fun x _ => localProd x
    _ = ∑ p : Assignment key n none × ((k : Bag) → Assignment key n (some k)),
      ∏ k : Bag, piece H key zero p.1 k (p.2 k) w := e.sum_comp (fun p => ∏ k : Bag, piece H key zero p.1 k (p.2 k) w)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.prod_sum]


end VWZClique.SparseProof

end

/- UniformFoldEvaluator -/
section

open VWZClique VWZClique.FoldProof VWZClique.WeightedProof
namespace VWZClique.UniformFolds

abbrev LeafEval (L : ℕ) :=
  (H : SimpleGraph V) → (¬ HasWedges H) → (WeightKey (2^L) → ℚ) → ℚ





open SparseProof in
noncomputable def leafKey (H : SimpleGraph V) (hw : ¬ HasWedges H) : V → Bucket :=
  Classical.choose (matching_partition H hw)

open SparseProof in
noncomputable def sparseLeaf (L : ℕ) : LeafEval L := fun H hw w =>
  let key := leafKey H hw
  let zero : Fin (2^L) := ⟨0,by positivity⟩
  ∑ z : Assignment key (2^L) none, ∏ b : Bag,
    ∑ y : Assignment key (2^L) (some b), piece H key zero z b y w

open SparseProof in
theorem sparseLeaf_correct (L : ℕ) (H : SimpleGraph V) (hw : ¬ HasWedges H)
    (w : WeightKey (2^L) → ℚ) : sparseLeaf L H hw w = weightedSum H w :=
  (factorization H (leafKey H hw) (Classical.choose_spec (matching_partition H hw)).2.2 _ w).symm








end VWZClique.UniformFolds

end

/- IntegerTiling -/
section

namespace VWZClique.Double.IntegerTiling



theorem exact_shape (L q : ℕ) : blocks L q * side L q = (2^L)^3 := by
  have h := Nat.div_le_self L q
  unfold blocks side
  rw [← pow_add, ← pow_mul]
  congr 1
  omega



end VWZClique.Double.IntegerTiling

end

/- UniformFoldBudget -/
section

namespace VWZClique.UniformFolds










/-- One projection and the actual numbers of left, right and double-mask calls.
The three per-call units allow for coefficient multiplications and accumulation. -/
def splitWork (m projection prep left right both : ℕ) : ℕ :=
  projection + m*(prep+left+3) + m*(prep+right+3) + m^2*(prep+both+3) + 3

/-- Integer scalar-work recurrence for the same static windows and graph branches
as the evaluator. Local setup and sparse leaves may each cost U n^5, preparing a
single child's weights may cost G n^2, and the transform constant is T. -/
noncomputable def planWork (mm : ℕ → ℕ) (T U G L : ℕ) : {H : SimpleGraph V} → Plan H → ℕ
  | _,.leaf _ _ => U*(2^L)^5
  | _,.split H _ _ kids =>
    let e := Nat.card H.edgeSet
    let q := windowExpansion (windowAt e) L
    splitWork (Fintype.card q.Index)
      (projectionWork mm T (tileAt e) L q.labels.card + U*(2^L)^5) (G*(2^L)^2)
      (planWork mm T U G L (kids .left)) (planWork mm T U G L (kids .right))
      (planWork mm T U G L (kids .both))









end VWZClique.UniformFolds

end

/- IntegerFoldEvaluation -/
section

open VWZClique VWZClique.SparseProof
namespace VWZClique.UniformFolds

def bitValue (x : ℚ) : ℤ := if x=1 then 1 else 0

theorem bitValue_cast {x : ℚ} (h : Binary x) : (bitValue x:ℚ) = x := by
  rcases h with rfl | rfl <;> norm_num [bitValue]

open Classical in
noncomputable def integerFactor {n : ℕ} (H : SimpleGraph V) (w : WeightKey n → ℚ)
    (x : V → Fin n) : Token → ℤ
  | .inl i => bitValue (w (.inl (i,x i)))
  | .inr (i,j) => if i < j ∧ H.Adj i j then bitValue (w (.inr (i,j,x i,x j))) else 1

theorem integerFactor_cast {n : ℕ} (H : SimpleGraph V) (w : WeightKey n → ℚ)
    (hw : ∀ k, Binary (w k)) (x : V → Fin n) (t : Token) :
    (integerFactor H w x t:ℚ) = factor H w x t := by
  classical
  cases t with
  | inl i => exact bitValue_cast (hw _)
  | inr a =>
    obtain ⟨i,j⟩ := a
    by_cases he : i < j ∧ H.Adj i j <;> simp [integerFactor,factor,he,bitValue_cast (hw _)]

/-- Evaluate the static sparse partition using integer products and sums. -/
noncomputable def integerLeaf (L : ℕ) (H : SimpleGraph V) (hh : ¬ HasWedges H)
    (w : WeightKey (2^L) → ℚ) : ℤ :=
  let key := leafKey H hh
  let zero : Fin (2^L) := ⟨0,by positivity⟩
  ∑ z : Assignment key (2^L) none, ∏ b : Bag,
    ∑ y : Assignment key (2^L) (some b), ∏ t ∈ Finset.univ.filter (fun t => owner key t = b),
      integerFactor H w (localAssignment key zero z b y) t

theorem integerLeaf_cast (L : ℕ) (H : SimpleGraph V) (hh : ¬ HasWedges H)
    (w : WeightKey (2^L) → ℚ) (hw : ∀ k, Binary (w k)) :
    (integerLeaf L H hh w:ℚ) = sparseLeaf L H hh w := by
  simp only [integerLeaf,sparseLeaf,piece,Int.cast_sum,Int.cast_prod,integerFactor_cast H w hw]


/-- Integer addition, subtraction, multiplication and exact quotient suffice
throughout the signed recursion on binary weight tables. -/
noncomputable def integerPlan (L : ℕ) :
    {H : SimpleGraph V} → Plan H → (WeightKey (2^L) → ℚ) → ℤ
  | _,.leaf H hh,w => integerLeaf L H hh w
  | _,.split H π _ kids,w =>
    let K := windowAt (Nat.card H.edgeSet)
    let q := windowExpansion K L
    let call (d : Branch) (a b : Option (Mask L)) :=
      integerPlan L (kids d) ((Round.mk H π a b).apply w)
    integerTrace K L H π w +
      (∑ i, q.coefficients i * call .left (some (q.masks i)) none) +
      (∑ j, q.coefficients j * call .right none (some (q.masks j))) -
      ∑ i, ∑ j, (q.coefficients i * q.coefficients j) *
        call .both (some (q.masks i)) (some (q.masks j))






end VWZClique.UniformFolds

end

/- NativeFoldTraversal -/
section

namespace VWZClique.NativeTraversal
open UniformFolds IntegerRAM IntegerRAM.Structured










noncomputable def childWeights {L : ℕ} (H : SimpleGraph V) (π : Equiv.Perm V) (c : Call L)
    (w : WeightKey (2^L) → ℚ) := (Round.mk H π c.a c.b).apply w










end VWZClique.NativeTraversal

end

/- NativeFoldProgram -/
section

namespace VWZClique.NativeTraversal
open UniformFolds IntegerRAM IntegerRAM.Structured
open WeightedProof

structure Charges where
  small : SimpleGraph V → ℕ
  projection : SimpleGraph V → ℕ
  push : SimpleGraph V → ℕ
  pop : ℕ
  reset : ℕ
  finish : ℕ







end VWZClique.NativeTraversal

end

/- NativeLeafCore -/
section

namespace VWZClique.IntegerRAM.NativeLeaf
open Structured
open Graph.Table (wordIndex)

structure Data where
  W : ℕ
  n : ℕ
  base : ℕ
  w : WeightKey n → ℤ
  pos : 0 < n
  guard : ∀ j : ℕ, j ≤ n → Fits W ((j:ℤ)-n)
  address : ∀ i : WeightKey n, Fits W ((base+wordIndex i : ℕ):ℤ)

structure Ready {I : Type} (p : Data) (r : I → ℤ) (x : I → Fin p.n) (m : Memory) : Prop where
  base : m (-1) = p.base
  dim : m (-2) = p.n
  one : m (-3) = 1
  vars : ∀ i, m (r i) = (x i).val
  table : ∀ i, m ((p.base+wordIndex i : ℕ):ℤ) = p.w i

def Frame (z : ℤ) (m o : Memory) := ∀ a, z<a → o a=m a

theorem Frame.trans {z : ℤ} {m o v : Memory} (a : Frame z m o) (b : Frame z o v) : Frame z m v :=
  fun k h => (b k h).trans (a k h)

theorem Frame.weaken {z z' : ℤ} {m o : Memory} (f : Frame z m o) (h : z ≤ z') : Frame z' m o :=
  fun k hk => f k (by omega)

theorem frameUpdate (m : Memory) (a z v : ℤ) (h : a≤z) : Frame z m (update m a v) := by
  intro k hk
  simp [update,show k≠a by omega]

theorem Ready.frame {I : Type} {p : Data} {r : I → ℤ} {x : I → Fin p.n} {m o : Memory}
    (h : Ready p r x m) {z : ℤ} (hz : z < -3) (hr : ∀ i, z < r i) (f : Frame z m o) :
    Ready p r x o :=
  ⟨(f _ (by omega)).trans h.base, (f _ (by omega)).trans h.dim, (f _ (by omega)).trans h.one,
    fun i => (f _ (hr i)).trans (h.vars i),fun i => (f _ (by have := Int.natCast_nonneg (p.base+wordIndex i); omega)).trans (h.table i)⟩

abbrev Sem (I : Type) := (p : Data) → (I → Fin p.n) → ℤ

/-- A fixed machine block for all input sizes. Its scratch cells lie at or below z. -/
def Builds {I : Type} (d : ℕ) (f : Sem I) : Prop :=
  ∀ (z : ℤ), z < -3 → ∀ (r : I → ℤ), (∀ i, z<r i) → ∃ (c : Command) (C : ℕ),
    ∀ (p : Data) (x : I → Fin p.n) (m : Memory), Ready p r x m →
      ∃ t o, Runs p.W c m t o ∧ t ≤ C*p.n^d ∧ o z=f p x ∧ Frame z m o

theorem mono {I : Type} {f : Sem I} {d e : ℕ} (h : Builds d f) (hle : d≤e) : Builds e f := by
  intro z hz r hr
  obtain ⟨c,C,H⟩ := h z hz r hr
  refine ⟨c,C,?_⟩
  intro p x m ready
  obtain ⟨t,o,run,cost,val,fr⟩ := H p x m ready
  exact ⟨t,o,run,cost.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right p.pos hle)),val,fr⟩

theorem fromReg {I : Type} (f : Sem I) (reg : (I → ℤ) → ℤ)
    (read : ∀ (p : Data) (r : I → ℤ) (x : I → Fin p.n) (m : Memory),
      Ready p r x m → m (reg r)=f p x) : Builds 0 f := by
  intro z hz r hr
  refine ⟨.atom (.mul z (reg r) (-3)),1,?_⟩
  intro p x m h
  refine ⟨1,_,.atom (.mul _ _ _ _),by simp,?_,frameUpdate _ _ _ _ le_rfl⟩
  simp [update,h.one,read p r x m h]

theorem one {I : Type} : Builds 0 (fun (_ : Data) (_ : I → _) => 1) :=
  fromReg _ (fun _ => -3) (fun _ _ _ _ h => h.one)

theorem dim {I : Type} : Builds 0 (fun (p : Data) (_ : I → _) => (p.n:ℤ)) :=
  fromReg _ (fun _ => -2) (fun _ _ _ _ h => h.dim)

theorem start {I : Type} : Builds 0 (fun (p : Data) (_ : I → _) => (p.base:ℤ)) :=
  fromReg _ (fun _ => -1) (fun _ _ _ _ h => h.base)

theorem coord {I : Type} (i : I) : Builds 0 (fun (_ : Data) (x : I → _) => ((x i).val:ℤ)) :=
  fromReg _ (fun r => r i) (fun _ _ _ _ h => h.vars i)

theorem zero {I : Type} : Builds 0 (fun (_ : Data) (_ : I → _) => 0) := by
  intro z hz r hr
  refine ⟨.atom (.sub z (-3) (-3)),1,?_⟩
  intro p x m h
  exact ⟨1,_,.atom (.sub _ _ _ _),by simp,by simp [update],frameUpdate _ _ _ _ le_rfl⟩

theorem binary {I : Type} {d : ℕ} {f g : Sem I} (hf : Builds d f) (hg : Builds d g)
    (op : ℤ → ℤ → ℤ) (ins : ℤ → ℤ → ℤ → Atom)
    (step : ∀ (W : ℕ) (m : Memory) (z a b : ℤ), Step W (ins z a b) m (update m z (op (m a) (m b)))) :
    Builds d (fun p x => op (f p x) (g p x)) := by
  intro z hz r hr
  obtain ⟨u,C,hu⟩ := hf z hz r hr
  obtain ⟨v,D,hv⟩ := hg (z-1) (by omega) r (fun i => lt_trans (by omega) (hr i))
  refine ⟨.seq u (.seq v (.atom (ins z z (z-1)))),C+D+1,?_⟩
  intro p x m ready
  obtain ⟨s,o,rr,sc,sv,sf⟩ := hu p x m ready
  obtain ⟨t,a,tt,tc,tv,tf⟩ := hv p x o (ready.frame hz hr sf)
  refine ⟨_,_,rr.seq (tt.seq (.atom (step _ _ _ _ _))),?_,?_,
    (sf.trans (tf.weaken (by omega))).trans (frameUpdate _ _ _ _ le_rfl)⟩
  · have hp : 1 ≤ p.n^d := Nat.one_le_pow _ _ p.pos
    rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]; omega
  · simp [update,tf z (by omega),sv,tv]

theorem plus {I : Type} {d : ℕ} {f g : Sem I} (hf : Builds d f) (hg : Builds d g) :
    Builds d (fun p x => f p x + g p x) := binary hf hg (·+·) .add (fun _ => Step.add)

theorem times {I : Type} {d : ℕ} {f g : Sem I} (hf : Builds d f) (hg : Builds d g) :
    Builds d (fun p x => f p x * g p x) := binary hf hg (·*·) .mul (fun _ => Step.mul)

theorem literal {I : Type} (k : ℕ) : Builds 0 (fun (_ : Data) (_ : I → _) => (k:ℤ)) := by
  induction k with
  | zero => simpa using (zero (I:=I))
  | succ k ih => simpa using (plus ih (one (I:=I)))

theorem readKey {I : Type} (key : (p : Data) → (I → Fin p.n) → WeightKey p.n)
    (hf : Builds 0 (fun p x => ((p.base+wordIndex (key p x):ℕ):ℤ))) :
    Builds 0 (fun p x => p.w (key p x)) := by
  intro z hz r hr
  obtain ⟨u,C,hu⟩ := hf z hz r hr
  refine ⟨.seq u (.atom (.load z z)),C+1,?_⟩
  intro p x m h
  obtain ⟨s,o,run,sc,sv,sf⟩ := hu p x m h
  have fits : Fits p.W (o z) := sv ▸ p.address (key p x)
  refine ⟨_,_,run.seq (.atom (.load _ _ _ fits)),by simpa using Nat.add_le_add_right sc 1,?_,
    sf.trans (frameUpdate _ _ _ _ le_rfl)⟩
  simp only [update,if_pos rfl,sv]
  exact (h.frame hz hr sf).table _

end VWZClique.IntegerRAM.NativeLeaf

end

/- NativeLeafSum -/
section

namespace VWZClique.IntegerRAM.NativeLeaf
open Structured

theorem rename {I J : Type} {f : Sem I} {d : ℕ} (h : Builds d f) (ι : I → J) :
    Builds d (fun p x => f p (x ∘ ι)) := by
  intro z hz r hr
  obtain ⟨c,C,H⟩ := h z hz (r ∘ ι) (fun i => hr (ι i))
  refine ⟨c,C,?_⟩
  intro p x m ready
  exact H p (x ∘ ι) m ⟨ready.base,ready.dim,ready.one,fun i => ready.vars (ι i),ready.table⟩

def bind {I α : Type} (a : α) (x : I → α) : Option I → α := fun i => i.elim a x

/-- Bind a single summation index using one fixed loop under the published native semantics. -/
theorem sumOne {I : Type} {d : ℕ} {f : Sem (Option I)} (body : Builds d f) :
    Builds (d+1) (fun p x => ∑ i : Fin p.n, f p (bind i x)) := by
  intro z hz r hr
  let ix := z-1
  let fl := z-2
  let tmp := z-3
  let rr : Option I → ℤ := bind ix r
  have ht : tmp < -3 := by dsimp [tmp]; omega
  have hrr : ∀ i, tmp < rr i := by
    intro i; cases i with
    | none => change z-3 < z-1; omega
    | some i => change z-3 < r i; have := hr i; omega
  obtain ⟨u,C,hu⟩ := body tmp ht rr hrr
  let step := Command.seq u (.atom (.add z z tmp))
  let init := Command.seq (.atom (.sub z (-3) (-3))) (.atom (.sub ix (-3) (-3)))
  refine ⟨.seq init (repeatN step ix (-3) (-2) fl), C+6,?_⟩
  intro p x m ready
  let g : ℕ → ℤ := fun j => if h : j < p.n then f p (bind ⟨j,h⟩ x) else 0
  let pref (q : ℕ) := ∑ j ∈ Finset.range q, g j
  let inv (q : ℕ) (s : Memory) := Ready p r x s ∧ s ix=(q:ℤ) ∧ s z=pref q ∧ Frame z m s
  let m₁ := update m z 0
  let m₂ := update m₁ ix 0
  have first : Runs p.W (.atom (.sub z (-3) (-3))) m 1 m₁ := by
    simpa [m₁] using Runs.atom (Step.sub (W:=p.W) m z (-3) (-3))
  have second : Runs p.W (.atom (.sub ix (-3) (-3))) m₁ 1 m₂ := by
    simpa [m₂] using Runs.atom (Step.sub (W:=p.W) m₁ ix (-3) (-3))
  have hxz : ix < z := by dsimp [ix]; omega
  have hfz : fl < z := by dsimp [fl]; omega
  have htx : tmp < ix := by dsimp [tmp,ix]; omega
  have htz : tmp < z := htx.trans hxz
  have hzi : z ≠ ix := ne_of_gt hxz
  have hif : ix ≠ fl := by dsimp [ix,fl]; omega
  have baseFrame : Frame z m m₂ := (frameUpdate _ _ _ _ le_rfl).trans (frameUpdate _ _ _ _ hxz.le)
  have initInv : inv 0 m₂ := ⟨ready.frame hz hr baseFrame,by simp [m₂,update],
    by simp [m₂,m₁,update,hzi,pref],baseFrame⟩
  have iteration (j : ℕ) (hj : j < p.n) (s : Memory) (hs : inv j s) :
      ∃ t : ℕ, t ≤ C*p.n^d+1 ∧ ∃ a : Memory, Runs p.W step s t a ∧
        a ix=j ∧ a (-3)=1 ∧ a (-2)=p.n ∧ inv (j+1) (nextMemory a ix fl j p.n) := by
    obtain ⟨sready,six,sz,sframe⟩ := hs
    let v : Fin p.n := ⟨j,hj⟩
    have sbody : Ready p rr (bind v x) s := by
      refine ⟨sready.base,sready.dim,sready.one,?_,sready.table⟩
      intro i; cases i with
      | none => exact six
      | some i => exact sready.vars i
    obtain ⟨t,b,run,cost,bv,bf⟩ := hu p (bind v x) s sbody
    let a := update b z (b z+b tmp)
    have frA : Frame z m a :=
      (sframe.trans (bf.weaken htz.le)).trans (frameUpdate _ _ _ _ le_rfl)
    have ra := ready.frame hz hr frA
    have aix : a ix=j := by simp [a,update,ne_of_lt hxz,bf ix htx,six]
    have suma : a z=pref (j+1) := by simp [a,update,bf z htz,sz,bv,pref,Finset.sum_range_succ,g,hj,v]
    have frB : Frame z m (nextMemory a ix fl j p.n) :=
      (frA.trans (frameUpdate _ _ _ _ hxz.le)).trans (frameUpdate _ _ _ _ hfz.le)
    refine ⟨t+1,Nat.add_le_add_right cost 1,a,run.seq (.atom (.add _ _ _ _)),aix,ra.one,ra.dim,
      ready.frame hz hr frB,?_,?_,frB⟩
    · simp [nextMemory,update,hif]
    · simpa [nextMemory,update,hzi,ne_of_gt hfz] using suma
  obtain ⟨cost,cb,o,run,oval⟩ := repeatN_runs (B:=C*p.n^d+1) p.pos step
    (show (-2:ℤ) ≠ ix by dsimp [ix]; omega) inv p.guard iteration initInv
  have final : pref p.n = ∑ i : Fin p.n, f p (bind i x) := by
    change (∑ j ∈ Finset.range p.n, g j) = _
    rw [← Fin.sum_univ_eq_sum_range g]
    simp [g]
  refine ⟨_,o,(first.seq second).seq run,?_,oval.2.2.1.trans final,oval.2.2.2⟩
  have hp : 1 ≤ p.n^d := Nat.one_le_pow _ _ p.pos
  have scale : p.n ≤ p.n^d * p.n := by simpa using Nat.mul_le_mul_right p.n hp
  have pos := p.pos
  rw [pow_succ]
  calc
    _ ≤ 2 + p.n*(C*p.n^d+1+3) := Nat.add_le_add_left cb _
    _ ≤ (C+6)*(p.n^d*p.n) := by nlinarith

end VWZClique.IntegerRAM.NativeLeaf

end

/- NativeLeafBind -/
section

namespace VWZClique.IntegerRAM.NativeLeaf

theorem extBuild {I : Type} {d : ℕ} {f g : Sem I} (h : Builds d f)
    (eqn : ∀ p x, f p x = g p x) : Builds d g :=
  (show f=g from funext fun p => funext (eqn p)) ▸ h

def route {I : Type} (l : ℕ) : I ⊕ Fin (l+1) → Option I ⊕ Fin l :=
  Sum.elim (fun i => .inl (some i)) (Fin.cases (.inl none) Sum.inr)

theorem sumFin {d : ℕ} (l : ℕ) {I : Type} {f : Sem (I ⊕ Fin l)} (h : Builds d f) :
    Builds (d+l) (fun p x => ∑ y : Fin l → Fin p.n, f p (Sum.elim x y)) := by
  induction l generalizing I with
  | zero =>
    let e : I ⊕ Fin 0 → I := Sum.elim id Fin.elim0
    apply extBuild (rename h e)
    intro p x
    rw [Fintype.sum_unique]
    congr 1
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact i.elim0
  | succ l ih =>
    have sub := ih (rename h (route (I:=I) l))
    apply extBuild (sumOne sub)
    intro p x
    let F (y : Fin (l+1) → Fin p.n) := f p (Sum.elim x y)
    let e := Fin.consEquiv (fun _ : Fin (l+1) => Fin p.n)
    change _ = ∑ y, F y
    rw [← e.sum_comp F, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply congrArg (f p)
    funext i
    cases i with
    | inl i => rfl
    | inr i =>
      exact Fin.cases (motive:=fun i => ((Sum.elim (bind a x) b) ∘ route l) (.inr i) = Sum.elim x (e (a,b)) (.inr i))
        rfl (fun _ => rfl) i

theorem sumVars {I J : Type} [Fintype J] [DecidableEq J] {d : ℕ} {f : Sem (I ⊕ J)} (h : Builds d f) :
    Builds (d+Fintype.card J) (fun p x => ∑ y : J → Fin p.n, f p (Sum.elim x y)) := by
  classical
  let e := Fintype.equivFin J
  let up : I ⊕ J → I ⊕ Fin (Fintype.card J) := Sum.map id e
  apply extBuild (sumFin _ (rename h up))
  intro p x
  let E := e.symm.arrowCongr (Equiv.refl (Fin p.n))
  rw [← E.sum_comp (fun y => f p (Sum.elim x y))]
  apply Finset.sum_congr rfl
  intro y _
  apply congrArg (f p)
  funext i
  cases i <;> rfl

theorem product {I J : Type} {d : ℕ} (s : Finset J) (f : J → Sem I)
    (h : ∀ j ∈ s, Builds d (f j)) : Builds d (fun p x => ∏ j ∈ s, f j p x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using mono (one (I:=I)) (Nat.zero_le d)
  | @insert j s hj ih =>
    have g := times (h j (by simp)) (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))
    simpa [Finset.prod_insert,hj] using g

end VWZClique.IntegerRAM.NativeLeaf

end

/- NativeLeaf -/
section

namespace VWZClique.IntegerRAM.NativeLeaf
open SparseProof
open Graph.Table (wordIndex)

abbrev Label (I : Type) := (p : Data) → (I → Fin p.n) → Fin p.n

theorem unary {I : Type} (i : V) (a : Label I) (ha : Builds 0 (fun p x => ((a p x).val:ℤ))) :
    Builds 0 (fun p x => p.w (.inl (i,a p x))) := by
  apply readKey (fun p x => .inl (i,a p x))
  simpa only [wordIndex,Nat.cast_add,Nat.cast_mul] using
    plus (start (I:=I)) (plus (times (literal i.val) dim) ha)

theorem edge {I : Type} (i j : V) (a b : Label I)
    (ha : Builds 0 (fun p x => ((a p x).val:ℤ))) (hb : Builds 0 (fun p x => ((b p x).val:ℤ))) :
    Builds 0 (fun p x => p.w (.inr (i,j,a p x,b p x))) := by
  apply readKey (fun p x => .inr (i,j,a p x,b p x))
  simpa only [wordIndex,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
    plus (start (I:=I)) (plus (plus (plus (times (literal 9) dim)
      (times (literal (i.val*9+j.val)) (times dim dim))) (times ha dim)) hb)

abbrev Inner (key : V → Bucket) (b : Bag) := Fiber key none ⊕ Fiber key (some b)

def label (key : V → Bucket) (b : Bag) (i : V) : Label (Inner key b) := fun p x =>
  localAssignment key ⟨0,p.pos⟩ (fun u => x (.inl u)) b (fun u => x (.inr u)) i

theorem label_build (key : V → Bucket) (b : Bag) (i : V) :
    Builds 0 (fun p x => ((label key b i p x).val:ℤ)) := by
  by_cases hc : key i = none
  · simpa [label,localAssignment,hc] using (coord (I:=Inner key b) (.inl ⟨i,hc⟩))
  by_cases hb : key i = some b
  · simpa [label,localAssignment,hc,hb] using (coord (I:=Inner key b) (.inr ⟨i,hb⟩))
  · simpa [label,localAssignment,hc,hb] using (zero (I:=Inner key b))

open Classical in
noncomputable def rawFactor (H : SimpleGraph V) (key : V → Bucket) (b : Bag) : Token → Sem (Inner key b)
  | .inl i => fun p x => p.w (.inl (i,label key b i p x))
  | .inr (i,j) => if i<j ∧ H.Adj i j then
      fun p x => p.w (.inr (i,j,label key b i p x,label key b j p x)) else fun _ _ => 1

theorem factor_build (H : SimpleGraph V) (key : V → Bucket) (b : Bag) (t : Token) :
    Builds 0 (rawFactor H key b t) := by
  classical
  cases t with
  | inl i => exact unary _ _ (label_build _ _ _)
  | inr ij =>
    rcases ij with ⟨i,j⟩
    by_cases h : i<j ∧ H.Adj i j
    · simpa [rawFactor,h] using edge i j _ _ (label_build key b i) (label_build key b j)
    · simpa [rawFactor,h] using (one (I:=Inner key b))

noncomputable def bagProduct (H : SimpleGraph V) (key : V → Bucket) (b : Bag) : Sem (Inner key b) :=
  fun p x => ∏ t ∈ Finset.univ.filter (fun t => owner key t = b), rawFactor H key b t p x

noncomputable def bagSum (H : SimpleGraph V) (key : V → Bucket) (b : Bag) : Sem (Fiber key none) :=
  fun p z => ∑ y : Assignment key p.n (some b), bagProduct H key b p (Sum.elim z y)

noncomputable def rawLeaf (H : SimpleGraph V) (key : V → Bucket) (p : Data) :=
  ∑ z : Assignment key p.n none, ∏ b : Bag, bagSum H key b p z

theorem raw_build (H : SimpleGraph V) (key : V → Bucket)
    (hroot : Fintype.card (Fiber key none) ≤ 3)
    (hbag : ∀ b, Fintype.card (Fiber key (some b)) ≤ 2) :
    Builds 5 (fun (p : Data) (_ : Empty → _) => rawLeaf H key p) := by
  classical
  have localB (b : Bag) : Builds 0 (bagProduct H key b) :=
    product _ _ (fun t _ => factor_build H key b t)
  have smallB (b : Bag) : Builds 2 (bagSum H key b) :=
    mono (sumVars (localB b)) (by simpa using hbag b)
  have pieces := product Finset.univ (fun b => bagSum H key b) (fun b _ => smallB b)
  have closed := sumVars (rename pieces (Sum.inr : Fiber key none → Empty ⊕ Fiber key none))
  apply (mono (f:=fun (p:Data) (_ : Empty → _) => rawLeaf H key p) _ (by omega : 2+Fintype.card (Fiber key none)≤5))
  exact closed

theorem raw_cast (H : SimpleGraph V) (key : V → Bucket) (b : Bag) (t : Token)
    (p : Data) (z : Assignment key p.n none) (y : Assignment key p.n (some b)) :
    (rawFactor H key b t p (Sum.elim z y):ℚ) =
      factor H (fun a => (p.w a:ℚ)) (localAssignment key ⟨0,p.pos⟩ z b y) t := by
  classical
  cases t with
  | inl i => rfl
  | inr ij =>
    rcases ij with ⟨i,j⟩
    by_cases h : i<j ∧ H.Adj i j <;> simp [rawFactor,factor,h,label]

theorem raw_correct (H : SimpleGraph V) (key : V → Bucket)
    (hedge : ∀ i j, H.Adj i j → key i=none ∨ key j=none ∨ key i=key j) (p : Data) :
    (rawLeaf H key p:ℚ) = weightedSum H (fun i => (p.w i:ℚ)) := by
  classical
  rw [factorization H key hedge ⟨0,p.pos⟩]
  simp only [rawLeaf,bagSum,bagProduct,piece,Int.cast_sum,Int.cast_prod,raw_cast]

/-- One command per fixed wedge-free pattern evaluates any table in the contiguous
layout, with a dimension-independent constant times n^5 instructions. It preserves
all addresses above the return register, including its input and caller registers. -/
theorem sparse_native (H : SimpleGraph V) (hw : ¬ ∃ f g : Fin 3 → V,
    wedge H f ∧ wedge H g ∧ ∀ i j, f i ≠ g j) (dst : ℤ) (hdst : dst < -3) :
    ∃ (c : Structured.Command) (C : ℕ), ∀ (p : Data) (m : Memory),
      Ready p (Empty.elim : Empty → ℤ) (Empty.elim : Empty → Fin p.n) m →
      ∃ t o, Structured.Runs p.W c m t o ∧ t≤C*p.n^5 ∧
        (o dst:ℚ)=weightedSum H (fun i => (p.w i:ℚ)) ∧ Frame dst m o := by
  obtain ⟨key,hroot,hbags,edges⟩ := matching_partition H hw
  obtain ⟨c,C,run⟩ := raw_build H key hroot hbags dst hdst Empty.elim (fun i => i.elim)
  refine ⟨c,C,?_⟩
  intro p m hm
  obtain ⟨t,o,rr,cc,rv,fr⟩ := run p Empty.elim m hm
  exact ⟨t,o,rr,cc,(congrArg (Int.cast : ℤ → ℚ) rv).trans (raw_correct H key edges p),fr⟩

end VWZClique.IntegerRAM.NativeLeaf

end

/- NativeLeafWord -/
section

namespace VWZClique.IntegerRAM.NativeLeaf
open Graph.Table (wordIndex)
open Structured UniformFolds TrulySubcubicAPSP

theorem index_lt {n : ℕ} (i : WeightKey n) : wordIndex i < 9*n+81*(n*n) := by
  rcases i with ⟨j,x⟩|⟨i,j,x,y⟩
  · have a := Nat.mul_le_mul_right n j.isLt
    rw [Nat.succ_mul] at a
    have := x.isLt
    change j.val*n+x.val < _
    omega
  · have ix : i.val*9+j.val<81 := by have := i.isLt; have := j.isLt; omega
    have a := Nat.mul_le_mul_right (n*n) ix
    have b := Nat.mul_le_mul_right n x.isLt
    rw [Nat.succ_mul] at a b
    have := y.isLt
    change 9*n+(i.val*9+j.val)*(n*n)+x.val*n+y.val < _
    omega

def inputData {W n base M : ℕ} (hn : 0<n) (cap : Graph.Division.Room W M)
    (room : base+9*n+81*(n*n)≤M) (w : WeightKey n → ℤ) : Data where
  W := W
  n := n
  base := base
  w := w
  pos := hn
  guard := by
    intro j hj
    apply cap.fits <;> omega
  address := by
    intro i
    have := index_lt i
    apply cap.fits <;> omega


end VWZClique.IntegerRAM.NativeLeaf

end

/- NativeFrameStack -/
section

namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal



theorem StackLayout.transferAll (lay : StackLayout) (d : ℕ) (H : SimpleGraph V) (m o : Memory)
    (fr : ∀ a : ℕ, 297≤a → o a=m a) : lay.prepared d H m → lay.prepared d H o :=
  lay.transfer d H m o (fun a ha _ => fr a (le_trans (by decide : 297≤512) ((lay.large d).trans ha)))







theorem Globals.transfer {L lay} {m o : Memory} (h : Globals L lay m)
    (dim : o 0=m 0) (len : o 320=m 320) (out : o 321=m 321) : Globals L lay o :=
  ⟨dim.trans h.dim,len.trans h.length,out.trans h.output⟩


theorem weights_transfer {L : ℕ} {lay : StackLayout} {d w} {m o : Memory} (h : @Weights L lay d w m)
    (ptr : o (reg d .weights)=m (reg d .weights)) (fr : ∀ a : ℕ, 297≤a → o a=m a) :
    Weights lay d w o :=
  ⟨ptr.trans h.1,fun a => (congrArg (Int.cast : ℤ → ℚ)
    (fr (lay.base d+Graph.Table.wordIndex a) (le_trans (by decide : 297≤512) (le_trans (lay.large d) (Nat.le_add_right _ _))))).trans (h.2 a)⟩

theorem saved_transfer {L} (lay : StackLayout) (d : ℕ) (s : List (NativeTraversal.Slot L)) {m o : Memory}
    (plane : ∀ a : ℕ, 297≤a → o a=m a) (regs : ∀ i<d, ∀ f, o (reg i f)=m (reg i f))
    (pre : Saved lay d s m) : Saved lay d s o := by
  induction s generalizing d with
  | nil => trivial
  | cons h t ih =>
    obtain ⟨lt,vd,arm,tail⟩ := pre
    refine ⟨lt,?_,?_,ih _ (fun j hj f => regs j (hj.trans lt) f) tail⟩
    · cases h with
      | input n w => exact weights_transfer vd (regs n lt _) plane
      | value n z => exact (regs n lt _).trans vd
      | cursor n H π b w i z =>
        obtain ⟨a,c,l,ix,v⟩ := vd
        exact ⟨weights_transfer a (regs n lt _) plane,lay.transferAll _ _ _ _ plane c,
          fun j => (regs n lt _).trans (l j),(regs n lt _).trans ix,(regs n lt _).trans v⟩
    · cases h with
      | input => exact False.elim arm
      | value => exact False.elim arm
      | cursor n H π b w i z =>
        obtain ⟨hi,hc⟩ := arm
        exact ⟨hi,(regs n lt _).trans hc⟩








theorem distinctData {a d : ℕ} (ha : 297 ≤ a) (hd : d ≤ 36) (f : Field) : (a:ℤ)≠reg d f := by
  have := reg_below hd f; omega







end VWZClique.IntegerRAM.NativeFrame

end

/- CliqueIntegerPlan -/
section

/-! Apply the integer recursion to the original graph at every input size. -/

namespace VWZClique.BlockReduction
open UniformFolds WeightedProof OAI.MatrixMultiplication.Arithmetic

def graphLength (n k : ℕ) := Nat.clog 2 (n^((k+8)/9))

/-- Put the grouped weights in the next dyadic domain, zeroing the added entries. -/
noncomputable def graphWeights {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) (k : ℕ)
    (i : WeightKey (2^graphLength n k)) : ℚ :=
  literal (weights (F := ℚ) (t := (k+8)/9) G k ⟨0,hn⟩) (padTag i)




end VWZClique.BlockReduction

end

/- NativeSquareExpr -/
section

namespace VWZClique.IntegerRAM.SquareCode
open Structured

/-- Straight-line formulas for one kernel write, with address arithmetic and
indirect loads. Registers and heap cells above the scratch area are readable. -/
inductive Expr where
  | zero | one | reg (i : ℤ) | read (a : Expr)
  | add (a b : Expr) | sub (a b : Expr) | mul (a b : Expr)
deriving Inhabited




def binary (a b : Command) (op : Atom) := Command.seq a (.seq b (.atom op))

def Expr.code (d : ℤ) : Expr → Command
  | .zero => .atom (.sub d d d)
  | .one => .atom (.one d)
  | .reg i => .seq (.atom (.sub d d d)) (.atom (.add d d i))
  | .read a => .seq (a.code d) (.atom (.load d d))
  | .add a b => binary (a.code d) (b.code (d-1)) (.add d d (d-1))
  | .sub a b => binary (a.code d) (b.code (d-1)) (.sub d d (d-1))
  | .mul a b => binary (a.code d) (b.code (d-1)) (.mul d d (d-1))

def Expr.steps : Expr → ℕ
  | .zero | .one => 1
  | .reg _ => 2
  | .read a => a.steps+1
  | .add a b | .sub a b | .mul a b => a.steps+(b.steps+1)




def Expr.num : ℕ → Expr
  | 0 => .zero
  | n+1 => .add (num n) .one

def Expr.int : ℤ → Expr
  | .ofNat n => num n
  | .negSucc n => .sub .zero (num (n+1))





/-- Compute the destination and value independently then store one word.
The negative scratch segment may be overwritten. -/
def write (d : ℤ) (addr value : Expr) : Command :=
  .seq (addr.code d) (.seq (value.code (d-1)) (.atom (.store d (d-1))))


end VWZClique.IntegerRAM.SquareCode

end

/- NativeSquareRegs -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout

/-- Read the data registers for one (parent, child-row, child-column) kernel.
All compiled formulas use scratch at or below register -128. -/
def base := Expr.reg (-1)
def nodes := Expr.reg (-2)
def side := Expr.reg (-3)
def node := Expr.reg (-4)
def row := Expr.reg (-5)
def col := Expr.reg (-6)
def floor : ℤ := -128

def num := Expr.num
def plus := Expr.add
def times := Expr.mul

end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareControl -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

/-- Assign a register using the expression scratch segment. -/
def assign (reg : ℤ) (e : Expr) := Command.seq (e.code floor)
  (.seq (.atom (.sub reg reg reg)) (.atom (.add reg reg floor)))


def divOne : ℤ := -10
def divK : ℤ := -11
def divQ : ℤ := -12
def divTest : ℤ := -13

def quotientBody (num : ℤ) := Command.seq (.atom (.sub num num divK))
  (.seq (.atom (.add divQ divQ divOne)) (.atom (.sub divTest divTest divTest)))

-- A negative remainder is the loop guard, so an exact positive multiple
-- performs precisely q subtraction rounds.
def quotientIter (num : ℤ) := Command.seq (quotientBody num) (.atom (.sub divTest divTest num))


def quotientCmd (d : ℕ) (num : ℤ) := Command.seq (assign divK (Expr.num d))
  (.seq (.atom (.one divOne))
  (.seq (.atom (.sub divQ divQ divQ))
  (.seq (.repeatWhileNegative (quotientIter num) divTest)
    (assign num (.reg divQ)))))


end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeDyadicWrite -/
section

namespace VWZClique.IntegerRAM.DyadicCell
open Graph Structured SquareCode

def space (N : ℕ) := 9*N+81*(N*N)
def origin (n₀ : ℕ) := 1+n₀*n₀
def target (n₀ N : ℕ) := origin n₀+space N





end VWZClique.IntegerRAM.DyadicCell

end

/- NativeSquareGrid -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured



def loop (i lim : ℤ) (body : Command) := Command.seq (.atom (.one (-7))) <|
  .seq (.atom (.sub i i i)) (repeatN body i (-7) lim (-8))


/-- Parent, row and column are generated by three nested loops, with no
division or remainder operations for unpacking a linear address. -/
def grid (body : Command) := loop (-4) (-2) (loop (-5) (-3) (loop (-6) (-3) body))

def gridCost (N side B : ℕ) := 2+N*((2+side*((2+side*(B+3))+3))+3)



end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeDyadicGraph -/
section

namespace VWZClique.IntegerRAM.DyadicCell
open Structured Graph BlockReduction


theorem header_floor {n : ℕ} (hn : 32≤n) (N : ℕ) : 512≤target n N := by
  have := Nat.mul_le_mul hn hn
  unfold target origin; omega

end VWZClique.IntegerRAM.DyadicCell

end

/- NativeArenaLayout -/
section

namespace VWZClique.IntegerRAM.NativeArena
open NativeFrame NativeTraversal UniformFolds BlockReduction MaskScan.Arena




noncomputable def forGraph (n k : ℕ) (hn : 32≤n) : StackLayout :=
  layout (graphLength n k) (DyadicCell.target n (n^((k+8)/9))) (DyadicCell.origin n) (DyadicCell.header_floor hn _)

end VWZClique.IntegerRAM.NativeArena

end

/- NativeProjectionArena -/
section

namespace VWZClique.IntegerRAM.Projected
open Structured UniformFolds NativeFrame NativeTraversal NativeArena

/-- The live prefix at the instant the projection starts. Temporary pointer
words and compact-table storage above the parent weights may be overwritten. -/
def projectionPrefix (base n j : ℕ) :=
  j<297 ∨ j=320 ∨ j=321 ∨ 512≤j ∧ j < metaBase base n


end VWZClique.IntegerRAM.Projected

end

/- NativeProjectionSetup -/
section

namespace VWZClique.IntegerRAM.Projected.Setup
open Structured SquareCode SquareCode.Layout









def readWord (i : ℕ) := Expr.read (.num i)


end VWZClique.IntegerRAM.Projected.Setup

end

/- NativeProjectionHeaders -/
section

namespace VWZClique.IntegerRAM.Projected.Headers
open Structured SquareCode SquareCode.Layout

/-- All per-call constants come from fixed positive header slots. A header
expression never depends on negative registers clobbered by an earlier call. -/
inductive Value where
  | nat (v : ℕ)
  | word (src : ℕ)
  | add (a b : Value)
  | mul (a b : Value)
  deriving DecidableEq

def Value.expr : Value → Expr
  | .nat v => .num v
  | .word k => Setup.readWord k
  | .add a b => .add a.expr b.expr
  | .mul a b => .mul a.expr b.expr





abbrev Fields := List (ℤ × Value)

def command : Fields → Command
  | [] => .skip
  | a::xs => .seq (command xs) (assign a.1 a.2.expr)

def time : Fields → ℕ
  | [] => 0
  | a::xs => time xs+(a.2.expr.steps+2)







end VWZClique.IntegerRAM.Projected.Headers

end

/- NativeProjectionTiles -/
section

namespace VWZClique.IntegerRAM.Projected

abbrev Tile (s : ℕ) := Matrix (Fin s) (Fin s) ℤ








end VWZClique.IntegerRAM.Projected

end

/- NativeProjectionWorkspace -/
section

namespace VWZClique.IntegerRAM.Projected.Workspace

/-- Retained labels and recursive mask data end at `start`; all projector
writes lie in this suffix. A level uses two packed arrays of length 8^h. -/
def level (start : ℕ) : ℕ → ℕ
  | 0 => start
  | h+1 => level start h+2*8^h



structure Banks where
  support : ℕ
  left : ℕ
  middle : ℕ
  right : ℕ
  transform : ℕ
  weights : ℕ
  packetsLeft : ℕ
  packetsRight : ℕ
  output : ℕ

/-- Four dense tables and three padded tile banks each reserve at most N^6
words. Small products can reuse the three tile banks before packing begins. -/
def banks (start n : ℕ) : Banks :=
  let lb := start+4*n^3
  let step := n^6
  ⟨start,lb,lb+step,lb+2*step,lb+3*step,lb+4*step,lb+5*step,lb+6*step,lb+7*step⟩




end VWZClique.IntegerRAM.Projected.Workspace

end

/- NativeProjectionInit -/
section

namespace VWZClique.IntegerRAM.Projected.Init
open Structured Headers NativeFrame MaskScan RankSwap UniformFolds

def n : Value := .word 0
def mul (k : ℕ) (a : Value) : Value := .mul (.nat k) a
def sq : Value := .mul n n
def cube : Value := .mul sq n
def sixth : Value := .mul cube cube
def parent (d : ℕ) : Value := .word (8+8*d)
def orig (d : ℕ) : Value := .add (.add (parent d) (mul 9 n)) (mul 81 sq)
def slot (d i : ℕ) : Value := .add (orig d) (mul i cube)
def start (d : ℕ) : Value := .add (slot d 7) (.nat 2)
def dense (d i : ℕ) : Value := .add (.add (start d) (mul 4 cube)) (mul i sixth)

def fields (d : ℕ) : Fields := [(350,parent d),(356,dense d 4),(358,slot d 5),(370,slot d 6),
  (371,dense d 0),(372,dense d 1),(373,dense d 2),(374,dense d 3),
  (375,dense d 4),(376,dense d 5),(377,dense d 6),(378,dense d 7),(379,start d),
  (380,.add (slot d 7) (.nat 1))]

def countExpr := SquareCode.Expr.read (.reg 380)
def command (d : ℕ) := Command.seq (Headers.command (fields d)) (SquareCode.Layout.assign 359 countExpr)

structure Params (base n count : ℕ) (m : Memory) : Prop where
  weights : m 350=base
  codeBase : m 358=Arena.slot base n 5
  size : m 359=count
  coefficients : m 370=Arena.slot base n 6
  start : m 379 = (Arena.slot base n 7+2:ℕ)
  source : m 371=(Workspace.banks (Arena.slot base n 7+2) n).left
  middle : m 372=(Workspace.banks (Arena.slot base n 7+2) n).middle
  right : m 373=(Workspace.banks (Arena.slot base n 7+2) n).right
  raw : m 374=(Workspace.banks (Arena.slot base n 7+2) n).transform
  smallWork : m 356=(Workspace.banks (Arena.slot base n 7+2) n).weights
  wt : m 375=(Workspace.banks (Arena.slot base n 7+2) n).weights
  leftPack : m 376=(Workspace.banks (Arena.slot base n 7+2) n).packetsLeft
  rightPack : m 377=(Workspace.banks (Arena.slot base n 7+2) n).packetsRight
  product : m 378=(Workspace.banks (Arena.slot base n 7+2) n).output


end VWZClique.IntegerRAM.Projected.Init

end

/- ProjectionFactors -/
section

open OAI.MatrixMultiplication.Arithmetic
namespace VWZClique.Projection

/-- On the support of a basis vector the first string fixes the second. -/
def partner {L : ℕ} (j : BasisLabel L) (s : Bits L) : Bits L :=
  fun i => if j i = 0 then false else if j i = 1 then true else !(s i)






inductive Source where
  | pivot (second : Bool)
  | center
  | other (i : Fin 3)

def nearSource (i : Fin 3) : Source :=
  if i = 0 then .pivot false else if i = 1 then .pivot true else .center

def source (rev : Bool) : Slot → Source
  | .inl i => if rev then .other i else nearSource i
  | .inr i => if rev then nearSource i else .other i




inductive Group where
  | pivotCenter
  | pivotOther
  | centerOther
  deriving DecidableEq

/-- An ordered pair of positions can depend on at most two of the three inputs. -/
def group : Source → Source → Group
  | .other _, .pivot _ | .pivot _, .other _ => .pivotOther
  | .other _, _ | _, .other _ => .centerOther
  | _, _ => .pivotCenter




abbrev Factor := Slot ⊕ Slot × Slot

def factorGroup (rev : Bool) : Factor → Group
  | .inl i => group (source rev i) (source rev i)
  | .inr (i,k) => group (source rev i) (source rev k)















end VWZClique.Projection

end

/- NativeProjectionFactors -/
section

namespace VWZClique.IntegerRAM.Projected.Factors
open Projection UniformFolds WeightedProof FoldProof SquareCode

/-! The pattern, wedge placement, channel and factor group are compile-time
parameters on each of the fixed plan's branches. All word sizes, vertex labels,
table addresses and assignment-domain lengths are runtime data. -/

abbrev sideReg : ℤ := -60
abbrev baseReg : ℤ := -61


def src (args : Source → Expr) (rev : Bool) (s : Slot) := args (source rev s)

def keyU (i : V) (x : Expr) : Expr :=
  .read (.add (.reg baseReg) (.add (.mul (.num i.val) (.reg sideReg)) x))

def keyE (i j : V) (x y : Expr) : Expr :=
  let n := Expr.reg sideReg
  let off := Expr.add (.mul (.num 9) n) (.mul (.num (i.val*9+j.val)) (.mul n n))
  .read (.add (.reg baseReg) (.add off (.add (.mul x n) y)))

def entry (args : Source → Expr) (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3) : Factor → Expr
  | .inl (.inl i) => keyU (π (site h i)) (src args rev (.inl i))
  | .inl (.inr _) => .one
  | .inr (a,b) =>
    let i := π (endpoint h a)
    let j := π (endpoint h b)
    if (h,a,b) ∈ E then
      if i < j then keyE i j (src args rev a) (src args rev b) else keyE j i (src args rev b) (src args rev a)
    else .one





def prodExpr (xs : List Expr) : Expr := xs.foldr Expr.mul .one


/-- These 42 flags and the shape of the straight-line code are independent of n and L. -/
noncomputable def component (args : Source → Expr) (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool)
    (h : Fin 3) (g : Group) : Expr :=
  prodExpr ((Finset.univ : Finset Factor).toList.map
    fun f => if factorGroup rev f=g then entry args π E rev h f else .one)









end VWZClique.IntegerRAM.Projected.Factors

end

/- NativeProjectionSlices -/
section

namespace VWZClique.IntegerRAM.Projected.Slices

open Projection UniformFolds TraceDyadic
variable {L : ℕ}











/-- A zero eigenbasis row need not store its partner. The two probe
transforms return packed vertex zero on those rows. -/
def lookupPartner (j : BasisLabel L) (x : Bits L) : Bits L :=
  if basisInt j (x,partner j x)=0 then (wordIndex L).symm 0 else partner j x







end VWZClique.IntegerRAM.Projected.Slices

end

/- WordButterflyTransform -/
section

/-! A uniform native program for all bit lengths. A stage moves the leading raw
    digit to a transformed trailing digit. After all stages the trailing labels
    are in their original order. -/

namespace VWZClique.IntegerRAM.Butterfly
open Structured TrulySubcubicAPSP













def swapBuffers : List Atom := [
  .one Reg.one, .sub Reg.zero Reg.one Reg.one,
  .add Reg.swap Reg.srcBase Reg.zero, .add Reg.srcBase Reg.dstBase Reg.zero,
  .add Reg.dstBase Reg.swap Reg.zero, .add Reg.stages Reg.stages Reg.one]

def iteration : Command := .seq stage (line swapBuffers)
def allStages : Command := .repeatWhileNegative iteration Reg.stages

def butterflySetupAtoms : List Atom := [.one Reg.one,.sub Reg.zero Reg.one Reg.one,
  .sub Reg.swap Reg.stages Reg.one,.sub Reg.stages Reg.zero Reg.stages]

def full : Command := .seq (line butterflySetupAtoms) (.whenNonnegative Reg.swap allStages)












end VWZClique.IntegerRAM.Butterfly

end

/- WordButterflyLayout -/
section

/-! Explicit reversible indexing of all input pairs and output labels. -/

namespace VWZClique.IntegerRAM.Butterfly
open Structured TrulySubcubicAPSP

def splitLabel (l : ℕ) : BasisLabel (l+1) ≃ Fin 4 × BasisLabel l where
  toFun j := (j 0,fun i => j i.succ)
  invFun t := Fin.cons t.1 t.2
  left_inv := by
    intro j
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv := by intro j; simp

/-- The successive base-four digits give a computable bijection with the contiguous
    cells from zero up to the table size. -/
def labelIndex : (l : ℕ) → BasisLabel l ≃ Fin (4^l)
  | 0 => {
      toFun := fun _ => ⟨0,by decide⟩
      invFun := fun _ => Fin.elim0
      left_inv := by intro j; funext i; exact i.elim0
      right_inv := by intro i; apply Fin.ext; have h := i.isLt; simp at h; omega }
  | n+1 => (splitLabel n).trans (((Equiv.refl (Fin 4)).prodCongr (labelIndex n)).trans
      (finProdFinEquiv.trans (finCongr (by rw [pow_succ,mul_comm]))))











end VWZClique.IntegerRAM.Butterfly

end

/- NativeProjectionSupportDP -/
section

namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured Projection UniformFolds TraceDyadic SquareCode

/-- Prefixing a basis digit and a first-vertex bit determines the corresponding
partner prefix and the one-bit factor in the sign. -/
def localPartner (d : Fin 4) (b : Bool) := if d=0 then false else if d=1 then true else !b
def coeff (d : Fin 4) (b : Bool) : ℤ := (oneBit d b (localPartner d b)).num
def bit (b : Bool) : ℕ := if b then 1 else 0




def sign {L : ℕ} (j : BasisLabel L) (x : Bits L) := basisInt j (x,partner j x)
def index {L : ℕ} (j : BasisLabel L) (x : Bits L) : ℤ := (wordIndex L (Slices.lookupPartner j x)).val



abbrev inSign : ℤ := -80
abbrev inIndex : ℤ := -81
abbrev outSign : ℤ := -82
abbrev outIndex : ℤ := -83

def n := Expr.reg (-3)
def vertex := Expr.reg (-4)
def label := Expr.add (.mul (.reg (-5)) n) (.reg (-6))
def plane := Expr.mul n n
def src (base : ℤ) := Expr.add (.reg base) (.add (.mul vertex plane) label)
def dst (d : Fin 4) (b : Bool) (base : ℤ) := Expr.add (.reg base) <|
  .add (.mul (.add (.mul (.num (bit b)) n) vertex) (.mul (.num 4) plane))
    (.add (.mul (.num d.val) plane) label)
def signValue (d : Fin 4) (b : Bool) := Expr.mul (.int (coeff d b)) (.read (src inSign))
def indexValue (d : Fin 4) (b : Bool) := Expr.mul (.mul (signValue d b) (signValue d b))
  (.add (.mul (.num (bit (localPartner d b))) n) (.read (src inIndex)))

def cell (d : Fin 4) (b wantIndex : Bool) := write Layout.floor
  (dst d b (if wantIndex then outIndex else outSign)) (if wantIndex then indexValue d b else signValue d b)

def cellCost (d : Fin 4) (b wantIndex : Bool) :=
  (dst d b (if wantIndex then outIndex else outSign)).steps+((if wantIndex then indexValue d b else signValue d b).steps+1)





end VWZClique.IntegerRAM.Projected.SupportDP

end

/- NativeProjectionSupportStage -/
section

namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured SquareCode.Layout

abbrev Tag := Fin 4 × Bool × Bool


def tags : List Tag := (List.finRange 4).flatMap fun d => [ (d,false,false),(d,false,true),(d,true,false),(d,true,true) ]







def commands : List Tag → Command
  | [] => .skip
  | k::ks => .seq (grid (cell k.1 k.2.1 k.2.2)) (commands ks)



end VWZClique.IntegerRAM.Projected.SupportDP

end

/- NativeProjectionSupportFull -/
section

namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured Projection UniformFolds TraceDyadic SquareCode.Layout Workspace


structure BanksAt (h sig pr : ℕ) (m : Memory) : Prop where
  signs : ∀ (j : BasisLabel h) (x : Bits h),
    m (sig+(wordIndex h x).val*4^h+(Butterfly.labelIndex h j).val:ℕ)=sign j x
  partners : ∀ (j : BasisLabel h) (x : Bits h),
    m (pr+(wordIndex h x).val*4^h+(Butterfly.labelIndex h j).val:ℕ)=index j x



/-- One level has a uniform integer cubic cost. The tag-specific costs only
depend on the finite instruction list in each compiled cell. -/
def constant := (tags.map fun k => cellCost k.1 k.2.1 k.2.2+23).sum


end VWZClique.IntegerRAM.Projected.SupportDP

end

/- NativeProjectionSupportLoop -/
section

namespace VWZClique.IntegerRAM.Projected.SupportDP
open UniformFolds Structured SquareCode.Layout Workspace Butterfly Graph
abbrev outerI : ℤ := -90
abbrev total : ℤ := -91
abbrev unit : ℤ := -92
abbrev guardReg : ℤ := -93
abbrev temp : ℤ := -94
abbrev zeroR : ℤ := -95

def initBlock : List Atom := [.one unit,.sub zeroR unit unit,.sub outerI unit unit,.mul total 320 unit,
  .one (-2),.one (-3),.add inIndex inSign unit,.add outSign inIndex unit,
  .add temp unit unit,.add temp temp temp,.add temp temp temp,.add outIndex outSign temp,
  .store inSign unit,.store inIndex zeroR,.sub guardReg total unit]
def bumpBlock : List Atom := [.sub temp outIndex outSign,.mul inSign outSign unit,.mul inIndex outIndex unit,
  .add outSign outIndex temp,.add temp temp temp,.add temp temp temp,.add temp temp temp,.add outIndex outSign temp,
  .add (-3) (-3) (-3),.mul (-2) (-3) unit]
def body := Command.seq (commands tags) (line bumpBlock)
def execute := Command.seq (line initBlock) (.whenNonnegative guardReg (repeatN body outerI unit total guardReg))




end VWZClique.IntegerRAM.Projected.SupportDP

end

/- NativeProjectionSupportHeaders -/
section

namespace VWZClique.IntegerRAM.Projected.SupportDP
open Structured Butterfly Graph Workspace
abbrev startHeader : ℤ := 379
abbrev signHeader : ℤ := 351
abbrev pairHeader : ℤ := 352

def readSupport : List Atom := [.one unit,.mul inSign startHeader unit]
def writeSupport : List Atom := [.one unit,.mul signHeader inSign unit,.mul pairHeader inIndex unit]
def withHeaders := Command.seq (line readSupport) (.seq execute (line writeSupport))


end VWZClique.IntegerRAM.Projected.SupportDP

end

/- NativeSquareDepth -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM
def nReg : ℤ := -34
def scaleReg : ℤ := -15
def paddingTest : ℤ := -14
def scaleMultiply (c : ℤ) := Expr.mul (.reg scaleReg) (.int c)
def padComparison := Expr.sub side (.add (.reg nReg) .one)
def padIter (b : ℕ) (c : ℤ) := Command.seq (assign (-3) (times side (num b)))
  (.seq (assign scaleReg (scaleMultiply c)) (assign paddingTest padComparison))
def padCommand (b : ℕ) (c : ℤ) := Command.seq (.atom (.one (-3)))
  (.seq (.atom (.one scaleReg)) (.repeatWhileNegative (padIter b c) paddingTest))

def padSteps (b : ℕ) (c : ℤ) := ((times side (num b)).steps+2) +
  (((scaleMultiply c).steps+2)+((padComparison.steps+2)) )+1


end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeProjectionSmallScale -/
section

namespace VWZClique.IntegerRAM.Projected.SmallScale
open Structured Butterfly Graph BlockMM SquareCode.Layout
abbrev header : ℤ := 367
abbrev one : ℤ := -92
def loadN := [Atom.one one,.mul nReg 0 one]
def writeScale := [Atom.one one,.mul header SquareCode.Layout.scaleReg one]
def calculate (b c : ℕ) := Command.seq (line loadN) (.seq (padCommand b c) (line writeScale))


end VWZClique.IntegerRAM.Projected.SmallScale

end

/- NativeProjectionBatchStep -/
section

namespace VWZClique.IntegerRAM.Projected.Batch
open Structured FoldBits

abbrev labels : ℤ := 358
abbrev labelCount : ℤ := 359
abbrev clock : ℤ := 360
abbrev rowReg : ℤ := 361
abbrev colReg : ℤ := 362
abbrev unit : ℤ := 363
abbrev limit : ℤ := 364
abbrev test : ℤ := 365
abbrev slab : ℤ := 366
abbrev carryTest : ℤ := -187




def headers : List Atom := [.add carryTest labels slab,.load 353 carryTest,.mul 354 rowReg unit,
  .mul 355 colReg unit,.mul 357 slab unit]


def plusCol : List Atom := [.add colReg colReg unit,.sub carryTest colReg 0]
def wrapCol : List Atom := [.sub colReg unit unit,.add rowReg rowReg unit,.sub carryTest rowReg 0]
def wrapRow : List Atom := [.sub rowReg unit unit,.add slab slab unit]
def carry := Command.seq (code plusCol) (.whenNonnegative carryTest
  (.seq (code wrapCol) (.whenNonnegative carryTest (code wrapRow))))


end VWZClique.IntegerRAM.Projected.Batch

end

/- NativeProjectionPrepare -/
section

namespace VWZClique.IntegerRAM.Projected.Preparation
open Structured UniformFolds NativeFrame NativeTraversal NativeArena BlockMM

def command (d K b c : ℕ) := Command.seq (MaskScan.Arena.buildMaskMetadata K (reg d .weights))
  (.seq (Init.command d) (.seq SupportDP.withHeaders (SmallScale.calculate b c)))

def headerTime (d : ℕ) := Headers.time (Init.fields d)+(Init.countExpr.steps+2)
def ticks (d K b c L : ℕ) := (1200+30*K)*(2^L)^5+headerTime d+
  (SupportDP.constant+35)*(2^L)^5+(6+(L+1)*SquareCode.Layout.padSteps b c)

structure Ready (L K base count b c : ℕ) (w : WeightKey (2^L)→ℚ) (m : Memory) : Prop where
  metadata : MaskScan.Arena.Prepared L K base m
  params : Init.Params base (2^L) count m
  weights : ∀ i, (m (base+Graph.Table.wordIndex i:ℕ):ℚ)=w i
  domain : m 0=((2^L:ℕ):ℤ)
  length : m 320=L
  banks : SupportDP.BanksAt L (Workspace.level (MaskScan.Arena.slot base (2^L) 7+2) L)
    (Workspace.level (MaskScan.Arena.slot base (2^L) 7+2) L+8^L) m
  signBase : m 351=Workspace.level (MaskScan.Arena.slot base (2^L) 7+2) L
  partnerBase : m 352=((Workspace.level (MaskScan.Arena.slot base (2^L) 7+2) L+8^L:ℕ):ℤ)
  scale : m 367=((c^depth b (2^L):ℕ):ℤ)






end VWZClique.IntegerRAM.Projected.Preparation

end

/- NativeSquareGuarded -/
section

namespace VWZClique.IntegerRAM.SquareCode
open Structured

/-- False guards produce a zero entry without evaluating the guarded indirect load. -/
def gatedWrite (d : ℤ) (dst g k value : Expr) : Command :=
  .seq (dst.code d) (.seq (g.code (d-1)) (.seq (k.code (d-2))
    (.seq (.atom (.sub (d-3) (d-3) (d-3)))
      (.seq (.whenNonnegative (d-1) (.whenNonnegative (d-2) (value.code (d-3)))) (.atom (.store d (d-3)))))))

def gatedSteps (dst g k value : Expr) := dst.steps+g.steps+k.steps+value.steps+4


end VWZClique.IntegerRAM.SquareCode

end

/- NativeProjectionRaster -/
section

namespace VWZClique.IntegerRAM.Projected.Raster
open Structured

abbrev row : ℤ := -5
abbrev col : ℤ := -6
abbrev unit : ℤ := -7
abbrev lim : ℤ := -3
abbrev rowFlag : ℤ := -8
abbrev colFlag : ℤ := -9
abbrev floor : ℤ := -128








def scanRow (body : Command) := Command.seq (.atom (.sub col col col)) (repeatN body col unit lim colFlag)
def run (body : Command) := Command.seq (.atom (.one unit)) <| .seq (.atom (.sub row row row)) <|
  repeatN (scanRow body) row unit lim rowFlag


end VWZClique.IntegerRAM.Projected.Raster

end

/- NativeSquareProjectPacking -/
section

namespace VWZClique.IntegerRAM.Projected.Packing
open Structured SquareCode

inductive Role where | weight | middle | right

abbrev src : ℤ := -51
abbrev short : ℤ := -52
abbrev count : ℤ := -53
abbrev packet : ℤ := -54
abbrev dst : ℤ := -55

def rowCheck : Role → Bool | .right => false | _ => true
def colCheck : Role → Bool | .middle => false | _ => true

def check (active : Bool) (reg : ℤ) : Expr := if active then .sub (.sub (.reg short) .one) (.reg reg) else .zero
def target := Expr.add (.reg dst) (.add (.mul (.reg Raster.row) (.reg Raster.lim)) (.reg Raster.col))

def source (which : Role) : Expr :=
  let a := Expr.reg short
  let s := Expr.reg Raster.lim
  let r := Expr.reg Raster.row
  let c := Expr.reg Raster.col
  let start := Expr.mul (.reg packet) s
  let idx := match which with
    | .weight => Expr.add (.mul c a) r
    | .middle => Expr.add (.mul r (.mul (.reg count) s)) (.add start c)
    | .right => Expr.add (.mul (.add start r) a) c
  .add (.reg src) idx




def writeCell (which : Role) :=
  gatedWrite Raster.floor target (check (rowCheck which) Raster.row) (check (colCheck which) Raster.col) (.read (source which))
def cellCost (which : Role) :=
  gatedSteps target (check (rowCheck which) Raster.row) (check (colCheck which) Raster.col) (.read (source which))
def pack (which : Role) := Raster.run (writeCell which)


end VWZClique.IntegerRAM.Projected.Packing

end

/- WordDot -/
section

namespace VWZClique.IntegerRAM.WordDot
open Structured




namespace Reg
abbrev leftPtr : ℤ := -1
abbrev rightPtr : ℤ := -2
abbrev x : ℤ := -3
abbrev y : ℤ := -4
abbrev acc : ℤ := -5
abbrev one : ℤ := -6
abbrev count : ℤ := -7
abbrev guard : ℤ := -8
abbrev leftStride : ℤ := -9
abbrev rightStride : ℤ := -10
abbrev length : ℤ := -11
end Reg


def init : Command :=
  .seq (.atom (.one Reg.one))
  (.seq (.atom (.sub Reg.acc Reg.one Reg.one))
  (.seq (.atom (.sub Reg.count Reg.acc Reg.length))
        (.atom (.sub Reg.guard Reg.length Reg.one))))

def body : Command :=
  .seq (.atom (.load Reg.x Reg.leftPtr))
  (.seq (.atom (.load Reg.y Reg.rightPtr))
  (.seq (.atom (.mul Reg.x Reg.x Reg.y))
  (.seq (.atom (.add Reg.acc Reg.acc Reg.x))
  (.seq (.atom (.add Reg.leftPtr Reg.leftPtr Reg.leftStride))
  (.seq (.atom (.add Reg.rightPtr Reg.rightPtr Reg.rightStride))
        (.atom (.add Reg.count Reg.count Reg.one)))))))

def loop : Command := .repeatWhileNegative body Reg.count

def command : Command := .seq init (.whenNonnegative Reg.guard loop)














end VWZClique.IntegerRAM.WordDot

end

/- NativeProjectionLoop -/
section

namespace VWZClique.IntegerRAM.Projected
open Structured WordDot

namespace Cell
abbrev lhs : ℤ := -30
abbrev rhs : ℤ := -31
abbrev prod : ℤ := -32
abbrev wt : ℤ := -33
abbrev side : ℤ := -34
abbrev area : ℤ := -35
abbrev zero : ℤ := -36
abbrev idx : ℤ := -40
abbrev one : ℤ := -41
abbrev lim : ℤ := -42
abbrev flag : ℤ := -43
abbrev acc : ℤ := -44
end Cell

structure Layout where
  lhs : ℕ
  rhs : ℕ
  prod : ℕ
  wt : ℕ
  preserve : ℕ := 0

def flat {s : ℕ} (a : Tile s) (i : Fin (s*s)) : ℤ :=
  let p := finProdFinEquiv.symm i
  a p.1 p.2

def bank (m : Memory) {s : ℕ} (b : ℕ) (a : Tile s) : Prop :=
  ∀ i : Fin (s*s), m ((b+i.val:ℕ):ℤ) = flat a i

structure Tables (m : Memory) {s t : ℕ} (l : Layout) (a : Tile s) (b c : Fin t → Tile s) : Prop where
  weights : bank m l.wt a
  left : ∀ p, bank m (l.lhs+p.val*(s*s)) (b p)
  right : ∀ p, bank m (l.rhs+p.val*(s*s)) (c p)


/-- One row-major square multiplication on three runtime pointers. Its scratch
area may be reused in all packets. Only input banks and control cells survive. -/
def SquareRun (W K : ℕ) (μ : ℤ) (square : Command) {s t : ℕ} (l : Layout) (a : Tile s)
    (b c : Fin t → Tile s) : Prop :=
  ∀ (p : Fin t) (m : Memory), Tables m l a b c →
    m Cell.lhs = (l.lhs+p.val*(s*s):ℕ) → m Cell.rhs = (l.rhs+p.val*(s*s):ℕ) →
    m Cell.prod = l.prod → m Cell.side = s →
    ∃ f, f ≤ K ∧ ∃ out, Runs W square m f out ∧
      bank out l.prod (fun i j => μ*(b p * c p) i j) ∧ Tables out l a b c ∧
      (∀ z : ℤ, -44 ≤ z → z≤ -30 → out z=m z) ∧
      (∀ z : ℕ, z<l.preserve → out z=m z)

def copy (dst src : ℤ) : Command := .atom (.add dst src Cell.zero)
def setupDot : Command :=
  .seq (copy Reg.leftPtr Cell.wt)
    (.seq (copy Reg.rightPtr Cell.prod)
      (.seq (.atom (.one Reg.leftStride))
        (.seq (.atom (.one Reg.rightStride)) (copy Reg.length Cell.area))))






def advance : Command :=
  .seq (.atom (.add Cell.acc Cell.acc Reg.acc))
    (.seq (.atom (.add Cell.lhs Cell.lhs Cell.area)) (.atom (.add Cell.rhs Cell.rhs Cell.area)))



def onePacket (square : Command) : Command :=
  .seq square (.seq setupDot (.seq WordDot.command advance))
def packetLoop (square : Command) : Command :=
  repeatN (onePacket square) Cell.idx Cell.one Cell.lim Cell.flag






end VWZClique.IntegerRAM.Projected

end

/- NativeSquarePackMany -/
section

namespace VWZClique.IntegerRAM.Projected.Packing
open Structured

abbrev areaReg : ℤ := -56
abbrev packOne : ℤ := -57
abbrev packFlag : ℤ := -58

def onePacket (role : Role) := Command.seq (pack role) (.atom (.add dst dst areaReg))
def packMany (role : Role) := Command.seq (.atom (.mul areaReg Raster.lim Raster.lim))
  (.seq (.atom (.one packOne)) (.seq (.atom (.sub packet packet packet))
    (repeatN (onePacket role) packet packOne count packFlag)))




end VWZClique.IntegerRAM.Projected.Packing

end

/- MMWordLayout -/
section

namespace VWZClique.BlockMM.WordLayout


/-- One level contains three contiguous banks, each storing N row-major square matrices. -/
def plane (b h N : ℕ) := N*(b^h*b^h)
def size (b h N : ℕ) := 3*plane b h N

















/-- Number of cells in all breadth-first layers. -/
def space (b r : ℕ) : (h N : ℕ) → ℕ
  | 0,N => size b 0 N
  | h+1,N => size b (h+1) N + space b r h (N*r)





end VWZClique.BlockMM.WordLayout

end

/- NativeSquareCell -/
section

namespace VWZClique.IntegerRAM.SquareCode
open Structured
open VWZClique.BlockMM
namespace Layout
open VWZClique.BlockMM.WordLayout


/-- Address in bank-major, node-major, row-major order. -/
def atWord (start count len bank p i j : Expr) : Expr :=
  plus start (plus (times (plus (times (plus (times bank count) p) len) i) len) j)

def parentSide (b : ℕ) := times (num b) side
def next (b : ℕ) := plus base (times (times (times (num 3) nodes) (parentSide b)) (parentSide b))
def parentCell {b : ℕ} (k : Fin 3) (a d : Fin b) : Expr :=
  atWord base nodes (parentSide b) (num k) node (plus (times (num a) side) row)
    (plus (times (num d) side) col)
def childCell (b r : ℕ) (k : Fin 3) (s : Fin r) : Expr :=
  atWord (next b) (times nodes (num r)) side (num k) (plus (times node (num r)) (num s)) row col




def sumFin : (n : ℕ) → (Fin n → Expr) → Expr
  | 0,_ => .zero
  | n+1,f => .add (f 0) (sumFin n (fun i => f i.succ))



def downVal {b : ℕ} (k : Fin 3) (w : Square (Fin b)) :=
  sumFin b fun a => sumFin b fun d => times (.int (w a d)) (.read (parentCell k a d))
def upVal {b r : ℕ} (S : Scheme b r) (a d : Fin b) :=
  sumFin r fun s => times (.int (S.out a d s)) (.read (childCell b r 2 s))


/-- The code for one transformed child input is a fixed instruction sequence
depending only on scheme coefficients and the bank and rank slot. -/
def downCode {b r : ℕ} (k : Fin 3) (s : Fin r) (w : Square (Fin b)) :=
  write floor (childCell b r k s) (downVal k w)


def upCode {b r : ℕ} (S : Scheme b r) (a d : Fin b) :=
  write floor (parentCell 2 a d) (upVal S a d)


end Layout
end VWZClique.IntegerRAM.SquareCode

end

/- NativeSquareLeaf -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

def levelAddr (k : ℕ) := plus base (plus (times (num k) nodes) node)
def levelProd := times (.read (levelAddr 0)) (.read (levelAddr 1))
def leafBody := write floor (levelAddr 2) levelProd
def leafBodySteps := (levelAddr 2).steps+(levelProd.steps+1)




/-- All scalar products on one bottom layer, measured from arbitrary input memory. -/
def leafLayer := Command.seq (.atom (.one (-7))) <| .seq (.atom (.sub (-4) (-4) (-4)))
  (repeatN leafBody (-4) (-7) (-2) (-8))



end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareCatalog -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

def codes {I : Type*} (cmd : I → Command) : List I → Command
  | [] => .skip
  | j::js => .seq (cmd j) (codes cmd js)

noncomputable def all (I : Type*) [Fintype I] : List I := Finset.univ.toList





def weightDown {b r : ℕ} (S : Scheme b r) (j : Fin 3 × Fin r) : Square (Fin b) :=
  if j.1=0 then S.left j.2 else if j.1=1 then S.right j.2 else 0

def downBatchCode {b r : ℕ} (S : Scheme b r) (j : Fin 3 × Fin r) :=
  grid (downCode j.1 j.2 (weightDown S j))

noncomputable def downLevel {b r : ℕ} (S : Scheme b r) := codes (downBatchCode S) (all (Fin 3 × Fin r))

def downBatchCost {b r : ℕ} (S : Scheme b r) (j : Fin 3 × Fin r) :=
  (childCell b r j.1 j.2).steps+((downVal j.1 (weightDown S j)).steps+1)



end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareAscent -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

def upBatchCode {b r : ℕ} (S : Scheme b r) (j : Fin b × Fin b) := grid (upCode S j.1 j.2)
def upBatchCost {b r : ℕ} (S : Scheme b r) (j : Fin b × Fin b) :=
  (parentCell 2 j.1 j.2).steps+((upVal S j.1 j.2).steps+1)
noncomputable def upLevel {b r : ℕ} (S : Scheme b r) := codes (upBatchCode S) (all (Fin b × Fin b))




end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareAdvance -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout





def rootReg : ℤ := -9

def downAdj (b r : ℕ) := Command.seq (assign (-1) (next b)) (assign (-2) (times nodes (num r)))
def back (b : ℕ) := Expr.sub base (times (times (times (num 3) nodes) (parentSide b)) (parentSide b))
def grow (b : ℕ) := assign (-3) (parentSide b)
noncomputable def downOnce {b r : ℕ} (S : Scheme b r) :=
  Command.seq (quotientCmd b (-3)) (.seq (downLevel S) (downAdj b r))
noncomputable def upOnce {b r : ℕ} (S : Scheme b r) :=
  Command.seq (quotientCmd r (-2)) (.seq (assign (-1) (back b)) (.seq (upLevel S) (grow b)))

def downAdjTime (b r : ℕ) := ((next b).steps+2)+((times nodes (num r)).steps+2)
def quotTime (d q : ℕ) := (Expr.num d).steps+2+(1+(1+(5*q+4)))
noncomputable def downTime {b r : ℕ} (S : Scheme b r) (h N : ℕ) := quotTime b (b^h) +
    (((all (Fin 3 × Fin r)).map (fun j => gridCost N (b^h) (downBatchCost S j))).sum+downAdjTime b r)
noncomputable def upTime {b r : ℕ} (S : Scheme b r) (h N : ℕ) := quotTime r N + ((back b).steps+2+
    (((all (Fin b × Fin b)).map (fun j => gridCost N (b^h) (upBatchCost S j))).sum+((parentSide b).steps+2)))





end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareFlight -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

def flag : ℤ := -14
def downTest := Expr.sub .one side
def upTest := Expr.sub side (.reg rootReg)
noncomputable def downStep {b r : ℕ} (S : Scheme b r) := Command.seq (downOnce S) (assign flag downTest)
noncomputable def upStep {b r : ℕ} (S : Scheme b r) := Command.seq (upOnce S) (assign flag upTest)

noncomputable def charge {b r : ℕ} (S : Scheme b r) : (h N : ℕ) → ℕ
  | 0,N => 2+N*(leafBodySteps+3)
  | h+1,N => downTime S h N + (downTest.steps+3) + charge S h (N*r) + upTime S h N + (upTest.steps+3)

def Room (W M : ℕ) := ∀ x : ℤ, -(M:ℤ) ≤ x → x ≤ M → Fits W x






end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareRate -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout OAI.MatrixMultiplication.Arithmetic

noncomputable def core {b r : ℕ} (S : Scheme b r) := Command.seq (assign rootReg side)
   (.seq (.repeatWhileNegative (downStep S) flag) (.seq leafLayer (.repeatWhileNegative (upStep S) flag)))




end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareSetup -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

abbrev Setup := List (ℤ × Expr)
def setupCode : Setup → Command
  | [] => .skip
  | (i,e)::xs => .seq (assign i e) (setupCode xs)
def setupCost : Setup → ℕ
  | [] => 0
  | (_,e)::xs => (e.steps+2)+setupCost xs


end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeProjectPackBanks -/
section

namespace VWZClique.IntegerRAM.Projected.Large
open Structured SquareCode SquareCode.Layout Packing

structure Banks where
  A : ℕ
  B : ℕ
  C : ℕ
  temp : ℕ
  w : ℕ
  left : ℕ
  right : ℕ
  output : ℕ

def Banks.bound (l : Banks) (s a b : ℕ) :=
  l.A+a*a ≤ l.w ∧ l.B+a*(b*s) ≤ l.w ∧ l.C+(b*s)*a ≤ l.w ∧
  l.w+s*s ≤ l.left ∧ l.left+b*(s*s) ≤ l.right ∧ l.right+b*(s*s) ≤ l.output

structure Pointers (m : Memory) (l : Banks) : Prop where
  A : m 371=l.A
  B : m 372=l.B
  C : m 373=l.C
  temp : m 374=l.temp
  w : m 375=l.w
  left : m 376=l.left
  right : m 377=l.right
  output : m 378=l.output

def select (ins outs : ℕ) : Setup := [(src,.reg ins),(dst,.reg outs),(packet,.zero)]
def packBank (role : Role) (ins outs : ℕ) := Command.seq (setupCode (select ins outs)) (packMany role)
def packOneW := Command.seq (setupCode (select 371 375)) (pack .weight)





def planeCost (role : Role) (s : ℕ) := 2+s*(1+s*(cellCost role+3)+3)
def bankCost (role : Role) (ins outs b s : ℕ) := setupCost (select ins outs)+(3+b*(planeCost role s+4))




end VWZClique.IntegerRAM.Projected.Large

end

/- NativeProjectPacked -/
section

namespace VWZClique.IntegerRAM.Projected.Large
open Structured Packing


structure Sources {a b s : ℕ} (m : Memory) (l : Banks) (A : Tile a)
    (B : Matrix (Fin a) (Fin b × Fin s) ℤ) (C : Matrix (Fin b × Fin s) (Fin a) ℤ) : Prop where
  weight : ∀ i j : Fin a, m (l.A+(i.val*a+j.val):ℕ)=A i j
  middle : ∀ i : Fin a, ∀ p : Fin b, ∀ c : Fin s, m (l.B+(i.val*(b*s)+(p.val*s+c.val)):ℕ)=B i (p,c)
  right : ∀ p : Fin b, ∀ r : Fin s, ∀ i : Fin a, m (l.C+((p.val*s+r.val)*a+i.val):ℕ)=C (p,r) i




def allPacks := Command.seq packOneW (.seq (packBank .middle 372 376) (packBank .right 373 377))
def allCost (s b : ℕ) := (SquareCode.Layout.setupCost (select 371 375)+planeCost .weight s)+
  (bankCost .middle 372 376 b s+bankCost .right 373 377 b s)


end VWZClique.IntegerRAM.Projected.Large

end

/- NativeProjectPacketInit -/
section

namespace VWZClique.IntegerRAM.Projected.Large
open Structured SquareCode SquareCode.Layout BlockMM

def setSide : SquareCode.Layout.Setup := [(nReg,.reg Raster.lim)]
def scaleSetup (b : ℕ) (c : ℤ) := Command.seq (setupCode setSide) (.seq (padCommand b c) (.atom (.store 374 scaleReg)))


def controls : SquareCode.Layout.Setup :=
  [(Cell.lhs,.reg 376),(Cell.rhs,.reg 377),(Cell.prod,.reg 378),(Cell.wt,.reg 375),
   (Cell.area,.mul (.reg Cell.side) (.reg Cell.side)),(Cell.zero,.zero),(Cell.idx,.zero),(Cell.one,.one),
   (Cell.lim,.reg Packing.count),(Cell.acc,.zero)]



end VWZClique.IntegerRAM.Projected.Large

end

/- NativeProjectPower -/
section

namespace VWZClique.IntegerRAM.Projected.Power
open Structured

abbrev pos : ℤ := -63
abbrev one : ℤ := -64
abbrev flag : ℤ := -65
abbrev test : ℤ := -66

def code (base exponent : ℤ) := Command.seq (.atom (.one base)) (.seq (.atom (.one one))
  (.seq (.atom (.sub pos pos pos)) (.seq (.atom (.sub test exponent one))
    (.whenNonnegative test (repeatN (.atom (.add base base base)) pos one exponent flag)))))



end VWZClique.IntegerRAM.Projected.Power

end

/- NativeProjectShape -/
section

namespace VWZClique.IntegerRAM.Projected.Shape
open Structured SquareCode SquareCode.Layout UniformFolds Double

abbrev short : ℤ := -52
abbrev count : ℤ := -53
abbrev side : ℤ := -3
abbrev eCount : ℤ := -61
abbrev eSide : ℤ := -62
abbrev gap : ℤ := -67
def long := Expr.mul (.reg 0) (.mul (.reg 0) (.reg 0))
def header : Setup := [(WindowInit.Lreg,.reg 320),(short,.mul (.reg 359) (.reg 0))]
def exponents : Setup := [(eCount,.reg SignedDivision.result),(eSide,.sub (.mul (.num 3) (.reg 320)) (.reg eCount))]
def chooseGap : Setup := [(gap,.sub (.sub (.reg short) (.reg side)) .one)]
def fallback : Setup := [(count,.one),(side,long)]
def quotient (q : ℕ) : Command := if q=0 then .atom (.sub SignedDivision.result SignedDivision.result SignedDivision.result)
  else WindowInit.ratio 1 q
def code (q : ℕ) := Command.seq (setupCode header) (.seq (quotient q) (.seq (setupCode exponents)
  (.seq (Power.code count eCount) (.seq (Power.code side eSide)
    (.seq (setupCode chooseGap) (.whenNonnegative gap (setupCode fallback)))))))


def amount (q L : ℕ) := setupCost header+(13*(L+1)+q+17)+(setupCost exponents)+(5+4*L)+(5+4*(3*L))+
  setupCost chooseGap+1+setupCost fallback


end VWZClique.IntegerRAM.Projected.Shape

end

/- NativeSquareTransfer -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

abbrev srcPointer : ℤ := -17
abbrev srcStride : ℤ := -18
abbrev dstPointer : ℤ := -19
abbrev dstStride : ℤ := -20

def tileAddr (ptr stride : ℤ) := plus (.reg ptr) (plus (times (.reg stride) row) col)
def tileLoad (copy : Bool) : Expr := if copy then .read (tileAddr srcPointer srcStride) else .zero
def tileStore (copy : Bool) := write floor (tileAddr dstPointer dstStride) (tileLoad copy)
def tilePass (copy : Bool) := grid (tileStore copy)
def tileSteps (copy : Bool) := (tileAddr dstPointer dstStride).steps+((tileLoad copy).steps+1)




end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareJob -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured

abbrev rawSide : ℤ := -34
abbrev padSide : ℤ := -16
abbrev workPtr : ℤ := -21
abbrev lhsPtr : ℤ := -30
abbrev rhsPtr : ℤ := -31
abbrev resultPtr : ℤ := -32

structure Anchors where
  raw : ℕ
  pad : ℕ
  work : ℕ
  lhs : ℕ
  rhs : ℕ
  result : ℕ

inductive Width where | raw | padded
inductive Origin where | left | right | result | bank (k : ℕ)

def Width.expr : Width → Expr | .raw => .reg rawSide | .padded => .reg padSide
def Width.val (a : Anchors) : Width → ℕ | .raw => a.raw | .padded => a.pad

def Origin.expr : Origin → Expr
  | .left => .reg lhsPtr | .right => .reg rhsPtr | .result => .reg resultPtr
  | .bank k => plus (.reg workPtr) (times (num k) (times (.reg padSide) (.reg padSide)))








structure Job where
  copy : Bool
  dim : Width
  src : Origin
  srcStep : Width
  dst : Origin
  dstStep : Width

def Job.setup (q : Job) : Setup :=
  [(-2,.one),(-3,q.dim.expr),(srcPointer,q.src.expr),(srcStride,q.srcStep.expr),
    (dstPointer,q.dst.expr),(dstStride,q.dstStep.expr)]

def Job.cmd (q : Job) := Command.seq (setupCode q.setup) (tilePass q.copy)
def Job.cost (a : Anchors) (q : Job) := setupCost q.setup+gridCost 1 (q.dim.val a) (tileSteps q.copy)




end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareBoundary -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

def fillBank (k : ℕ) : Job := ⟨false,.padded,.left,.raw,.bank k,.padded⟩
def copyInto (src : Origin) (k : ℕ) : Job := ⟨true,.raw,src,.raw,.bank k,.padded⟩
def ingest (src : Origin) (k : ℕ) := Command.seq (fillBank k).cmd (copyInto src k).cmd











end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareBootstrap -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

def chooseArea : Setup :=
  [(padSide,.reg (-3)),(workPtr,plus (.reg resultPtr) (times (.reg rawSide) (.reg rawSide)))]

def startSquare (b : ℕ) (c : ℤ) := Command.seq (padCommand b c) (setupCode chooseArea)



def pointCore : Setup := [(-1,.reg workPtr),(-2,.one),(-3,.reg padSide)]




def emitJob : Job := ⟨true,.raw,.bank 2,.padded,.result,.raw⟩
noncomputable def multiply {b r : ℕ} (S : Scheme b r) :=
  Command.seq (startSquare b S.scale) (.seq (ingest .left 0) (.seq (ingest .right 1)
    (.seq (setupCode pointCore) (.seq (core S) emitJob.cmd))))

end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareMultiply -/
section

namespace VWZClique.IntegerRAM.SquareCode.Layout
open Structured BlockMM BlockMM.WordLayout

noncomputable def runtimeCost {b r : ℕ} (S : Scheme b r) (a : Anchors) :=
  (2+(depth b a.raw)*padSteps b S.scale + setupCost chooseArea) +
  ((fillBank 0).cost a+(copyInto .left 0).cost a + ((fillBank 1).cost a+(copyInto .right 1).cost a +
  (setupCost pointCore + (4+charge S (depth b a.raw) 1+emitJob.cost a))))


end VWZClique.IntegerRAM.SquareCode.Layout

end

/- NativeSquareProjectionCall -/
section

namespace VWZClique.IntegerRAM.Projected
open Structured BlockMM BlockMM.WordLayout
namespace SquareCaller
open SquareCode.Layout

noncomputable def duration {b r : ℕ} (S : Scheme b r) (s : ℕ) :=
  runtimeCost S ⟨s,b^(depth b s),0,0,0,0⟩





end SquareCaller
end VWZClique.IntegerRAM.Projected

end

/- NativeProjection -/
section

namespace VWZClique.IntegerRAM.Projected
open Structured UniformFolds TraceDyadic Double
open Double.IntegerTiling

/-- The retained labels are numbered by increasing addresses in the actual
butterfly output. The free third coordinate then gives the row-major node index. -/
noncomputable def labelNumber {L : ℕ} (S : Finset (BasisLabel L)) : S ≃ Fin S.card :=
  let e := (Butterfly.labelIndex L).toEmbedding
  (S.equivMap e).trans ((S.map e).orderIsoOfFin (Finset.card_map ..)).toEquiv.symm

noncomputable def nodeNumber {L : ℕ} (S : Finset (BasisLabel L)) :
    Node S ≃ Fin (S.card * 2^L) := ((labelNumber S).prodCongr (wordIndex L)).trans finProdFinEquiv

/-- The long dimension consists of three packed vertices. The low tile
coordinate is the remainder in the integer power-of-two blocking schedule. -/
def threeVertices (L : ℕ) : Block L ≃ PairBits L × Bits L where
  toFun b := ((b 0,b 1),b 2)
  invFun p := block p.1 p.2
  left_inv b := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨x,y⟩,z⟩; rfl

def longNumber (L : ℕ) : Block L ≃ Fin ((2^L)^3) :=
  let pair := ((wordIndex L).prodCongr (wordIndex L)).trans finProdFinEquiv
  (threeVertices L).trans ((pair.prodCongr (wordIndex L)).trans
    (finProdFinEquiv.trans (finCongr (by ring))))


def blockNumber (L q : ℕ) : Block L ≃ Fin (blocks L q) × Fin (IntegerTiling.side L q) :=
  ((longNumber L).trans (finCongr (exact_shape L q).symm)).trans finProdFinEquiv.symm


noncomputable def shortWeight {L} (S : Finset (BasisLabel L)) (K : ℕ) (w : ChannelKey L → ℚ) :
    Tile (S.card*2^L) :=
  fun i j => leftTable S S K K w ((nodeNumber S).symm i) ((nodeNumber S).symm j)

noncomputable def middle {L} (S : Finset (BasisLabel L)) (q : ℕ) (w : ChannelKey L → ℚ) :
    Matrix (Fin (S.card*2^L)) (Fin (blocks L q) × Fin (IntegerTiling.side L q)) ℤ :=
  fun i j => midTable S w ((nodeNumber S).symm i) ((blockNumber L q).symm j)

noncomputable def right {L} (S : Finset (BasisLabel L)) (q : ℕ) (w : ChannelKey L → ℚ) :
    Matrix (Fin (blocks L q) × Fin (IntegerTiling.side L q)) (Fin (S.card*2^L)) ℤ :=
  fun i j => rightTable S w ((blockNumber L q).symm i) ((nodeNumber S).symm j)






end VWZClique.IntegerRAM.Projected

end

/- NativeProjectionTileScale -/
section

namespace VWZClique.IntegerRAM.Projected

def scaleMat {I J : Type*} (z : ℤ) (A : Matrix I J ℤ) : Matrix I J ℤ := fun i j => z*A i j



end VWZClique.IntegerRAM.Projected

end

/- NativeProjectLarge -/
section

namespace VWZClique.IntegerRAM.Projected.Large
open Structured SquareCode SquareCode.Layout BlockMM BlockMM.WordLayout UniformFolds TraceDyadic Double IntegerTiling

noncomputable def code {b r : ℕ} (q : ℕ) (S : Scheme b r) :=
  Command.seq (Projected.Shape.code q) (.seq allPacks (.seq (scaleSetup b S.scale) (.seq (setupCode controls)
    (.seq (packetLoop (multiply S)) (.atom (.load scaleReg 374))))))

noncomputable def cost {b r : ℕ} (q : ℕ) (S : Scheme b r) (L s packets : ℕ) :=
  Projected.Shape.amount q L + (allCost s packets + ((setupCost setSide+((2+depth b s*padSteps b S.scale)+1))+
    (setupCost controls+(packets*(SquareCaller.duration S s+8*(s*s)+16)+1))))


structure Limits (b r q L labels s packets : ℕ) (l : Banks) (M : ℕ) : Prop where
  ratio : 2^(L+1)*q ≤ M
  side : (2^L)^3+1 ≤ M
  short : labels*2^L ≤ M
  clock : 3*L+1 ≤ M
  workspace : l.output+s*s+space b r (depth b s) 1 ≤ M
  banks : l.bound s (labels*2^L) packets
  header : 378<l.temp
  temp : l.temp<l.w


end VWZClique.IntegerRAM.Projected.Large

end

/- NativeProjectLargeBounds -/
section

namespace VWZClique.IntegerRAM.Projected.Large
open Structured SquareCode.Layout BlockMM BlockMM.WordLayout UniformFolds TraceDyadic Double IntegerTiling

def workspaceBanks (start n : ℕ) : Banks :=
  let l := Workspace.banks start n
  ⟨l.left,l.middle,l.right,l.transform,l.weights,l.packetsLeft,l.packetsRight,l.output⟩



end VWZClique.IntegerRAM.Projected.Large

end

/- NativeProjectionBatch -/
section

namespace VWZClique.IntegerRAM.Projected.Batch
open Structured FoldBits

def init : List Atom := [.one unit,.sub clock unit unit,.sub slab unit unit,.sub rowReg unit unit,
  .sub colReg unit unit,.mul limit labelCount 0,.mul limit limit 0,.sub carryTest limit unit]
def visit (job : Command) := Command.seq (code headers) (.seq job carry)
def grid (job : Command) := Command.seq (code init) (.whenNonnegative carryTest (repeatN (visit job) clock unit limit test))



end VWZClique.IntegerRAM.Projected.Batch

end

/- NativeProjectionScatter -/
section

namespace VWZClique.IntegerRAM.Projected.Scatter
open Structured SquareCode SquareCode.Layout

abbrev src : ℤ := -14
abbrev anchor : ℤ := -15
abbrev rowStride : ℤ := -16
abbrev colStride : ℤ := -17


def destination : Expr := .add (.add (.reg anchor) (.mul row (.reg rowStride))) (.mul col (.reg colStride))
def inputAddress : Expr := .add (.add (.reg src) (.mul row side)) col
def source : Expr := .read inputAddress
def cell := SquareCode.write floor destination source
def run := grid cell



end VWZClique.IntegerRAM.Projected.Scatter

end

/- NativeProjectionScatterLayout -/
section

namespace VWZClique.IntegerRAM.Projected.Scatter
open Structured SquareCode SquareCode.Layout

inductive Channel | left | middle | right deriving DecidableEq

abbrev sourceBase : ℤ := -50
abbrev targetBase : ℤ := -51
abbrev labelID : ℤ := -52
abbrev labels : ℤ := -53
abbrev remoteX : ℤ := -54
abbrev remoteY : ℤ := -55
abbrev pairCode : ℤ := -56












open FoldBits (code)

def initOps := [Atom.one (-2),.mul (-3) 0 (-2),.mul src sourceBase (-2),.mul (-57) 0 0,
  .mul (-58) 0 (-57),.mul (-59) labelID 0,.mul (-60) labels 0,
  .mul (-61) remoteX 0,.add (-61) (-61) remoteY,.mul (-61) (-61) 0]

def arrange : Channel → List Atom
  | .middle => [.mul anchor (-59) (-58),.add anchor anchor targetBase,.add anchor anchor (-61),
      .mul rowStride (-58) (-2),.one colStride]
  | .right => [.mul anchor (-61) (-60),.add anchor anchor targetBase,.add anchor anchor (-59),
      .one rowStride,.mul colStride (-60) (-2)]
  | .left => [.mul anchor (-59) 0,.mul anchor anchor (-57),.add anchor anchor targetBase,
      .add anchor anchor pairCode,.mul rowStride (-58) (-2),.mul colStride (-57) (-2)]

def prepare (b : Channel) := code (initOps++arrange b)


def command (b : Channel) := Command.seq (prepare b) run



end VWZClique.IntegerRAM.Projected.Scatter

end

/- NativeProjectionLeftGather -/
section

namespace VWZClique.IntegerRAM.Projected.LeftGather
open Structured SquareCode SquareCode.Layout

abbrev codes : ℤ := -20
abbrev coeff : ℤ := -21
abbrev inputBase : ℤ := -22
abbrev dest : ℤ := -23
abbrev stride : ℤ := -24
abbrev rowScalar : ℤ := -25
abbrev limit : ℤ := -3
abbrev index : ℤ := -5
abbrev unit : ℤ := -7
abbrev flag : ℤ := -8

def entry (r : ℤ) := Expr.read (.add (.reg r) (.reg index))
def source := Expr.read (.add (.reg inputBase) (entry codes))
def address := Expr.add (.reg dest) (.mul (.reg index) (.reg stride))
def val := Expr.mul (.mul (.reg rowScalar) (entry coeff)) source
def body := SquareCode.write floor address val
def run := Command.seq (.atom (.one unit)) (.seq (.atom (.sub index index index)) (repeatN body index unit limit flag))





end VWZClique.IntegerRAM.Projected.LeftGather

end

/- NativeProjectionLeftSetup -/
section

namespace VWZClique.IntegerRAM.Projected.LeftSetup
open Structured FoldBits Butterfly

abbrev first : ℤ := -70
abbrev second : ℤ := -71
abbrev current : ℤ := -72
abbrev next : ℤ := -73
abbrev one : ℤ := -74
abbrev save : ℤ := -75
abbrev idx : ℤ := -76
abbrev test : ℤ := -77
abbrev firstOrig : ℤ := -78
abbrev sq : ℤ := -79


def start := [Atom.one one,.mul sq 0 0,.mul firstOrig 357 0,.add firstOrig firstOrig 354,
  .mul firstOrig firstOrig 0,.add firstOrig firstOrig 355,.mul firstOrig firstOrig sq,.add firstOrig firstOrig 374,
  .mul first firstOrig one,.mul second 356 one,.one next,.sub idx one one]
def step := [Atom.mul save first one,.mul first second one,.mul second save one,.mul current next one,
  .add next next next,.add next next next]
def loop := repeatN (FoldBits.code step) idx one 320 test
def kernel := Command.seq (FoldBits.code start) loop
def control := [Atom.mul Reg.srcBase firstOrig one,.mul Reg.dstBase 356 one,.mul Reg.stride current one,.mul Reg.stages 320 one]
def configure := Command.seq kernel (FoldBits.code control)





end VWZClique.IntegerRAM.Projected.LeftSetup

end

/- NativeProjectionLeftJob -/
section

namespace VWZClique.IntegerRAM.Projected.LeftSetup
open Structured FoldBits Butterfly UniformFolds TraceDyadic Double



def prepareGather : List Atom := [.mul LeftGather.limit 359 one,.mul LeftGather.codes 358 one,
  .mul LeftGather.coeff 370 one,.mul LeftGather.inputBase first one,.mul LeftGather.stride 0 one,
  .mul LeftGather.dest 357 0,.add LeftGather.dest LeftGather.dest 354,.mul save 359 0,
  .mul LeftGather.dest LeftGather.dest save,.add LeftGather.dest LeftGather.dest 371,.add LeftGather.dest LeftGather.dest 355,
  .add save 370 357,.load LeftGather.rowScalar save]


def job := Command.seq configure (.seq full (.seq kernel (.seq (FoldBits.code prepareGather) LeftGather.run)))
def budget (L a : ℕ) := (16+9*L)+(5+L*(15+20*4^(L-1)))+(12+9*L)+13+
  (2+a*(LeftGather.address.steps+(LeftGather.val.steps+1)+3))



end VWZClique.IntegerRAM.Projected.LeftSetup

end

/- NativeProjectionCells -/
section

namespace VWZClique.IntegerRAM.Projected.Slices.Fill
open Structured Projection WeightedProof UniformFolds TraceDyadic SquareCode Factors

abbrev signBase : ℤ := -68
abbrev partnerBase : ℤ := -69
abbrev label : ℤ := -70
abbrev remote0 : ℤ := -71
abbrev remote1 : ℤ := -72
abbrev dest : ℤ := -73
abbrev labelCount : ℤ := -74

def row := Expr.reg (-5)
def col := Expr.reg (-6)
def supportEntry (tab : ℤ) (x : Expr) : Expr :=
  .read (.add (.reg tab) (.add (.mul x (.reg labelCount)) (.reg label)))

def idx (g : Group) : Expr := if g=.pivotCenter then col else row
def coords (g : Group) : Source → Expr
  | .pivot false => if g=.centerOther then .zero else idx g
  | .pivot true  => if g=.centerOther then .zero else supportEntry partnerBase (idx g)
  | .center      => if g=.pivotOther then .zero else row
  | .other i     => if g=.pivotCenter then .zero else
      if i=0 then .reg remote0 else if i=1 then .reg remote1 else col


def arrayPosition := Expr.add (.reg dest) (.add (.mul row (.reg sideReg)) col)

noncomputable def entryValue (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool)
    (h : Fin 3) (g : Group) : Expr :=
  let factors := component (coords g) π E rev h g
  if g=.pivotCenter then .mul (supportEntry signBase col) factors else factors

noncomputable def cell (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool)
    (h : Fin 3) (g : Group) := write Layout.floor arrayPosition (entryValue π E rev h g)









end VWZClique.IntegerRAM.Projected.Slices.Fill

end

/- NativeProjectionHadamard -/
section

namespace VWZClique.IntegerRAM.Projected.Pointwise
open Structured Butterfly

abbrev src : ℤ := -50
abbrev dst : ℤ := -51
abbrev factor : ℤ := -52
abbrev value : ℤ := -53
abbrev unit : ℤ := -54
abbrev index : ℤ := -55
abbrev limit : ℤ := -56
abbrev guard : ℤ := -57

/-- Scale every entry of a square multiplication result in place, using the
corresponding entry in a separate weight array. -/
def ops : List Atom := [.load factor src,.load value dst,.mul value factor value,.store dst value,
  .add src src unit,.add dst dst unit]
def kernel : Command := repeatN (line ops) index unit limit guard




end VWZClique.IntegerRAM.Projected.Pointwise

end

/- NativeProjectionSmall -/
section

namespace VWZClique.IntegerRAM.Projected.Small
open Structured Projection WeightedProof UniformFolds TraceDyadic Slices Slices.Fill SquareCode

/-- The caller prepares these positive scratch words once per slice. -/
abbrev weightsH : ℕ := 350
abbrev signsH : ℕ := 351
abbrev partsH : ℕ := 352
abbrev labelH : ℕ := 353
abbrev f0H : ℕ := 354
abbrev f1H : ℕ := 355
abbrev workH : ℕ := 356

def dim := Headers.Value.word 0
def area := Headers.Value.mul dim dim
def offset (k : ℕ) := Headers.Value.add (.word workH) (.mul (.nat k) area)
def plane : Group → ℕ | .pivotCenter => 0 | .pivotOther => 1 | .centerOther => 2

def sheetFields (g : Group) : Headers.Fields := [(Raster.lim,dim),(Factors.sideReg,dim),
  (Factors.baseReg,.word weightsH),(Fill.signBase,.word signsH),(Fill.partnerBase,.word partsH),
  (Fill.label,.word labelH),(Fill.remote0,.word f0H),(Fill.remote1,.word f1H),(Fill.dest,offset (plane g)),
  (Fill.labelCount,area)]

noncomputable def sheet (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3) (g : Group) :=
  Command.seq (Headers.command (sheetFields g)) (Raster.run (Fill.cell π E rev h g))

def squareFields : Headers.Fields := [(Cell.lhs,offset 0),(Cell.rhs,offset 1),(Cell.prod,offset 3),(Cell.side,dim)]
def pointFields : Headers.Fields := [(Pointwise.src,offset 2),(Pointwise.dst,offset 3),
  (Pointwise.unit,.nat 1),(Pointwise.index,.nat 0),(Pointwise.limit,area)]

noncomputable def job (square : Command) (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3) :=
  Command.seq (sheet π E rev h .pivotCenter) <| .seq (sheet π E rev h .pivotOther) <|
    .seq (sheet π E rev h .centerOther) <| .seq (Headers.command squareFields) <|
    .seq square <| .seq (Headers.command pointFields) Pointwise.kernel




noncomputable def sheetTime (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3) (g : Group) (n : ℕ) :=
  Headers.time (sheetFields g)+ (2+n*(1+n*(Fill.arrayPosition.steps+((Fill.entryValue π E rev h g).steps+1)+3)+3))





noncomputable def jobTime (π : Equiv.Perm V) (E : Finset EdgeSlot) (rev : Bool) (h : Fin 3)
    (n squareCost : ℕ) := sheetTime π E rev h .pivotCenter n+(sheetTime π E rev h .pivotOther n+
    (sheetTime π E rev h .centerOther n+(Headers.time squareFields+
    (squareCost+(Headers.time pointFields+9*(n*n))))))



end VWZClique.IntegerRAM.Projected.Small

end

/- NativeProjectionPairScan -/
section

namespace VWZClique.IntegerRAM.Projected.PairScan
open Structured FoldBits

abbrev x : ℤ := -140
abbrev y : ℤ := -141
abbrev a : ℤ := -142
abbrev b : ℤ := -143
abbrev test : ℤ := -145
abbrev counter : ℤ := -146
abbrev tmp : ℤ := -147
abbrev one : ℤ := -148
abbrev cross : ℤ := -149
abbrev ans : ℤ := -56
abbrev srcX : ℤ := -54
abbrev srcY : ℤ := -55

def extract (v bit : ℤ) := Command.seq (.atom (.add v v v)) <|
  .seq (.atom (.sub test v 0)) <| .seq (.atom (.sub bit bit bit)) <|
  .whenNonnegative test (.seq (.atom (.sub v v 0)) (.atom (.one bit)))


def finish : List Atom := [.add tmp a b,.add tmp tmp tmp,.add tmp tmp a,
  .mul cross a b,.add cross cross cross,.add cross cross cross,.sub tmp tmp cross,
  .add ans ans ans,.add ans ans ans,.add ans ans tmp,.add counter counter one]
def body := Command.seq (extract x a) (.seq (extract y b) (code finish))
def loop := Command.repeatWhileNegative body counter








def init := [Atom.one one,.mul x srcX one,.mul y srcY one,.sub ans one one,
  .sub counter one one,.sub counter counter 320]
def command := Command.seq (code init) loop


end VWZClique.IntegerRAM.Projected.PairScan

end

/- NativeProjectionScatterValues -/
section

namespace VWZClique.IntegerRAM.Projected.Scatter
open Structured Slices UniformFolds TraceDyadic


def rev : Channel → Bool | .left | .middle => false | .right => true
def index : Channel → Fin 3 | .left => 0 | .middle => 1 | .right => 2


end VWZClique.IntegerRAM.Projected.Scatter

end

/- NativeProjectionScatterHeader -/
section

namespace VWZClique.IntegerRAM.Projected.Scatter
open Structured UniformFolds FoldBits

def bufferReg : Channel → ℤ | .left => 374 | .middle => 372 | .right => 373


def setup (b : Channel) : List Atom := [.one (-62),.mul (-50) 0 0,.add (-63) (-50) (-50),
  .add (-50) (-50) (-63),.add (-50) 356 (-50),.mul (-51) (bufferReg b) (-62),.mul (-52) 357 (-62),
  .mul (-53) 359 (-62),.mul (-54) 354 (-62),.mul (-55) 355 (-62)]

def fromHeaders (b : Channel) := Command.seq (FoldBits.code (setup b)) (.seq PairScan.command (command b))





end VWZClique.IntegerRAM.Projected.Scatter

end

/- NativeProjectionChannels -/
section

namespace VWZClique.IntegerRAM.Projected.Channels
open Structured Projection UniformFolds WeightedProof TraceDyadic BlockMM Scatter  

noncomputable def job {b r} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot) (ch : Channel) :=
  Command.seq (Small.job (SquareCode.Layout.multiply S) π E (rev ch) (index ch)) (fromHeaders ch)

noncomputable def time {b r} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot) (ch : Channel) (L : ℕ) :=
  Small.jobTime π E (rev ch) (index ch) (2^L) (SquareCaller.duration S (2^L))+
  (16+24*L+128*(2^L)^2)





end VWZClique.IntegerRAM.Projected.Channels

end

/- NativeProjectionChannelGrid -/
section

namespace VWZClique.IntegerRAM.Projected.Channels
open Structured BlockMM   Scatter Projection WeightedProof UniformFolds


noncomputable def program {b r} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot) (ch : Channel) :=
  Batch.grid (job S π E ch)

noncomputable def cost {b r} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot) (ch : Channel) (L a : ℕ) :=
  9+(a*2^L*2^L)*(time S π E ch L+17)


end VWZClique.IntegerRAM.Projected.Channels

end

/- NativeProjectionThree -/
section

namespace VWZClique.IntegerRAM.Projected.Dense
open Structured BlockMM Scatter  UniformFolds Projection WeightedProof

abbrev labelSet (K L : ℕ) := (windowExpansion K L).labels

abbrev Bank (base L : ℕ) := Workspace.banks (MaskScan.Arena.slot base (2^L) 7+2) (2^L)





noncomputable def three {b r} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot) : Command :=
  .seq (Channels.program S π E .middle) (.seq (Channels.program S π E .right) (Channels.program S π E .left))

noncomputable def threeCost {b r} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot) (L a : ℕ) :=
  Channels.cost S π E .middle L a+(Channels.cost S π E .right L a+Channels.cost S π E .left L a)


end VWZClique.IntegerRAM.Projected.Dense

end

/- NativeProjectionDense -/
section

namespace VWZClique.IntegerRAM.Projected.Dense
open Structured BlockMM Projection UniformFolds WeightedProof Double

noncomputable def code {b r} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot) :=
  Command.seq (three S π E) (Batch.grid LeftSetup.job)

noncomputable def cost {b r} (S : Scheme b r) (π : Equiv.Perm V) (E : Finset EdgeSlot) (L a : ℕ) :=
  threeCost S π E L a+(9+a*2^L*2^L*(LeftSetup.budget L a+17))


end VWZClique.IntegerRAM.Projected.Dense

end

/- NativeLeafPlan -/
section

namespace VWZClique.IntegerRAM.NativeLeaf
open UniformFolds Structured

/-- One leading constant covers all static sparse leaves at every dyadic
length. A returned integer agrees with the recursion's exact integer leaf.
The signed input may occupy any contiguous segment disjoint from scratch. -/
theorem plan_leaf (dst : ℤ) (hdst : dst < -3) :
    ∃ C : ℕ, ∀ (H : SimpleGraph V) (hh : ¬ HasWedges H),
      ∃ c : Command, ∀ (L W base M : ℕ) (cap : Graph.Division.Room W M)
        (room : base+9*(2^L)+81*(2^L*2^L)≤M)
        (w : WeightKey (2^L) → ℤ) (hb : ∀ i, w i=0 ∨ w i=1) (m : Memory),
        Ready (inputData (by positivity) cap room w) (Empty.elim : Empty → ℤ)
          (Empty.elim : Empty → Fin (2^L)) m →
        ∃ t o, Runs W c m t o ∧ t≤C*(2^L)^5 ∧
          o dst=integerLeaf L H hh (fun i => (w i:ℚ)) ∧ Frame dst m o := by
  classical
  let Leaf := {H : SimpleGraph V // ¬ HasWedges H}
  let _ : Fintype Leaf := Fintype.ofFinite _
  choose cmd coeff kernel using (fun j : Leaf => sparse_native j.val j.property dst hdst)
  refine ⟨∑ j : Leaf, coeff j,?_⟩
  intro H hh
  let j : Leaf := ⟨H,hh⟩
  refine ⟨cmd j,?_⟩
  intro L W base M cap room w hb m ready
  obtain ⟨t,o,run,cost,val,fr⟩ := kernel j (inputData (by positivity) cap room w) m ready
  have small : coeff j ≤ ∑ h : Leaf, coeff h :=
    Finset.single_le_sum (fun h _ => Nat.zero_le (coeff h)) (Finset.mem_univ j)
  have hw (i) : Binary (w i:ℚ) := by
    rcases hb i with h|h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simp [h])
  have refValue := (integerLeaf_cast L H hh _ hw).trans (sparseLeaf_correct L H hh _)
  refine ⟨t,o,run,cost.trans (Nat.mul_le_mul_right _ small),?_,fr⟩
  exact_mod_cast val.trans refValue.symm

end VWZClique.IntegerRAM.NativeLeaf

end

/- NativeFrameLeaf -/
section

namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal

def enterLeaf (d : ℕ) : Command :=
  .seq (.atom (.one (-3))) (.seq (.atom (.mul (-2) 0 (-3)))
    (.atom (.mul (-1) (reg d .weights) (-3))))

theorem enterLeaf_runs (W d : ℕ) (m : Memory) :
    ∃ o, Runs W (enterLeaf d) m 3 o ∧ o (-1)=m (reg d .weights) ∧
      o (-2)=m 0 ∧ o (-3)=1 ∧ ∀ a : ℤ, 0≤a → o a=m a := by
  let u := update m (-3) 1
  let v := update u (-2) (m 0)
  let o := update v (-1) (m (reg d .weights))
  have p := reg_positive d .weights
  have s : Runs W (.atom (.one (-3))) m 1 u := .atom (.one _ _)
  have t : Runs W (.atom (.mul (-2) 0 (-3))) u 1 v := by
    simpa [u,v,update] using Runs.atom (Step.mul (W:=W) u (-2) 0 (-3))
  have t' : Runs W (.atom (.mul (-1) (reg d .weights) (-3))) v 1 o := by
    simpa [o,v,u,update,show reg d .weights≠ -2 by omega,show reg d .weights≠ -3 by omega] using
      Runs.atom (Step.mul (W:=W) v (-1) (reg d .weights) (-3))
  refine ⟨o,s.seq (t.seq t'),?_,?_,?_,?_⟩
  · simp [o,update]
  · simp [o,v,update]
  · simp [o,v,u,update]
  · intro a ha
    simp [o,v,u,update,show a≠ -1 by omega,show a≠ -2 by omega,show a≠ -3 by omega]

/-- Fixed commands for every leaf and depth of the traversal. The table
description and suspended parent frames are the same as those of reset and pop. -/
theorem leaf_transitions :
    ∃ (op : ℕ → SimpleGraph V → Command) (C : ℕ), ∀ (L W d : ℕ) (hd : d≤36)
      (lay : StackLayout) (H : SimpleGraph V) (hh : ¬HasWedges H) (w : WeightKey (2^L) → ℚ)
      (hb : ∀ i, Binary (w i)) (q : List (NativeTraversal.Slot L))
      (_cap : Graph.Division.Room W (lay.base d+9*(2^L)+81*(2^L*2^L))),
      Transition W (Repr lay) (op d H) (.input d w::q) (.value d (integerLeaf L H hh w)::q)
        (C*(2^L)^5) := by
  classical
  obtain ⟨C,all⟩ := NativeLeaf.plan_leaf (-4) (by decide)
  let cmd (H : SimpleGraph V) := if h : ¬HasWedges H then Classical.choose (all H h) else Command.skip
  let op (d : ℕ) (H : SimpleGraph V) := Command.seq (enterLeaf d) (.seq (cmd H) (copy (reg d .value) (-4)))
  refine ⟨op,C+5,?_⟩
  intro L W d hd lay H hh w hb q cap m init
  obtain ⟨global,⟨ptr,tab⟩,anc⟩ := init
  obtain ⟨s,enter,bas,nn,one,keep⟩ := enterLeaf_runs W d m
  let N := 2^L
  let raw (i : WeightKey N) := m ((lay.base d+Graph.Table.wordIndex i:ℕ):ℤ)
  have asRat : (fun i => (raw i:ℚ)) = w := funext tab
  have bin : ∀ i, raw i=0 ∨ raw i=1 := by
    intro i
    rcases hb i with a|b
    · left; exact_mod_cast (tab i).trans a
    · right; exact_mod_cast (tab i).trans b
  have ready : NativeLeaf.Ready (NativeLeaf.inputData (by positivity) cap le_rfl raw)
      (Empty.elim : Empty → ℤ) (Empty.elim : Empty → Fin N) s :=
    ⟨bas.trans ptr,nn.trans global.dim,one,fun i => i.elim,fun i => keep _ (Int.natCast_nonneg _)⟩
  obtain ⟨t,y,body,cost,out,fr⟩ :=
    Classical.choose_spec (all H hh) L W _ _ cap le_rfl raw bin s ready
  have native : Runs W (cmd H) s t y := by simpa only [cmd,dif_pos hh] using body
  rw [asRat] at out
  have retPos := reg_positive d .value
  have cp := copy_runs W (reg d .value) (-4) (by omega) y
  let o := update y (reg d .value) (y (-4))
  have preserved (a : ℤ) (ha : 0≤a) (hne : a ≠ reg d .value) : o a=m a := by
    rw [show o a=y a by simp [o,update,hne],fr a (by omega),keep a ha]
  have plane (a : ℕ) (ha : 297≤a) := preserved a (Int.natCast_nonneg _) (distinctData ha hd _)
  have parent (j : ℕ) (hj : j<d) (f : Field) := preserved (reg j f) (reg_positive j f).le
    (ne_of_lt (separate hj _ _))
  refine ⟨3+(t+2),?_,o,enter.seq (native.seq cp),global.transfer (preserved 0 le_rfl (ne_of_lt retPos)) (plane 320 (by decide)) (plane 321 (by decide)),
    ?_,saved_transfer lay d q plane parent anc⟩
  · have hp : 0 < (2^L:ℕ)^5 := by positivity
    rw [Nat.add_mul]
    omega
  · change o (reg d .value) = _
    simpa [o,update] using out

end VWZClique.IntegerRAM.NativeFrame

end

/- NativeFrameAssembly -/
section

namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal

noncomputable def leafCoefficient : ℕ := Classical.choose (Classical.choose_spec leaf_transitions)


noncomputable def fees (L : ℕ) (P B : SimpleGraph V → ℕ) : Charges :=
  ⟨fun _ => leafCoefficient*(2^L)^5, P, B, 5, 1, 0⟩

/-- The remaining nonrecursive native components are the projected contraction
(which initializes the cursor), and construction of each masked child (which
also installs its signed coefficient on the suspended parent). -/
structure Kernels {L} (W : ℕ) (lay : StackLayout)
    (proj : ℕ → SimpleGraph V → Equiv.Perm V → Command)
    (push : ℕ → SimpleGraph V → Equiv.Perm V → Branch → Command)
    (P B : SimpleGraph V → ℕ) : Prop where
  projected : ∀ d H π w (q : List (NativeTraversal.Slot L)), d+Nat.card (SimpleGraph.edgeSet H)≤36 →
    (∀ i, Binary (w i)) → Transition W (Repr lay) (proj d H π) (.input d w::q)
      (.cursor d H π .left w 0 (integerTrace (windowAt (Nat.card H.edgeSet)) L H π w)::q) (P H)
  child : ∀ depth H π b (i : Fin (visits (number L H) b)) w z (q : List (NativeTraversal.Slot L)), depth<36 →
    (∀ j, Binary (w j)) → Transition W (Repr lay) (push depth H π b) (.cursor depth H π b w i.val z::q)
      (.input (depth+1) (childWeights H π (numbered H b i) w):: .cursor depth H π b w i.val z::q) (B H)



end VWZClique.IntegerRAM.NativeFrame

end

/- NativeFoldRate -/
section

namespace VWZClique.NativeTraversal
open UniformFolds BlockReduction WeightedProof IntegerRAM IntegerRAM.Structured
open OAI.MatrixMultiplication.Arithmetic


/-- This interface includes all setup and final write-back from the original
adjacency input. All constants and bytecode must be fixed before n is supplied. -/
def Realizes (mm : ℕ→ℕ) (T U A : ℕ) : Prop :=
  ∃ cutoff : ℕ, ∀ k ≥ cutoff, ∃ (machine : Command) (b p : ℕ) (D : ℝ), k+3≤b ∧ 0<D ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (hn : 2≤n), cutoff≤n →
    ∃ (f : ℕ) (out : Memory), let L := graphLength n k
      (f:ℝ)≤D*((L+1:ℕ):ℝ)^p*(planWork mm T U A L (fixed ⊤):ℝ) ∧
      Runs (b*(n.log2+1)) machine (input (MonDepMW.graphInput G)) f out ∧
      out ((MonDepMW.graphInput G).length:ℤ)=integerPlan L (fixed ⊤) (graphWeights G (by omega) k)


end VWZClique.NativeTraversal

end

/- NativeAssemblyRate -/
section

namespace VWZClique.IntegerRAM.NativeFrame
open Structured UniformFolds NativeTraversal BlockReduction Graph WeightedProof

/-- The two bytecode families are fixed for all input lengths. Their data and
the accounting bounds depend only on the current dyadic dimension and the
static pattern. The compiler chooses its word-width multiplier once per k. -/
structure Implemented (mm : ℕ→ℕ) (T U A : ℕ) where
  projection : ℕ → SimpleGraph V → Equiv.Perm V → Command
  push : ℕ → SimpleGraph V → Equiv.Perm V → Branch → Command
  projectTime : ℕ → SimpleGraph V → ℕ
  pushTime : ℕ → SimpleGraph V → ℕ
  factor : ℕ
  logPower : ℕ
  positive : 0<U
  sparseTime : ∀ L H, (fees L (projectTime L) (pushTime L)).small H ≤
    (factor*(L+1)^logPower)*(U*(2^L)^5)
  projectedTime : ∀ L H, projectTime L H + 2 ≤
    (factor*(L+1)^logPower)*(NativeTraversal.projected mm T U L H+3)
  pushBound : ∀ L H, pushTime L H + 6 ≤ (factor*(L+1)^logPower)*(U*(2^L)^5)
  kernels : ∀ k≥32, ∃ b : ℕ, k+3≤b ∧ 2*((k+8)/9)+11≤b ∧ ∀ n (hn : 32≤n),
    let L := graphLength n k
    let W := b*(n.log2+1)
    let layout := NativeArena.forGraph n k hn
    @Kernels L W layout projection push (projectTime L) (pushTime L) ∧
    (∀ d≤36, Division.Room W (layout.base d+9*2^L+81*(2^L*2^L))) ∧ Division.Room W ((2^L)^6)


end VWZClique.IntegerRAM.NativeFrame

end


