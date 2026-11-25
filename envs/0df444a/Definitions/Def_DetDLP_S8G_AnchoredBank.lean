-- Prove2me | Definitions.Def_DetDLP_S8G_AnchoredBank
-- name    : DetDLP_S8G_AnchoredBank
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:50:49.77799+00:00
-- url     : https://prove2.me/theorems/ab71a6ee-fa63-4970-a982-4df6e3eb5f4c
-- title:
--   Tag 1 anchored moment layout, gate surjectivity, and raw bank bijection
-- statement:
--   Constructs the anchored factor layout and tests for all four Fp moment branches, proves gate surjectivity, bijects satisfying assignments with accepted raw register banks, and identifies physical prefix rows with the seed filter.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8G_Routes
import Definitions.Def_DetDLP_S8G_FpMomentLayout
import Definitions.Def_DetDLP_S8H0_PointGraph

set_option autoImplicit false
namespace DetDLP.S8G.Semantics
open S8H0 S8J.CircuitRealizes NamedBlocks RegisterMap ResidueWires
open SeedAndAtomBank Routes RangeRows FpAtomRows GateRoutes HashRows
private abbrev hd (p : ℕ) : 1 ≤ bitLen p + 1 := Nat.succ_pos _
abbrev shape (p m : ℕ) (j : Fin 4) := bank j m (bitLen p+1) (edges (hd p))
def net (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  joinB (PointGraph.zeroLast (shape p m j).size) (Routes.network (hd p) p m j T η)
private abbrev C (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  AnchoredLayout.block (net p m j T η).core ((shape p m j).size+1)
private abbrev wires (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) :=
  AnchoredLayout.wiring (net p m j T η).core (net p m j T η).name
def layout (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) : w3_FactorLayout :=
  circuit (C p m j T η) (wires p m j T η)
def tests (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) : w3_factorTest (layout p m j T η) :=
  test (C p m j T η) (wires p m j T η)

private abbrev Full (A : w3_FactorLayout) := Function.Surjective A.gate
private theorem joinFull {A B : w3_FactorLayout} (ha : Full A) (hb : Full B) : Full (S8J.join A B) := by
  intro g; induction g using Fin.addCases with
  | left i => obtain ⟨e,rfl⟩ := ha i; exact ⟨e.castAdd _,by simp [S8J.join,S8J.splitMap]⟩
  | right i => obtain ⟨e,rfl⟩ := hb i; exact ⟨Fin.natAdd _ e,by simp [S8J.join,S8J.splitMap]⟩
private theorem joinBFull {k} {a b : B k} (ha : Full a.core.A) (hb : Full b.core.A) :
    Full (joinB a b).core.A := joinFull ha hb
private theorem manyFull {k n} {f : Fin (n+1) → B k} (h : ∀ i, Full (f i).core.A) :
    Full (many n f).core.A := by
  induction n with
  | zero => exact h 0
  | succ n ih => exact joinBFull (h 0) (ih (fun i => h i.succ))
private theorem allFull {s n} {f : Fin n → B (Shape.size s+1)} (h : ∀ i, Full (f i).core.A) :
    Full (allRows n f).core.A := by cases n with | zero => exact fun i => i.elim0 | succ n => exact manyFull h
private theorem rowsFull {s n m} {r : Fin n → Fin m → Ref s} {t} (i : Fin m) : Full (rows n m r t).core.A :=
  fun g => ⟨finProdFinEquiv (g,i),congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (g,i))⟩
private theorem addFull {d} : Full (S8C.AddLayout.layout d) := fun i => ⟨_,S8C.AddLayout.col_pos i 0⟩

open w4_M5GraphBounds in
private theorem mulFull {d : ℕ} (h : 1 ≤ d) : Full (w3_fpMulLayout d h) := by
  intro g
  obtain ⟨v,rfl⟩ := (vertexIndex d).surjective g
  let z : Fin (w4_MulParams.L1 d) := ⟨0,w4_MulParams.L1_pos d⟩
  let b : Fin (w4_MulParams.L2 d) := ⟨0,w4_MulParams.L2_pos d⟩
  have left (e : Edge d (W d)) : ∃ i, (w3_fpMulLayout d h).gate i = vertexIndex d (src h e) := by
    refine ⟨((edgeIndex d _) e).castAdd _,?_⟩
    simp [w3_fpMulLayout,w3_m5Layout,w3_m5HalfGate,w3_forgetSides,graph]
  have right (e : Edge d (W d)) : ∃ i, (w3_fpMulLayout d h).gate i = vertexIndex d (dst h e) := by
    refine ⟨Fin.natAdd _ ((edgeIndex d _) e),?_⟩
    simp only [w3_fpMulLayout,w3_m5Layout,w3_m5HalfGate,w3_forgetSides,graph,Fin.addCases_right,Equiv.symm_apply_apply]
  cases v with
  | inputBit a i => exact left (.input a i)
  | pack a i => exact left (.packForward a i 0)
  | forward1 a i => exact left (.forwardMiddle a i z 0)
  | forward2 a i => exact left (.forwardPoint a b i 0)
  | pointwise i j => exact left (.pointInverse i j 0)
  | inverse1 j => exact left (.inverseMiddle b j 0)
  | inverse2 i => exact right (.inverseMiddle i z 0)
  | carry i => exact right (.coefficient i 0)
  | carrySpacer i => exact left (.carryRight i 0)
  | outputBit i => exact right (.output i)

private theorem orFull {s} (n : ℕ) (x : Fin n → Ref s) (b : Ref s) (t : Fin n → Ref s) :
    Full (orRows n x b t).core.A := by
  induction n generalizing b with
  | zero => exact rowsFull 0
  | succ n ih => exact joinBFull (rowsFull 0) (ih _ _ _)

set_option maxHeartbeats 1500000 in
private theorem netFull (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) : Full (net p m j T η).core.A := by
  unfold net Routes.network seedBlock seedSlotBlock atomBankBlock atomSlotBlock HashRows.block
    chainBlock stageAt stageBlock stageProducts stageSum product eqs checker sumRows
  dsimp only
  repeat' first
    | with_reducible apply joinBFull
    | with_reducible apply allFull; intro i
    | exact addFull
    | exact mulFull _
    | exact orFull _ _ _ _
    | exact rowsFull 0
    | exact Function.surjective_id

theorem gate_surj (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) :
    Function.Surjective (layout p m j T η).gate := by
  have h : Full (C p m j T η).A := joinFull Function.surjective_id (netFull p m j T η)
  intro g; induction g using Fin.addCases with
  | left i => obtain ⟨e,rfl⟩ := h i; exact ⟨e.castAdd _,by simp [layout,circuit,S8H.CopyCycle.layout]⟩
  | right i => refine ⟨Fin.natAdd _ (i.castAdd _),?_⟩; simp only [layout,circuit,S8H.CopyCycle.layout,Fin.addCases_right,Fin.addCases_left]

private def unpin (s : Shape) (N : B (s.size+1)) : {u // (joinB (PointGraph.zeroLast s.size) N).OK u} ≃
    {v : s.Data // N.OK (Fin.lastCases (motive := fun _ => Bool) false (s.decode.symm v))} := by
  let e := PointGraph.dropLast.trans s.decode
  let drop (u : {u // (joinB (PointGraph.zeroLast s.size) N).OK u}) :
      {u : Bits (s.size+1) // u (Fin.last _) = false} := ⟨u.val,(PointGraph.zeroLast_iff _).mp ((joinB_iff ..).mp u.property).1⟩
  refine ⟨fun u => ⟨e (drop u),?_⟩,fun v => ⟨(e.symm v.val).val,(joinB_iff ..).mpr
    ⟨(PointGraph.zeroLast_iff _).mpr (e.symm v.val).property,v.property⟩⟩,?_,?_⟩
  · change N.OK (e.symm (e (drop u))).val
    rw [e.symm_apply_apply]; exact ((joinB_iff ..).mp u.property).2
  · intro u; apply Subtype.ext; change (e.symm (e (drop u))).val = (drop u).val; rw [e.symm_apply_apply]
  · intro v; exact Subtype.ext (e.apply_symm_apply v.val)

/-- Undo the copy cycles and anchors, then discard the pinned constant wire. -/
noncomputable def assignments (p m : ℕ) (j : Fin 4) (T : ℕ) (η : List Bool) :
    {x : Fin (layout p m j T η).nb → Bool //
      ∀ g, tests p m j T η g (fun e => x ((layout p m j T η).bit e.val)) = true} ≃
    {v : (shape p m j).Data // (Routes.network (hd p) p m j T η).OK
      (Fin.lastCases (motive := fun _ => Bool) false ((shape p m j).decode.symm v))} := by
  exact (w3_factorEquiv _ _).symm.trans ((S8J.CircuitRealizes.decode (C p m j T η) (wires p m j T η)).trans
    ((AnchoredLayout.assignments _ _).trans (unpin _ _)))

/-- The physical prefix reads the same big-endian coefficient bits as the seed filter. -/
theorem prefix_iff {p m d : ℕ} {s : Shape} (q : Path (seedShape m d) s) (u : Bits (s.size+1))
    (S : FpSeed p m) (η : List Bool) (hη : η.length ≤ m*2*bitLen p)
    (ha : ∀ i : Fin m, evalWord (seedA (fun a => q (.vec i a))) u ((S i).1.val+1))
    (hb : ∀ i : Fin m, evalWord (seedB (fun a => q (.vec i a))) u (S i).2.val) :
    (∀ i : Fin η.length, i.val < m*2*bitLen p ∧ (prefixBit p q i).eval u = η[i]) ↔
      S ∈ FpMoment.seedSet p m η := by
  let L := List.ofFn (M89S1.fpBits S)
  have len : (L.take η.length).length = η.length := List.length_take_of_le (by simpa [L] using hη)
  have readBit (i : Fin η.length) : (prefixBit p q i).eval u = (L.take η.length)[i.val]'(by rw [len]; exact i.isLt) := by
    have hi := i.isLt.trans_le hη
    simp only [L,List.getElem_take,List.getElem_ofFn,prefixBit,dif_pos hi,M89S1.fpBits,M89S1.packBits,M89S1.fpWords]
    split <;> rename_i h
    · apply ha
    · apply hb
  change _ ↔ S ∈ Finset.univ.filter _
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change _ ↔ L.take η.length = η
  constructor
  · intro H; apply List.ext_getElem len; intro i _ hi
    exact (readBit ⟨i,hi⟩).symm.trans (H ⟨i,hi⟩).2
  · intro H i; refine ⟨i.isLt.trans_le hη,(readBit i).trans ?_⟩; simp only [H]; rfl

end DetDLP.S8G.Semantics


