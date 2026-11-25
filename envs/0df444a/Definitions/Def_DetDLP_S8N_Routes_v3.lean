-- Prove2me | Definitions.Def_DetDLP_S8N_Routes_v3
-- name    : DetDLP_S8N_Routes_v3
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T05:17:22.829104+00:00
-- url     : https://prove2.me/theorems/1d38fb72-5a16-4fe5-899c-f51463757b9b
-- title:
--   EC moment query routes v3
-- statement:
--   EC point seed, atom, conversion, and fold routing for the four moment queries
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8N_ECSeedBank
import Definitions.Def_DetDLP_S8M_ECAtomSlot
import Definitions.Def_DetDLP_S8M_ECMapRows
import Definitions.Def_DetDLP_S8M_ECFoldRoutes
import Definitions.Def_DetDLP_S8M_Routes

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 200000
namespace DetDLP.S8N.RoutesV2
open S8H0 RegisterMap NamedBlocks ResidueWires RangeRows HashRows GateRoutes
open DetDLP.S8M.ECAtomSlot DetDLP.S8M.ECMapRows DetDLP.S8M.ECFoldRoutes
open DetDLP.S8G.SeedAndAtomBank (allRows allRows_iff)

def copies (j : Fin 4) : ℕ := min j.val 2
def outputs (j : Fin 4) : ℕ := if j.val = 3 then 1 else 0

theorem copies_of_outputs {j : Fin 4} (h : 0 < outputs j) : copies j = 2 := by
  fin_cases j <;> simp [outputs, copies] at h ⊢

def targetShape (d : ℕ) : Shape := Shape.pair .bit (Shape.pair (triple d) (triple d))
def productShape (m d e : ℕ) : Shape :=
  Shape.pair (targetShape d) (Shape.pair (.vec (2*m) (mapShape d e)) (.vec 2 (foldShape (m-1) d e)))
def bank (j : Fin 4) (m d e : ℕ) : Shape :=
  Shape.pair (DetDLP.S8N.ECSeedBank.ecSeedShape m d)
    (Shape.pair (.vec (copies j) (Shape.vec m (slotShape d e)))
      (.vec (outputs j) (productShape m d e)))

theorem routeCounts :
    (copies 0, outputs 0) = (0, 0) ∧ (copies 1, outputs 1) = (1, 0) ∧
    (copies 2, outputs 2) = (2, 0) ∧ (copies 3, outputs 3) = (2, 1) := by decide

variable {s : Shape} {j : Fin 4} {m d e : ℕ}

def seeds (q : Path (bank j m d e) s) : Path (DetDLP.S8N.ECSeedBank.ecSeedShape m d) s := fun a => q (.fst a)
def atoms (q : Path (bank j m d e) s) (k : Fin (copies j)) : Path (Shape.vec m (slotShape d e)) s :=
  fun a => q (.snd (.fst (.vec k a)))
def atom (q : Path (bank j m d e) s) (k : Fin (copies j)) (i : Fin m) : Path (slotShape d e) s :=
  fun a => atoms q k (.vec i a)
def product (q : Path (bank j m d e) s) (t : Fin (outputs j)) : Path (productShape m d e) s :=
  fun a => q (.snd (.snd (.vec t a)))
def target (q : Path (productShape m d e) s) : Path (targetShape d) s := fun a => q (.fst a)
def maps (q : Path (productShape m d e) s) : Path (Shape.vec (2*m) (mapShape d e)) s := fun a => q (.snd (.fst a))
def folds (q : Path (productShape m d e) s) : Path (Shape.vec 2 (foldShape (m-1) d e)) s := fun a => q (.snd (.snd a))
def mapPath (q : Path (productShape m d e) s) (k : Fin (2*m)) : Path (mapShape d e) s := fun a => maps q (.vec k a)
def foldPath (q : Path (productShape m d e) s) (k : Fin 2) : Path (foldShape (m-1) d e) s := fun a => folds q (.vec k a)
def seedSlotPath (q : Path (DetDLP.S8N.ECSeedBank.ecSeedShape m d) s) (i : Fin m) (b : Bool) :
    Path (DetDLP.S8G.SeedAndAtomBank.seedSlot d) s :=
  fun a => q (.vec i (if b then .snd a else .fst a))
def seedA (q : Path (bank j m d e) s) (i : Fin m) (b : Bool) : Word s :=
  DetDLP.S8N.ECSeedBank.ecSeedA (seedSlotPath (seeds q) i b)
def seedB (q : Path (bank j m d e) s) (i : Fin m) (b : Bool) : Word s :=
  DetDLP.S8N.ECSeedBank.ecSeedB (seedSlotPath (seeds q) i b)

def ecPrefixBit (p : ℕ) (path : Path (DetDLP.S8N.ECSeedBank.ecSeedShape m d) s) (idx : ℕ) : Ref s :=
  if h : idx < m * 4 * bitLen p then
    let t : Fin (m * 4) × Fin (bitLen p) := finProdFinEquiv.symm ⟨idx, h⟩
    let ik : Fin m × Fin 4 := finProdFinEquiv.symm t.1
    let q := seedSlotPath path ik.1 (decide (2 ≤ ik.2.val))
    (if ik.2.val % 2 = 0 then DetDLP.S8N.ECSeedBank.ecSeedA q else DetDLP.S8N.ECSeedBank.ecSeedB q) t.2.rev.val
  else .pin false

def ecSeedBlockV2 (p m : ℕ) (η : List Bool) (path : Path (DetDLP.S8N.ECSeedBank.ecSeedShape m d) s) : B (s.size+1) :=
  joinB (allRows m fun i => joinB
    (DetDLP.S8N.ECSeedBank.ecSeedSlotBlock p (seedSlotPath path i false))
    (DetDLP.S8N.ECSeedBank.ecSeedSlotBlock p (seedSlotPath path i true)))
    (rows η.length 1 (fun i _ => ecPrefixBit p path i.val)
      (fun i f => decide (i.val < m * 4 * bitLen p ∧ f 0 = η[i])))

theorem ecSeedBlockV2_iff (p m : ℕ) (η : List Bool) (path : Path (DetDLP.S8N.ECSeedBank.ecSeedShape m d) s) (u : Bits (s.size+1)) :
    (ecSeedBlockV2 p m η path).OK u ↔
      (∀ i : Fin m, (DetDLP.S8N.ECSeedBank.ecSeedSlotBlock p (seedSlotPath path i false)).OK u ∧
        (DetDLP.S8N.ECSeedBank.ecSeedSlotBlock p (seedSlotPath path i true)).OK u) ∧
      ∀ i : Fin η.length, i.val < m * 4 * bitLen p ∧ (ecPrefixBit p path i.val).eval u = η[i] := by
  simp only [ecSeedBlockV2, joinB_iff, allRows_iff, rows_iff, decide_eq_true_eq]

def pointFlag (q : Path (slotShape d e) s) : Ref s := .reg (q (.fst CurveRows.flag))
def pointX (q : Path (slotShape d e) s) : Word s := word (fun i : Addr (.word d) => q (.fst (xa (.fst i))))
def pointY (q : Path (slotShape d e) s) : Word s := word (fun i : Addr (.word d) => q (.fst (ya (.fst i))))
def targetFlag (q : Path (targetShape d) s) : Ref s := .reg (q (.fst .bit))
def targetX (q : Path (targetShape d) s) : Word s := word (fun i : Addr (.word d) => q (.snd (.fst (.fst i))))
def targetY (q : Path (targetShape d) s) : Word s := word (fun i : Addr (.word d) => q (.snd (.snd (.fst i))))
def mapFlag (q : Path (mapShape d e) s) : Ref s := .reg (q (.fst (.fst .bit)))
def mapX (q : Path (mapShape d e) s) : Word s := word (fun i : Addr (.word d) => q (.fst (.snd (.fst (.fst i)))))
def mapY (q : Path (mapShape d e) s) : Word s := word (fun i : Addr (.word d) => q (.fst (.snd (.snd (.fst i)))))
def slotIdx (hm : 1 ≤ m) (k : Fin (2*m)) : Fin m := ⟨k.val % m, Nat.mod_lt _ (by omega)⟩
def copyIdx {j : Fin 4} (h : 0 < outputs j) (k : Fin (2*m)) : Fin (copies j) :=
  ⟨k.val / m, by rw [copies_of_outputs h]; have hk := k.isLt; exact Nat.div_lt_of_lt_mul (by omega)⟩
private theorem foldIndex_lt (hm : 1 ≤ m) (k : Fin 2) (i : Fin (m-1)) :
    k.val * m + i.val + 1 < 2*m := by
  have hk := k.isLt
  have hi := i.isLt
  interval_cases k.val <;> simp_all <;> omega
private theorem firstIndex_lt (hm : 1 ≤ m) (k : Fin 2) : k.val * m < 2*m := by
  have hk := k.isLt
  interval_cases k.val <;> simp_all <;> omega
def foldFlag (hm : 1 ≤ m) (q : Path (productShape m d e) s) (k : Fin 2) (i : Fin (m-1)) : Ref s :=
  mapFlag (mapPath q ⟨k.val * m + i.val + 1, foldIndex_lt hm k i⟩)
def foldX (hm : 1 ≤ m) (q : Path (productShape m d e) s) (k : Fin 2) (i : Fin (m-1)) : Word s :=
  mapX (mapPath q ⟨k.val * m + i.val + 1, foldIndex_lt hm k i⟩)
def foldY (hm : 1 ≤ m) (q : Path (productShape m d e) s) (k : Fin 2) (i : Fin (m-1)) : Word s :=
  mapY (mapPath q ⟨k.val * m + i.val + 1, foldIndex_lt hm k i⟩)

def targetBlock (p : ℕ) (q : Path (targetShape d) s) : B (s.size+1) :=
  joinB (checker p (fun a => q (.snd (.fst a)))) <|
  joinB (checker p (fun a => q (.snd (.snd a)))) <|
    rows d 3 (fun i => ![targetFlag q, targetX q i, targetY q i])
      (fun _ r => decide (!r 0 || (r 1 = false ∧ r 2 = false)))

def network (hd : 1 ≤ d) (hm : 1 ≤ m) (p T : ℕ) (c : Coeff) (b2 neg1 three c4Term : ℕ)
    (j : Fin 4) (η : List Bool) (q : Path (bank j m d (w4_M5GraphBounds.graph d hd).nE) s) : B (s.size+1) :=
  joinB (ecSeedBlockV2 p m η (seeds q)) <|
  joinB (allRows (copies j) fun k =>
    allRows m fun i =>
      slotBlock hd p T c
        (seedA q i false) (seedB q i false) (seedA q i true) (seedB q i true) (atom q k i)) <|
  allRows (outputs j) fun t =>
    have hout : 0 < outputs j := Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt
    let r := product q t
    let z := target r
    let mapsBlock := allRows (2*m) fun k =>
      let a := atom q (copyIdx hout k) (slotIdx hm k)
      mapBlock hd p b2 c.a1 c.a3 (pointFlag a) (pointX a) (pointY a) (mapPath r k)
    let foldsBlock := allRows 2 fun k =>
      let qf := foldPath r k
      let first := mapPath r ⟨k.val * m, firstIndex_lt hm k⟩
      foldBlock hd p neg1 three c4Term
        (mapFlag first) (mapX first) (mapY first)
        (foldFlag hm r k) (foldX hm r k) (foldY hm r k)
        (targetFlag z) (targetX z) (targetY z) qf
    joinB (targetBlock p z) (joinB mapsBlock foldsBlock)

theorem network_iff (hd : 1 ≤ d) (hm : 1 ≤ m) (p T : ℕ) (c : Coeff) (b2 neg1 three c4Term : ℕ)
    (j : Fin 4) (η : List Bool) (q : Path (bank j m d (w4_M5GraphBounds.graph d hd).nE) s) (u : Bits (s.size+1)) :
    (network hd hm p T c b2 neg1 three c4Term j η q).OK u ↔
      (ecSeedBlockV2 p m η (seeds q)).OK u ∧
      (∀ k : Fin (copies j), ∀ i : Fin m,
        (slotBlock hd p T c
          (seedA q i false) (seedB q i false) (seedA q i true) (seedB q i true) (atom q k i)).OK u) ∧
      (∀ t : Fin (outputs j),
        let hout : 0 < outputs j := Nat.lt_of_le_of_lt (Nat.zero_le _) t.isLt
        (targetBlock p (target (product q t))).OK u ∧
        (∀ k : Fin (2*m),
          (mapBlock hd p b2 c.a1 c.a3
            (pointFlag (atom q (copyIdx hout k) (slotIdx hm k)))
            (pointX (atom q (copyIdx hout k) (slotIdx hm k)))
            (pointY (atom q (copyIdx hout k) (slotIdx hm k)))
            (mapPath (product q t) k)).OK u) ∧
        (∀ k : Fin 2,
          (foldBlock hd p neg1 three c4Term
            (mapFlag (mapPath (product q t) ⟨k.val * m, firstIndex_lt hm k⟩))
            (mapX (mapPath (product q t) ⟨k.val * m, firstIndex_lt hm k⟩))
            (mapY (mapPath (product q t) ⟨k.val * m, firstIndex_lt hm k⟩))
            (foldFlag hm (product q t) k) (foldX hm (product q t) k) (foldY hm (product q t) k)
            (targetFlag (target (product q t))) (targetX (target (product q t))) (targetY (target (product q t)))
            (foldPath (product q t) k)).OK u)) := by
  unfold network
  simp only [joinB_iff, allRows_iff]

end DetDLP.S8N.RoutesV2


