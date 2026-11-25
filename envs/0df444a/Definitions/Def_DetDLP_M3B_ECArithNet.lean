-- Prove2me | Definitions.Def_DetDLP_M3B_ECArithNet
-- name    : DetDLP_M3B_ECArithNet
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:31:55.536265+00:00
-- url     : https://prove2.me/theorems/12a99bf4-32ed-4b1a-8798-34c9cdf8d62b
-- title:
--   EC address banks, prefix pins, and physical lookup wiring
-- statement:
--   Builds the named address bank and prefix checker around a supplied arithmetic block, realizes their semantics on physical wires, and proves parsimonious extension of the EC certificates.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_M3B_ECAddrGadget
import Definitions.Def_DetDLP_M3B_ECLayout

set_option autoImplicit false
namespace DetDLP.M3B.ECArithNet
open S8H0 S8H0.NamedBlocks S8H0.RegisterMap ECCert ECAddrGadget

/-- Use one unsatisfiable row for an overlong prefix. This keeps the graph
    size independent of the length of a malformed public prefix. -/
def prefixBlock {r : Shape} (refs : List (Ref r)) (pre : List Bool) : B (r.size+1) :=
  if h : pre.length ≤ refs.length then
    rows pre.length 1 (fun i _ => refs.get (Fin.castLE h i))
      (fun i a => decide (a 0 = pre.get i))
  else rows 1 1 (fun _ _ => .pin false) (fun _ _ => false)

theorem prefix_iff {r : Shape} (refs : List (Ref r)) (pre : List Bool) (x : Fin (r.size+1) → Bool) :
    (prefixBlock refs pre).OK x ↔ pre <+: refs.map (fun v => v.eval x) := by
  unfold prefixBlock
  split_ifs with h
  · rw [rows_iff,List.prefix_iff_eq_take]
    simp only [decide_eq_true_eq]
    constructor
    · intro H
      apply List.ext_getElem
      · simp [h]
      · intro i hi _; simpa using (H ⟨i,hi⟩).symm
    · intro H i
      have eq := congrArg (fun l : List Bool => l[i.val]?) H
      simpa [List.getElem?_eq_getElem, i.isLt, i.isLt.trans_le h] using eq.symm
  · rw [rows_iff]
    constructor
    · intro H; exact Bool.noConfusion (H 0)
    · intro H; exact (h (by simpa using H.length_le)).elim

theorem prefix_edges {r : Shape} (refs : List (Ref r)) (pre : List Bool) :
    (prefixBlock refs pre).core.A.ne ≤ max 1 refs.length := by
  unfold prefixBlock; split_ifs with h
  · change pre.length*1 ≤ _; omega
  · change 1*1 ≤ _; omega

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
variable (F : Fin m → List (Point E)) (S : ECSeed p m) (T k : ℕ)

private theorem point_len (b : ℕ) (A : Point E) :
    ((pointCoords A).flatMap (w3_bits b)).length = 3*b := by
  cases A <;> simp [pointCoords,w3_bits] <;> omega

/-- Each word includes the full-width infinity tag as well as both coordinates. -/
theorem code_length (t : Tuples E F) :
    (w3_tupleWord (base E F) (fun A => (pointCoords A).flatMap (w3_bits (bitLen p))) t.1 t.2).length =
      4*m*(3*bitLen p) := by
  let word := fun A : Point E => (pointCoords A).flatMap (w3_bits (bitLen p))
  have hw (A : Point E) : (word A).length = 3*bitLen p := point_len E _ A
  change (w3_tupleWord (base E F) word t.1 t.2).length = _
  simp [w3_tupleWord,List.length_flatMap,hw,List.finRange_succ] <;> ring

abbrev SlotAux := Aux (width p k)
abbrev Checked (i : Fin m) := {a : Slot E S T i × SlotAux (p:=p) k // slotOK a.1 k a.2}

/-- Erasing the selected word, address word, and carry word forgets no choice. -/
noncomputable def forget (hT : T ≤ p) (hk : 2*T ≤ 2^k) (i : Fin m) :
    Checked E S T k i ≃ Slot E S T i where
  toFun a := a.1.1
  invFun w := ⟨(w,(slot_unique w k hT hk).exists.choose),(slot_unique w k hT hk).exists.choose_spec⟩
  left_inv a := Subtype.ext (Prod.ext rfl ((slot_unique a.1.1 k hT hk).unique
    (slot_unique a.1.1 k hT hk).exists.choose_spec a.2))
  right_inv _ := rfl

abbrev CheckedTable := (i : Fin m) → Fin 2 → Bool → Checked E S T k i
noncomputable def forgetTable (hT : T ≤ p) (hk : 2*T ≤ 2^k) : CheckedTable E S T k ≃ Table E S T :=
  Equiv.piCongrRight fun i => Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ => forget E S T k hT hk i

noncomputable def tableDecode (mul : w3_modMulInterface) (hT : T ≤ p) (hk : 2*T ≤ 2^k)
    (hF : ListsOK E F S T) := (forgetTable E S T k hT hk).trans (tableEquiv E F S T mul hT hF)

theorem address_at (mul : w3_modMulInterface) (hT : T ≤ p) (hk : 2*T ≤ 2^k)
    (hF : ListsOK E F S T) (a : CheckedTable E S T k) (i : Fin m) (j : Fin 2) (s : Bool) :
    let t := tableDecode E F S T k mul hT hk hF a
    bitsToNat (low (a i j s).1.2) = ECAddress.address E S T i ((F i).get (if s then t.2 i j else t.1 i j)) := by
  cases s <;> exact low_address (a i j _).1.1 k F mul hT hF hk (a i j _).2

noncomputable def certEquiv (hp : 3 < p) (P : Point E) (mul : w3_modMulInterface)
    (hT : T ≤ p) (hk : 2*T ≤ 2^k) (hF : ListsOK E F S T) (pre : List Bool) :
    let D := tableDecode E F S T k mul hT hk hF
    {a : CheckedTable E S T k × Joined E // prefixOK E F pre (D a.1) ∧ joinedOK E F hp P (D a.1) a.2} ≃
    {t : Tuples E F // (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P ∧ prefixOK E F pre t} := by
  apply Equiv.trans _ (nativeCertEquiv E F S T hp P mul hT hF pre)
  exact (Equiv.prodCongr (forgetTable E S T k hT hk) (Equiv.refl _)).subtypeEquiv (fun _ => Iff.rfl)

section Physical
open S8J S8J.CircuitRealizes
variable {r : Shape} {d n : ℕ}

private def many {v : ℕ} : (n : ℕ) → (Fin n → B v) → B v
  | 0, _ => ⟨empty,Fin.elim0⟩
  | n+1, f => joinB (f 0) (many n (fun i => f i.succ))

private theorem many_iff {v : ℕ} (n : ℕ) (f : Fin n → B v) (x : Fin v → Bool) :
    (many n f).OK x ↔ ∀ i, (f i).OK x := by
  induction n with
  | zero => exact ⟨fun _ i => i.elim0,fun _ i => i.elim0⟩
  | succ n ih => rw [many,joinB_iff,ih,Fin.forall_fin_succ]

structure Inputs (r : Shape) (n d : ℕ) where
  parity : Fin n → Ref r
  hash : Fin n → Fin d → Ref r
  selected : Fin n → Fin d → Ref r
  addr : Fin n → Fin d → Addr r
  carry : Fin n → Fin d → Ref r

variable (v : Inputs r n d) (th : ℕ)

def bank := many n fun i => ECAddrGadget.block th (v.parity i) (v.hash i) (v.selected i)
  (fun j => .reg (v.addr i j)) (v.carry i)

theorem bank_iff (x : Fin (r.size+1) → Bool) : (bank v th).OK x ↔
    ∀ i, good th ((v.parity i).eval x) (fun j => (v.hash i j).eval x)
      (fun j => (v.selected i j).eval x,fun j => (Ref.reg (v.addr i j)).eval x,
       fun j => (v.carry i j).eval x) := by
  unfold bank; rw [many_iff]; exact forall_congr' fun i => block_iff ..

variable (arithmetic : B (r.size+1)) (refs : List (Ref r)) (pre : List Bool)
def body := joinB arithmetic (joinB (bank v th) (prefixBlock refs pre))

theorem body_iff (x : Fin (r.size+1) → Bool) : (body v th arithmetic refs pre).OK x ↔
    arithmetic.OK x ∧ (bank v th).OK x ∧ pre <+: refs.map (fun a => a.eval x) := by
  simp only [body,joinB_iff,prefix_iff]

variable (k' : ℕ) (hd : k' ≤ d)
include hd in
def withLookups : w3_FactorLayout :=
  let b := body v th arithmetic refs pre
  let a := AnchoredLayout.block b.core (r.size+1)
  let W := AnchoredLayout.wiring b.core b.name
  ECLayout.layout (circuit a W) (fun i j => W.rep (v.addr i (Fin.castLE hd j)).index.castSucc)

def physicalTest : w3_factorTest (withLookups v th arithmetic refs pre k' hd) :=
  let b := body v th arithmetic refs pre
  let a := AnchoredLayout.block b.core (r.size+1)
  let W := AnchoredLayout.wiring b.core b.name
  ECLayout.test (circuit a W) _ (CircuitRealizes.test a W)

/-- On physical bit assignments this erases both lookup reads and equality-copy
    cycles. The argument `arithmetic` must constrain all remaining named registers. -/
def physicalEquiv :
    {x // Accept (withLookups v th arithmetic refs pre k' hd) (physicalTest v th arithmetic refs pre k' hd) x} ≃
    {x // arithmetic.OK x ∧ (bank v th).OK x ∧ pre <+: refs.map (fun a => a.eval x)} := by
  let b := body v th arithmetic refs pre
  let a := AnchoredLayout.block b.core (r.size+1)
  let W := AnchoredLayout.wiring b.core b.name
  let L := circuit a W
  let t := CircuitRealizes.test a W
  let bus (i : Fin n) (j : Fin k') : Fin L.nb := W.rep (v.addr i (Fin.castLE hd j)).index.castSucc
  exact (ECLayout.acceptEquiv L bus t).trans (((w3_factorEquiv L t).symm.trans
    ((CircuitRealizes.decode a W).trans (AnchoredLayout.assignments b.core b.name))).trans
    (Equiv.subtypeEquivRight (body_iff v th arithmetic refs pre)))

end Physical
end DetDLP.M3B.ECArithNet


