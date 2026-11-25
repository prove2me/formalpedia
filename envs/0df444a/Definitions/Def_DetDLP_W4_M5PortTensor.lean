-- Prove2me | Definitions.Def_DetDLP_W4_M5PortTensor
-- name    : DetDLP_W4_M5PortTensor
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:43:30.704422+00:00
-- url     : https://prove2.me/theorems/15d5bb14-d095-43d5-840c-94656f31d06e
-- title:
--   Parsimonious multiplication tensor on the ordered ports
-- statement:
--   Identifies typed graph-edge assignments with the interface bits and a transcript and proves that the Boolean checks on actual sorted incidence lists encode multiplication parsimoniously.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Definitions.Def_DetDLP_W4_M5GraphBounds
import Definitions.Def_DetDLP_W4_M5Transcript

set_option autoImplicit false

namespace DetDLP.w4_M5PortTensor
open w4_M5GraphBounds w4_M5TranscriptBridge w4_MulParams

abbrev Wire (d : ℕ) := Edge d (W d) → Bool

def tag (a : Bool) : Fin 2 := if a then 1 else 0

def flag (a : Fin 2) : Bool := decide (a.val = 1)

@[simp] theorem flag_tag (a : Bool) : flag (tag a) = a := by cases a <;> decide
@[simp] theorem tag_flag (a : Fin 2) : tag (flag a) = a := by fin_cases a <;> decide

def inPos {d : ℕ} (a : Bool) (i : Fin d) : Fin (4*d) :=
  if a then ⟨d+i.val, by omega⟩ else ⟨i.val, by omega⟩

def outPos {d : ℕ} (i : Fin (2*d)) : Fin (4*d) := ⟨2*d+i.val, by omega⟩

def extEdge {d : ℕ} (i : Fin (4*d)) : Edge d (W d) :=
  if h : i.val < d then .input 0 ⟨i.val,h⟩
  else if h : i.val < 2*d then .input 1 ⟨i.val-d,by omega⟩
  else .output ⟨i.val-2*d,by omega⟩

@[simp] theorem ext_inPos {d : ℕ} (a : Bool) (i : Fin d) :
    extEdge (inPos a i) = .input (tag a) i := by
  cases a <;> simp [inPos, extEdge, tag, i.isLt, show d + i.val < 2*d by omega]

@[simp] theorem ext_outPos {d : ℕ} (i : Fin (2*d)) : extEdge (outPos i) = .output i := by
  simp [extEdge, outPos, show ¬(2*d+i.val < d) by omega]

def position {d : ℕ} : Edge d (W d) → Option (Fin (4*d))
  | .input a i => some (inPos (flag a) i)
  | .output i => some (outPos i)
  | _ => none

@[simp] theorem position_ext {d : ℕ} (i : Fin (4*d)) : position (extEdge i) = some i := by
  unfold extEdge
  split <;> rename_i h
  · simp [position, inPos, flag]
  · split <;> rename_i h'
    · simp [position, inPos, flag, Fin.ext_iff]; omega
    · simp [position, outPos, Fin.ext_iff]; omega

def unpack {d : ℕ} (w : Wire d) : Transcript d where
  packed a i b := w (.packForward (tag a) i b)
  forwardMiddle a i t b := w (.forwardMiddle (tag a) t i b)
  forwardPoint a i t b := w (.forwardPoint (tag a) t i b)
  pointInverse i t b := w (.pointInverse t i b)
  inverseMiddle i t b := w (.inverseMiddle t i b)
  coefficient i b := w (.coefficient i b)
  carryLeft i b := w (.carryLeft i b)
  carryRight i b := w (.carryRight i b)

def pack {d : ℕ} (x : Fin (4*d) → Bool) (p : Transcript d) : Wire d
  | .input a i => x (inPos (flag a) i)
  | .packForward a i b => p.packed (flag a) i b
  | .forwardMiddle a t i b => p.forwardMiddle (flag a) i t b
  | .forwardPoint a t i b => p.forwardPoint (flag a) i t b
  | .pointInverse t i b => p.pointInverse i t b
  | .inverseMiddle t i b => p.inverseMiddle i t b
  | .coefficient i b => p.coefficient i b
  | .carryLeft i b => p.carryLeft i b
  | .carryRight i b => p.carryRight i b
  | .output i => x (outPos i)

@[simp] theorem unpack_pack {d : ℕ} (x : Fin (4*d) → Bool) (p : Transcript d) :
    unpack (pack x p) = p := by
  ext <;> simp [unpack, pack]

@[simp] theorem pack_ext {d : ℕ} (x : Fin (4*d) → Bool) (p : Transcript d) (i : Fin (4*d)) :
    pack x p (extEdge i) = x i := by
  have h := position_ext i
  generalize extEdge i = e at h ⊢
  cases e <;> simp_all [position, pack]

@[simp] theorem pack_unpack {d : ℕ} (w : Wire d) : pack (fun i => w (extEdge i)) (unpack w) = w := by
  funext e
  cases e <;> simp [pack, unpack]

@[simp] theorem operand_ext {d : ℕ} (w : Wire d) (a : Bool) (i : Fin d) :
    operand (fun j => w (extEdge j)) a i = w (.input (tag a) i) := by
  cases a with
  | false => exact congrArg w (ext_inPos false i)
  | true => exact congrArg w (ext_inPos true i)

@[simp] theorem output_ext {d : ℕ} (w : Wire d) (i : Fin (2*d)) :
    output (fun j => w (extEdge j)) i = w (.output i) := by
  exact congrArg w (ext_outPos i)

def node {d : ℕ} (v : Vertex d) (w : Wire d) : Bool :=
  let x := fun i => w (extEdge i)
  let p := unpack w
  match v with
  | .inputBit .. | .outputBit .. => true
  | .pack a u => packCheck x p (flag a) u
  | .forward1 a b => forward1Check p (flag a) b
  | .forward2 a i => forward2Check p (flag a) i
  | .pointwise t i => pointCheck p i t
  | .inverse1 i => inverse1Check p i
  | .inverse2 b => inverse2Check p b
  | .carry u => carryCheck x p u
  | .carrySpacer i => spacerCheck p i

theorem checks_iff {d : ℕ} (w : Wire d) :
    (∀ v, node v w = true) ↔ AllChecks (fun i => w (extEdge i)) (unpack w) := by
  constructor
  · intro h
    exact ⟨fun a u => by simpa only [node, flag_tag] using h (.pack (tag a) u),
      fun a b => by simpa only [node, flag_tag] using h (.forward1 (tag a) b),
      fun a i => by simpa only [node, flag_tag] using h (.forward2 (tag a) i),
      fun i t => h (.pointwise t i), fun i => h (.inverse1 i), fun b => h (.inverse2 b),
      fun j => h (.carrySpacer j), fun u => h (.carry u)⟩
  · rintro ⟨pa,f₁,f₂,pt,i₁,i₂,sp,ca⟩ v
    cases v with
    | inputBit | outputBit => rfl
    | pack a u => exact pa (flag a) u
    | forward1 a b => exact f₁ (flag a) b
    | forward2 a i => exact f₂ (flag a) i
    | pointwise t i => exact pt i t
    | inverse1 i => exact i₁ i
    | inverse2 b => exact i₂ b
    | carry u => exact ca u
    | carrySpacer j => exact sp j

theorem node_local {d : ℕ} (hd : 1 ≤ d) (v : Vertex d) (w z : Wire d)
    (h : ∀ e, src hd e = v ∨ dst hd e = v → w e = z e) : node v w = node v z := by
  cases v with
  | inputBit | outputBit => rfl
  | pack a u =>
    apply packCheck_congr
    · funext r; simp only [unpack, tag_flag]; exact h _ (Or.inl rfl)
    · intro i hi; simp only [operand_ext,tag_flag]; exact h _ (Or.inr (congrArg (Vertex.pack a) (Fin.ext hi)))
  | forward1 a b =>
    apply forward1Check_congr
    · intro u hu; funext r; simp only [unpack,tag_flag]
      exact h _ (Or.inr (congrArg (Vertex.forward1 a) (Fin.ext hu)))
    · intro i; funext r; simp only [unpack,tag_flag]; exact h _ (Or.inl rfl)
  | forward2 a i =>
    apply forward2Check_congr
    · intro b; funext r; simp only [unpack,tag_flag]; exact h _ (Or.inr rfl)
    · intro b; funext r; simp only [unpack,tag_flag]; exact h _ (Or.inl rfl)
  | pointwise t i =>
    apply pointCheck_congr
    · intro a; funext r; exact h _ (Or.inr rfl)
    · funext r; exact h _ (Or.inl rfl)
  | inverse1 i =>
    apply inverse1Check_congr
    · intro t; funext r; exact h _ (Or.inr rfl)
    · intro b; funext r; exact h _ (Or.inl rfl)
  | inverse2 b =>
    apply inverse2Check_congr
    · intro i; funext r; exact h _ (Or.inr rfl)
    · intro u hu; funext r; exact h _ (Or.inl (congrArg Vertex.inverse2 (Fin.ext hu)))
  | carry u =>
    apply carryCheck_congr
    · funext r; exact h _ (Or.inr rfl)
    · intro j hj; funext r; exact h _ (Or.inr (congrArg Vertex.carry (Fin.ext hj)))
    · intro j hj; funext r; exact h _ (Or.inl (congrArg Vertex.carry (Fin.ext hj)))
    · intro i hi; simp only [output_ext]; exact h _ (Or.inl (congrArg Vertex.carry (Fin.ext hi)))
  | carrySpacer j =>
    apply spacerCheck_congr
    · funext r; exact h _ (Or.inr rfl)
    · funext r; exact h _ (Or.inl rfl)

/-- Reconstruct the incident bits in increasing physical port order; all unobserved bits default to zero. -/
def readWire {d : ℕ} (hd : 1 ≤ d) (v : Fin (graph d hd).nV)
    (a : Fin ((graph d hd).deg v) → Bool) (e : Edge d (W d)) : Bool :=
  (List.ofFn a)[((graph d hd).ports v).idxOf (edgeIndex d (W d) e)]?.getD false

def tensor {d : ℕ} (hd : 1 ≤ d) (v : Fin (graph d hd).nV)
    (a : Fin ((graph d hd).deg v) → Bool) : Bool :=
  node ((vertexIndex d).symm v) (readWire hd v a)

def ext {d : ℕ} (hd : 1 ≤ d) (i : Fin (4*d)) : Fin (graph d hd).nE := edgeIndex d (W d) (extEdge i)

theorem agrees {d : ℕ} (hd : 1 ≤ d) (v : Vertex d) (y : Fin (graph d hd).nE → Bool) :
    tensor hd (vertexIndex d v) (fun j => y (((graph d hd).ports (vertexIndex d v)).get j)) =
      node v (fun e => y (edgeIndex d (W d) e)) := by
  unfold tensor
  rw [Equiv.symm_apply_apply]
  apply node_local hd
  intro e he
  let G := graph d hd
  let E := edgeIndex d (W d) e
  let V := vertexIndex d v
  have inc : (G.endpoints E).1 = V ∨ (G.endpoints E).2 = V := by
    simpa only [G, E, V, graph, Equiv.symm_apply_apply, Equiv.apply_eq_iff_eq] using he
  let k := w4_M5Network.PortLookup.index G V E inc
  have hk : (G.ports V).get k = E := w4_M5Network.PortLookup.get_index _ _ _ _
  change ((List.ofFn fun j => y ((G.ports V).get j))[k.val]?).getD false = y E
  rw [List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact k.isLt), Option.getD_some, List.getElem_ofFn]
  exact congrArg y hk

theorem satisfies_iff {d : ℕ} (hd : 1 ≤ d) (y : Fin (graph d hd).nE → Bool) :
    (∀ v, tensor hd v (fun j => y (((graph d hd).ports v).get j)) = true) ↔
    AllChecks (fun i => y (ext hd i)) (unpack (fun e => y (edgeIndex d (W d) e))) := by
  unfold ext
  rw [← checks_iff (fun e => y (edgeIndex d (W d) e))]
  constructor
  · intro h v; rw [← agrees hd v y]; exact h _
  · intro h v; obtain ⟨u,rfl⟩ := (vertexIndex d).surjective v
    rw [agrees]; exact h _

/-- Parsimony for the concrete numbered graph, with its sorted lists of physical edge ports. -/
theorem parsimonious {d : ℕ} (hd : 1 ≤ d) : IsParsimonious (graph d hd) (tensor hd) (ext hd)
    (fun x => bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
      bitsToNat (fun i : Fin d => x ⟨d+i.val, by omega⟩) =
      bitsToNat (fun i : Fin (2*d) => x ⟨2*d+i.val, by omega⟩)) := by
  refine ⟨fun i j h => Option.some.inj ?_, fun x => ⟨?_,?_⟩⟩
  · simpa only [position_ext] using congrArg position ((edgeIndex d (W d)).injective h)
  · intro hx
    obtain ⟨p,hp,uniq⟩ := (allChecks_parsimony hd x).1 hx
    let y := fun e => pack x p ((edgeIndex d (W d)).symm e)
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · intro i; simp [y,ext]
    · apply (satisfies_iff hd y).2; simpa [y,ext] using hp
    · rintro z ⟨he,hs⟩
      let w : Wire d := fun e => z (edgeIndex d (W d) e)
      have hE : (fun i => w (extEdge i)) = x := funext he
      have hc : AllChecks x (unpack w) := hE ▸ (satisfies_iff hd z).1 hs
      have hp' := uniq _ hc
      have hw : pack x p = w := by rw [←hp', ←hE, pack_unpack]
      funext e
      obtain ⟨q,rfl⟩ := (edgeIndex d (W d)).surjective e
      change w q = pack x p ((edgeIndex d (W d)).symm ((edgeIndex d (W d)) q))
      rw [Equiv.symm_apply_apply]; exact (congrFun hw q).symm
  · rintro hx ⟨y,he,hs⟩
    apply (allChecks_parsimony hd x).2 hx
    exact ⟨_, funext he ▸ (satisfies_iff hd y).1 hs⟩

end DetDLP.w4_M5PortTensor


