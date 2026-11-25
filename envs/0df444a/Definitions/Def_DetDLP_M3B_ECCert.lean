-- Prove2me | Definitions.Def_DetDLP_M3B_ECCert
-- name    : DetDLP_M3B_ECCert
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:04:56.435645+00:00
-- url     : https://prove2.me/theorems/c9ab26dc-12e1-4bf2-b5c9-eed8f4047e0a
-- title:
--   Stage II EC native separator certificate
-- statement:
--   Establishes the parsimonious witness bijection for short-Weierstrass Stage II separator queries.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8H4_ElemTiles
import Definitions.Def_DetDLP_S8M_ECPairWitness
import Definitions.Def_DetDLP_W3_Separator
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
namespace DetDLP.M3B.ECCert
open S8H4 S8M.ECPair S8H.ECPointArithmetic

variable {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
abbrev Point := E.toAffine.Point
variable (F : Fin m → List (Point E))
abbrev base : IndexedFactorBase (Point E) m := ⟨F⟩
abbrev Tuples := (base E F).BlockTuple × (base E F).BlockTuple
variable (S : ECSeed p m) (T : ℕ)
abbrev ListsOK := ∀ i, (F i).Nodup ∧ (F i).toFinset = ecFactorBlock E T S i
abbrev Slot (i : Fin m) := ElemTiles.accepted E S i T (bitLen p) []
abbrev Table := (i : Fin m) → Fin 2 → Bool → Slot E S T i

/-- The inverse of `get` uses the public block list only after the slot has passed
    its curve, parity-selected hash and strict threshold checks. -/
noncomputable def indexEquiv (mul : w3_modMulInterface) (hT : T ≤ p)
    (hF : ListsOK E F S T) (i : Fin m) : Slot E S T i ≃ Fin (F i).length := by
  classical
  refine (ElemTiles.pointEquiv E S i mul T (bitLen p) hT []).trans
    ((Equiv.subtypeEquivRight ?_).trans ((hF i).1.getEquiv (F i)).symm)
  intro A
  rw [← List.mem_toFinset, (hF i).2]
  simp [S8H.ECPointGadget.elemPin, ecFactorBlock]

def split : ((i : Fin m) → Fin 2 → Bool → Fin (F i).length) ≃ Tuples E F where
  toFun s := (fun i j => s i j false, fun i j => s i j true)
  invFun t := fun i j side => if side then t.2 i j else t.1 i j
  left_inv s := by funext i j side; cases side <;> rfl
  right_inv _ := rfl

noncomputable def tableEquiv (mul : w3_modMulInterface) (hT : T ≤ p)
    (hF : ListsOK E F S T) : Table E S T ≃ Tuples E F :=
  (Equiv.piCongrRight fun i => Equiv.piCongrRight fun _ => Equiv.piCongrRight fun _ =>
    indexEquiv E F S T mul hT hF i).trans (split E F)

/-- Interleave the two entries of each block in the same order as `tupleVal`. -/
def factors (X : (base E F).BlockTuple) : List (Point E) :=
  Witness.interleave (fun i => (F i).get (X i 0), fun i => (F i).get (X i 1))

theorem factors_length (X : (base E F).BlockTuple) : (factors E F X).length = 2*m :=
  Witness.interleave_length _

theorem factors_sum (X : (base E F).BlockTuple) : (factors E F X).sum = (base E F).tupleVal X :=
  Witness.interleave_sum _

variable (hp : 3 < p) (P : Point E)
abbrev Joined := Point E × Witness.Trace p × Witness.Trace p
noncomputable def traceOK (a : Point E) (X : (base E F).BlockTuple) (z : Point E)
    (w : Witness.Trace p) : Prop :=
  Witness.ok E (a :: factors E F X) (coords (Witness.sw E hp z)) w

noncomputable def joinedOK (t : Tuples E F) (r : Joined E) : Prop :=
  traceOK E F hp P t.1 r.1 r.2.1 ∧ traceOK E F hp 0 t.2 r.1 r.2.2

theorem trace_sound (mul : w3_modMulInterface) (a : Point E) (X : (base E F).BlockTuple)
    (z : Point E) (w : Witness.Trace p) (hw : traceOK E F hp a X z w) :
    (base E F).tupleVal X + a = z := by
  simpa only [List.sum_cons, factors_sum, add_comm a] using
    (Witness.sound E hp mul a (factors E F X) z w hw)

theorem trace_unique (mul : w3_modMulInterface) (a : Point E) (X : (base E F).BlockTuple)
    (z : Point E) (hz : (base E F).tupleVal X + a = z) : ∃! w, traceOK E F hp a X z w := by
  have he : (a :: factors E F X).sum = z := by simpa [factors_sum, add_comm a] using hz
  unfold traceOK
  rw [← he]
  exact Witness.complete E hp mul a _

theorem joined_sound (mul : w3_modMulInterface) (t : Tuples E F) (r : Joined E)
    (hr : joinedOK E F hp P t r) : (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P := by
  have hx := trace_sound E F hp mul P _ _ _ hr.1
  have hy := trace_sound E F hp mul 0 _ _ _ hr.2
  rw [add_zero] at hy
  exact hy.trans hx.symm

theorem joined_unique (mul : w3_modMulInterface) (t : Tuples E F)
    (he : (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P) :
    ∃! r, joinedOK E F hp P t r := by
  let z := (base E F).tupleVal t.2
  obtain ⟨w, hw, uw⟩ := trace_unique E F hp mul P t.1 z he.symm
  obtain ⟨v, hv, uv⟩ := trace_unique E F hp mul 0 t.2 z (add_zero _)
  refine ⟨(z,w,v), ⟨hw,hv⟩, ?_⟩
  rintro ⟨z',w',v'⟩ ⟨hx,hy⟩
  have hz : z = z' := by simpa only [add_zero] using trace_sound E F hp mul 0 _ _ _ hy
  subst z'
  exact Prod.ext rfl (Prod.ext (uw w' hx) (uv v' hy))

/-- This prefix is the separator's coordinate-list encoding, not the element
    gadget's private sign-tagged encoding. -/
def prefixOK (pre : List Bool) (t : Tuples E F) : Prop :=
  pre <+: w3_tupleWord (base E F) (fun A => (pointCoords A).flatMap (w3_bits (bitLen p))) t.1 t.2

noncomputable def joinedEquiv (mul : w3_modMulInterface) (pre : List Bool) :
    {a : Tuples E F × Joined E // prefixOK E F pre a.1 ∧ joinedOK E F hp P a.1 a.2} ≃
    {t : Tuples E F // (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P ∧ prefixOK E F pre t} := by
  refine Equiv.ofBijective (fun a => ⟨a.1.1, joined_sound E F hp P mul _ _ a.2.2, a.2.1⟩) ⟨?_,?_⟩
  · rintro ⟨⟨t,r⟩,ht,hr⟩ ⟨⟨t',s⟩,ht',hs⟩ h
    obtain rfl : t = t' := congrArg Subtype.val h
    exact Subtype.ext (congrArg (Prod.mk t) ((joined_unique E F hp P mul t
      (joined_sound E F hp P mul t r hr)).unique hr hs))
  · rintro ⟨t,he,ht⟩
    obtain ⟨r,hr,_⟩ := joined_unique E F hp P mul t he
    exact ⟨⟨(t,r),ht,hr⟩,rfl⟩

/-- Erasing all slot and chain witnesses is a bijection, including when the
    prefix is too long or some public block is empty. -/
noncomputable def nativeCertEquiv (mul : w3_modMulInterface) (hT : T ≤ p)
    (hF : ListsOK E F S T) (pre : List Bool) :
    let D := tableEquiv E F S T mul hT hF
    {a : Table E S T × Joined E // prefixOK E F pre (D a.1) ∧ joinedOK E F hp P (D a.1) a.2} ≃
    {t : Tuples E F // (base E F).tupleVal t.2 = (base E F).tupleVal t.1 + P ∧ prefixOK E F pre t} := by
  let D := tableEquiv E F S T mul hT hF
  apply Equiv.trans _ (joinedEquiv E F hp P mul pre)
  exact (Equiv.prodCongr D (Equiv.refl _)).subtypeEquiv (fun _ => Iff.rfl)

end DetDLP.M3B.ECCert


