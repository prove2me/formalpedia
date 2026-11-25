-- Prove2me | Definitions.Def_DetDLP_S8J_HashGatePoly
-- name    : DetDLP_S8J_HashGatePoly
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:51:29.42437+00:00
-- url     : https://prove2.me/theorems/ea54da9f-5e9b-419d-bbbf-fa70d7b5340a
-- title:
--   Hash-gate layout polynomial interfaces and witness equivalences
-- statement:
--   Reusable polynomial-time numeric endpoint and gate-check adapters for established multiplication and hash layouts, together with equivalences capturing uniqueness of hash-gate auxiliary assignments and subtraction comparison witnesses.
-- source:
--   S. Liu, B. Zhang, and K. Ren, “A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem”, Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8J_HashGateLayout
import Definitions.Def_DetDLP_W4_M5Evaluator

set_option autoImplicit false
namespace DetDLP.S8J.HashGatePoly
open Groundwork Groundwork.PolyT
open DetDLP

/-- Numeric source endpoint of the established W4 multiplication graph. -/
def mulLayoutSrc (d e : ℕ) : ℕ := w4_M5EdgeNat.srcNat d e
/-- Numeric destination endpoint of the established W4 multiplication graph. -/
def mulLayoutDst (d e : ℕ) : ℕ := w4_M5EdgeNat.dstNat d e
/-- Gate evaluator for the existing multiplication tensor, indexed by its port word. -/
def mulLayoutCheck (d : ℕ) (g : ℕ) (portBits : List Bool) : Bool :=
  w4_M5Dispatch.evalNat (List.replicate d ()) g portBits

/-- Numeric source endpoint of an addition layout edge. -/
def addLayoutSrc (d : ℕ) (e : Fin (d*5)) : ℕ :=
  ((S8C.AddLayout.layout d).gate e).val
/-- Numeric destination endpoint of an addition layout edge. -/
def addLayoutDst (d : ℕ) (e : Fin (d*5)) : ℕ :=
  ((S8C.AddLayout.layout d).bit e).val
/-- Structural validity check for a flattened addition-layout port assignment. -/
def addLayoutCheck (d g : ℕ) (portBits : List Bool) : Bool :=
  decide (g < d) && decide (d > 0) && decide (portBits.length = d*4)

/-- Numeric source endpoint adapter for the hash-gate layout. -/
def hashLayoutSrc (d e : ℕ) : ℕ := mulLayoutSrc d e
/-- Numeric destination endpoint adapter for the hash-gate layout. -/
def hashLayoutDst (d e : ℕ) : ℕ := mulLayoutDst d e
/-- Gate-check adapter for the hash-gate layout. -/
def hashLayoutCheck (d g : ℕ) (portBits : List Bool) : Bool := mulLayoutCheck d g portBits

section Polynomial
variable {α : Type} [Enc α]
variable {d e g : α → ℕ} {portBits : α → List Bool}
 theorem mulLayoutSrc_poly (hd : PolyT d) (he : PolyT e) :
    PolyT (fun x => mulLayoutSrc (d x) (e x)) := w4_M5EdgeNat.srcNat_poly hd he
 theorem mulLayoutDst_poly (hd : PolyT d) (he : PolyT e) :
    PolyT (fun x => mulLayoutDst (d x) (e x)) := w4_M5EdgeNat.dstNat_poly hd he
 theorem mulLayoutCheck_poly (hu : Unary d) (hg : PolyT g) (ha : PolyT portBits) :
    PolyT (fun x => mulLayoutCheck (d x) (g x) (portBits x)) := by
  exact w4_M5Dispatch.evalNat_poly (q := fun x => List.replicate (d x) ()) hu hg ha
 theorem hashLayoutSrc_poly (hd : PolyT d) (he : PolyT e) :
    PolyT (fun x => hashLayoutSrc (d x) (e x)) := mulLayoutSrc_poly hd he
 theorem hashLayoutDst_poly (hd : PolyT d) (he : PolyT e) :
    PolyT (fun x => hashLayoutDst (d x) (e x)) := mulLayoutDst_poly hd he
 theorem hashLayoutCheck_poly (hu : Unary d) (hg : PolyT g) (ha : PolyT portBits) :
    PolyT (fun x => hashLayoutCheck (d x) (g x) (portBits x)) := mulLayoutCheck_poly hu hg ha
end Polynomial

namespace HashWitness
open HashGateLayout

/-- Accepted hash witness bit assignments are equivalent to a singleton witness
condition; uniqueness is supplied by `w3_slotHash_spec`. -/
noncomputable def bitsEquivCheck {d p a b x z : ℕ} (hd : 1 ≤ d)
    (hp : p < 2^d) (hb : b < p) (hz : z < p)
    (r : w3_fpHashCert d p hd) :
    {w : w3_slotHashAux d // w3_slotHashBits hd a b x z r w} ≃
      {_h : w3_fpHashCheck hd a b x z r // True} := by
  let H := w3_slotHash_spec (a := a) (x := x) hd hp hb hz r
  apply Equiv.ofBijective (fun w => ⟨H.1 w.1 w.2, True.intro⟩)
  constructor
  · intro w v _
    apply Subtype.ext
    exact (H.2 (H.1 w.1 w.2)).unique w.2 v.2
  · rintro ⟨h, _⟩
    obtain ⟨w, hw, _⟩ := H.2 h
    exact ⟨⟨w,hw⟩, Subtype.ext (Subsingleton.elim _ _)⟩

/-- The subtraction witnesses for `w3_slotLt` are equivalent to the comparison
predicate, with the unique subtraction word supplied by `w3_slotLt_spec`. -/
noncomputable def ltWitnessEquiv {d u B : ℕ} (hu : u < 2^d) (hB : B ≤ 2^d) :
    {r : w3_slotDiff d // w3_slotLt d u B r} ≃ {_h : u < B // True} := by
  let H := w3_slotLt_spec hu hB
  apply Equiv.ofBijective (fun r => ⟨H.1 r.1 r.2, True.intro⟩)
  constructor
  · intro r s _
    apply Subtype.ext
    exact (H.2 (H.1 r.1 r.2)).unique r.2 s.2
  · rintro ⟨h, _⟩
    obtain ⟨r,hr,_⟩ := H.2 h
    exact ⟨⟨r,hr⟩, Subtype.ext (Subsingleton.elim _ _)⟩

end HashWitness
end DetDLP.S8J.HashGatePoly


