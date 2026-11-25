-- Prove2me | Definitions.Def_DetDLP_S8C_FpQueryCount
-- name    : DetDLP_S8C_FpQueryCount
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:13:00.821204+00:00
-- url     : https://prove2.me/theorems/3c1a91ce-2166-4a1c-8c0e-f2170c3040a5
-- title:
--   Certificate counts for prefix-constrained finite-field queries
-- statement:
--   Filtering the affine-hash and target-product certificates by the original most-significant-bit prefix gives exactly the element and tuple-pair counts of the query semantics.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_S8C_FpAtom
set_option autoImplicit false
namespace DetDLP.S8C
open M89S1

theorem atom_sound {p m : ℕ} [Fact p.Prime] (mul : w3_modMulInterface) (S : FpSeed p m)
    (i : Fin m) (T : ℕ) (u : (ZMod p)ˣ) (r : AtomRun p) (hr : atomOK S i T (w3_fpResidue u) r) :
    u ∈ fpFactorBlock T S i := by
  let a : Fin p := ⟨(S i).1.val+1,by have := (S i).1.isLt; omega⟩
  have he := w3_fpHash_sound (Nat.succ_pos (bitLen p)) (Fact.out : p.Prime).two_le (primeFitsAtom p) mul a
    (S i).2 (w3_fpResidue u) r.1 r.2 hr.2.2
  change r.1.val = w3_fpHashWord S i (w3_fpResidue u).val at he
  exact (residue_mem_iff S i T u).mpr ⟨hr.1,he ▸ hr.2.1⟩

theorem product_sound {p m : ℕ} [Fact p.Prime] (mul : w3_modMulInterface) (ab : UnitPair p m)
    (X : (ZMod p)ˣ) (r : ProductRun p) (hr : productOK ab X r) : (∏ i, ab.1 i * ab.2 i) = X := by
  let Y := ∏ i, ab.1 i * ab.2 i
  obtain ⟨s,hs,_⟩ := (product_iff mul ab Y).mpr rfl
  have out (U : (ZMod p)ˣ) (q : ProductRun p) (hq : productOK ab U q) :=
    w3_checkStages_output (Nat.succ_pos (bitLen p)) (Fact.out : p.Prime).two_le (primeFitsAtom p) mul _ _ _ _ hq
  exact Units.ext (ZMod.val_injective p ((out Y s hs).trans (out X r hr).symm))

/-- Projection from a checked auxiliary certificate to the finite set of semantic witnesses. -/
noncomputable def certEquiv {A C : Type} (F : Finset A) (P : A → C → Prop)
    (sound : ∀ a c, P a c → a ∈ F) (complete : ∀ a ∈ F, ∃! c, P a c) :
    {v : A × C // P v.1 v.2} ≃ ↥F := by
  classical
  refine Equiv.ofBijective (fun v => ⟨v.1.1,sound _ _ v.2⟩) ⟨?_,?_⟩
  · rintro ⟨⟨a,c⟩,hc⟩ ⟨⟨b,d⟩,hd⟩ h
    have hab : a = b := congrArg Subtype.val h
    subst b
    exact Subtype.ext (congrArg (Prod.mk a) ((complete a (sound a c hc)).unique hc hd))
  · rintro ⟨a,ha⟩; obtain ⟨c,hc,_⟩ := complete a ha; exact ⟨⟨(a,c),hc⟩,rfl⟩

abbrev elemWord {p : ℕ} [NeZero p] (u : (ZMod p)ˣ) := digitWord (bitLen p) (u : ZMod p).val

noncomputable def elemSet {p m : ℕ} [Fact p.Prime] (S : FpSeed p m) (i : Fin m) (T : ℕ) (η : List Bool) :=
  (fpFactorBlock T S i).filter fun u => (elemWord u).take η.length = η

def elemOK {p m : ℕ} [Fact p.Prime] (S : FpSeed p m) (i : Fin m) (T : ℕ) (η : List Bool)
    (u : (ZMod p)ˣ) (r : AtomRun p) : Prop := atomOK S i T (w3_fpResidue u) r ∧ (elemWord u).take η.length = η

noncomputable def elemEquiv {p m : ℕ} [Fact p.Prime] (mul : w3_modMulInterface) (S : FpSeed p m)
    (i : Fin m) (T : ℕ) (η : List Bool) :
    {v : (ZMod p)ˣ × AtomRun p // elemOK S i T η v.1 v.2} ≃ ↥(elemSet S i T η) := by
  apply certEquiv
  · rintro u r ⟨hr,hη⟩; exact Finset.mem_filter.mpr ⟨atom_sound mul S i T u r hr,hη⟩
  · intro u hu; obtain ⟨hm,hη⟩ := Finset.mem_filter.mp hu
    obtain ⟨r,hr,ur⟩ := (atom_mem_iff mul S i T u).mpr hm
    exact ⟨r,⟨hr,hη⟩,fun r' h' => ur _ h'.1⟩

theorem elemSet_card {p m : ℕ} [Fact p.Prime] (S : FpSeed p m) (i : Fin m) (T : ℕ) (η : List Bool) :
    Fintype.card ↥(elemSet S i T η) = elemCount (fpFactorBlock T S i) elemWord η := Fintype.card_coe _

abbrev PairRun (p m : ℕ) := (Fin m → AtomRun p) × (Fin m → AtomRun p) × ProductRun p

def pairOK {p m : ℕ} [Fact p.Prime] (S : FpSeed p m) (T : ℕ) (X : (ZMod p)ˣ) (η : List Bool)
    (ab : UnitPair p m) (r : PairRun p m) : Prop :=
  (∀ i, atomOK S i T (w3_fpResidue (ab.1 i)) (r.1 i)) ∧
  (∀ i, atomOK S i T (w3_fpResidue (ab.2 i)) (r.2.1 i)) ∧
  (tupleWord elemWord ab).take η.length = η ∧ productOK ab X r.2.2

noncomputable def pairSet {p m : ℕ} [Fact p.Prime] (S : FpSeed p m) (T : ℕ) (X : (ZMod p)ˣ) (η : List Bool) : Finset (UnitPair p m) := by
  classical exact Finset.univ.filter fun ab => (∀ i, ab.1 i ∈ fpFactorBlock T S i ∧ ab.2 i ∈ fpFactorBlock T S i) ∧
    (tupleWord elemWord ab).take η.length = η ∧ (∏ i, ab.1 i * ab.2 i) = X

noncomputable def pairEquiv {p m : ℕ} [Fact p.Prime] (mul : w3_modMulInterface) (S : FpSeed p m)
    (T : ℕ) (X : (ZMod p)ˣ) (η : List Bool) :
    {v : UnitPair p m × PairRun p m // pairOK S T X η v.1 v.2} ≃ ↥(pairSet S T X η) := by
  classical
  apply certEquiv
  · rintro ab r ⟨ha,hb,hη,hr⟩; exact Finset.mem_filter.mpr ⟨Finset.mem_univ ab,
      fun i => ⟨atom_sound mul S i T _ _ (ha i),atom_sound mul S i T _ _ (hb i)⟩,hη,product_sound mul ab X _ hr⟩
  · intro ab hab
    obtain ⟨_,hm,hη,hx⟩ := Finset.mem_filter.mp hab
    have A := fun i => (atom_mem_iff mul S i T (ab.1 i)).mpr (hm i).1
    have B := fun i => (atom_mem_iff mul S i T (ab.2 i)).mpr (hm i).2
    choose a ha ua using A
    choose b hb ub using B
    obtain ⟨r,hr,ur⟩ := (product_iff mul ab X).mpr hx
    refine ⟨(a,b,r),⟨ha,hb,hη,hr⟩,?_⟩
    rintro ⟨a',b',r'⟩ ⟨ha',hb',_,hr'⟩
    exact Prod.ext (funext fun i => ua i _ (ha' i)) (Prod.ext (funext fun i => ub i _ (hb' i)) (ur _ hr'))

theorem pairSet_card {p m : ℕ} [Fact p.Prime] (S : FpSeed p m) (T : ℕ) (X : (ZMod p)ˣ) (η : List Bool) :
    Fintype.card ↥(pairSet S T X η) = pairCount (fpFactorBlock T S) elemWord (fun ab => (∏ i, ab.1 i * ab.2 i) = X) η :=
  by
    rw [Fintype.card_coe]
    unfold pairCount pairSet
    apply congrArg Finset.card
    apply Finset.ext
    intro ab
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]

end DetDLP.S8C


