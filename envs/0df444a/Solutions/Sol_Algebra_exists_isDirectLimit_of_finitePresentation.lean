-- Prove2me | solution 1 for Algebra.exists_isDirectLimit_of_finitePresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/8c860604-f6e7-54fb-9f96-80fd57153df8

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_isDirectLimit_of_finitePresentation

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace C1Aux

open MvPolynomial
open scoped Classical

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

noncomputable def res (s : Finset A) : MvPolynomial A R →ₐ[R] MvPolynomial ↥s R :=
  aeval fun a => if h : a ∈ s then X ⟨a, h⟩ else 0

private noncomputable def _root_.C1Aux.ext (s : Finset A) : MvPolynomial ↥s R →ₐ[R] MvPolynomial A R :=
  rename (fun x : ↥s => (x : A))

p2m_export "C1Aux" "ext"

noncomputable def ev : MvPolynomial A R →ₐ[R] A := aeval (R := R) id

def incl {s s' : Finset A} (h : s ⊆ s') : ↥s → ↥s' := fun x => ⟨x.1, h x.2⟩

theorem res_ext (s : Finset A) (g : MvPolynomial ↥s R) : res (R := R) s (ext s g) = g := by
  have : (res (R := R) s).comp (ext s) = AlgHom.id R _ := by
    apply algHom_ext
    intro x
    rw [AlgHom.comp_apply, ext, rename_X, res, aeval_X, dif_pos x.2, AlgHom.id_apply]
  exact congrArg (fun f : MvPolynomial ↥s R →ₐ[R] MvPolynomial ↥s R => f g) this

theorem res_ext_of_subset {s s' : Finset A} (h : s ⊆ s') (g : MvPolynomial ↥s R) :
    res (R := R) s' (ext s g) = rename (incl h) g := by
  have : (res (R := R) s').comp (ext s) = rename (incl h) := by
    apply algHom_ext
    intro x
    rw [AlgHom.comp_apply, ext, rename_X, res, aeval_X, dif_pos (h x.2), rename_X]
    rfl
  exact congrArg (fun f : MvPolynomial ↥s R →ₐ[R] MvPolynomial ↥s' R => f g) this

theorem ext_rename_incl {s s' : Finset A} (h : s ⊆ s') (g : MvPolynomial ↥s R) :
    ext (R := R) s' (rename (incl h) g) = ext s g := by
  simp only [ext, rename_rename]
  rfl

theorem ev_ext (s : Finset A) (g : MvPolynomial ↥s R) :
    ev (R := R) (ext s g) = aeval (fun x : ↥s => (x : A)) g := by
  simp only [ev, ext, aeval_rename]
  rfl

def Supp (s : Finset A) (f : MvPolynomial A R) : Prop := ext s (res s f) = f

theorem supp_mono {s s' : Finset A} (h : s ⊆ s') {f : MvPolynomial A R} (hf : Supp s f) : Supp s' f := by
  unfold Supp at hf ⊢
  conv_lhs => rw [← hf]
  rw [res_ext_of_subset h, ext_rename_incl, hf]

theorem supp_ext (s : Finset A) (g : MvPolynomial ↥s R) : Supp (R := R) s (ext s g) := by
  unfold Supp
  rw [res_ext]

def Idx (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] : Type u :=
  {p : Finset A × Finset (MvPolynomial A R) // ∀ f ∈ p.2, Supp p.1 f ∧ ev f = 0}

scoped instance : Preorder (Idx R A) where
  le i j := i.1.1 ⊆ j.1.1 ∧ i.1.2 ⊆ j.1.2
  le_refl i := ⟨subset_rfl, subset_rfl⟩
  le_trans i j k hij hjk := ⟨hij.1.trans hjk.1, hij.2.trans hjk.2⟩

scoped instance : Nonempty (Idx R A) := ⟨⟨(∅, ∅), by simp⟩⟩

theorem idx_directed : IsDirected (Idx R A) (· ≤ ·) := by
  constructor
  intro i j
  refine ⟨⟨(i.1.1 ∪ j.1.1, i.1.2 ∪ j.1.2), ?_⟩, ?_, ?_⟩
  · intro f hf
    rcases Finset.mem_union.mp hf with h | h
    · exact ⟨supp_mono Finset.subset_union_left (i.2 f h).1, (i.2 f h).2⟩
    · exact ⟨supp_mono Finset.subset_union_right (j.2 f h).1, (j.2 f h).2⟩
  · exact ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  · exact ⟨Finset.subset_union_right, Finset.subset_union_right⟩

def rel (i : Idx R A) : Ideal (MvPolynomial ↥i.1.1 R) := Ideal.span ((res (R := R) i.1.1) '' (i.1.2 : Set (MvPolynomial A R)))

abbrev Stage (i : Idx R A) : Type u := MvPolynomial ↥i.1.1 R ⧸ rel i

theorem stage_fp (i : Idx R A) : Algebra.FinitePresentation R (Stage i) := by
  classical
  haveI : Algebra.FinitePresentation R (MvPolynomial ↥i.1.1 R) := Algebra.FinitePresentation.mvPolynomial R R _
  have hfg : (rel i).FG := ⟨i.1.2.image (res (R := R) i.1.1), by rw [Finset.coe_image]; rfl⟩
  exact Algebra.FinitePresentation.quotient hfg

theorem rel_le_comap {i j : Idx R A} (h : i ≤ j) :
    rel i ≤ (rel j).comap (rename (R := R) (incl h.1)) := by
  rw [rel, Ideal.span_le]
  rintro _ ⟨f, hf, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, ← res_ext_of_subset h.1, (i.2 f hf).1]
  exact Ideal.subset_span ⟨f, h.2 hf, rfl⟩

private noncomputable def _root_.C1Aux.trans (i j : Idx R A) (h : i ≤ j) : Stage i →ₐ[R] Stage j :=
  Ideal.quotientMapₐ (rel j) (rename (incl h.1)) (rel_le_comap h)

p2m_export "C1Aux" "trans"
theorem trans_mk {i j : Idx R A} (h : i ≤ j) (g : MvPolynomial ↥i.1.1 R) :
    trans i j h (Ideal.Quotient.mk (rel i) g) = Ideal.Quotient.mk (rel j) (rename (incl h.1) g) := rfl

noncomputable def coc (i : Idx R A) : Stage i →ₐ[R] A :=
  Ideal.Quotient.liftₐ (rel i) (aeval fun x : ↥i.1.1 => (x : A)) (by
    intro a ha
    rw [rel] at ha
    refine Submodule.span_induction (p := fun a _ => aeval (fun x : ↥i.1.1 => (x : A)) a = 0) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨f, hf, rfl⟩
      rw [← ev_ext, (i.2 f hf).1]
      exact (i.2 f hf).2
    · simp
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, add_zero]
    · intro r a _ ha
      rw [smul_eq_mul, map_mul, ha, mul_zero])

theorem coc_mk (i : Idx R A) (g : MvPolynomial ↥i.1.1 R) :
    coc i (Ideal.Quotient.mk (rel i) g) = aeval (fun x : ↥i.1.1 => (x : A)) g := rfl

scoped instance : DirectedSystem (fun i : Idx R A => Stage i) fun i j h => ⇑(trans i j h) where
  map_self := by
    intro i x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [trans_mk]
    have : incl (le_refl i).1 = (id : ↥i.1.1 → ↥i.1.1) := funext fun x => Subtype.ext rfl
    rw [this, rename_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [trans_mk, trans_mk, trans_mk, rename_rename]
    rfl

theorem isDirectLimit :
    IsDirectLimit (fun (i j : Idx R A) h => ⇑(trans i j h)) fun i => ⇑(coc i) where
  surj := by
    intro a
    let i : Idx R A := ⟨({a}, ∅), by simp⟩
    refine ⟨i, Ideal.Quotient.mk (rel i) (X ⟨a, Finset.mem_singleton_self a⟩), ?_⟩
    rw [coc_mk, aeval_X]
  compatibility := by
    intro i j hij x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [trans_mk, coc_mk, coc_mk, aeval_rename]
    rfl
  inj := by
    intro i j mi mj hm
    obtain ⟨gi, rfl⟩ := Ideal.Quotient.mk_surjective mi
    obtain ⟨gj, rfl⟩ := Ideal.Quotient.mk_surjective mj
    rw [coc_mk, coc_mk] at hm

    set g : MvPolynomial A R := ext i.1.1 gi - ext j.1.1 gj with hg
    have hg_ev : ev (R := R) g = 0 := by
      rw [hg, map_sub, ev_ext, ev_ext, hm, sub_self]
    have hsub_i : i.1.1 ⊆ i.1.1 ∪ j.1.1 := Finset.subset_union_left
    have hsub_j : j.1.1 ⊆ i.1.1 ∪ j.1.1 := Finset.subset_union_right
    have hg_supp : Supp (i.1.1 ∪ j.1.1) g := by
      unfold Supp
      rw [hg, map_sub, map_sub, res_ext_of_subset hsub_i, res_ext_of_subset hsub_j, ext_rename_incl, ext_rename_incl]
    let k : Idx R A := ⟨(i.1.1 ∪ j.1.1, insert g (i.1.2 ∪ j.1.2)), by
      intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hf
      · exact ⟨hg_supp, hg_ev⟩
      · rcases Finset.mem_union.mp hf with h | h
        · exact ⟨supp_mono hsub_i (i.2 f h).1, (i.2 f h).2⟩
        · exact ⟨supp_mono hsub_j (j.2 f h).1, (j.2 f h).2⟩⟩
    have hik : i ≤ k := ⟨hsub_i, fun f hf => Finset.mem_insert_of_mem (Finset.mem_union_left _ hf)⟩
    have hjk : j ≤ k := ⟨hsub_j, fun f hf => Finset.mem_insert_of_mem (Finset.mem_union_right _ hf)⟩
    refine ⟨k, hik, hjk, ?_⟩
    rw [trans_mk, trans_mk]
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    have : rename (incl hik.1) gi - rename (incl hjk.1) gj = res (R := R) k.1.1 g := by
      rw [hg, map_sub, res_ext_of_subset hsub_i, res_ext_of_subset hsub_j]
    rw [this]
    exact Ideal.subset_span ⟨g, Finset.mem_insert_self g _, rfl⟩

end C1Aux
p2m_reactivate "P2MW.S_Algebra_exists_isDirectLimit_of_finitePresentation.C1Aux"

end
p2m_reactivate "P2MW.S_Algebra_exists_isDirectLimit_of_finitePresentation.C1Aux"

open C1Aux in
theorem solution
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : Nonempty ι) (_ : IsDirected ι (· ≤ ·))
      (S : ι → Type u) (_ : ∀ i, CommRing (S i)) (_ : ∀ i, Algebra R (S i))
      (_ : ∀ i, Algebra.FinitePresentation R (S i))
      (t : ∀ i j : ι, i ≤ j → (S i →ₐ[R] S j)) (c : ∀ i, S i →ₐ[R] A)
      (_ : DirectedSystem S fun i j h => ⇑(t i j h)),
      IsDirectLimit (fun i j h => ⇑(t i j h)) fun i => ⇑(c i) := by
  classical
  exact ⟨Idx R A, inferInstance, inferInstance, idx_directed, fun i => Stage i, inferInstance, inferInstance,
    fun i => stage_fp i, trans, coc, inferInstance, isDirectLimit⟩

end S_Algebra_exists_isDirectLimit_of_finitePresentation
end P2MW
export P2MW.S_Algebra_exists_isDirectLimit_of_finitePresentation (solution)
