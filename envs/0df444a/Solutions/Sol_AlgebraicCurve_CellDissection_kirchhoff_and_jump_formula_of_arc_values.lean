-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.kirchhoff_and_jump_formula_of_arc_values
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/0f5dc29d-5afd-51ce-81f0-13bf8b28b2be

import Definitions.Def_AlgebraicCurve_CellDissection
import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Cell CellDissection Place.evalAt Place IsCurveOver"
namespace Cell
p2m_export "AlgebraicCurve.Cell" "arc hKt R"
p2m_open "AlgebraicCurve.Cell AlgebraicCurve"
variable {F : Type*} [Field F] [Algebra ℂ F] [TopologicalSpace (Place ℂ F)]
  [ChartedSpace ℂ (Place ℂ F)]

private def _root_.AlgebraicCurve.Cell.U (C : Cell F) : Set ℂ := C.ζ.target
p2m_export "AlgebraicCurve.Cell" "U"
theorem hU (C : Cell F) : IsOpen C.U := C.ζ.open_target
theorem hKU (C : Cell F) : C.R.K ⊆ C.U := C.hKt
theorem hUt (C : Cell F) : C.U ⊆ C.ζ.target := fun _ h => h
end AlgebraicCurve.Cell

section Part_book

namespace CellPeriods

p2m_open "Complex MeasureTheory Set Filter intervalIntegral AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values.AlgebraicCurve"
open scoped Real Topology Interval Manifold ContDiff

section Arc

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

end Arc

section Edge

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end Edge

section Global

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

private noncomputable abbrev _root_.CellPeriods.arcOf (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) :
    Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N :=
  𝒟.arcOf q

p2m_export "CellPeriods" "arcOf"
omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem side_arcOf (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) :
    𝒟.side (arcOf 𝒟 q).1 (arcOf 𝒟 q).2 = q :=
  Function.surjInv_eq (f := fun p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) => 𝒟.side p.1 p.2)
    𝒟.side_bij.surjective q

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem arcOf_side (𝒟 : AlgebraicCurve.CellDissection F) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :
    arcOf 𝒟 (𝒟.side p.1 p.2) = p :=
  Function.leftInverse_surjInv 𝒟.side_bij p

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

end Global

end CellPeriods

end Part_book

section Part_cycles

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Cycles

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

def FlowDecomp (A : Type*) [AddCommGroup A] (𝒟 : AlgebraicCurve.CellDissection F) (𝒯 : Finset 𝒟.ιE)
    (Z : 𝒟.ιE → 𝒟.ιE → ℤ) : Prop :=
  ∀ f : 𝒟.ιE → A,
    (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
    ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j

variable {κ : Type*}

end Cycles

end CellPeriods

end Part_cycles

section Part_wordid

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section WordId

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

variable {κ : Type*} {𝒟 : AlgebraicCurve.CellDissection F} {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ}
  {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

def endV (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1

def startV (𝒟 : AlgebraicCurve.CellDissection F) (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2

end WordId

end CellPeriods

end Part_wordid

section Part_chords

namespace CellPeriods

section Chords

variable {E : Type*} [Fintype E] [DecidableEq E] {𝒯s : Finset E} {m : ℕ} [NeZero m]

def wordChain (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e : E) (he : e ∉ 𝒯s) (f : E) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
      (i - wd.symm ⟨(e, true), he⟩).val <
        (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
    (if (wd i).1.2 then (1 : ℤ) else -1) * (if (wd i).1.1 = f then 1 else 0)

omit [Fintype E] in
theorem wordChain_of_mem (wd : ZMod m ≃ {q : E × Bool // q.1 ∉ 𝒯s}) (e : E) (he : e ∉ 𝒯s)
    {f : E} (hf : f ∈ 𝒯s) : wordChain wd e he f = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have h : ¬ (wd i).1.1 = f := fun h => (wd i).2 (h ▸ hf)
  rw [if_neg h, mul_zero]

end Chords

end CellPeriods

end Part_chords

section Part_identity

namespace CellPeriods

p2m_open "Complex Set Filter AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values.AlgebraicCurve"
open scoped Real Topology Manifold ContDiff

section Identity

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] [T2Space (Place ℂ F)]
variable [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)]

variable
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))

variable {κ : Type*} [Fintype κ]
variable {𝒟 : AlgebraicCurve.CellDissection F}

variable {η : κ → Ω[F⁄ℂ]} {V : 𝒟.ιC → Set ℂ} {Ψ : κ → 𝒟.ιC → ℂ → ℂ}

noncomputable def wordMatrix {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) (j l : 𝒟.ιE) : ℤ :=
  if hj : j ∉ 𝒯s then wordChain wd j hj l else 0

omit [IsCurveOver ℂ F] [Algebra.EssFiniteType ℂ F] [T2Space (Place ℂ F)]
  [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] in
theorem wordMatrix_of_not_mem {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) {j : 𝒟.ιE} (hj : j ∉ 𝒯s) (l : 𝒟.ιE) :
    wordMatrix wd j l = wordChain wd j hj l := by
  simp [wordMatrix, hj]

end Identity

end CellPeriods

end Part_identity

section Part_g2comb

namespace CellPeriods

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values.AlgebraicCurve"

section Comb

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
variable (𝒟 : AlgebraicCurve.CellDissection F)
variable {𝔸 : Type*} [AddCommGroup 𝔸]

def sv (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : 𝒟.ιV := startV 𝒟 (𝒟.side p.1 p.2)

def ev (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) : 𝒟.ιV := endV 𝒟 (𝒟.side p.1 p.2)

theorem sv_arcOf (q : 𝒟.ιE × Bool) : sv 𝒟 (arcOf 𝒟 q) = startV 𝒟 q := by
  simp [sv, side_arcOf]

theorem ev_arcOf (q : 𝒟.ιE × Bool) : ev 𝒟 (arcOf 𝒟 q) = endV 𝒟 q := by
  simp [ev, side_arcOf]

structure ArcValues (A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸) (I J : 𝒟.ιE → 𝔸)
    (rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N) : Prop where
  hW : ∀ p, B p - A p = if (𝒟.side p.1 p.2).2 then I (𝒟.side p.1 p.2).1 else -I (𝒟.side p.1 p.2).1
  hbij : ∀ C, Function.Bijective (rot C)
  hrot : ∀ C k, ev 𝒟 ⟨C, k⟩ = sv 𝒟 ⟨C, rot C k⟩
  hC : ∀ C k, A ⟨C, rot C k⟩ = B ⟨C, k⟩
  hJ1 : ∀ e, J e = B (arcOf 𝒟 (e, true)) - A (arcOf 𝒟 (e, false))
  hJ2 : ∀ e, J e = A (arcOf 𝒟 (e, true)) - B (arcOf 𝒟 (e, false))
  hinj : ∀ C, Function.Injective fun k : Fin (𝒟.cell C).R.N => sv 𝒟 ⟨C, k⟩

variable {𝒟}
variable {A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸} {I J : 𝒟.ιE → 𝔸}
variable {rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N}

theorem ArcValues.kirchhoff (h : ArcValues 𝒟 A B I J rot) (v : 𝒟.ιV) :
    (∑ e with (𝒟.ends e).2 = v, J e) = ∑ e with (𝒟.ends e).1 = v, J e := by
  classical
  rw [← sub_eq_zero, Finset.sum_filter, Finset.sum_filter]

  have hl : (∑ e, if (𝒟.ends e).2 = v then J e else 0) - ∑ e, (if (𝒟.ends e).1 = v then J e else 0) =
      (∑ q : 𝒟.ιE × Bool, if endV 𝒟 q = v then B (arcOf 𝒟 q) else 0) -
        ∑ q : 𝒟.ιE × Bool, if startV 𝒟 q = v then A (arcOf 𝒟 q) else 0 := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, endV, startV, if_true, Bool.false_eq_true, if_false]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h2 : (𝒟.ends e).2 = v <;> by_cases h1 : (𝒟.ends e).1 = v <;>
      simp only [h2, h1, if_true, if_false] <;>
      [rw [sub_self, show B (arcOf 𝒟 (e, true)) + B (arcOf 𝒟 (e, false)) -
            (A (arcOf 𝒟 (e, true)) + A (arcOf 𝒟 (e, false))) =
          (B (arcOf 𝒟 (e, true)) - A (arcOf 𝒟 (e, false))) -
            (A (arcOf 𝒟 (e, true)) - B (arcOf 𝒟 (e, false))) by abel, ← h.hJ1 e, ← h.hJ2 e,
          sub_self];
        (rw [h.hJ1 e]; abel); (rw [h.hJ2 e]; abel); abel]
  rw [hl]

  have hB : (∑ q : 𝒟.ιE × Bool, if endV 𝒟 q = v then B (arcOf 𝒟 q) else 0) =
      ∑ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), if ev 𝒟 p = v then B p else 0 := by
    rw [← Function.Bijective.sum_comp 𝒟.side_bij]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [arcOf_side]; rfl
  have hA : (∑ q : 𝒟.ιE × Bool, if startV 𝒟 q = v then A (arcOf 𝒟 q) else 0) =
      ∑ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), if sv 𝒟 p = v then A p else 0 := by
    rw [← Function.Bijective.sum_comp 𝒟.side_bij]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [arcOf_side]; rfl
  rw [hB, hA, Fintype.sum_sigma, Fintype.sum_sigma, ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun C _ => ?_
  rw [sub_eq_zero]

  rw [← Function.Bijective.sum_comp (h.hbij C) (fun k => if sv 𝒟 ⟨C, k⟩ = v then A ⟨C, k⟩ else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [h.hrot C k, h.hC C k]

open scoped Classical in

noncomputable def vval (𝒟 : AlgebraicCurve.CellDissection F) (A : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸)
    (C : 𝒟.ιC) (v : 𝒟.ιV) : 𝔸 :=
  ∑ k : Fin (𝒟.cell C).R.N, if sv 𝒟 ⟨C, k⟩ = v then A ⟨C, k⟩ else 0

theorem ArcValues.vval_sv (h : ArcValues 𝒟 A B I J rot) (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N) :
    vval 𝒟 A C (sv 𝒟 ⟨C, k⟩) = A ⟨C, k⟩ := by
  classical
  unfold vval
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hne
    rw [if_neg]
    exact fun heq => hne (h.hinj C heq)
  · simp

theorem ArcValues.B_eq_vval (h : ArcValues 𝒟 A B I J rot) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :
    B p = vval 𝒟 A p.1 (ev 𝒟 p) := by
  obtain ⟨C, k⟩ := p
  rw [h.hrot C k, h.vval_sv, h.hC]

theorem ArcValues.A_eq_vval (h : ArcValues 𝒟 A B I J rot) (p : Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :
    A p = vval 𝒟 A p.1 (sv 𝒟 p) := by
  obtain ⟨C, k⟩ := p
  rw [h.vval_sv]

theorem ArcValues.vval_eq_of_link (h : ArcValues 𝒟 A B I J rot) {g : 𝒟.ιE} (hg : J g = 0)
    {v : 𝒟.ιV} (hv : v = (𝒟.ends g).1 ∨ v = (𝒟.ends g).2) {D D' : 𝒟.ιC}
    (hDD' : ((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
      ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) :
    vval 𝒟 A D v = vval 𝒟 A D' v := by
  have hkey : vval 𝒟 A (arcOf 𝒟 (g, true)).1 v = vval 𝒟 A (arcOf 𝒟 (g, false)).1 v := by
    rcases hv with rfl | rfl
    ·
      have h1 : A (arcOf 𝒟 (g, true)) = vval 𝒟 A (arcOf 𝒟 (g, true)).1 (𝒟.ends g).1 := by
        rw [h.A_eq_vval, sv_arcOf]; rfl
      have h2 : B (arcOf 𝒟 (g, false)) = vval 𝒟 A (arcOf 𝒟 (g, false)).1 (𝒟.ends g).1 := by
        rw [h.B_eq_vval, ev_arcOf]; rfl
      rw [← h1, ← h2]
      exact sub_eq_zero.1 ((h.hJ2 g).symm.trans hg)
    ·
      have h1 : B (arcOf 𝒟 (g, true)) = vval 𝒟 A (arcOf 𝒟 (g, true)).1 (𝒟.ends g).2 := by
        rw [h.B_eq_vval, ev_arcOf]; rfl
      have h2 : A (arcOf 𝒟 (g, false)) = vval 𝒟 A (arcOf 𝒟 (g, false)).1 (𝒟.ends g).2 := by
        rw [h.A_eq_vval, sv_arcOf]; rfl
      rw [← h1, ← h2]
      exact sub_eq_zero.1 ((h.hJ1 g).symm.trans hg)
  rcases hDD' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hkey
  · exact hkey.symm

theorem ArcValues.corner (h : ArcValues 𝒟 A B I J rot) {𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {q q' : 𝒟.ιE × Bool} (hv : endV 𝒟 q = startV 𝒟 q')
    (hcs : ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 q).1 ∧
      cs.getLast? = some (arcOf 𝒟 q').1 ∧
      cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
        (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
          ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
        (endV 𝒟 q = (𝒟.ends g).1 ∨ endV 𝒟 q = (𝒟.ends g).2))) :
    B (arcOf 𝒟 q) = A (arcOf 𝒟 q') := by
  obtain ⟨cs, hhd, hlast, hch⟩ := hcs
  rw [h.B_eq_vval, h.A_eq_vval, ev_arcOf, sv_arcOf, ← hv]
  set v := endV 𝒟 q with hvdef
  have hall : ∀ D ∈ cs, vval 𝒟 A D v = vval 𝒟 A (arcOf 𝒟 q).1 v := by
    refine hch.induction (fun D => vval 𝒟 A D v = vval 𝒟 A (arcOf 𝒟 q).1 v) cs ?_ ?_
    · rintro D D' ⟨g, hg, hDD', hvg⟩ hD
      rw [← hD]
      exact (h.vval_eq_of_link (hJ0 g hg) hvg hDD').symm
    · intro hne
      obtain ⟨ys, rfl⟩ := List.head?_eq_some_iff.1 hhd
      rfl
  exact (hall _ (List.mem_of_getLast? hlast)).symm

def sgn (q : 𝒟.ιE × Bool) : ℤ := if q.2 then 1 else -1

theorem ArcValues.B_sub_A (h : ArcValues 𝒟 A B I J rot) (q : 𝒟.ιE × Bool) :
    B (arcOf 𝒟 q) - A (arcOf 𝒟 q) = sgn q • I q.1 := by
  have := h.hW (arcOf 𝒟 q)
  rw [side_arcOf] at this
  rw [this, sgn]
  split_ifs <;> simp

theorem ArcValues.word_identity (h : ArcValues 𝒟 A B I J rot) {𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
        cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
            ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
          (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2)))
    (j : 𝒟.ιE) (hj : j ∉ 𝒯s) :
    J j = -∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
        (i - wd.symm ⟨(j, true), hj⟩).val < (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
      sgn (wd i).1 • I (wd i).1.1 := by
  classical
  set α : ZMod m := wd.symm ⟨(j, true), hj⟩ with hα
  set β : ZMod m := wd.symm ⟨(j, false), hj⟩ with hβ
  set D : ℕ := (β - α).val with hD
  have hαβ : α ≠ β := by
    intro h'
    have := wd.symm.injective (hα.symm.trans (h'.trans hβ))
    simp at this
  have hD0 : 0 < D := by
    rw [hD, Nat.pos_iff_ne_zero]
    intro h0
    exact hαβ (eq_of_sub_eq_zero ((ZMod.val_eq_zero _).1 h0)).symm
  have hwdα : (wd α).1 = (j, true) := by rw [hα, Equiv.apply_symm_apply]
  have hwdβ : (wd β).1 = (j, false) := by rw [hβ, Equiv.apply_symm_apply]
  set T : ZMod m → 𝔸 := fun i => sgn (wd i).1 • I (wd i).1.1 with hT

  have htel : ∀ d : ℕ, 1 ≤ d → d ≤ D →
      A (arcOf 𝒟 (wd (α + d)).1) = B (arcOf 𝒟 (j, true)) + ∑ d' ∈ Finset.Ico 1 d, T (α + d') := by
    intro d hd1 hdD
    induction d with
    | zero => omega
    | succ d ih =>
      rcases Nat.eq_zero_or_pos d with rfl | hdpos
      · simp only [zero_add, Nat.cast_one, Finset.Ico_self, Finset.sum_empty, add_zero]
        rw [← hwdα]
        exact (h.corner hJ0 (hW1 α).1 (hW1 α).2).symm
      · have ih' := ih hdpos (by omega)
        rw [Finset.sum_Ico_succ_top hdpos, ← add_assoc, ← ih']
        have hc := h.corner hJ0 (hW1 (α + d)).1 (hW1 (α + d)).2
        have hstep := h.B_sub_A (wd (α + d)).1
        push_cast
        rw [← add_assoc, ← hc, hT]
        simp only
        rw [← hstep]
        abel
  have hαD : α + (D : ZMod m) = β := by
    rw [hD, ZMod.natCast_zmod_val]; abel
  have hfinal := htel D hD0 le_rfl
  rw [hαD, hwdβ] at hfinal

  rw [h.hJ1 j, hfinal]
  have hsum : ∑ d' ∈ Finset.Ico 1 D, T (α + d') =
      ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ α ∧ (i - α).val < D), T i := by
    refine Finset.sum_nbij' (fun d' => α + (d' : ZMod m)) (fun i => (i - α).val) ?_ ?_ ?_ ?_ ?_
    · intro d' hd'
      rw [Finset.mem_Ico] at hd'
      have hd'm : d' < m := by have := ZMod.val_lt (β - α); omega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, add_sub_cancel_left,
        ZMod.val_cast_of_lt hd'm]
      refine ⟨fun h' => ?_, hd'.2⟩
      have : ((d' : ℕ) : ZMod m) = 0 := by
        have := congrArg (· - α) h'; simpa using this
      rw [ZMod.natCast_eq_zero_iff] at this
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_Ico]
      refine ⟨Nat.one_le_iff_ne_zero.2 fun h0 => hi.1 ?_, hi.2⟩
      exact eq_of_sub_eq_zero ((ZMod.val_eq_zero _).1 h0)
    · intro d' hd'
      rw [Finset.mem_Ico] at hd'
      have hd'm : d' < m := by have := ZMod.val_lt (β - α); omega
      simp only [add_sub_cancel_left, ZMod.val_cast_of_lt hd'm]
    · intro i hi
      simp only [ZMod.natCast_zmod_val, add_sub_cancel]
    · intro d' hd'
      rfl
  rw [hsum]
  simp only [hT]
  abel

def zvA (Z : 𝒟.ιE → 𝒟.ιE → ℤ) (I : 𝒟.ιE → 𝔸) (l : 𝒟.ιE) : 𝔸 := ∑ e, Z l e • I e

omit [AddCommGroup 𝔸] in
theorem sum_word_eq_sum_wordChainA [AddCommGroup 𝔸] {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) (j : 𝒟.ιE) (hj : j ∉ 𝒯s) (I : 𝒟.ιE → 𝔸) :
    ∑ i ∈ Finset.univ.filter (fun i : ZMod m => i ≠ wd.symm ⟨(j, true), hj⟩ ∧
        (i - wd.symm ⟨(j, true), hj⟩).val <
          (wd.symm ⟨(j, false), hj⟩ - wd.symm ⟨(j, true), hj⟩).val),
      sgn (wd i).1 • I (wd i).1.1 =
    ∑ f, wordChain wd j hj f • I f := by
  classical
  simp only [wordChain, sgn]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem sum_chain_smulA {𝒯 : Finset 𝒟.ιE} {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (p : 𝒟.ιE → ℤ)
    (hp : ∀ w, (∑ e with (𝒟.ends e).2 = w, p e) = ∑ e with (𝒟.ends e).1 = w, p e)
    (I : 𝒟.ιE → 𝔸) :
    ∑ f, p f • I f = ∑ l ∈ 𝒯ᶜ, p l • zvA Z I l := by
  classical
  have hdec : ∀ f, p f = ∑ l ∈ 𝒯ᶜ, Z l f • p l := hZ p hp
  calc ∑ f, p f • I f = ∑ f, ∑ l ∈ 𝒯ᶜ, (Z l f * p l) • I f := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        rw [hdec f]
        simp
    _ = ∑ l ∈ 𝒯ᶜ, ∑ f, (Z l f * p l) • I f := Finset.sum_comm
    _ = ∑ l ∈ 𝒯ᶜ, p l • zvA Z I l := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [zvA, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [mul_comm]

theorem ArcValues.jump_formula (h : ArcValues 𝒟 A B I J rot) {𝒯 𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    {m : ℕ} [NeZero m] (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
        cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
            ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
          (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2)))
    (hW3 : ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
      (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
        ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f)
    (j : 𝒟.ιE) (hj : j ∉ 𝒯s) :
    J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, wordMatrix wd j l • zvA Z I l := by
  classical
  rw [h.word_identity hJ0 wd hW1 j hj, sum_word_eq_sum_wordChainA wd j hj,
    sum_chain_smulA hZ _ (hW3 j hj) I]
  congr 1
  rw [Finset.compl_union]
  have h0 : ∀ l ∈ 𝒯ᶜ, l ∉ 𝒯ᶜ ∩ 𝒯sᶜ → wordChain wd j hj l • zvA Z I l = 0 := by
    intro l hl hl'
    have hls : l ∈ 𝒯s := by
      by_contra h'
      exact hl' (Finset.mem_inter.2 ⟨hl, Finset.mem_compl.2 h'⟩)
    rw [wordChain_of_mem wd j hj hls, zero_smul]
  rw [← Finset.sum_subset Finset.inter_subset_left h0]
  exact Finset.sum_congr rfl fun l _ => by rw [wordMatrix_of_not_mem wd hj]

theorem ArcValues.jump_mem_closure (h : ArcValues 𝒟 A B I J rot) {𝒯 𝒯s : Finset 𝒟.ιE}
    (hJ0 : ∀ e ∈ 𝒯s, J e = 0) {Z : 𝒟.ιE → 𝒟.ιE → ℤ} (hZ : FlowDecomp ℤ 𝒟 𝒯 Z)
    (hZA : FlowDecomp 𝔸 𝒟 𝒯 Z)
    {m : ℕ} [NeZero m] (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, endV 𝒟 (wd i).1 = startV 𝒟 (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (arcOf 𝒟 (wd i).1).1 ∧
        cs.getLast? = some (arcOf 𝒟 (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((arcOf 𝒟 (g, true)).1 = D ∧ (arcOf 𝒟 (g, false)).1 = D') ∨
            ((arcOf 𝒟 (g, true)).1 = D' ∧ (arcOf 𝒟 (g, false)).1 = D)) ∧
          (endV 𝒟 (wd i).1 = (𝒟.ends g).1 ∨ endV 𝒟 (wd i).1 = (𝒟.ends g).2)))
    (hW3 : ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
      (∑ f with (𝒟.ends f).2 = w, wordChain wd e he f) =
        ∑ f with (𝒟.ends f).1 = w, wordChain wd e he f) (f : 𝒟.ιE) :
    J f ∈ AddSubgroup.closure ((zvA Z I) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE)) := by
  classical
  rw [hZA J h.kirchhoff f]
  refine AddSubgroup.sum_mem _ fun j hj => ?_
  by_cases hjs : j ∈ 𝒯s
  · rw [hJ0 j hjs, smul_zero]; exact zero_mem _
  · refine AddSubgroup.zsmul_mem _ ?_ _
    rw [h.jump_formula hJ0 hZ wd hW1 hW3 j hjs]
    refine AddSubgroup.neg_mem _ (AddSubgroup.sum_mem _ fun l hl => ?_)
    have hmem : zvA Z I l ∈ (zvA Z I) '' ((𝒯 ∪ 𝒯s)ᶜ : Finset 𝒟.ιE) := ⟨l, hl, rfl⟩
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure hmem) _

end Comb

end CellPeriods

end Part_g2comb

open scoped Manifold ContDiff Topology Real
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values.AlgebraicCurve Complex Set"

universe u

theorem CellPeriods.image_finset_eq_range_comb {α β : Type*} (f : α → β) (s : Finset α) :
    f '' (s : Set α) = Set.range (fun l : s => f l) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, Finset.mem_coe.1 ha⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨a, Finset.mem_coe.2 ha, rfl⟩

theorem solution
    {F : Type u} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (𝒟 : CellDissection F) (𝔸 : Type) [AddCommGroup 𝔸]
    (A B : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) → 𝔸) (I J : 𝒟.ιE → 𝔸)
    (rot : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → Fin (𝒟.cell C).R.N)
    (𝒯 𝒯s : Finset 𝒟.ιE) (Z : 𝒟.ιE → 𝒟.ιE → ℤ)
    (m : ℕ) [NeZero m] (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}) :
    let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
    let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
    let pe : ∀ e : 𝒟.ιE, e ∉ 𝒯s → 𝒟.ιE → ℤ := fun e he e' =>
      ∑ i ∈ Finset.univ.filter
          (fun i : ZMod m => i ≠ wd.symm ⟨(e, true), he⟩ ∧
            (i - wd.symm ⟨(e, true), he⟩).val <
              (wd.symm ⟨(e, false), he⟩ - wd.symm ⟨(e, true), he⟩).val),
        (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
    (∀ p, B p - A p =
      if (𝒟.side p.1 p.2).2 then I (𝒟.side p.1 p.2).1 else -I (𝒟.side p.1 p.2).1) →
    (∀ C, Function.Bijective (rot C)) →
    (∀ C k, endV (𝒟.side C k) = startV (𝒟.side C (rot C k))) →
    (∀ C k, A ⟨C, rot C k⟩ = B ⟨C, k⟩) →
    (∀ e, J e = B (𝒟.arcOf (e, true)) - A (𝒟.arcOf (e, false))) →
    (∀ e, J e = A (𝒟.arcOf (e, true)) - B (𝒟.arcOf (e, false))) →
    (∀ C, Function.Injective fun k : Fin (𝒟.cell C).R.N => startV (𝒟.side C k)) →
    (∀ e ∈ 𝒯s, J e = 0) →
    (∀ f : 𝒟.ιE → ℤ,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j) →
    (∀ f : 𝒟.ιE → 𝔸,
      (∀ w, (∑ e with (𝒟.ends e).2 = w, f e) = ∑ e with (𝒟.ends e).1 = w, f e) →
      ∀ e, f e = ∑ j ∈ 𝒯ᶜ, Z j e • f j) →
    (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
      ∃ cs : List 𝒟.ιC, cs.head? = some (𝒟.arcOf (wd i).1).1 ∧
        cs.getLast? = some (𝒟.arcOf (wd (i + 1)).1).1 ∧
        cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
          (((𝒟.arcOf (g, true)).1 = D ∧ (𝒟.arcOf (g, false)).1 = D') ∨
            ((𝒟.arcOf (g, true)).1 = D' ∧ (𝒟.arcOf (g, false)).1 = D)) ∧
          (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) →
    (∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s) (w : 𝒟.ιV),
      (∑ f with (𝒟.ends f).2 = w, pe e he f) = ∑ f with (𝒟.ends f).1 = w, pe e he f) →
    (∀ w, (∑ e with (𝒟.ends e).2 = w, J e) = ∑ e with (𝒟.ends e).1 = w, J e) ∧
    (∀ (j : 𝒟.ιE) (hj : j ∉ 𝒯s),
      J j = -∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, pe j hj l • ∑ e, Z l e • I e) ∧
    ∀ f : 𝒟.ιE, ∃ n : 𝒟.ιE → ℤ, J f = ∑ l ∈ (𝒯 ∪ 𝒯s)ᶜ, n l • ∑ e, Z l e • I e := by
  intro startV endV pe hW hbij hrot hC hJ1 hJ2 hinj hJ0 hZ hZA hW1 hW3
  classical
  have hAV : CellPeriods.ArcValues 𝒟 A B I J rot := ⟨hW, hbij, hrot, hC, hJ1, hJ2, hinj⟩
  refine ⟨hAV.kirchhoff, fun j hj => ?_, fun f => ?_⟩
  · rw [hAV.jump_formula hJ0 hZ wd hW1 hW3 j hj]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [CellPeriods.wordMatrix_of_not_mem wd hj]
    rfl
  have hmem := hAV.jump_mem_closure hJ0 hZ hZA wd hW1 hW3 f
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    CellPeriods.image_finset_eq_range_comb, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  refine ⟨fun l => if hl : l ∈ (𝒯 ∪ 𝒯s)ᶜ then c ⟨l, hl⟩ else 0, ?_⟩
  rw [← hc, ← Finset.sum_coe_sort ((𝒯 ∪ 𝒯s)ᶜ)]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [dif_pos l.2]
  rfl

end S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_kirchhoff_and_jump_formula_of_arc_values (solution)
