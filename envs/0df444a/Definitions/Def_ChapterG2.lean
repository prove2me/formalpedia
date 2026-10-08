-- Prove2me | Definitions.Def_ChapterG2
-- name    : ChapterG2
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T01:35:33.377052+00:00
-- url     : https://prove2.me/theorems/297db503-58f0-4d14-9c43-d9b06f7d2b8b
-- title:
--   Chapter G2
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterG2.lean`): generated def bundle for ChapterG2. See BookProof/ChapterG2.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterG2.lean

import Definitions.Def_ChapterG
import Mathlib


/-!
# Chapter G II — Gribov ambiguity, BRST cohomology, general Dirac obstruction

This file formalizes work-package **N9** of `FORMALIZATION_ROADMAP.md`,
completing the book's chapters on gauge symmetry and the Gribov ambiguity
(book lines 2128 ff. and 7125 ff.).

Sections:
* G.8  conditioning fails on null constraint sets,
* G.9  the Dirac obstruction for any countably infinite gauge group,
* G.10 the Gribov ambiguity: no *continuous* complete gauge fixing of the circle,
* G.11 BRST cohomology of the gauge-mechanics model,
* G.12 Haar averaging is the invariant projection.

Everything is `sorry`-free and `axiom`-free (no `EXTERNAL` hypothesis).
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace BookProof.ChapterG2

/-! ## G.8 — Conditioning fails on null constraint sets -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-
Conditioning on a null set yields the zero measure (book 2230–2245).
-/


/-
Conditioning on a null set does not yield a probability measure — this is
the negative half that motivates the pushforward construction of G.5.
-/


/-! ## G.9 — The Dirac obstruction in general form -/

/-
There is no translation-invariant probability measure on any countably
infinite group (book 2270–2292, Dirac 1955).
-/


/-
A translation-invariant vector in `ℓ²(G)` is zero, for `G` infinite.
-/


/-
There is no translation-invariant unit vector in `ℓ²(G)`, for `G` infinite.
-/


/-! ## G.10 — HEADLINE: the Gribov ambiguity -/

/-
**The Gribov ambiguity (book 2294–2340 + 7125–7180).** There is no
*continuous* complete gauge fixing of the circle parametrization
`Circle.exp : ℝ → Circle`: complete gauge fixings exist set-theoretically
(G.4, by choice) but never continuously.
-/


/-
Corollary: any set-theoretic gauge-fixing section of the circle is
discontinuous.
-/


/-! ## G.11 — BRST cohomology of the gauge-mechanics model -/

section BRST

open BookProof.ChapterG

variable {A : Type*} [CommRing A] (Q : A)

/-- The BRST kernel: the closed states, `ker Ω`. -/
def brstKer : Submodule A (Fin 2 → A) :=
  LinearMap.ker (Matrix.mulVecLin (BRST Q))

/-- The BRST image: the exact states, `range Ω`. -/
def brstIm : Submodule A (Fin 2 → A) :=
  LinearMap.range (Matrix.mulVecLin (BRST Q))



/-- Membership in the BRST kernel: `Ω v = 0 ↔ Q · v₀ = 0`. -/
theorem mem_brstKer_iff (v : Fin 2 → A) :
    v ∈ brstKer Q ↔ Q * v 0 = 0 := by
  unfold brstKer;
  simp [ BRST, funext_iff, Fin.forall_fin_two ];
  rfl

/-- Membership in the BRST image: `v` is exact iff `v₀ = 0` and `v₁ ∈ (Q)`. -/
theorem mem_brstIm_iff (v : Fin 2 → A) :
    v ∈ brstIm Q ↔ v 0 = 0 ∧ ∃ a, v 1 = Q * a := by
  constructor;
  · rintro ⟨ w, rfl ⟩ ; simp [ BRST ] ;
  · rintro ⟨ hv₀, a, hv₁ ⟩;
    use ![a, 0];
    ext i; fin_cases i <;> simp only [BRST, Fin.zero_eta, Fin.isValue, Matrix.mulVecBilin_apply,
        Matrix.mulVec_cons, Nat.succ_eq_add_one, Nat.reduceAdd, zero_smul, Matrix.mulVec_empty,
            add_zero, Pi.add_apply, Pi.smul_apply, Function.comp_apply, Matrix.cons_val_zero,
                Matrix.head_cons, smul_eq_mul, mul_zero, Pi.zero_apply, hv₀, Fin.mk_one,
                    Matrix.cons_val_one, Matrix.cons_val_fin_one, hv₁] ;
    exact mul_comm _ _

/-- The BRST cohomology of the gauge-mechanics model. -/
abbrev brstCohomology : Type _ :=
  brstKer Q ⧸ (brstIm Q).comap (brstKer Q).subtype

/-- The forward linear map out of the closed states: `v ↦ (v₀, [v₁])`, landing
in `ker (·Q) × A⧸(Q)`. -/
noncomputable def brstFwd :
    brstKer Q →ₗ[A] (LinearMap.ker (LinearMap.mulLeft A Q) × (A ⧸ Ideal.span {Q})) where
  toFun v := (⟨(v : Fin 2 → A) 0, by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply]; exact (mem_brstKer_iff Q _).1 v.2⟩,
    Ideal.Quotient.mk _ ((v : Fin 2 → A) 1))
  map_add' := by intro x y; ext <;> simp
  map_smul' := by
    intro c x; ext
    · simp
    · simp [Algebra.smul_def]

/-- `brstFwd` kills the exact states, so it descends to cohomology. -/
theorem brstFwd_ker :
    (brstIm Q).comap (brstKer Q).subtype ≤ LinearMap.ker (brstFwd Q) := by
  intro v hv
  rw [Submodule.mem_comap] at hv
  simp only [Submodule.coe_subtype] at hv
  rw [mem_brstIm_iff] at hv
  obtain ⟨h0, a, h1⟩ := hv
  rw [LinearMap.mem_ker]
  apply Prod.ext
  · apply Subtype.ext; simp [brstFwd, h0]
  · simp only [brstFwd, LinearMap.coe_mk, AddHom.coe_mk]
    rw [h1]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr ⟨a, mul_comm a Q ▸ rfl⟩)

/-- The ghost-0 injection `ker (·Q) → H`, `a ↦ [![a,0]]`. -/
noncomputable def brstG1 :
    (LinearMap.ker (LinearMap.mulLeft A Q)) →ₗ[A] brstCohomology Q :=
  (Submodule.mkQ _) ∘ₗ
    (LinearMap.codRestrict (brstKer Q)
      ((LinearMap.single A (fun _ : Fin 2 => A) 0) ∘ₗ
        (LinearMap.ker (LinearMap.mulLeft A Q)).subtype)
      (by intro a
          rw [mem_brstKer_iff]
          have h := a.2
          rw [LinearMap.mem_ker, LinearMap.mulLeft_apply] at h
          simpa using h))

/-- The ghost-1 injection base `A → H`, `b ↦ [![0,b]]`. -/
noncomputable def brstG2base : A →ₗ[A] brstCohomology Q :=
  (Submodule.mkQ _) ∘ₗ
    (LinearMap.codRestrict (brstKer Q)
      (LinearMap.single A (fun _ : Fin 2 => A) 1)
      (by intro b; rw [mem_brstKer_iff]; simp))

/-- `brstG2base` kills `(Q)`, so it descends to `A⧸(Q)`. -/
theorem brstG2base_ker : Ideal.span {Q} ≤ LinearMap.ker (brstG2base Q) := by
  intro b hb
  rw [LinearMap.mem_ker]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hb
  simp only [brstG2base, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_brstIm_iff]
  exact ⟨by simp, a, by simp [ha]⟩

/-- The ghost-1 injection `A⧸(Q) → H`. -/
noncomputable def brstG2 : (A ⧸ Ideal.span {Q}) →ₗ[A] brstCohomology Q :=
  Submodule.liftQ _ (brstG2base Q) (brstG2base_ker Q)

/-- The inverse map `ker (·Q) × A⧸(Q) → H`. -/
noncomputable def brstGinv :
    (LinearMap.ker (LinearMap.mulLeft A Q) × (A ⧸ Ideal.span {Q}))
      →ₗ[A] brstCohomology Q :=
  LinearMap.coprod (brstG1 Q) (brstG2 Q)

theorem brstCohomology_equiv_right :
    (Submodule.liftQ _ (brstFwd Q) (brstFwd_ker Q)) ∘ₗ (brstGinv Q) = LinearMap.id := by
  ext ⟨a, y⟩; focus (simp [brstGinv, brstG1, brstG2]);
  · rfl;
  · simp only [brstFwd, Fin.isValue, brstGinv, brstG1, brstG2, LinearMap.coe_comp,
      LinearMap.coe_inl, Function.comp_apply, Submodule.mkQ_apply, LinearMap.coprod_apply,
      LinearMap.inl_apply, map_zero, zero_add, LinearMap.id_comp];
    erw [Submodule.liftQ_apply]; simp;
  · simp only [brstFwd, Fin.isValue, brstGinv, brstG1, brstG2, LinearMap.coe_comp,
      LinearMap.coe_inr, Function.comp_apply, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk, map_one,
          LinearMap.coprod_apply, map_zero, zero_add, LinearMap.id_comp, ZeroMemClass.coe_zero,
              ZeroMemClass.coe_eq_zero];
    erw [ Submodule.liftQ_apply ] ; simp ;
  · simp only [brstFwd, Fin.isValue, brstGinv, brstG1, brstG2, LinearMap.coe_comp,
      LinearMap.coe_inr, Function.comp_apply, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk, map_one,
          LinearMap.coprod_apply, map_zero, zero_add, LinearMap.id_comp];
    erw [ Submodule.liftQ_apply ] ; simp  ;

theorem brstCohomology_equiv_left :
    (brstGinv Q) ∘ₗ (Submodule.liftQ _ (brstFwd Q) (brstFwd_ker Q)) = LinearMap.id := by
  ext ⟨v, hv⟩;
  simp only [brstGinv, brstFwd, Fin.isValue, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.coprod_apply, LinearMap.id_comp];
  erw [ Submodule.Quotient.eq ];
  simp only [Fin.isValue, Submodule.mem_comap, Submodule.subtype_apply, AddSubgroupClass.coe_sub,
      Submodule.coe_add, LinearMap.codRestrict_apply, LinearMap.coe_comp, LinearMap.coe_single,
          Submodule.coe_subtype, Function.comp_apply, mem_brstIm_iff, Pi.sub_apply, Pi.add_apply,
              Pi.single_eq_same, ne_eq, zero_ne_one, not_false_eq_true, Pi.single_eq_of_ne,
                  add_zero, sub_self, one_ne_zero, zero_add, true_and];
  exact ⟨ 0, by simp ⟩

/-- **Cohomology computation (book 2403–2455).** The BRST cohomology of the
gauge-mechanics model splits as the gauge-invariant states (`ker (·Q)`) in the
ghost-0 sector times the coinvariants (`A ⧸ (Q)`) in the ghost-1 sector. -/
noncomputable def brstCohomology_equiv :
    brstCohomology Q ≃ₗ[A]
      (LinearMap.ker (LinearMap.mulLeft A Q) × (A ⧸ Ideal.span {Q})) :=
  LinearEquiv.ofLinear
    (Submodule.liftQ _ (brstFwd Q) (brstFwd_ker Q))
    (brstGinv Q)
    (brstCohomology_equiv_right Q)
    (brstCohomology_equiv_left Q)



end BRST

/-! ## G.12 — Haar averaging is the invariant projection -/

section Haar

open BookProof.ChapterG

variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]







end Haar

/-! ## G.16 — Simultaneous diagonalization of bounded commuting normal operators

From book.tex line 2358: "bounded commuting normal operators can always be
simultaneously diagonalized." This is the spectral theorem for commuting
normal operators.
-/



/-! ## G.17 — Haar measure for locally compact gauge groups

From book.tex lines 2392–2394: "for a locally compact gauge group (a Lie group,
for instance), a constant measure (Haar measure) always exists which allows
to create a functional which is gauge invariant."

This is already formalized in `ChapterG.lean` via `haarAverage` and the
Haar measure construction. We state the headline theorem here for
completeness.
-/



end BookProof.ChapterG2


