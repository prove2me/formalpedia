-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_UpSmith
-- name    : ReciprocityTheory_DualLattices_UpSmith
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:14.08479+00:00
-- url     : https://prove2.me/theorems/fd42642a-d16a-475f-8d2d-a8455dff6bb0
-- title:
--   Up Smith
-- statement:
--   Definitions and structural lemmas for Up Smith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpSmith.lean

import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up.Smith
section general
variable {R : Type} [CommRing R]
def consEquiv (a : R) {b : ℕ} (c : Fin b → R) :
    ((R ⧸ Ideal.span {a}) × ((k : Fin b) → R ⧸ Ideal.span {c k})) ≃ₗ[R]
      ((j : Fin (b + 1)) → R ⧸ Ideal.span {(Fin.cons a c : Fin (b + 1) → R) j}) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, fun k => x k.succ)
  map_add' p q := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  map_smul' r p := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  left_inv p := rfl
  right_inv x := by
    ext j
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
theorem eq_of_removeNth {b : ℕ} (i0 : Fin (b + 1)) {x y : Fin (b + 1) → R} (h0 : x i0 = y i0)
    (h : Fin.removeNth i0 x = Fin.removeNth i0 y) : x = y := by
  rw [← Fin.insertNth_self_removeNth i0 x, ← Fin.insertNth_self_removeNth i0 y, h0, h]
theorem pivot_equiv {b : ℕ} {ι : Type} [Fintype ι] (g : ι → Fin (b + 1) → R) (i0 : Fin (b + 1))
    (a : R) (u : Fin (b + 1) → R) (s : ι → R) (hu : u i0 = 1)
    (hau : a • u ∈ Submodule.span R (Set.range g)) (hs : ∀ j, g j i0 = a * s j) :
    Nonempty (((Fin (b + 1) → R) ⧸ Submodule.span R (Set.range g)) ≃ₗ[R]
      ((R ⧸ Ideal.span {a}) × ((Fin b → R) ⧸
        Submodule.span R (Set.range fun j => Fin.removeNth i0 (g j - s j • a • u))))) := by
  classical
  set K'' := Submodule.span R (Set.range fun j => Fin.removeNth i0 (g j - s j • a • u)) with hK''
  let P : (Fin (b + 1) → R) →ₗ[R] (Fin (b + 1) → R) :=
    LinearMap.id - (LinearMap.proj i0).smulRight u
  let rem : (Fin (b + 1) → R) →ₗ[R] (Fin b → R) := LinearMap.funLeft R R i0.succAbove
  have hP : ∀ x, P x = x - x i0 • u := fun x => rfl
  have hrem : ∀ x, rem x = Fin.removeNth i0 x := fun x => rfl
  let Φ : (Fin (b + 1) → R) →ₗ[R] (R ⧸ Ideal.span {a}) × ((Fin b → R) ⧸ K'') :=
    ((Ideal.span {a}).mkQ ∘ₗ LinearMap.proj i0).prod (K''.mkQ ∘ₗ rem ∘ₗ P)
  have hΦ : ∀ x, Φ x = (Submodule.Quotient.mk (x i0), Submodule.Quotient.mk
      (Fin.removeNth i0 (x - x i0 • u))) := fun x => rfl
  have hsurj : Function.Surjective Φ := by
    rintro ⟨q1, q2⟩
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q1
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q2
    refine ⟨r • u + (Fin.insertNth i0 (0 : R) y : Fin (b + 1) → R), ?_⟩
    have hx0 : (r • u + (Fin.insertNth i0 (0 : R) y : Fin (b + 1) → R)) i0 = r := by
      simp [hu]
    rw [hΦ, hx0]
    congr 2
    ext k
    simp [Fin.removeNth, Fin.insertNth_apply_succAbove]
  have hker : LinearMap.ker Φ = Submodule.span R (Set.range g) := by
    ext x
    rw [LinearMap.mem_ker, hΦ, Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 h1
      obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
      have hx : x = t • (a • u) + ∑ j, cc j • (g j - s j • a • u) := by
        have hsum : x - x i0 • u = ∑ j, cc j • (g j - s j • a • u) := by
          apply eq_of_removeNth i0
          · have hz : ∀ j, (cc j • (g j - s j • a • u)) i0 = 0 := by
              intro j; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hs, hu]; ring
            rw [Finset.sum_apply, Finset.sum_eq_zero (fun j _ => hz j)]
            simp [hu]
          · rw [← hcc]
            ext k
            simp [Fin.removeNth, Finset.sum_apply]
        rw [← hsum, ← mul_smul, ht]
        abel
      rw [hx]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ hau) (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩)
          (Submodule.smul_mem _ _ hau)))
    · intro hx
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
      have hx0 : (∑ j, r j • g j) i0 = (∑ j, r j * s j) * a := by
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hs, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      refine ⟨Ideal.mem_span_singleton'.2 ⟨_, hx0.symm⟩, ?_⟩
      have e : (∑ j, r j • g j) - (∑ j, r j • g j) i0 • u =
          ∑ j, r j • (g j - s j • a • u) := by
        rw [hx0]
        simp only [smul_sub, Finset.sum_sub_distrib]
        congr 1
        rw [Finset.sum_mul, Finset.sum_smul]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, smul_smul, mul_assoc]
      rw [e]
      have hlin : Fin.removeNth i0 (∑ j, r j • (g j - s j • a • u)) =
          ∑ j, r j • Fin.removeNth i0 (g j - s j • a • u) := by
        ext k; simp [Fin.removeNth, Finset.sum_apply]
      rw [hlin]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (Φ.quotKerEquivOfSurjective hsurj)⟩
instance instSubsingletonQuotientFinZero (K : Submodule R (Fin 0 → R)) :
    Subsingleton ((Fin 0 → R) ⧸ K) :=
  ⟨fun x y => by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Subsingleton.elim x y]⟩
end general
variable {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]
theorem exists_pivot (hv : v.Integers R) {b : ℕ} {ι : Type} [Fintype ι]
    (g : ι → Fin (b + 1) → R) :
    ∃ (i0 : Fin (b + 1)) (a : R) (u : Fin (b + 1) → R) (s : ι → R), u i0 = 1 ∧
      a • u ∈ Submodule.span R (Set.range g) ∧ (∀ j, g j i0 = a * s j) ∧
      (a = 0 → ∀ j, g j = 0) ∧ (a ≠ 0 → ∃ j0, g j0 = a • u ∧ s j0 = 1) := by
  classical
  have : IsDomain R := hv.hom_inj.isDomain
  by_cases hall : ∀ j, g j = 0
  · refine ⟨0, 0, Pi.single 0 1, 0, by simp, by simp, fun j => by simp [hall j],
      fun _ => hall, fun h => absurd rfl h⟩
  · push Not at hall
    obtain ⟨j1, hj1⟩ := hall
    obtain ⟨i1, hi1⟩ : ∃ i, g j1 i ≠ 0 := by
      by_contra h; push Not at h; exact hj1 (funext h)
    obtain ⟨⟨j0, i0⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (ι × Fin (b + 1)))
      (fun p => v (algebraMap R C (g p.1 p.2))) ⟨(j1, i1), Finset.mem_univ _⟩
    set a := g j0 i0 with ha
    have hdvd : ∀ j i, a ∣ g j i := fun j i =>
      hv.dvd_of_le (hmax (j, i) (Finset.mem_univ _))
    have ha0 : a ≠ 0 := by
      intro h0
      have := hmax (j1, i1) (Finset.mem_univ _)
      rw [h0, map_zero, map_zero, le_zero_iff, Valuation.zero_iff] at this
      exact hi1 (hv.hom_inj (by rw [this, map_zero]))
    choose u hu using hdvd j0
    choose s hs using fun j => hdvd j i0
    have hu0 : u i0 = 1 := by
      have h1 : a * u i0 = a * 1 := by rw [← hu i0, mul_one]
      exact mul_left_cancel₀ ha0 h1
    have hau : a • u = g j0 := by ext i; simp [hu i]
    refine ⟨i0, a, u, s, hu0, hau ▸ Submodule.subset_span ⟨j0, rfl⟩, hs, fun h => absurd h ha0,
      fun _ => ⟨j0, hau.symm, ?_⟩⟩
    have h1 : a * s j0 = a * 1 := by rw [← hs j0, mul_one]
    exact mul_left_cancel₀ ha0 h1
theorem smith_gen (hv : v.Integers R) : ∀ (b : ℕ) {ι : Type} [Fintype ι] (g : ι → Fin b → R),
    ∃ c : Fin b → R, Nonempty (((Fin b → R) ⧸ Submodule.span R (Set.range g)) ≃ₗ[R]
      ((i : Fin b) → R ⧸ Ideal.span {c i}))
  | 0, _, _, g => ⟨Fin.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩⟩
  | b + 1, _, _, g => by
    obtain ⟨i0, a, u, s, hu, hau, hs, -, -⟩ := exists_pivot hv g
    obtain ⟨e1⟩ := pivot_equiv g i0 a u s hu hau hs
    obtain ⟨c', ⟨e2⟩⟩ := smith_gen hv b (fun j => Fin.removeNth i0 (g j - s j • a • u))
    exact ⟨Fin.cons a c', ⟨(e1.trans ((LinearEquiv.refl R _).prodCongr e2)).trans (consEquiv a c')⟩⟩
end ReciprocityTheory.PGsh.Up.Smith


