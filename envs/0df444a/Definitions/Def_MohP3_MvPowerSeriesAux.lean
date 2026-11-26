-- Prove2me | Definitions.Def_MohP3_MvPowerSeriesAux
-- name    : MohP3_MvPowerSeriesAux
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:04:58.589929+00:00
-- url     : https://prove2.me/theorems/d7a9e9bf-eb96-48b8-b5dc-d44bb410bfb0
-- title:
--   Mv Power Series Aux
-- statement:
--   Definitions and structural lemmas for Mv Power Series Aux, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/MvPowerSeriesAux.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Finsupp
namespace MvPowerSeries
variable {σ τ R : Type*} [CommSemiring R]
lemma emd_comp (e : σ ≃ τ) (d : σ →₀ ℕ) :
    Finsupp.equivMapDomain e.symm (Finsupp.equivMapDomain e d) = d := by
  rw [← Finsupp.equivMapDomain_trans]; simp
lemma emd_comp' (e : σ ≃ τ) (d : τ →₀ ℕ) :
    Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm d) = d := by
  rw [← Finsupp.equivMapDomain_trans]; simp
lemma emd_add (e : σ ≃ τ) (a b : σ →₀ ℕ) :
    Finsupp.equivMapDomain e (a + b) =
      Finsupp.equivMapDomain e a + Finsupp.equivMapDomain e b :=
  Finsupp.ext (congrFun rfl)
def reindexFun (e : σ ≃ τ) (f : MvPowerSeries σ R) : MvPowerSeries τ R :=
  fun d => f (Finsupp.equivMapDomain e.symm d)
@[simp] lemma coeff_reindexFun (e : σ ≃ τ) (f : MvPowerSeries σ R) (d : τ →₀ ℕ) :
    coeff d (reindexFun e f) = coeff (Finsupp.equivMapDomain e.symm d) f := rfl
lemma reindexFun_mul (e : σ ≃ τ) (f g : MvPowerSeries σ R) :
    reindexFun e (f * g) = reindexFun e f * reindexFun e g := by
  classical
  ext d
  rw [coeff_reindexFun, coeff_mul, coeff_mul]
  refine Finset.sum_nbij'
      (fun p => (Finsupp.equivMapDomain e p.1, Finsupp.equivMapDomain e p.2))
      (fun q => (Finsupp.equivMapDomain e.symm q.1, Finsupp.equivMapDomain e.symm q.2))
      ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab ⊢
    rw [← emd_add, hab, emd_comp']
  · rintro ⟨a, b⟩ hab
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab ⊢
    rw [← emd_add, hab]
  · rintro ⟨a, b⟩ _
    simp [emd_comp]
  · rintro ⟨a, b⟩ _
    simp [emd_comp']
  · rintro ⟨a, b⟩ _
    simp [emd_comp]
def reindexEquiv (e : σ ≃ τ) : MvPowerSeries σ R ≃+* MvPowerSeries τ R where
  toFun := reindexFun e
  invFun := reindexFun e.symm
  left_inv f := by ext d; simp only [coeff_reindexFun, Equiv.symm_symm, emd_comp]
  right_inv g := by ext d; simp only [coeff_reindexFun, Equiv.symm_symm, emd_comp']
  map_add' f g := by ext d; rfl
  map_mul' := reindexFun_mul e
def optionFun (f : MvPowerSeries (Option σ) R) : PowerSeries (MvPowerSeries σ R) :=
  fun (n : Unit →₀ ℕ) => (fun (d : σ →₀ ℕ) => f (Finsupp.optionElim (n ()) d))
def optionInv (F : PowerSeries (MvPowerSeries σ R)) : MvPowerSeries (Option σ) R :=
  fun e => coeff e.some (PowerSeries.coeff (e none) F)
@[simp] lemma coeff_optionFun (f : MvPowerSeries (Option σ) R) (n : ℕ) (d : σ →₀ ℕ) :
    coeff d (PowerSeries.coeff n (optionFun f)) = coeff (Finsupp.optionElim n d) f := by
  simp [optionFun, PowerSeries.coeff, coeff_apply]
@[simp] lemma coeff_optionInv (F : PowerSeries (MvPowerSeries σ R)) (e : Option σ →₀ ℕ) :
    coeff e (optionInv F) = coeff e.some (PowerSeries.coeff (e none) F) := rfl
lemma optionInv_optionFun (f : MvPowerSeries (Option σ) R) : optionInv (optionFun f) = f := by
  ext e
  rw [coeff_optionInv, coeff_optionFun, Finsupp.optionElim_some]
lemma optionFun_optionInv (F : PowerSeries (MvPowerSeries σ R)) : optionFun (optionInv F) = F := by
  ext n d
  rw [coeff_optionFun, coeff_optionInv, Finsupp.some_optionElim,
    Finsupp.optionElim_apply_none]
lemma optionFun_add (f g : MvPowerSeries (Option σ) R) :
    optionFun (f + g) = optionFun f + optionFun g := by
  ext n d
  simp [coeff_optionFun]
lemma sum_antidiagonal_optionElim {M : Type*} [AddCommMonoid M] [DecidableEq σ]
    (n : ℕ) (d : σ →₀ ℕ) (F : ((Option σ →₀ ℕ) × (Option σ →₀ ℕ)) → M) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.optionElim n d), F p =
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n,
        ∑ r ∈ Finset.HasAntidiagonal.antidiagonal d,
        F (Finsupp.optionElim q.1 r.1, Finsupp.optionElim q.2 r.2) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
      (fun p => ((p.1 none, p.2 none), (p.1.some, p.2.some)))
      (fun q => (Finsupp.optionElim q.1.1 q.2.1, Finsupp.optionElim q.1.2 q.2.2))
      ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hab
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal]
    constructor
    · have := congrArg (fun (u : Option σ →₀ ℕ) => u none) hab
      simpa using this
    · have : (a + b).some = (Finsupp.optionElim n d).some := by rw [hab]
      simpa using this
  · rintro ⟨⟨i, j⟩, ⟨d1, d2⟩⟩ hq
    simp only [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal] at hq
    simp only [Finset.HasAntidiagonal.mem_antidiagonal]
    obtain ⟨h1, h2⟩ := hq
    ext a
    cases a with
    | none => simpa [Finsupp.optionElim_apply_none] using h1
    | some s =>
        have := congrArg (fun (u : σ →₀ ℕ) => u s) h2
        simpa [Finsupp.optionElim_apply_some] using this
  · rintro ⟨a, b⟩ _
    simp
  · rintro ⟨⟨i, j⟩, ⟨d1, d2⟩⟩ _
    simp
  · rintro ⟨a, b⟩ _
    simp
lemma optionFun_mul (f g : MvPowerSeries (Option σ) R) :
    optionFun (f * g) = optionFun f * optionFun g := by
  classical
  ext n d
  rw [coeff_optionFun, coeff_mul, PowerSeries.coeff_mul, map_sum]
  rw [sum_antidiagonal_optionElim n d
    (fun p => coeff p.1 f * coeff p.2 g)]
  refine Finset.sum_congr rfl ?_
  rintro ⟨i, j⟩ _
  rw [coeff_mul]
  refine Finset.sum_congr rfl ?_
  rintro ⟨d1, d2⟩ _
  rw [coeff_optionFun, coeff_optionFun]
def optionEquiv : MvPowerSeries (Option σ) R ≃+* PowerSeries (MvPowerSeries σ R) where
  toFun := optionFun
  invFun := optionInv
  left_inv := optionInv_optionFun
  right_inv := optionFun_optionInv
  map_add' := optionFun_add
  map_mul' := optionFun_mul
def pemptyEquiv (σ : Type*) [IsEmpty σ] : R ≃+* MvPowerSeries σ R := by
  refine RingEquiv.ofBijective (MvPowerSeries.C (σ := σ) (R := R)) ⟨?_, ?_⟩
  · intro a b hab
    have := congrArg (MvPowerSeries.constantCoeff (σ := σ) (R := R)) hab
    simpa using this
  · intro f
    refine ⟨coeff 0 f, ?_⟩
    ext d
    have hd : d = 0 := Subsingleton.elim _ _
    subst hd
    simp
instance mohP3_isNoetherianRing_fin {R : Type*} [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
      exact isNoetherianRing_of_ringEquiv R (pemptyEquiv (Fin 0))
  | succ n ih =>
      have e1 : MvPowerSeries (Fin (n + 1)) R ≃+* MvPowerSeries (Option (Fin n)) R :=
        reindexEquiv (_root_.finSuccEquiv n)
      have e2 : MvPowerSeries (Option (Fin n)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) :=
        optionEquiv
      have : IsNoetherianRing (PowerSeries (MvPowerSeries (Fin n) R)) := inferInstance
      exact isNoetherianRing_of_ringEquiv _ (e1.trans e2).symm
end MvPowerSeries


