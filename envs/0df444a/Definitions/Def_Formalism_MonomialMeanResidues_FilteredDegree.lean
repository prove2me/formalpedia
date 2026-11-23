-- Prove2me | Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
-- name    : Formalism_MonomialMeanResidues_FilteredDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:35:11.957689+00:00
-- url     : https://prove2.me/theorems/74d423f4-fc1b-426d-826d-5304a9c70101
-- title:
--   Filtered Degree
-- statement:
--   Definitions and structural lemmas for Filtered Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/FilteredDegree.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
namespace Formalism.HermiteSiegelSlopes
open Formalism.HN
section Defs
variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
def degT (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (L : Submodule (𝓞 K) V) : ℝ :=
  -Real.log (ht b X L) / (2 * (nPl K : ℝ))
def meanPl (A : InfinitePlace K → ℝ) : ℝ := (1 / (nPl K : ℝ)) * ∑ v, A v
def diagFrame {κ : Type*} [DecidableEq κ] (c : InfinitePlace K → κ → ℝ) :
    InfinitePlace K → Matrix κ κ ℂ :=
  fun v => Matrix.diagonal fun y => ((c v y : ℝ) : ℂ)
def piLattice₂ {σ κ : Type*} (Γ : Submodule (𝓞 K) (κ → K)) : Submodule (𝓞 K) (σ × κ → K) where
  carrier := {g | ∀ α, (fun y => g (α, y)) ∈ Γ}
  add_mem' := fun ha hb α => Γ.add_mem (ha α) (hb α)
  zero_mem' := fun _ => Γ.zero_mem
  smul_mem' := fun c _ hg α => Γ.smul_mem c (hg α)
def prodLat {n δ : ℕ} (j : ℕ) (w : Fin n → Fin δ → K) (Λc : Submodule (𝓞 K) (Fin δ → K)) :
    Submodule (𝓞 K) (Fin δ → K) :=
  Submodule.span (𝓞 K) {g | ∃ e : Fin j → Fin n, ∃ l ∈ Λc, g = (∏ t, w (e t)) * l}
def ptHeight {n δ : ℕ} (w : Fin n → Fin δ → K) (c1 : InfinitePlace K → Fin δ → ℝ) (y : Fin δ) : ℝ :=
  degT (Pi.basisFun K (Fin 1)) (diagFrame fun v _ => c1 v y)
    (Submodule.span (𝓞 K) (Set.range fun k => (fun _ : Fin 1 => w k y)))
end Defs
def DegTMu : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ L : Submodule (𝓞 K) V, L.FG →
      degT b X L = (rkK L : ℝ) * muDef b X L / 2
def SubLower : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (B : Submodule (𝓞 K) V) (Λ : ℝ), B.FG →
      (∃ s : Set V, s ⊆ (B : Set V) ∧ (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp Λ) ∧
        (B : Set V) ⊆ (Submodule.span K s : Set V)) →
      -((rkK B : ℝ) * Λ) ≤ degT b X B
def QuotLower : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (B : Submodule (𝓞 K) V) (U : Submodule K V) (Λ : ℝ), B.FG →
      (∃ s : Set V, s ⊆ (B : Set V) ∧ (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp Λ) ∧
        (B : Set V) ⊆ (Submodule.span K s : Set V)) →
      -(((rkK B : ℝ) - (rkK (B ⊓ U.restrictScalars (𝓞 K)) : ℝ)) * Λ) ≤
        degT b X B - degT b X (B ⊓ U.restrictScalars (𝓞 K))
def GradedStep : Prop :=
  ∀ (K V ι κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (XG : InfinitePlace K → Matrix κ κ ℂ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (XG v).det) →
    ∀ (φ : V →ₗ[K] (κ → K)) (U : Submodule K V) (M : Submodule (𝓞 K) V)
      (Γ : Submodule (𝓞 K) (κ → K)) (A : InfinitePlace K → ℝ),
      M.FG → Submodule.span K (M : Set V) = ⊤ → Submodule.IsLattice K Γ → (∀ v, 0 < A v) →
      (∀ γ ∈ Γ, ∃ f ∈ M, f ∈ U ∧ φ f = γ) →
      (∀ v, ∀ x ∈ U, ∀ ε : ℝ, 0 < ε → ∃ y ∈ U, φ y = 0 ∧
        Formalism.HermitianLatticesTheory.normAt b X v (x - y) ≤ A v * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K κ) XG v (φ x) + ε) →
      Module.finrank K U = Module.finrank K (U ⊓ LinearMap.ker φ : Submodule K V) + Fintype.card κ ∧
      degT (Pi.basisFun K κ) XG Γ - (Fintype.card κ : ℝ) * meanPl (fun v => Real.log (A v)) ≤
        degT b X (M ⊓ U.restrictScalars (𝓞 K))
          - degT b X (M ⊓ (U ⊓ LinearMap.ker φ).restrictScalars (𝓞 K))
def FilteredDegree : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (κ : ℕ → Type) [∀ a, Fintype (κ a)] [∀ a, DecidableEq (κ a)]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (XG : ∀ a, InfinitePlace K → Matrix (κ a) (κ a) ℂ),
    (∀ v, IsUnit (X v).det) → (∀ a v, IsUnit (XG a v).det) →
    ∀ (k : ℕ) (φ : ∀ a, V →ₗ[K] (κ a → K)) (U : ℕ → Submodule K V) (M : Submodule (𝓞 K) V)
      (Γ : ∀ a, Submodule (𝓞 K) (κ a → K)) (A : ℕ → InfinitePlace K → ℝ) (ΛP ΛT : ℝ),
      M.FG → Submodule.span K (M : Set V) = ⊤ →
      (∀ a < k, U (a + 1) = U a ⊓ LinearMap.ker (φ a)) →
      (∀ a < k, Submodule.IsLattice K (Γ a)) → (∀ a < k, ∀ v, 0 < A a v) →
      (∀ a < k, ∀ γ ∈ Γ a, ∃ f ∈ M, f ∈ U a ∧ φ a f = γ) →
      (∀ a < k, ∀ v, ∀ x ∈ U a, ∀ ε : ℝ, 0 < ε → ∃ y ∈ U a, φ a y = 0 ∧
        Formalism.HermitianLatticesTheory.normAt b X v (x - y) ≤
          A a v * Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (κ a)) (XG a) v (φ a x) + ε) →
      (∃ s : Set V, s ⊆ (M : Set V) ∧ s ⊆ (U k : Set V) ∧
        (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp ΛP) ∧ U k ≤ Submodule.span K s) →
      (∃ s : Set V, s ⊆ (M : Set V) ∧ (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp ΛT) ∧
        Submodule.span K s = ⊤) →
      Module.finrank K (U 0) = (∑ a ∈ range k, Fintype.card (κ a)) + Module.finrank K (U k) ∧
      (∑ a ∈ range k, (degT (Pi.basisFun K (κ a)) (XG a) (Γ a)
            - (Fintype.card (κ a) : ℝ) * meanPl (fun v => Real.log (A a v))))
          - (Module.finrank K (U k) : ℝ) * ΛP
          - ((Module.finrank K V : ℝ) - (Module.finrank K (U 0) : ℝ)) * ΛT ≤ degT b X M
def PositionSum : Prop :=
  ∀ (K σ κ : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
    (Γ : Submodule (𝓞 K) (κ → K)) (c : InfinitePlace K → κ → ℝ) (t : InfinitePlace K → σ → ℝ),
    Submodule.IsLattice K Γ → (∀ v y, 0 < c v y) → (∀ v α, 0 < t v α) →
    Submodule.IsLattice K (piLattice₂ (σ := σ) Γ) ∧
    degT (Pi.basisFun K (σ × κ)) (diagFrame fun v p => c v p.2 / t v p.1) (piLattice₂ (σ := σ) Γ) =
      ∑ α : σ, (degT (Pi.basisFun K κ) (diagFrame c) Γ
        - (Fintype.card κ : ℝ) * meanPl (fun v => Real.log (t v α)))
def GammaDegree : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n δ j : ℕ)
    (w : Fin n → Fin δ → K) (Λc : Submodule (𝓞 K) (Fin δ → K))
    (c1 c2 : InfinitePlace K → Fin δ → ℝ),
    Submodule.IsLattice K Λc → (∀ v y, 0 < c1 v y) → (∀ v y, 0 < c2 v y) →
    (∀ y, ∃ k, w k y ≠ 0) →
    (∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → δ < Ideal.absNorm P) →
    Submodule.IsLattice K (prodLat j w Λc) ∧
    degT (Pi.basisFun K (Fin δ)) (diagFrame c2) Λc + (j : ℝ) * ∑ y, ptHeight w c1 y ≤
      degT (Pi.basisFun K (Fin δ)) (diagFrame fun v y => c2 v y * c1 v y ^ j) (prodLat j w Λc)
def BaseChange : Prop :=
  ∀ (F E ι : Type) [Field F] [NumberField F] [StarRing F] [IsTotallyComplex F]
    [Field E] [NumberField E] [StarRing E] [IsTotallyComplex E] [Algebra F E]
    [Fintype ι] [DecidableEq ι]
    (XF : InfinitePlace F → Matrix ι ι ℂ) (XE : InfinitePlace E → Matrix ι ι ℂ),
    (∀ v, IsUnit (XF v).det) → (∀ w, IsUnit (XE w).det) →
    (∀ (w : InfinitePlace E) (x : ι → F),
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun E ι) XE w (fun i => algebraMap F E (x i)) =
        Formalism.HermitianLatticesTheory.normAt (Pi.basisFun F ι) XF (w.comap (algebraMap F E)) x) →
    ∀ M : Submodule (𝓞 F) (ι → F), M.FG →
      rkK (Submodule.span (𝓞 E) ((fun (x : ι → F) (i : ι) => algebraMap F E (x i)) '' (M : Set (ι → F))))
        = rkK M ∧
      degT (Pi.basisFun E ι) XE
          (Submodule.span (𝓞 E) ((fun (x : ι → F) (i : ι) => algebraMap F E (x i)) '' (M : Set (ι → F))))
        = degT (Pi.basisFun F ι) XF M
def Avoid : Prop :=
  ∀ (k kbar : Type) [Field k] [Fintype k] [Field kbar] [Algebra k kbar] (n δ : ℕ)
    (ybar : Fin δ → Fin n → kbar), (∀ y, ybar y ≠ 0) → δ < Fintype.card k →
    ∃ x : Fin n → k, ∀ y, ∑ i, algebraMap k kbar (x i) * ybar y i ≠ 0
end Formalism.HermiteSiegelSlopes


