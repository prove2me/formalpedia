-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
-- name    : Formalism_PeriodIntegrals_DivisionRowsRationalLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:42:08.894043+00:00
-- url     : https://prove2.me/theorems/8f8907ad-67e6-428e-9380-bff334a62e08
-- title:
--   Division Rows Rational Lattice
-- statement:
--   Definitions and structural lemmas for Division Rows Rational Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/DivisionRowsRationalLattice.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.Dv
open Formalism.BasicNotions
section Abstract
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
def IsGLat (A : HLat K) (ρ : Representation K G A.V) : Prop :=
  A.Good ∧ (∀ g, ∀ x ∈ A.L, ρ g x ∈ A.L) ∧
  ∀ g v x, Formalism.HermitianLatticesTheory.normAt A.b A.X v (ρ g x) = Formalism.HermitianLatticesTheory.normAt A.b A.X v x
variable (A : HLat K) (ρ : Representation K G A.V)
def cutE (e : Module.End K A.V) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  M ⊓ (LinearMap.range e).restrictScalars (𝓞 K)
def imgE (e : Module.End K A.V) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  M.map (LinearMap.restrictScalars (𝓞 K) e)
def dimE (e : Module.End K A.V) : ℕ := Module.finrank K (LinearMap.range e)
def cut (a : MonoidAlgebra K G) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  cutE A (ρ.asAlgebraHom a) M
def img (a : MonoidAlgebra K G) (M : Submodule (𝓞 K) A.V) : Submodule (𝓞 K) A.V :=
  imgE A (ρ.asAlgebraHom a) M
def dimOf (a : MonoidAlgebra K G) : ℕ := dimE A (ρ.asAlgebraHom a)
def rkL (M : Submodule (𝓞 K) A.V) : ℕ := Formalism.HN.rkK M
def degL (M : Submodule (𝓞 K) A.V) : ℝ := (Formalism.HN.rkK M : ℝ) * Formalism.HN.muDef A.b A.X M
def muMaxL (M : Submodule (𝓞 K) A.V) : ℝ := Formalism.HN.muMaxDef A.b A.X M
def lenAt {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (M N : Submodule (𝓞 K) V) : ℕ∞ :=
  letI : w.asIdeal.IsPrime := w.isPrime
  Module.length (Localization.AtPrime w.asIdeal)
    (LocalizedModule w.asIdeal.primeCompl (↥M ⧸ N.comap M.subtype))
def idxAt {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    (M N : Submodule (𝓞 K) V) : ℤ :=
  ((lenAt w M N).toNat : ℤ) - ((lenAt w N M).toNat : ℤ)
def LocLe {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K)) (F : ℕ)
    (M N : Submodule (𝓞 K) V) : Prop :=
  ∀ x ∈ M, ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • x ∈ (w.asIdeal ^ F) • N
def vCard (G : Type) [Fintype G] (w : HeightOneSpectrum (𝓞 K)) : ℤ := vAdd w ((Fintype.card G : ℕ) : K)
def IsFull (M : Submodule (𝓞 K) A.V) : Prop := M.FG ∧ Submodule.span K (M : Set A.V) = ⊤
def IsProj (e : Module.End K A.V) (n : ℕ) : Prop :=
  A.Good ∧ 0 < n ∧ e * e = e ∧ (∀ x ∈ A.L, ((n : ℕ) : 𝓞 K) • e x ∈ A.L) ∧
  ∀ v x y, Formalism.HermitianLatticesTheory.majAt A.b A.X v (e x) y = Formalism.HermitianLatticesTheory.majAt A.b A.X v x (e y)
end Abstract
section Lemma2
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def ProjectionSandwichLength (A : HLat K) (e : Module.End K A.V) (n : ℕ) : Prop :=
  (∀ x ∈ imgE A e A.L, ((n : ℕ) : 𝓞 K) • x ∈ cutE A e A.L) ∧
  cutE A e A.L ≤ imgE A e A.L ∧
  Nonempty ((↥(imgE A e A.L) ⧸ (cutE A e A.L).comap (imgE A e A.L).subtype) ≃ₗ[𝓞 K]
    (↥(imgE A (1 - e) A.L) ⧸ (cutE A (1 - e) A.L).comap (imgE A (1 - e) A.L).subtype)) ∧
  (∀ w : HeightOneSpectrum (𝓞 K),
    idxAt w (imgE A e A.L) (cutE A e A.L) = idxAt w (imgE A (1 - e) A.L) (cutE A (1 - e) A.L) ∧
    0 ≤ idxAt w (imgE A e A.L) (cutE A e A.L) ∧
    idxAt w (imgE A e A.L) (cutE A e A.L) ≤
      (min (dimE A e) (dimE A (1 - e)) : ℕ) * vAdd w ((n : ℕ) : K)) ∧
  (∀ ψ : Module.Dual K A.V, ψ ∘ₗ e = ψ →
    (ψ ∈ Formalism.HN.dualLat (cutE A e A.L) ↔ ∃ φ ∈ A.dualL, ψ = φ ∘ₗ e))
def DegreeKernelLowerBound (A : HLat K) (e : Module.End K A.V) (n : ℕ) : Prop :=
  degL A A.L - (dimE A (1 - e) : ℝ) * (muMaxL A A.L + 2 * Real.log (n : ℝ)) ≤ degL A (cutE A e A.L)
def KernelIndexFullLattice (A : HLat K) (e : Module.End K A.V) : Prop :=
  ∀ Th : Submodule (𝓞 K) A.V, IsFull A Th →
    (∀ (w : HeightOneSpectrum (𝓞 K)) (F : ℕ), LocLe w F Th A.L →
      idxAt w (cutE A e A.L) (cutE A e Th) ≤ idxAt w A.L Th - (F : ℤ) * (dimE A (1 - e) : ℤ)) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (F : ℕ), LocLe w 0 ((w.asIdeal ^ F) • Th) A.L →
      idxAt w (cutE A e A.L) (cutE A e Th) ≤ idxAt w A.L Th + (F : ℤ) * (dimE A (1 - e) : ℤ)) ∧
    cutE A e Th ≤ imgE A e Th
def projection_sandwich_lattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V),
    IsGLat A ρ → ProjectionSandwichLength A (ρ.asAlgebraHom (eG T)) (Fintype.card G)
def MassRatio₂ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V),
    IsGLat A ρ → DegreeKernelLowerBound A (ρ.asAlgebraHom (eG T)) (Fintype.card G)
def kernel_index_full_lattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V),
    IsGLat A ρ → KernelIndexFullLattice A (ρ.asAlgebraHom (eG T))
def projection_lemma_base_level : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ), IsProj A e n → ProjectionSandwichLength A e n ∧ DegreeKernelLowerBound A e n ∧ KernelIndexFullLattice A e
end Lemma2
section Lemma4
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
def rS (T : GoodSet K G) (P0 : Pair K G) (A : HLat K) (ρ : Representation K G A.V) (s : T.S) : ℕ :=
  rkL A (cut A ρ (eps P0 * eS T s) A.L)
def rkT (T : GoodSet K G) (P0 P : Pair K G) (A : HLat K) (ρ : Representation K G A.V) : ℕ :=
  ∑ s, nS T P s * rS T P0 A ρ s
def delRk (T : GoodSet K G) (P0 P : Pair K G) (A : HLat K) (ρ : Representation K G A.V)
    (Gam : ∀ s : T.S, Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K)) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ s, ((nS T P s * rS T P0 A ρ s : ℕ) : ℝ) *
    ((vAdd w (algebraMap (𝓞 K) K (Gam s).det) : ℝ) / (nS T P s : ℝ) + (vCard (K := K) G w : ℝ))
def Conclusion4a : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∀ (A : HLat K) (ρ : Representation K G A.V), IsGLat A ρ →
      rkL A (cut A ρ (eps P * eG T) A.L) = rkT T P0 P A ρ ∧
      |degL A (cut A ρ (eps P * eG T) A.L) -
          ∑ s, (nS T P s : ℝ) * degL A (cut A ρ (eps P0 * eS T s) A.L)| ≤
        10 * laG G * (rkT T P0 P A ρ : ℝ) ∧
      (0 < rkT T P0 P A ρ →
        muMaxL A (cut A ρ (eps P * eG T) A.L) ≤ muMaxL A (cut A ρ (eps P0 * eG T) A.L) + 10 * laG G)
def Conclusion4b (C : ℝ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (P0 P : Pair K G), M1 T P0 →
    ∃ Gam : ∀ s : T.S, Matrix (Fin (nS T P s)) (Fin (nS T P s)) (𝓞 K), (∀ s, (Gam s).det ≠ 0) ∧
      ∀ (A : HLat K) (ρ : Representation K G A.V) (B : Submodule (𝓞 K) A.V),
        IsGLat A ρ → IsGLat (K := K) (G := G) { A with L := B } ρ →
        (∀ w, 0 ≤ delRk T P0 P A ρ Gam w ∧
          |(idxAt w (cut A ρ (eps P * eG T) A.L) (cut A ρ (eps P * eG T) B) : ℝ) -
            ∑ s, (nS T P s : ℝ) *
              (idxAt w (cut A ρ (eps P0 * eS T s) A.L) (cut A ρ (eps P0 * eS T s) B) : ℝ)| ≤
            C * delRk T P0 P A ρ Gam w) ∧
        ∑ᶠ w, lw K w * delRk T P0 P A ρ Gam w ≤ 8 * laG G * (rkT T P0 P A ρ : ℝ)
def Conclusion4 (C : ℝ) : Prop := Conclusion4a ∧ Conclusion4b C
end Lemma4
section Herm
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]
def StarIsConj (K : Type) [Field K] [StarRing K] : Prop :=
  ∃ σ0 : K →+* ℂ, ∀ x, σ0 (star x) = star (σ0 x)
def IsCM (z : K) : Prop := ∀ σ : K →+* ℂ, σ (star z) = star (σ z)
def IsConjPlK (w w' : HeightOneSpectrum (𝓞 K)) : Prop := ∀ x : K, vAdd w' x = vAdd w (star x)
def IsHermE (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ x y, h y x = star (h x y)) ∧ (∀ x, (∀ y, h x y = 0) → x = 0) ∧ ∀ x y, h (e x) y = h x (e y)
def IsGHerm (A : HLat K) (ρ : Representation K G A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ x y, h y x = star (h x y)) ∧ (∀ x, (∀ y, h x y = 0) → x = 0) ∧ ∀ g x y, h (ρ g x) (ρ g y) = h x y
def DualInAt (A : HLat K) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (M : Submodule (𝓞 K) A.V)
    (w : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ v : A.V, (∀ a ∈ M, h v a ∈ Set.range (algebraMap (𝓞 K) K)) → ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ s • v ∈ M
def IsBasisAt (A : HLat K) {d : ℕ} (a : Fin d → A.V) (M : Submodule (𝓞 K) A.V)
    (w w' : HeightOneSpectrum (𝓞 K)) : Prop :=
  LinearIndependent K a ∧ ∀ u ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))),
    LocLe u 0 (Submodule.span (𝓞 K) (Set.range a)) M ∧ LocLe u 0 M (Submodule.span (𝓞 K) (Set.range a))
def GramDetKernelValuation (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  ∀ w w' : HeightOneSpectrum (𝓞 K), IsConjPlK w w' → DualInAt A h A.L w → DualInAt A h A.L w' →
    ∀ (d : ℕ) (a : Fin d → A.V), IsBasisAt A a (cutE A e A.L) w w' →
      vAdd w (Matrix.of fun i j => h (a i) (a j)).det ≤ 2 * (dimE A (1 - e) : ℤ) * vAdd w ((n : ℕ) : K)
def gram_det_kernel_dual_lattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), StarIsConj K → IsGLat A ρ → IsGHerm A ρ h →
    GramDetKernelValuation A (ρ.asAlgebraHom (eG T)) (Fintype.card G) h
def gram_det_kernel_base_level : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → GramDetKernelValuation A e n h
def IsCMFormE (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ i j, IsCM (h (A.b i) (A.b j))) ∧ (∀ i j, IsCM (A.b.repr (e (A.b j)) i)) ∧
  ∀ (v : InfinitePlace K) i j, Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b i) (A.b j) = v.embedding (h (A.b i) (A.b j))
def IsCMForm (A : HLat K) (ρ : Representation K G A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  (∀ i j, IsCM (h (A.b i) (A.b j))) ∧ (∀ g i j, IsCM (A.b.repr (ρ g (A.b j)) i)) ∧
  ∀ (v : InfinitePlace K) i j, Formalism.HermitianLatticesTheory.majAt A.b A.X v (A.b i) (A.b j) = v.embedding (h (A.b i) (A.b j))
def LamStar (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) (y : A.V) : Prop :=
  y ∈ LinearMap.range e ∧ (∀ u ∈ U, h y u = 0) ∧
  ∀ m ∈ cutE A e A.L, h y m ∈ Set.range (algebraMap (𝓞 K) K)
def IsValG (A : HLat K) (e : Module.End K A.V) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (U : Submodule K A.V) (w : HeightOneSpectrum (𝓞 K)) (n : ℤ) : Prop :=
  ∃ w', IsConjPlK w w' ∧ ∃ (d : ℕ) (y : Fin d → A.V), LinearIndependent K y ∧
    (∀ u ∈ ({w, w'} : Set (HeightOneSpectrum (𝓞 K))),
      (∀ i, ∃ s : 𝓞 K, s ∉ u.asIdeal ∧ LamStar A e h U (s • y i)) ∧
      ∀ z, LamStar A e h U z → ∃ s : 𝓞 K, s ∉ u.asIdeal ∧
        s • z ∈ Submodule.span (𝓞 K) (Set.range y)) ∧
    n = - vAdd w (Matrix.of fun i j => h (y i) (y j)).det
def L7 (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) : Prop :=
  ∀ U : Submodule K A.V, U ≤ LinearMap.range e →
    (∀ w k, IsValG A e h U w k →
      k ≤ ((dimE A e : ℤ) - (Module.finrank K U : ℤ)) * vAdd w ((n : ℕ) : K)) ∧
    (∀ γ : HeightOneSpectrum (𝓞 K) → ℤ, (∀ w, IsValG A e h U w (γ w)) →
      degL A (cutE A e A.L ⊓ U.restrictScalars (𝓞 K)) - degL A (cutE A e A.L) ≤
        ∑ᶠ w, lw K w * (γ w : ℝ)) ∧
    (∀ φ ∈ A.dualL, (∀ u ∈ U, φ u = 0) →
      ∀ m ∈ cutE A e A.L, φ m ∈ Set.range (algebraMap (𝓞 K) K))
def division_rows_rational_lattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), StarIsConj K → IsGLat A ρ → IsGHerm A ρ h → IsCMForm A ρ h →
    (∀ w, DualInAt A h A.L w) → L7 A (ρ.asAlgebraHom (eG T)) (Fintype.card G) h
def division_rows_base_level : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K] [IsGalois ℚ K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K),
    StarIsConj K → IsProj A e n → IsHermE A e h → IsCMFormE A e h →
    (∀ w, DualInAt A h A.L w) → L7 A e n h
end Herm
section Parts
open NumberField IsDedekindDomain
def ProjA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ), IsProj A e n → ProjectionSandwichLength A e n
def ProjB : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ), IsProj A e n → DegreeKernelLowerBound A e n
def ProjC : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (A : HLat K) (e : Module.End K A.V) (n : ℕ), IsProj A e n → KernelIndexFullLattice A e
def GLatProj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V),
    IsGLat A ρ → IsProj A (ρ.asAlgebraHom (eG T)) (Fintype.card G)
def GLatHerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]
    (G : Type) [Group G] [Fintype G] (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K), StarIsConj K → IsGHerm A ρ h →
    IsHermE A (ρ.asAlgebraHom (eG T)) h ∧ (IsCMForm A ρ h → IsCMFormE A (ρ.asAlgebraHom (eG T)) h)
end Parts
end PI.Dv


