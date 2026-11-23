-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsConstMul
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsConstMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:22.154802+00:00
-- url     : https://prove2.me/theorems/1121f30e-aaf8-4edf-b387-4dfc4a10a7a1
-- title:
--   Is Const Mul
-- statement:
--   Definitions and structural lemmas for Is Const Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsConstMul.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_AdelicLattices_FactPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
abbrev under {Xo : Moduli D l} {c : Coeff l} {T : Scheme.{0}} (y : T ⟶ Xo.XF c) : T ⟶ Xo.X := y ≫ pullback.fst _ _
abbrev Vecs {Xo : Moduli D l} {c : Coeff l} {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (n : ℕ) : Type :=
  Fin n → (epsAt (under y) ⟶ Xo.univ.t.G)
abbrev FrameFn (Xo : Moduli D l) (c : Coeff l) : Type 1 :=
  ∀ (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), Vecs y D.p → Vecs y D.q → F
variable {Xo : Moduli D l} {c : Coeff l}
def IsFramed (U : Set (Xo.XF c)) (τ : E →+* ℂ) {F : Type} [Field F] (β : c.F →+* F) (y : Sp F ⟶ Xo.XF c)
    (v : Vecs y D.p) (w : Vecs y D.q) : Prop :=
  y ≫ pullback.snd _ _ = spMap β ∧ Set.range y ⊆ U ∧
    IsEigFrame Xo.univ.t.act (under y) (β.comp (tauIn c τ)) v ∧
    IsEigFrame Xo.univ.t.act (under y) (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w
structure IsLineFn (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) : Prop where
  ne : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w, IsFramed U τ β y v w → φ F y v w ≠ 0
  chg : ∀ (F : Type) [Field F] (β : c.F →+* F) y v w v' w' (A : Matrix (Fin D.p) (Fin D.p) F)
    (B : Matrix (Fin D.q) (Fin D.q) F), IsFramed U τ β y v w → IsFramed U τ β y v' w' →
    (∀ i, IsComb (A i) v (v' i)) → (∀ j, IsComb (B j) w (w' j)) → φ F y v' w' * A.det = φ F y v w * B.det
  nat : ∀ (F F' : Type) [Field F] [Field F'] (f : F →+* F') (β : c.F →+* F) y v w (y' : Sp F' ⟶ Xo.XF c) v' w',
    IsFramed U τ β y v w → y' = spMap f ≫ y → (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) →
    (∀ j, (w' j).left = spMap (dualMap f) ≫ (w j).left) → φ F' y' v' w' = f (φ F y v w)
def IsConstMul (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) : Prop :=
  ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ) (C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ)
    (Fm B : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ),
    IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed U τ (algebraMap c.F ℂ) y v w →
    (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
    (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
    (∀ a, tyPart ty τ (∑ m, C a m • P (e m)) = V a) →
    (∀ n, tyPart ty (ComplexEmbedding.conjugate τ) (P (e n)) = ∑ j, B j n • W j) →
    (∀ j n, ∑ m, Fm j m * τ (sesq (FU.Di i) (e m) (e n)) = B j n) →
    φ ℂ y v w * (Matrix.fromRows C Fm).det = ρ
structure IsFlatGen (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) : Prop where
  mem : ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
    y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U
  line : IsLineFn U τ φ
  flat : ∃ (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), LinearIndependent (𝓞 E) e ∧ IsConstMul U τ φ FU i e ρ
def HasInfNorm (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (s : c.F →+* ℂ) (t : ℝ) : Prop :=
  ∀ (y : Sp ℂ ⟶ Xo.XF c) v w (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed U τ s y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ →
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ →
    Real.log ‖φ ℂ y v w‖ + (Real.log ‖Γ.det‖ - Real.log ‖Δ.det‖) / 2 = t
def IsIntFrame {V K : Type} [CommRing V] [Field K] [Algebra V K] {y : Sp K ⟶ Xo.XF c} {t : SAB H (Sp V)}
    {tK : SAB H (Sp K)} (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK t (spMap (algebraMap V K)))
    (σ : 𝓞 E →+* K) {n : ℕ} (v : Vecs y n) : Prop :=
  ∃ (σV : 𝓞 E →+* V) (vV : Fin n → (epsAt (𝟙 (Sp V)) ⟶ t.G)), (algebraMap V K).comp σV = σ ∧
    IsEigFrame t.act (𝟙 (Sp V)) σV vV ∧ ∀ a, ∃ u : Sp (DualNumber K) ⟶ tK.G.left,
      u ≫ m.φ = (v a).left ∧ u ≫ m'.φ = spMap (dualMap (algebraMap V K)) ≫ (vV a).left
def HasFinNorm (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (t : ℝ) : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (j : K →+* ℂ_[p]) (β : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (T : SAB H (Sp V))
    (tK : SAB H (Sp K)) (m : SABMap tK Xo.univ.t (under y)) (m' : SABMap tK T (spMap (algebraMap V K))),
    (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp β = κ → IsFramed U τ β y v w →
    IsIntFrame m m' (β.comp (tauIn c τ)) v → IsIntFrame m m' (β.comp (tauIn c (ComplexEmbedding.conjugate τ))) w →
    Real.log ‖j (φ K y v w)‖ = t
def HasNorms (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (N : LogNorms c.F) : Prop :=
  (∀ s, HasInfNorm U τ φ s (N.inf s)) ∧ ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ
    (N.fin p κ + D.q * (logIdeal (κ.comp (tauIn c τ)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖((H.d : ℕ) : ℂ_[p])‖))
end GlobalTheory.CompanionTheory.Ar.Fl


