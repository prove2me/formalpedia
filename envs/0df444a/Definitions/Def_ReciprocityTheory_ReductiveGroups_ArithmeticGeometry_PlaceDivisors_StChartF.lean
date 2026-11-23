-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:42:00.677179+00:00
-- url     : https://prove2.me/theorems/611c6edd-6fea-4088-bf22-d22f900c3282
-- title:
--   St Chart F
-- statement:
--   Definitions and structural lemmas for St Chart F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/StChartF.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegOUnif
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
section Series
variable {O : Type} [CommRing O] {d : ℕ}
def IsCh (F : Fin d → PS O 2 d) (u : PS O 1 d) : Prop :=
  constantCoeff u = 1 ∧ ev (n := 2) ![addOf F (pt O (n := 2) d 0) (pt O (n := 2) d 1)] u =
    ev (n := 2) ![pt O (n := 2) d 0] u * ev (n := 2) ![pt O (n := 2) d 1] u
def dl (u : PS O 1 d) : Fin d → O :=
  fun j => coeff (Finsupp.single ((0 : Fin 1), j) 1) u
def res {s : ℕ} (w : Fin s → Fin d → O) : (Fin d → O) →ₗ[O] (Fin s → O) :=
  Matrix.mulVecLin (Matrix.of w)
def HasAF {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C] (F : Fin d → PS O 2 d) {s : ℕ}
    (w : Fin s → Fin d → O) (x : NNReal) : Prop :=
  ∃ (N : ℕ) (u : Fin N → PS O 1 d), (∀ k, IsCh F (u k)) ∧
    ReciprocityTheory.PGsh.Up.HasLen v O ((Fin s → O) ⧸ Submodule.span O (Set.range fun k => res w (dl (u k)))) x
def linPart (φ : Fin d → PS O 1 d) : Matrix (Fin d) (Fin d) O :=
  Matrix.of fun i j => coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)
def IsEigBasis {OE : Type} [CommRing OE] (act : OE → Fin d → PS O 1 d) (τ : OE →+* O) {s : ℕ}
    (w : Fin s → Fin d → O) : Prop :=
  (∀ i a, (linPart (act a)).mulVec (w i) = τ a • w i) ∧
    ∀ v : Fin d → O, (∀ a, (linPart (act a)).mulVec v = τ a • v) → ∃! c : Fin s → O, ∑ i, c i • w i = v
end Series
section Chart
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
variable {T : Type} [CommRing T] {d : ℕ}
def psJet {n : ℕ} (m : ℕ) (f : PS T n d) : JetR T (Fin n × Fin d) m :=
  Ideal.Quotient.mk _ (MvPowerSeries.trunc T (Finsupp.equivFunOnFinite.symm fun _ => m + 1) f)
theorem trunc_mem_span {n : ℕ} (m : ℕ) (f : PS T n d) (hf : constantCoeff f = 0) :
    MvPowerSeries.trunc T (Finsupp.equivFunOnFinite.symm fun _ => m + 1) f ∈
      Ideal.span (Set.range (MvPolynomial.X : Fin n × Fin d → MvPolynomial (Fin n × Fin d) T)) := by
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro a ha
  rw [MvPolynomial.mem_support_iff, MvPowerSeries.coeff_trunc] at ha
  split_ifs at ha with h
  · by_contra hne
    push_neg at hne
    have h0 : a = 0 := by
      ext i
      simpa using hne i (Set.mem_univ i)
    subst h0
    apply ha
    simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hf
  · exact absurd rfl ha
theorem aeval_kill {σ S : Type} [CommRing S] [Algebra T S] (m : ℕ) (g : σ → S) (J : Ideal S)
    (hg : ∀ i, g i ∈ J) (hJ : J ^ (m + 1) = ⊥) :
    ∀ a ∈ (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ T))) ^ (m + 1),
      MvPolynomial.aeval g a = 0 := by
  intro a ha
  have h1 : Ideal.map (MvPolynomial.aeval g : MvPolynomial σ T →ₐ[T] S)
      (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ T))) ≤ J := by
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simpa using hg i
  have h2 : MvPolynomial.aeval g a ∈ J ^ (m + 1) := by
    have h3 := Ideal.mem_map_of_mem (MvPolynomial.aeval g : MvPolynomial σ T →ₐ[T] S) ha
    rw [Ideal.map_pow] at h3
    exact Ideal.pow_right_mono h1 (m + 1) h3
  rw [hJ] at h2
  exact (Ideal.mem_bot).mp h2
theorem jet_aug_pow (κ : Type) (m : ℕ) :
    ((Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ T))).map
      (Ideal.Quotient.mk ((Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ T))) ^ (m + 1)))) ^ (m + 1) = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]
def substJ {n : ℕ} (m : ℕ) (φ : Fin d → PS T n d) (hφ : ∀ j, constantCoeff (φ j) = 0) :
    JetR T (Fin 1 × Fin d) m →ₐ[T] JetR T (Fin n × Fin d) m :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun q => psJet m (φ q.2))
    (aeval_kill m _ _ (fun q => Ideal.mem_map_of_mem _ (trunc_mem_span m (φ q.2) (hφ q.2)))
      (jet_aug_pow (Fin n × Fin d) m))
def jetPt {n : ℕ} (i : Fin n) (m : ℕ) : JetR T (Fin 1 × Fin d) m →ₐ[T] JetR T (Fin n × Fin d) m :=
  substJ m (fun j => (MvPowerSeries.X (i, j) : PS T n d)) (fun j => by simp)
structure IsChartJ (G : Over (Sp T)) [GrpObj G] (F : FGLaw T d)
    (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G) : Prop where
  trunc : ∀ m, algOverHom (jetTruncR T (Fin 1 × Fin d) m) ≫ x (m + 1) = x m
  zero : ∀ m, algOverHom (jetZeroR T (Fin 1 × Fin d) m) ≫ x m = toUnit _ ≫ η[G]
  univ : ∀ (κ : Type) (m : ℕ) (y : algOver T (JetR T κ m) ⟶ G),
    algOverHom (jetZeroR T κ m) ≫ y = toUnit _ ≫ η[G] →
    ∃! ψ : JetR T (Fin 1 × Fin d) m →ₐ[T] JetR T κ m,
      (∀ j, jetZeroR T κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m
  law : ∀ m, algOverHom (substJ m F.F F.const) ≫ x m =
    (algOverHom (jetPt (d := d) (0 : Fin 2) m) ≫ x m) * (algOverHom (jetPt (d := d) (1 : Fin 2) m) ≫ x m)
def ChartActs (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] {F : FGLaw T d}
    (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G) {OE : Type} [CommRing OE]
    (io : Out.RingAct G OE) (act : OAct OE F) : Prop :=
  ∀ m (a : OE), x m ≫ io.act a = algOverHom (substJ m (act.act a) (act.const a)) ≫ x m
end Chart
section Forms
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
def actMap {T O : Type} [CommRing T] [CommRing O] (iota : T →+* O) {d : ℕ} {F : FGLaw T d} {OE : Type}
    [CommRing OE] (act : OAct OE F) (a : OE) : Fin d → PS O 1 d :=
  fun i => MvPowerSeries.map iota (act.act a i)
def HTFSt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T], ¬ IsUnit (p : T) →
    ∀ (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
      (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
      (_ : Out.UnifPre (maximalIdeal T) D A G)
      (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x →
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
      (O : Type) [CommRing O] [Algebra O C], v.Integers O →
      ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (iota : T →+* O), IsLocalHom iota →
      ∃ (N : ℕ) (u : Fin N → PS O 1 d), (∀ k, IsCh (F.mapF iota) (u k)) ∧
        ∀ c : O, v (algebraMap O C c) ^ (p - 1) ≤ v (algebraMap O C (p : O)) →
          ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range fun k => dl (u k))
def AvFSt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T], ¬ IsUnit (p : T) →
    ∀ (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
      (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
      (U : Out.UnifPre (maximalIdeal T) D A G)
      (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x →
    ∀ (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
      [Module.Finite ℤ OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE)
      (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io →
    ∀ (act : OAct OE F), ChartActs G x io act →
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
      (O : Type) [CommRing O] [Algebra O C], v.Integers O →
      ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O]
        (iota : T →+* O), IsLocalHom iota →
      ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (vd : ℝ), HasVd p v w t vd →
      ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O),
        (∀ j, IsEigBasis (actMap iota act) ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) →
        (∀ τ ∈ Emb (O := O) w.bar, ∃ W' : Fin rm → Fin d → O, IsEigBasis (actMap iota act) τ W') →
      ∃ xs : Fin w.n → NNReal, (∀ j, HasAF v (F.mapF iota) (W j) (xs j)) ∧
        v (algebraMap O C (p : O)) ^ ((w.n : ℝ) * rm * (1 / ((p : ℝ) - 1) + vd / 2)) ≤ ∏ j, xs j
def UpFSt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [IsNoetherianRing T] [CharZero T]
    [IsAdicComplete (maximalIdeal T) T], ¬ IsUnit (p : T) →
    ∀ (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G]
      (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T))))
      (U : Out.UnifPre (maximalIdeal T) D A G)
      (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x →
    p ≠ 2 →
    ∀ (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
      [Module.Finite ℤ OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE)
      (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io →
      ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
    ∀ (act : OAct OE F), ChartActs G x io act →
    ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
      (O : Type) [CommRing O] [Algebra O C], v.Integers O →
      ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O]
        [Algebra ℤ_[p] O] (iota : T →+* O), IsLocalHom iota →
      ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e),
      (∃ b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e)),
        IsUnit (Matrix.det (Matrix.of fun i j =>
          tauExt ((t j : Emb (O := O) w.e) : OE →+* O) (b i : ℤ_[p] ⊗[ℤ] OE)))) →
      (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a -
          (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ maximalIdeal O) →
      ∀ (r : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (r τ) → Fin d → O),
        (∀ τ, IsEigBasis (actMap iota act) τ (W τ)) →
      ∀ j : Fin w.n, ∃ xs : NNReal, HasAF v (F.mapF iota) (W ((t j : Emb (O := O) w.e) : OE →+* O)) xs ∧
        v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) *
          (r (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp
            ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs
end Forms
end ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF


