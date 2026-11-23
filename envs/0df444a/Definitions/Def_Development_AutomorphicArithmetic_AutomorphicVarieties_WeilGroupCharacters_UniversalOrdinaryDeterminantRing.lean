-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_UniversalOrdinaryDeterminantRing
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_UniversalOrdinaryDeterminantRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:10.486286+00:00
-- url     : https://prove2.me/theorems/09f8f88f-de0f-4299-acad-f55089819b29
-- title:
--   Universal Ordinary Determinant Ring
-- statement:
--   Definitions and structural lemmas for Universal Ordinary Determinant Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/WeilGroupCharacters/UniversalOrdinaryDeterminantRing.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_WeilGroupCharacters_RepAlg
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_BaseRepGL3NormalisedOfPsiEqOne
import Theorems.Thm_UpperTheory_V_Alg_Lift_map_hom
import Theorems.Thm_UpperTheory_V_U3_unitaryThreeReflection_left
import Theorems.Thm_UpperTheory_V_U3_unitaryThreeReflection_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] UpperTheory.V.Alg.Lift.map_hom
attribute [local simp] UpperTheory.V.U3.unitaryThreeReflection_left
attribute [local simp] UpperTheory.V.U3.unitaryThreeReflection_right


set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix UpperTheory.V.Alg
namespace UpperTheory.V.W
structure GFrame (l : ℕ) [Fact l.Prime] : Type 1 where
  Γ : Type
  [grp : Group Γ]
  [top : TopologicalSpace Γ]
  [tgrp : IsTopologicalGroup Γ]
  [cpt : CompactSpace Γ]
  [tdisc : TotallyDisconnectedSpace Γ]
  η : Γ →* ℤˣ
  η_open : IsOpen (η.ker : Set Γ)
  c : Γ
  c_sq : c * c = 1
  η_c : η c = -1
  ε : Γ →* ℤ_[l]ˣ
  ε_cont : Continuous ε
  Vl : Type
  [finV : Fintype Vl]
  Gv : Vl → Type
  [gv : ∀ v, Group (Gv v)]
  [tv : ∀ v, TopologicalSpace (Gv v)]
  [tgv : ∀ v, IsTopologicalGroup (Gv v)]
  [cv : ∀ v, CompactSpace (Gv v)]
  [dv : ∀ v, TotallyDisconnectedSpace (Gv v)]
  φ : ∀ v, Gv v →* η.ker
  φ_cont : ∀ v, Continuous (φ v)
  Iv : ∀ v, Subgroup (Gv v)
  St : Type
  [finT : Fintype St]
  Iu : St → Subgroup η.ker
  D0 : Subgroup η.ker
  I0 : Subgroup η.ker
attribute [instance] GFrame.grp GFrame.top GFrame.tgrp GFrame.cpt GFrame.tdisc GFrame.finV GFrame.gv GFrame.tv GFrame.tgv
  GFrame.cv GFrame.dv GFrame.finT
def HasFlag {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k) (κ : Fin n → H →* kˣ) : Prop :=
  ∃ g : GL (Fin n) k, ∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) k) i j = 0) ∧
    ∀ i, (g * r s * g⁻¹ : GL (Fin n) k) i i = (κ i s : k)
def mat {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k) : H →* Matrix (Fin n) (Fin n) k :=
  (Units.coeHom _).comp r
def diagRep {H k : Type} [Group H] [CommRing k] {n : ℕ} (χ : Fin n → H →* kˣ) : H →* Matrix (Fin n) (Fin n) k where
  toFun s := diagonal fun i => (χ i s : k)
  map_one' := by simp
  map_mul' s t := by simp [diagonal_mul_diagonal]
abbrev pushCh {H A B : Type} [Group H] [CommRing A] [CommRing B] (f : A →+* B) (χ : H →* Aˣ) : H →* Bˣ :=
  (Units.map (f : A →* B)).comp χ
abbrev pushRep {H A B : Type} [Group H] [CommRing A] [CommRing B] {n : ℕ} (f : A →+* B) (r : H →* GL (Fin n) A) :
    H →* GL (Fin n) B := (GeneralLinearGroup.map f).comp r
namespace GFrame
variable {l : ℕ} [Fact l.Prime] (F : GFrame l)
abbrev G₀ : Type := F.η.ker
def conj : F.G₀ →* F.G₀ where
  toFun g := ⟨F.c * g * F.c⁻¹, (MonoidHom.normal_ker F.η).conj_mem _ g.2 _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [mul_assoc])
def G' : Subgroup F.G₀ := (F.ε.comp F.η.ker.subtype).ker
def mu (v : F.Vl) : Subgroup (F.Gv v) :=
  (CommGroup.primaryComponent (TopologicalAbelianization (F.Gv v)) l).comap (QuotientGroup.mk' _)
variable (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R]
def eps : F.G₀ →* Rˣ := pushCh ((algebraMap O R).comp (algebraMap ℤ_[l] O)) (F.ε.comp F.η.ker.subtype)
def starOp (n : ℕ) : MonoidAlgebra R F.G₀ →ₐ[R] (MonoidAlgebra R F.G₀)ᵐᵒᵖ :=
  MonoidAlgebra.lift R _ F.G₀
    { toFun := fun g => MulOpposite.op (MonoidAlgebra.single (F.conj g)⁻¹ ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R))
      map_one' := by simp [← MonoidAlgebra.one_def]
      map_mul' := fun g h => by
        rw [← MulOpposite.op_mul, MonoidAlgebra.single_mul_single, map_mul, map_mul, _root_.mul_inv_rev, mul_zpow,
          Units.val_mul, mul_comm ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)] }
def star (n : ℕ) (y : MonoidAlgebra R F.G₀) : MonoidAlgebra R F.G₀ := (F.starOp O R n y).unop
variable {R}
def oEl {n : ℕ} (v : F.Vl) (ψ : Fin n → F.Gv v →* Rˣ) (g : Fin n → F.Gv v) : MonoidAlgebra R F.G₀ :=
  (List.ofFn fun i => MonoidAlgebra.single (F.φ v (g i)) (1 : R) - MonoidAlgebra.single 1 ((ψ i (g i) : Rˣ) : R)).prod
def IsPolar {n : ℕ} (D : GDet n R F.G₀) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
    D.D B (F.star O B n y) = D.D B y
def IsForm (n : ℕ) {a : ℕ} (r : F.G₀ →* GL (Fin a) R) (P : GL (Fin a) R) : Prop :=
  ∀ g, (mat r g)ᵀ * (P : Matrix (Fin a) (Fin a) R) * mat r (F.conj g) =
    ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R) • (P : Matrix (Fin a) (Fin a) R)
end GFrame
variable {l : ℕ} [Fact l.Prime]
structure Resid (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (n : ℕ) where
  chib : Fin n → F.G₀ →* (ResidueField O)ˣ
  chib_open : ∀ i, IsOpen ((chib i).ker : Set F.G₀)
  chib_inj : Function.Injective chib
  polar : F.IsPolar O (GDet.ofRep (diagRep chib))
  psib : ∀ v, Fin n → F.Gv v →* (ResidueField O)ˣ
  psib_open : ∀ v i, IsOpen ((psib v i).ker : Set (F.Gv v))
  th : ∀ v, Fin n → F.mu v →* Oˣ
  th_comm : ∀ v i (g : F.mu v), (g : F.Gv v) ∈ (commutator (F.Gv v)).topologicalClosure → th v i g = 1
section Rings
variable {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n)
namespace Resid
def Dbar : GDet n (ResidueField O) F.G₀ := GDet.ofRep (diagRep r.chib)
def Ip (u : F.St) : Subgroup F.G₀ := F.Iu u ⊓ ⨅ i, (r.chib i).ker
variable {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
structure IsPsi (v : F.Vl) (i : Fin n) (ψ : F.Gv v →* Rˣ) : Prop where
  cont : AdicCont (maximalIdeal R) fun g => ((ψ g : Rˣ) : R)
  red : ∀ g, res O R (ψ g) = r.psib v i g
  mu : ∀ g : F.mu v, ((ψ g : Rˣ) : R) = algebraMap O R (r.th v i g)
end Resid
structure Pair (R : Type) [CommRing R] [Algebra O R] [IsCO O R] : Type 1 where
  D : GDet n R F.G₀
  ψ : ∀ v, Fin n → F.Gv v →* Rˣ
  cont : D.IsCont (maximalIdeal R)
  red : D.map (res O R : R →+* ResidueField O) = r.Dbar
  psi : ∀ v i, r.IsPsi v i (ψ v i)
  P : ∀ i g, D.lam i (F.star O R n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)
  Ord : ∀ v (g : Fin n → F.Gv v) (h : F.G₀), D.tr (MonoidAlgebra.single h 1 * F.oEl v (ψ v) g) = 0
  I : ∀ u, ∀ g ∈ r.Ip u, ∀ h : F.G₀, D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0
variable {r} in

def Pair.Maps {R A : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing A] (p : Pair r R) (f : R →+* A)
    (D : GDet n A F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Aˣ) : Prop :=
  p.D.map f = D ∧ ∀ v i, pushCh f (p.ψ v i) = ψ v i
structure UniversalOrdinaryDeterminantRing : Type 1 where
  B : Type
  [ring : CommRing B]
  [alg : Algebra O B]
  [co : IsCO O B]
  u : Pair r B
  univ : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R),
    ∃! f : B →ₐ[O] R, u.Maps (f : B →+* R) p.D p.ψ
attribute [instance] UniversalOrdinaryDeterminantRing.ring UniversalOrdinaryDeterminantRing.alg UniversalOrdinaryDeterminantRing.co
def IsInert {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (κ : ∀ v, Fin n → F.Iv v →* Rˣ) : Prop :=
  ∀ v i, ∃ ψ : F.Gv v →* Rˣ, r.IsPsi v i ψ ∧ κ v i = ψ.comp (F.Iv v).subtype
structure LamObj : Type 1 where
  Λ : Type
  [ring : CommRing Λ]
  [alg : Algebra O Λ]
  [co : IsCO O Λ]
  κ : ∀ v, Fin n → F.Iv v →* Λˣ
  inert : IsInert r κ
  univ : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (κ' : ∀ v, Fin n → F.Iv v →* Rˣ), IsInert r κ' →
    ∃! f : Λ →ₐ[O] R, ∀ v i, pushCh (f : Λ →+* R) (κ v i) = κ' v i
attribute [instance] LamObj.ring LamObj.alg LamObj.co
variable {r} in

def LamObj.toPair (Λ : LamObj r) {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (p : Pair r R) : Λ.Λ →ₐ[O] R :=
  (Λ.univ R (fun v i => (p.ψ v i).comp (F.Iv v).subtype) fun v i => ⟨_, p.psi v i, rfl⟩).choose
structure Point : Type 1 where
  K : Type
  [field : Field K]
  [fin : Finite K]
  [algk : Algebra (ResidueField O) K]
  [algO : Algebra O K]
  [tower : IsScalarTower O (ResidueField O) K]
  ρ : F.G₀ →* GL (Fin n) (PowerSeries K)
  cont : ∀ a b, AdicCont (maximalIdeal (PowerSeries K)) fun g => mat ρ g a b
  P : GL (Fin n) (PowerSeries K)
  symm : (P : Matrix (Fin n) (Fin n) (PowerSeries K))ᵀ = P
  form : F.IsForm O n ρ P
  red : (GDet.ofRep (mat ρ)).map (PowerSeries.constantCoeff : PowerSeries K →+* K) =
    r.Dbar.map (algebraMap (ResidueField O) K)
  ine : ∀ u, ∀ g ∈ r.Ip u, ρ g = 1
  ψ : ∀ v, Fin n → F.Gv v →* (PowerSeries K)ˣ
  ψ_red : ∀ v i, pushCh (PowerSeries.constantCoeff : PowerSeries K →+* K) (ψ v i) =
    pushCh (algebraMap (ResidueField O) K) (r.psib v i)
  flag : ∀ v, HasFlag (pushRep (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) (ρ.comp (F.φ v)))
    fun i => pushCh (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) (ψ v i)
attribute [instance] Point.field Point.fin Point.algk Point.algO Point.tower
variable {r}
namespace Point
variable (x : Point r)
abbrev A : Type := PowerSeries x.K
abbrev Fr : Type := FractionRing x.A
abbrev Fb : Type := AlgebraicClosure x.Fr
def ρF : F.G₀ →* GL (Fin n) x.Fr := pushRep (algebraMap x.A x.Fr) x.ρ
def N1 : Prop :=
  ∀ v, (∀ i j, i ≠ j → x.ψ v i ≠ x.ψ v j) ∧ ∀ i j, i < j → x.ψ v i ≠ x.ψ v j * (F.eps O x.A).comp (F.φ v)
def TypeI : Prop := U3.MatIrr F.G' (mat (pushRep (algebraMap x.Fr x.Fb) x.ρF))
def TypeE : Prop :=
  ∃ (a b : ℕ) (_ : 1 ≤ a) (_ : 1 ≤ b) (e : Fin n ≃ Fin a ⊕ Fin b) (Q : GL (Fin n) x.Fr)
    (r₁ : F.G₀ →* GL (Fin a) x.Fr) (r₂ : F.G₀ →* GL (Fin b) x.Fr),
    (∀ g, reindex e e ((Q * x.ρF g * Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) =
      fromBlocks (mat r₁ g) 0 0 (mat r₂ g)) ∧
    (∃ P₁, F.IsForm O n r₁ P₁) ∧ (∃ P₂, F.IsForm O n r₂ P₂) ∧
    U3.MatIrr F.G' (mat (pushRep (algebraMap x.Fr x.Fb) r₁)) ∧ U3.MatIrr F.G' (mat (pushRep (algebraMap x.Fr x.Fb) r₂)) ∧
    ∀ M : Matrix (Fin b) (Fin a) x.Fb, (∀ g ∈ F.G', M * mat (pushRep (algebraMap x.Fr x.Fb) r₁) g =
      mat (pushRep (algebraMap x.Fr x.Fb) r₂) g * M) → M = 0
def N3 : Prop :=
  ∀ U : Set F.G₀, IsOpen U → (U ∩ (F.G' : Set F.G₀)).Nonempty →
    ∃ σ ∈ U ∩ (F.G' : Set F.G₀), (mat x.ρF σ).charpoly.Separable
def N4 : Prop :=
  ∀ X : Matrix (Fin n) (Fin n) x.Fr,
    (∀ g ∈ F.D0, ((F.eps O x.Fr g : x.Frˣ) : x.Fr) • (mat x.ρF g * X) = X * mat x.ρF g) → X = 0
def NiceI : Prop := x.N1 ∧ x.TypeI ∧ x.N3 ∧ x.N4
def NiceE : Prop := x.N1 ∧ x.TypeE ∧ x.N3 ∧ x.N4
end Point
namespace UniversalOrdinaryDeterminantRing
variable (B : UniversalOrdinaryDeterminantRing r)
def IsPt (x : Point r) (f : B.B →ₐ[O] x.A) : Prop := B.u.Maps (f : B.B →+* x.A) (GDet.ofRep (mat x.ρ)) x.ψ
abbrev kap (q : PrimeSpectrum B.B) : Type := AlgebraicClosure q.asIdeal.ResidueField
def toKap (q : PrimeSpectrum B.B) : B.B →+* B.kap q :=
  (algebraMap q.asIdeal.ResidueField (B.kap q)).comp (algebraMap B.B q.asIdeal.ResidueField)
def IsStable (q : PrimeSpectrum B.B) : Prop :=
  ∃ ρ : F.G₀ →* Matrix (Fin n) (Fin n) (B.kap q), U3.MatIrr ⊤ ρ ∧ B.u.D.map (B.toKap q) = GDet.ofRep ρ
def E0gens : Set (MonoidAlgebra B.B F.G₀) :=
  B.u.D.CH ∪ {z | ∃ v g, z = F.oEl v (B.u.ψ v) g ∨ z = F.star O B.B n (F.oEl v (B.u.ψ v) g)} ∪
    {z | ∃ u, ∃ g ∈ r.Ip u, z = MonoidAlgebra.single g 1 - 1 ∨ z = F.star O B.B n (MonoidAlgebra.single g 1) - 1}
def GroupAlgebraKernelIdeal : TwoSidedIdeal (MonoidAlgebra B.B F.G₀) := closureIdeal (maximalIdeal B.B) B.E0gens
abbrev E0 : Type := B.GroupAlgebraKernelIdeal.ringCon.Quotient
abbrev E0kap (q : PrimeSpectrum B.B) : Type :=
  (TwoSidedIdeal.span (MonoidAlgebra.mapRingHom F.G₀ (B.toKap q) '' B.GroupAlgebraKernelIdeal)).ringCon.Quotient
def IsThick (q : PrimeSpectrum B.B) : Prop := ¬ B.IsStable q ∧ ¬ IsSemisimpleRing (B.E0kap q)
variable (J : Ideal B.B)
def P1core : Prop :=
  ∀ (x : Point r) (f : B.B →ₐ[O] x.A), x.NiceI → B.IsPt x f → J ≤ RingHom.ker f →
    ∀ q : PrimeSpectrum B.B, q.asIdeal ≤ RingHom.ker f → J ≤ q.asIdeal
def P2core : Prop :=
  ∀ (x : Point r) (f : B.B →ₐ[O] x.A), x.NiceE → B.IsPt x f →
    (∃ q₁ : PrimeSpectrum B.B, B.IsStable q₁ ∧ J ≤ q₁.asIdeal ∧ q₁.asIdeal ≤ RingHom.ker f) →
    ∀ q : PrimeSpectrum B.B, q.asIdeal ≤ RingHom.ker f → B.IsStable q ∨ B.IsThick q → J ≤ q.asIdeal
def P3core : Prop :=
  ∀ (h : ℕ) (x : Fin (h + 1) → Point r) (f : ∀ i, B.B →ₐ[O] (x i).A) (e : Fin h → PrimeSpectrum B.B),
    (∀ i, (x i).NiceE) → (∀ i, B.IsPt (x i) (f i)) →
    (∀ i, B.IsThick (e i) ∧ (e i).asIdeal ≤ RingHom.ker (f i.castSucc) ∧ (e i).asIdeal ≤ RingHom.ker (f i.succ)) →
    (∃ q₁ : PrimeSpectrum B.B, B.IsStable q₁ ∧ J ≤ q₁.asIdeal ∧ q₁.asIdeal ≤ RingHom.ker (f 0)) →
    ∀ q : PrimeSpectrum B.B, q.asIdeal ≤ RingHom.ker (f (Fin.last h)) → B.IsStable q ∨ B.IsThick q → J ≤ q.asIdeal
end UniversalOrdinaryDeterminantRing
end Rings
end UpperTheory.V.W


