-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:44:59.278361+00:00
-- url     : https://prove2.me/theorems/ee671c21-a20d-43ad-9163-a31211560a91
-- title:
--   Exponential Differential
-- statement:
--   Definitions and structural lemmas for Exponential Differential, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ExponentialDifferential.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
namespace GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
def In {R : Type} [CommRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens) : Prop :=
  (⊤ : (Sp R).Opens) ≤ x ⁻¹ᵁ U
def val {R : Type} [CommRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) {U : X.Opens} (h : In x U)
    (f : Γ(X, U)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((x.appLE U ⊤ h).hom f)
abbrev Pt (A : Over (Sp ℂ)) : Type := 𝟙_ (Over (Sp ℂ)) ⟶ A
abbrev Pt.mor {A : Over (Sp ℂ)} (x : Pt A) : Sp ℂ ⟶ A.left := x.left
abbrev EpsPt (A : Over (Sp ℂ)) : Type := epsPt (𝟙 (Sp ℂ)) ⟶ A
abbrev EpsPt.mor {A : Over (Sp ℂ)} (v : EpsPt A) : Sp (DualNumber ℂ) ⟶ A.left := v.left
open scoped Classical in

def extZero {V : Type} (s : Set V) (F : ∀ z, z ∈ s → ℂ) : V → ℂ := fun z => if h : z ∈ s then F z h else 0
section Hol
variable {g : ℕ} {A : Over (Sp ℂ)}
def pre (u : (Fin g → ℂ) → Pt A) (U : A.left.Opens) : Set (Fin g → ℂ) := {z | In (u z).mor U}
def comp (u : (Fin g → ℂ) → Pt A) (U : A.left.Opens) (f : Γ(A.left, U)) : (Fin g → ℂ) → ℂ :=
  extZero (pre u U) (fun z h => val (u z).mor h f)
def IsHol (u : (Fin g → ℂ) → Pt A) : Prop :=
  ∀ U : A.left.Opens, IsOpen (pre u U) ∧ ∀ f : Γ(A.left, U), DifferentiableOn ℂ (comp u U f) (pre u U)
variable [GrpObj A]
def IsTangent (v : EpsPt A) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.mor = (1 : Pt A).mor
def IsDiffAt (u : (Fin g → ℂ) → Pt A) (w : Fin g → ℂ) (v : EpsPt A) : Prop :=
  IsTangent v ∧ ∀ (U : A.left.Opens) (h : In v.mor U) (f : Γ(A.left, U)),
    HasDerivAt (fun t : ℂ => comp u U f (t • w)) (val v.mor h f).snd 0
end Hol
structure Exp (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) where
  exp : (Fin g → ℂ) → Pt A
  exp_add : ∀ z z', exp (z + z') = exp z * exp z'
  hol : IsHol exp
  onto : Function.Surjective exp
  locIso : ∀ v : EpsPt A, IsTangent v → ∃! w, IsDiffAt exp w v
  discrete : DiscreteTopology {z : Fin g → ℂ | exp z = 1}
  span : Submodule.span ℝ {z : Fin g → ℂ | exp z = 1} = ⊤
namespace Exp
variable {A : Over (Sp ℂ)} [GrpObj A] {g : ℕ} (E : Exp A g)
def hom : Multiplicative (Fin g → ℂ) →* Pt A :=
  MonoidHom.mk' (fun z => E.exp z.toAdd) (fun _ _ => E.exp_add _ _)
def lat : Submodule ℤ (Fin g → ℂ) := AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup' E.hom.ker)
instance : DiscreteTopology E.lat := E.discrete
instance : IsZLattice ℝ E.lat := ⟨E.span⟩
def IsDiff (w : Fin g → ℂ) (v : EpsPt A) : Prop := IsDiffAt E.exp w v
end Exp
structure Unif (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) extends Exp A g where
  isLB : L.IsLB
  fr : ∀ (i : L.ι) (z : Fin g → ℂ), z ∈ pre exp (L.U i) → ℂ
  fr_ne : ∀ i z h, fr i z h ≠ 0
  fr_hol : ∀ i, DifferentiableOn ℂ (extZero (pre exp (L.U i)) (fr i)) (pre exp (L.U i))
  fr_compat : ∀ (i j : L.ι) (z : Fin g → ℂ) (hi : z ∈ pre exp (L.U i)) (hj : z ∈ pre exp (L.U j))
    (hij : In (exp z).mor (L.U i ⊓ L.U j)),
    fr i z hi = val (exp z).mor hij (L.g i j : Γ(A.left, L.U i ⊓ L.U j)) * fr j z hj
structure AHDatum {g : ℕ} (La : Submodule ℤ (Fin g → ℂ)) where
  H : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ
  herm : ∀ x y, H y x = starRingEnd ℂ (H x y)
  pos : ∀ x, x ≠ 0 → 0 < (H x x).re
  integral : ∀ la mu : La, ∃ n : ℤ, (H la mu).im = n
  ch : La → ℂ
  ch_norm : ∀ la, ‖ch la‖ = 1
  ch_add : ∀ la mu : La,
    ch (la + mu) = ch la * ch mu * Complex.exp (π * Complex.I * ((H la mu).im : ℝ))
def AHDatum.factor {g : ℕ} {La : Submodule ℤ (Fin g → ℂ)} (D : AHDatum La) (la : La) (z : Fin g → ℂ) : ℂ :=
  D.ch la * Complex.exp (π * D.H z la + π * D.H la la / 2)
def gaussLat : Submodule ℤ (Fin 1 → ℂ) where
  carrier := {z | ∃ m n : ℤ, (z 0).re = m ∧ (z 0).im = n}
  add_mem' := by
    rintro x y ⟨m, n, h, h'⟩ ⟨m', n', k, k'⟩
    exact ⟨m + m', n + n', by simp [h, k], by simp [h', k']⟩
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  smul_mem' := by
    rintro c x ⟨m, n, h, h'⟩
    exact ⟨c * m, c * n, by simp [h], by simp [h']⟩
def gaussDatum : AHDatum gaussLat where
  H := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => 2 * (x 0 * starRingEnd ℂ (y 0)))
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
  herm := by
    intro x y
    simp only [LinearMap.mk₂'ₛₗ_apply, map_mul, Complex.conj_conj, map_ofNat]; ring
  pos := by
    intro x hx
    have h0 : x 0 ≠ 0 := fun h => hx (funext fun i => by rw [Subsingleton.elim i 0]; exact h)
    have := Complex.normSq_pos.2 h0
    simp only [LinearMap.mk₂'ₛₗ_apply, Complex.mul_conj]
    simpa using h0
  integral := by
    rintro ⟨x, m, n, h, h'⟩ ⟨y, m', n', k, k'⟩
    exact ⟨2 * (n * m' - m * n'), by simp [h, h', k, k']; ring⟩
  ch := fun _ => 1
  ch_norm := by simp
  ch_add := by
    rintro ⟨x, m, n, h, h'⟩ ⟨y, m', n', k, k'⟩
    have : (2 * (x 0 * starRingEnd ℂ (y 0))).im = 2 * ((n * m' - m * n' : ℤ) : ℝ) := by
      simp [h, h', k, k']; ring
    simp only [LinearMap.mk₂'ₛₗ_apply, this]
    rw [_root_.one_mul, _root_.one_mul]
    have e := Complex.exp_int_mul_two_pi_mul_I (n * m' - m * n')
    rw [← e]; congr 1; push_cast; ring
namespace Unif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (F : Unif A L g)
def IsSec (s : L.Sec) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (i : L.ι) (z : Fin g → ℂ) (h : z ∈ pre F.exp (L.U i)), val (F.exp z).mor h (s.f i) = θ z * F.fr i z h
def IsRig (rig : LB.Gen (L.pull (eSec A))) : Prop :=
  ∀ (j : PUnit → L.ι) (h : (0 : Fin g → ℂ) ∈ pre F.exp (L.U (j PUnit.unit)))
    (h' : In (R := ℂ) (X := (𝟙_ (Over (Sp ℂ))).left) (𝟙 (Sp ℂ)) ((L.pull (eSec A)).U j)),
    F.fr (j PUnit.unit) 0 h = val (R := ℂ) (X := (𝟙_ (Over (Sp ℂ))).left) (𝟙 (Sp ℂ)) h' (rig.s j).val
def HasFactor (a : F.toExp.lat → (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (la : F.toExp.lat) (z : Fin g → ℂ) (i : L.ι) (h : z ∈ pre F.exp (L.U i))
    (h' : z + la ∈ pre F.exp (L.U i)), F.fr i z h = a la z * F.fr i (z + la) h'
def IsAH (D : AHDatum F.toExp.lat) : Prop := F.HasFactor D.factor
end Unif
def e (x : ℂ) : ℂ := Complex.exp (2 * π * Complex.I * x)
def Siegel (g : ℕ) : Type :=
  {τ : Matrix (Fin g) (Fin g) ℂ // τ.IsSymm ∧ (τ.map Complex.im).PosDef}
instance (g : ℕ) : Inhabited (Siegel g) :=
  ⟨⟨Matrix.diagonal fun _ => Complex.I, Matrix.isSymm_diagonal _, by
    rw [Matrix.diagonal_map (by simp)]
    simpa using (Matrix.PosDef.one : (1 : Matrix (Fin g) (Fin g) ℝ).PosDef)⟩⟩
def thetaTerm {g : ℕ} (a b : Fin g → ℝ) (z : Fin g → ℂ) (τ : Matrix (Fin g) (Fin g) ℂ) (l : Fin g → ℤ) : ℂ :=
  e ((∑ i, ∑ j, ((l i : ℂ) + a i) * τ i j * ((l j : ℂ) + a j)) / 2 + ∑ i, ((l i : ℂ) + a i) * (z i + b i))
def theta {g : ℕ} (a b : Fin g → ℝ) (z : Fin g → ℂ) (τ : Siegel g) : ℂ :=
  ∑' l : Fin g → ℤ, thetaTerm a b z τ.1 l
example {g : ℕ} (a b : Fin g → ℝ) (z : Fin g → ℂ) (τ : Siegel g) :
    theta (-a) (-b) (-z) τ = theta a b z τ := by
  unfold theta
  rw [← (Equiv.neg (Fin g → ℤ)).tsum_eq]
  refine tsum_congr fun l => ?_
  unfold thetaTerm
  congr 2
  · congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.neg_apply, Pi.neg_apply]; push_cast; ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Equiv.neg_apply, Pi.neg_apply]; push_cast; ring
example (z : Fin 1 → ℂ) (τ : Siegel 1) : theta 0 0 z τ = jacobiTheta₂ (z 0) (τ.1 0 0) := by
  unfold theta jacobiTheta₂
  rw [← (Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [thetaTerm, e, jacobiTheta₂_term, Fin.sum_univ_one]
  congr 1
  simp
  ring
end GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms


