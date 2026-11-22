-- Prove2me | Definitions.Def_Formalism_FormalGroupWitt_Statement
-- name    : Formalism_FormalGroupWitt_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:39.954805+00:00
-- url     : https://prove2.me/theorems/ccc0be13-c393-4646-b7ea-215e997d5ef9
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/Statement.lean

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u v w
namespace Formalism.FG
open Formalism.G Formalism.LT
section Laws
variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι]
abbrev vX (i : ι) : MvPowerSeries (Fin 2 × ι) R := MvPowerSeries.X ((0 : Fin 2), i)
abbrev vY (i : ι) : MvPowerSeries (Fin 2 × ι) R := MvPowerSeries.X ((1 : Fin 2), i)
def atXv (g : MvPowerSeries ι R) : MvPowerSeries (Fin 2 × ι) R :=
  MvPowerSeries.subst (fun i : ι => (vX i : MvPowerSeries (Fin 2 × ι) R)) g
def atYv (g : MvPowerSeries ι R) : MvPowerSeries (Fin 2 × ι) R :=
  MvPowerSeries.subst (fun i : ι => (vY i : MvPowerSeries (Fin 2 × ι) R)) g
abbrev v3 (a : Fin 3) (i : ι) : MvPowerSeries (Fin 3 × ι) R := MvPowerSeries.X (a, i)
def IsFGL (F : ι → MvPowerSeries (Fin 2 × ι) R) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (F i) = 0) ∧
  (∀ i (x : Fin 2 × ι), MvPowerSeries.coeff (Finsupp.single x 1) (F i) = if x.2 = i then 1 else 0) ∧
  (∀ i, MvPowerSeries.subst
      (fun x : Fin 2 × ι => if x.1 = 0 then (MvPowerSeries.X x : MvPowerSeries (Fin 2 × ι) R)
        else 0) (F i) = vX i) ∧
  (∀ i, MvPowerSeries.subst
      (fun x : Fin 2 × ι => if x.1 = 1 then (MvPowerSeries.X x : MvPowerSeries (Fin 2 × ι) R)
        else 0) (F i) = vY i) ∧
  (∀ i, MvPowerSeries.subst
      (fun x : Fin 2 × ι => if x.1 = 0 then
          MvPowerSeries.subst (fun y : Fin 2 × ι => (v3 (Fin.castSucc y.1) y.2 :
            MvPowerSeries (Fin 3 × ι) R)) (F x.2)
        else v3 2 x.2) (F i) =
    MvPowerSeries.subst
      (fun x : Fin 2 × ι => if x.1 = 0 then v3 0 x.2 else
          MvPowerSeries.subst (fun y : Fin 2 × ι => (v3 y.1.succ y.2 :
            MvPowerSeries (Fin 3 × ι) R)) (F x.2)) (F i))
def IsCommV (F : ι → MvPowerSeries (Fin 2 × ι) R) : Prop :=
  ∀ i, MvPowerSeries.subst
      (fun x : Fin 2 × ι => (MvPowerSeries.X (Fin.rev x.1, x.2) : MvPowerSeries (Fin 2 × ι) R))
      (F i) = F i
def IsHomV (F G : ι → MvPowerSeries (Fin 2 × ι) R) (e : ι → MvPowerSeries ι R) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (e i) = 0) ∧
  ∀ i, MvPowerSeries.subst F (e i) =
    MvPowerSeries.subst
      (fun x : Fin 2 × ι => if x.1 = 0 then atXv (e x.2) else atYv (e x.2)) (G i)
def IsIdMod2 (f : ι → MvPowerSeries ι R) : Prop :=
  (∀ j, MvPowerSeries.constantCoeff (f j) = 0) ∧
  ∀ j i, MvPowerSeries.coeff (Finsupp.single i 1) (f j) = if i = j then 1 else 0
def IsLogV (F : ι → MvPowerSeries (Fin 2 × ι) R) (f : ι → MvPowerSeries ι R) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (F i) = 0) ∧ IsIdMod2 f ∧
    ∀ j, MvPowerSeries.subst F (f j) = atXv (f j) + atYv (f j)
end Laws
def AddLawExample : Prop :=
  IsFGL (fun i : Fin 2 => (vX i + vY i : MvPowerSeries (Fin 2 × Fin 2) ℤ)) ∧
    IsCommV (fun i : Fin 2 => (vX i + vY i : MvPowerSeries (Fin 2 × Fin 2) ℤ)) ∧
    IsHomV (fun i : Fin 2 => (vX i + vY i : MvPowerSeries (Fin 2 × Fin 2) ℤ))
      (fun i : Fin 2 => (vX i + vY i : MvPowerSeries (Fin 2 × Fin 2) ℤ)) MvPowerSeries.X ∧
    IsLogV (fun i : Fin 2 => (vX i + vY i : MvPowerSeries (Fin 2 × Fin 2) ℤ)) MvPowerSeries.X
def NotLawExample : Prop :=
  ¬ IsFGL (fun i : Fin 1 => (vX i + 2 * vY i : MvPowerSeries (Fin 2 × Fin 1) ℤ))
section FunEq
variable {K : Type u} [NormedField K]
def IsFunEqTypeV {ι : Type v} [Fintype ι] {τ : Type w} (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K)
    (M : ι → ι → K) (g : ι → MvPowerSeries τ K) : Prop :=
  ∀ j, IntegralMv (g j - (p : K)⁻¹ •
    ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (g k)))
def IntegralMat {ι : Type v} (M : ι → ι → K) : Prop := ∀ j k, ‖M j k‖ ≤ 1
end FunEq
def FunEqGroupV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ι → ι → K), IntegralMat M →
    ∀ f : ι → MvPowerSeries ι K, IsIdMod2 f → IsFunEqTypeV p q hq σ M f →
      ∃ F : ι → MvPowerSeries (Fin 2 × ι) K, (∀ i, IntegralMv (F i)) ∧ IsFGL F ∧ IsCommV F ∧
        IsLogV F f ∧
        ∀ F' : ι → MvPowerSeries (Fin 2 × ι) K, (∀ i, MvPowerSeries.constantCoeff (F' i) = 0) →
          (∀ j, MvPowerSeries.subst F' (f j) = atXv (f j) + atYv (f j)) → F' = F
def FunEqHomV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ι → ι → K), IntegralMat M →
    ∀ f : ι → MvPowerSeries ι K, IsIdMod2 f → IsFunEqTypeV p q hq σ M f →
    ∀ (τ : Type w) [Finite τ] (g : ι → MvPowerSeries τ K),
      (∀ j, MvPowerSeries.constantCoeff (g j) = 0) → IsFunEqTypeV p q hq σ M g →
      ∃ h : ι → MvPowerSeries τ K, (∀ i, MvPowerSeries.constantCoeff (h i) = 0) ∧
        (∀ i, IntegralMv (h i)) ∧ ∀ j, MvPowerSeries.subst h (f j) = g j
def FunEqCongrV : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ) (hq : q ≠ 0)
    (σ : K →+* K), FunctionalEquationSetting K p q σ →
    ∀ (ι : Type v) [Fintype ι] [DecidableEq ι] (M : ι → ι → K), IntegralMat M →
    ∀ f : ι → MvPowerSeries ι K, IsIdMod2 f → IsFunEqTypeV p q hq σ M f →
    ∀ (τ : Type w) [Finite τ] (α β : ι → MvPowerSeries τ K),
      (∀ i, MvPowerSeries.constantCoeff (α i) = 0) → (∀ i, MvPowerSeries.constantCoeff (β i) = 0) →
      (∀ i, IntegralMv (α i)) → (∀ i, IntegralMv (β i)) → ∀ r : ℕ, 1 ≤ r →
        ((∀ i, DivByMv ((p : K) ^ r) (α i - β i)) ↔
          ∀ j, DivByMv ((p : K) ^ r) (MvPowerSeries.subst α (f j) - MvPowerSeries.subst β (f j)))
def shiftLog (K : Type u) [Field K] (l m : ℕ) (j : ZMod m) : MvPowerSeries (ZMod m) K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0
def shiftMat (K : Type u) [Field K] (m : ℕ) (j k : ZMod m) : K := if k = j - 1 then 1 else 0
def ShiftFunEq : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (l : ℕ) (hl : l.Prime) (m : ℕ) [NeZero m]
    (σ : K →+* K),
    IsIdMod2 (shiftLog K l m) ∧
    ∀ j, shiftLog K l m j - (l : K)⁻¹ • ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) = MvPowerSeries.X j
def ShiftGroup : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) [NeZero m],
    ∃ F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l], IsFGL F ∧ IsCommV F ∧
      IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLog ℚ_[l] l m)
def iterV {R : Type u} [CommRing R] {ι : Type v} (e : ι → MvPowerSeries ι R) (n : ℕ) :
    ι → MvPowerSeries ι R :=
  (fun a : ι → MvPowerSeries ι R => fun i => MvPowerSeries.subst a (e i))^[n] MvPowerSeries.X
def ShiftHeight : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) [NeZero m] (F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l]),
    IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLog ℚ_[l] l m) →
    ∃ e : ZMod m → MvPowerSeries (ZMod m) ℤ_[l], IsHomV F F e ∧
      (∀ j, MvPowerSeries.subst (fun k => MvPowerSeries.map PadicInt.Coe.ringHom (e k))
          (shiftLog ℚ_[l] l m j) = (l : ℚ_[l]) • shiftLog ℚ_[l] l m j) ∧
      (∀ j n, (l : ℤ_[l]) ∣
        MvPowerSeries.coeff n (e j - MvPowerSeries.X (j - 1) ^ (l ^ 2))) ∧
      (∀ j n, (l : ℤ_[l]) ∣
        MvPowerSeries.coeff n (iterV e m j - MvPowerSeries.X j ^ (l ^ (2 * m))))
def ShiftTeich : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) [NeZero m] (F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l]),
    IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLog ℚ_[l] l m) →
    ∀ (R : Type u) [CommRing R] [IsDomain R] [CharZero R] (φ : ℤ_[l] →+* R) (w : R),
      w ^ ((l ^ 2) ^ m) = w →
      IsHomV (fun i => MvPowerSeries.map φ (F i)) (fun i => MvPowerSeries.map φ (F i))
        (fun j => MvPowerSeries.C (w ^ ((l ^ 2) ^ j.val)) * MvPowerSeries.X j)
def zlToW (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* WittVector l (AlgebraicClosure (ZMod l)) :=
  (WittVector.map (algebraMap (ZMod l) (AlgebraicClosure (ZMod l)))).comp
    (WittVector.equiv l).symm.toRingHom
def WittCharZero : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], CharZero (WittVector l (AlgebraicClosure (ZMod l)))
def WittTeichRoot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (d : ℕ), 1 ≤ d →
    ∃ ζ : WittVector l (AlgebraicClosure (ZMod l)), IsPrimitiveRoot ζ (l ^ d - 1)
def ShiftTeichWitt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) [NeZero m] (F : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℤ_[l]),
    IsLogV (fun i => MvPowerSeries.map PadicInt.Coe.ringHom (F i)) (shiftLog ℚ_[l] l m) →
    ∃ ζ : WittVector l (AlgebraicClosure (ZMod l)), IsPrimitiveRoot ζ (l ^ (2 * m) - 1) ∧
      IsHomV (fun i => MvPowerSeries.map (zlToW l) (F i))
        (fun i => MvPowerSeries.map (zlToW l) (F i))
        (fun j => MvPowerSeries.C (ζ ^ ((l ^ 2) ^ j.val)) * MvPowerSeries.X j)
def GaussLogShift : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (m : ℕ) [NeZero m] (c : ℝ), 0 < c → c ^ (l ^ 2 - 1) ≤ ‖(l : K)‖ →
      ∀ j, HasGauss c (shiftLog K l m j) ∧ gauss c (shiftLog K l m j) = c
def GaussExpShift : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ), l.Prime →
    ‖(l : K)‖ < 1 → ∀ (m : ℕ) [NeZero m] (c : ℝ), 0 < c → c ^ (l ^ 2 - 1) ≤ ‖(l : K)‖ →
      ∀ g : ZMod m → MvPowerSeries (ZMod m) K, (∀ j, MvPowerSeries.constantCoeff (g j) = 0) →
        (∀ j, MvPowerSeries.subst g (shiftLog K l m j) = MvPowerSeries.X j) →
        ∀ j, HasGauss c (g j) ∧ gauss c (g j) = c
def WeightInvariance : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (ι : Type v) [Fintype ι] (N : ℕ) (ζ : Rˣ),
    IsPrimitiveRoot ζ N → ∀ (wt : ι → ℤ) (P : MvPowerSeries ι R),
      MvPowerSeries.subst (fun i => MvPowerSeries.C ((ζ ^ wt i : Rˣ) : R) * MvPowerSeries.X i) P = P →
      ∀ n : ι →₀ ℕ, MvPowerSeries.coeff n P ≠ 0 → (N : ℤ) ∣ ∑ i, (n i : ℤ) * wt i
def LetterWeights : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] (l d : ℕ) [NeZero d], l.Prime → Even d → (ζ : Rˣ) →
    IsPrimitiveRoot ζ (l ^ d - 1) → ∀ P : MvPowerSeries (ZMod d) R,
      MvPowerSeries.subst (fun s : ZMod d => MvPowerSeries.C
          ((ζ ^ ((if s.val % 2 = 0 then 1 else -1) * (l : ℤ) ^ s.val) : Rˣ) : R) *
          MvPowerSeries.X s) P = P →
      ∀ n : ZMod d →₀ ℕ, MvPowerSeries.coeff n P ≠ 0 →
        ((l ^ d - 1 : ℕ) : ℤ) ∣
          ∑ s, (n s : ℤ) * ((if s.val % 2 = 0 then 1 else -1) * (l : ℤ) ^ s.val)
def GamSum : Prop :=
  ∀ l : ℕ, 2 ≤ l →
    HasSum (fun i : ℕ => (((l : ℝ)) ^ (2 * i + 1))⁻¹) ((l : ℝ) / ((l : ℝ) ^ 2 - 1)) ∧
      1 / ((l : ℝ) ^ 2 - 1) + (l : ℝ) / ((l : ℝ) ^ 2 - 1) = 1 / ((l : ℝ) - 1)
end Formalism.FG


