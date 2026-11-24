-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
-- name    : Formalism_PieriBlockIdeals_LocalFaithfullyFlat
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:57:10.877735+00:00
-- url     : https://prove2.me/theorems/18af2fbc-7f7f-4c3c-a9e4-cd114c6b65df
-- title:
--   Local Faithfully Flat
-- statement:
--   Definitions and structural lemmas for Local Faithfully Flat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/LocalFaithfullyFlat.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_JointTheoremALoc
import Definitions.Def_Formalism_SatakeDualWeyl_DualWeylRepApply
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA
def LocalFaithfullyFlat : Prop :=
  ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O] [IsDomain O]
    [IsLocalRing O] [Algebra R O] [IsLocalHom (algebraMap R O)],
    Function.Injective (algebraMap R O) → Module.FaithfullyFlat R O
def UnitsOfLocal : Prop :=
  ∀ (O : Type) [CommRing O] [IsLocalRing O] (l : ℕ), l.Prime → ¬ IsUnit (l : O) →
    ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : O)
def ZLocInO : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (_ : CharZero R)
      (_ : Algebra R O),
      IsLocalHom (algebraMap R O) ∧ Function.Injective (algebraMap R O) ∧
      (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) ∧
      (∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z)
def InclZIffOver : Prop :=
  ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] [CommRing O]
    [IsDomain O] [IsLocalRing O] [Algebra R O] [IsLocalHom (algebraMap R O)],
    Function.Injective (algebraMap R O) → ∀ l : ℕ, l.Prime →
    (∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) →
    (∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z) →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (e : ℕ),
      InclZ r n hn ν l e ↔ ∀ x ∈ dualWeyl O r n ν, (l : O) ^ e • x ∈ weyl O r n hn ν
def InclZIffO : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (e : ℕ),
      InclZ r n hn ν l e ↔ ∀ x ∈ dualWeyl O r n ν, (l : O) ^ e • x ∈ weyl O r n hn ν
def ExZEqO : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ),
      exZ r n hn ν l = sInf {e : ℕ | ∀ x ∈ dualWeyl O r n ν, (l : O) ^ e • x ∈ weyl O r n hn ν}
def deltaIn (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) :
    Submodule O (dualWeyl O r n ν) :=
  (weyl O r n hn ν).comap (dualWeyl O r n ν).subtype
def DeltaInMap : Prop :=
  ∀ (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    (deltaIn O r n hn ν).map (dualWeyl O r n ν).subtype = weyl O r n hn ν
def ExZEqExact : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ),
      exZ r n hn ν l = Formalism.CohomologicalDescent.exactExp (l : O) (deltaIn O r n hn ν)
def ExZLeastO : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ e : ℕ,
      LatIncl (l : O) (deltaIn O r n hn ν) e ↔ exZ r n hn ν l ≤ e
abbrev Nabla (O : Type) [CommRing O] {ι : Type} (r n : ι → ℕ) (ν : ∀ i, Fin (n i) → ℕ) : Type :=
  ⨂[O] i, ↥(dualWeyl O (r i) (n i) (ν i))
def Delta (O : Type) [CommRing O] {ι : Type} (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
    (ν : ∀ i, Fin (n i) → ℕ) : Submodule O (Nabla O r n ν) :=
  tensSub fun i => deltaIn O (r i) (n i) (hn i) (ν i)
def exSum {ι : Type} [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ)
    (l : ℕ) : ℕ :=
  ∑ i, exZ (r i) (n i) (hn i) (ν i) l
def eSum {ι : Type} [Fintype ι] (r n : ι → ℕ) (ν : ∀ i, Fin (n i) → ℕ) (l : ℕ) : ℕ :=
  ∑ i, eExp (lamU (r i) (n i) (ν i)) l
def TensorReal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) →
    ∀ y : Nabla O r n ν, (l : O) ^ exSum r n hn ν l • y ∈ Delta O r n hn ν
def TheoremAReal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) →
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν)),
    (∀ f ∈ AMFK O Γ K ρK, (l : O) ^ exSum r n hn ν l • f ∈ formsIn Γ K ρK (Delta O r n hn ν)) ∧
    sInf {J : ℕ | ∀ f ∈ AMFK O Γ K ρK, (l : O) ^ J • f ∈ formsIn Γ K ρK (Delta O r n hn ν)} ≤
      exSum r n hn ν l
def TheoremARealLoc : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) →
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν))
      (T : Type) [CommRing T] [Algebra O T] [Module T (AMFK O Γ K ρK)]
      [IsScalarTower O T (AMFK O Γ K ρK)] (S : Submonoid T),
    (∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ exSum r n hn ν l • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}) ∧
    sInf {J : ℕ | ∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ J • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}} ≤ exSum r n hn ν l
def ExSumLe : Prop :=
  LemmaAZ → ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
    (ν : ∀ i, Fin (n i) → ℕ), (∀ i, Antitone (ν i)) → ∀ l : ℕ, l.Prime →
    exSum r n hn ν l ≤ eSum r n ν l
def TheoremARealE : Prop :=
  LemmaAZ →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) →
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν)),
    (∀ f ∈ AMFK O Γ K ρK, (l : O) ^ eSum r n ν l • f ∈ formsIn Γ K ρK (Delta O r n hn ν)) ∧
    sInf {J : ℕ | ∀ f ∈ AMFK O Γ K ρK, (l : O) ^ J • f ∈ formsIn Γ K ρK (Delta O r n hn ν)} ≤
      eSum r n ν l
def TheoremARealLocE : Prop :=
  LemmaAZ →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) →
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν))
      (T : Type) [CommRing T] [Algebra O T] [Module T (AMFK O Γ K ρK)]
      [IsScalarTower O T (AMFK O Γ K ρK)] (S : Submonoid T),
    (∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ eSum r n ν l • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}) ∧
    sInf {J : ℕ | ∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ J • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}} ≤ eSum r n ν l
def TheoremARealLe2 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, r i ≤ 2) → (∀ i, Antitone (ν i)) →
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν)),
    (∀ f ∈ AMFK O Γ K ρK, (l : O) ^ eSum r n ν l • f ∈ formsIn Γ K ρK (Delta O r n hn ν)) ∧
    sInf {J : ℕ | ∀ f ∈ AMFK O Γ K ρK, (l : O) ^ J • f ∈ formsIn Γ K ρK (Delta O r n hn ν)} ≤
      eSum r n ν l
def TheoremARealLocLe2 : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, r i ≤ 2) → (∀ i, Antitone (ν i)) →
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν))
      (T : Type) [CommRing T] [Algebra O T] [Module T (AMFK O Γ K ρK)]
      [IsScalarTower O T (AMFK O Γ K ρK)] (S : Submonoid T),
    (∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ eSum r n ν l • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}) ∧
    sInf {J : ℕ | ∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ J • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}} ≤ eSum r n ν l
def PadicCoeff : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    IsDomain ℤ_[p] ∧ IsLocalRing ℤ_[p] ∧ CharZero ℤ_[p] ∧ ¬ IsUnit ((p : ℕ) : ℤ_[p])
def CoeffOver : Prop :=
  ∀ (O₀ O : Type) [CommRing O₀] [CharZero O₀] [CommRing O] [Algebra O₀ O]
    [IsLocalHom (algebraMap O₀ O)], Function.Injective (algebraMap O₀ O) →
    ∀ l : ℕ, ¬ IsUnit (l : O₀) → CharZero O ∧ ¬ IsUnit (l : O)
def FiniteOverPadic : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O],
    Function.Injective (algebraMap ℤ_[p] O) →
    IsLocalHom (algebraMap ℤ_[p] O) ∧ CharZero O ∧ ¬ IsUnit ((p : ℕ) : O)
def TheoremAPadic : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], Function.Injective (algebraMap ℤ_[l] O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) →
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν)),
    (∀ i, exZ (r i) (n i) (hn i) (ν i) l =
      Formalism.CohomologicalDescent.exactExp (l : O) (deltaIn O (r i) (n i) (hn i) (ν i))) ∧
    (∀ f ∈ AMFK O Γ K ρK, (l : O) ^ exSum r n hn ν l • f ∈ formsIn Γ K ρK (Delta O r n hn ν)) ∧
    (LemmaAZ →
      ∀ f ∈ AMFK O Γ K ρK, (l : O) ^ eSum r n ν l • f ∈ formsIn Γ K ρK (Delta O r n hn ν))
def TheoremAPadicLoc : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O], Function.Injective (algebraMap ℤ_[l] O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) →
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν))
      (T : Type) [CommRing T] [Algebra O T] [Module T (AMFK O Γ K ρK)]
      [IsScalarTower O T (AMFK O Γ K ρK)] (S : Submonoid T),
    (∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ exSum r n hn ν l • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)}) ∧
    (LemmaAZ → ∀ y : LocalizedModule S (AMFK O Γ K ρK),
        (algebraMap O T (l : O)) ^ eSum r n ν l • y ∈
          locSet S {x : AMFK O Γ K ρK | (x : G → Nabla O r n ν) ∈
            formsIn Γ K ρK (Delta O r n hn ν)})
def TheoremASharpOne : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    sInf {J : ℕ | ∀ f ∈ AMFK O (⊥ : Subgroup Unit) (⊥ : Subgroup Unit)
        (1 : Representation O (⊥ : Subgroup Unit)
          (Nabla O (ι := Unit) (fun _ => r) (fun _ => n) (fun _ => ν))),
        (l : O) ^ J • f ∈ formsIn (⊥ : Subgroup Unit) (⊥ : Subgroup Unit)
          (1 : Representation O (⊥ : Subgroup Unit)
            (Nabla O (ι := Unit) (fun _ => r) (fun _ => n) (fun _ => ν)))
          (Delta O (ι := Unit) (fun _ => r) (fun _ => n) (fun _ => hn) (fun _ => ν))} =
      exZ r n hn ν l
def Instance3 : Prop :=
  exZ 2 1 (by norm_num) (fun _ => 3) 3 = 1 ∧
  eExp (lamU 2 1 (fun _ => 3)) 3 = 1 ∧
  (∃ x ∈ dualWeyl ℤ_[3] 2 1 (fun _ => 3), x ∉ weyl ℤ_[3] 2 1 (by norm_num) (fun _ => 3)) ∧
  (∀ x ∈ dualWeyl ℤ_[3] 2 1 (fun _ => 3),
    (3 : ℤ_[3]) • x ∈ weyl ℤ_[3] 2 1 (by norm_num) (fun _ => 3)) ∧
  ∀ y : Nabla ℤ_[3] (ι := Fin 2) (fun _ => 2) (fun _ => 1) (fun _ _ => 3),
    (3 : ℤ_[3]) ^ 2 • y ∈
      Delta ℤ_[3] (ι := Fin 2) (fun _ => 2) (fun _ => 1) (fun _ => by norm_num) (fun _ _ => 3)
def nablaRep (O : Type) [CommRing O] {ι : Type} (r n : ι → ℕ) (ν : ∀ i, Fin (n i) → ℕ) :
    Representation O (∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O) (Nabla O r n ν) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun i => (dualWeylRep O (r i) (n i) (ν i)).comp (Pi.evalMonoidHom _ i))
def levelRep (O : Type) [CommRing O] {ι : Type} (r n : ι → ℕ) (ν : ∀ i, Fin (n i) → ℕ)
    {G : Type} [Group G] (K : Subgroup G) (φ : K →* ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O) :
    Representation O K (Nabla O r n ν) :=
  (nablaRep O r n ν).comp φ
def NablaRepTprod : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) (r n : ι → ℕ) (ν : ∀ i, Fin (n i) → ℕ)
    (g : ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O)
    (a : ∀ i, ↥(dualWeyl O (r i) (n i) (ν i))),
    nablaRep O r n ν g (PiTensorProduct.tprod O a) =
      PiTensorProduct.tprod O (fun i => dualWeylRep O (r i) (n i) (ν i) (g i) (a i)) ∧
    ∀ i, ((dualWeylRep O (r i) (n i) (ν i) (g i) (a i) : ↥(dualWeyl O (r i) (n i) (ν i))) :
      MvPolynomial (Fin (r i) × Fin (n i)) O) = dwAct O (r i) (n i) (g i) (a i)
def DeltaInStable : Prop :=
  ∀ (O : Type) [CommRing O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ)
    (g : Matrix.GeneralLinearGroup (Fin r) O), ∀ x ∈ deltaIn O r n hn ν,
    dualWeylRep O r n ν g x ∈ deltaIn O r n hn ν
def DeltaStable : Prop :=
  ∀ (O : Type) [CommRing O] (ι : Type) (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i)
    (ν : ∀ i, Fin (n i) → ℕ),
    (∀ (g : ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O), ∀ x ∈ Delta O r n hn ν,
      nablaRep O r n ν g x ∈ Delta O r n hn ν) ∧
    ∀ (G : Type) [Group G] (K : Subgroup G)
      (φ : K →* ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O),
      IsStable (levelRep O r n ν K φ) (Delta O r n hn ν)
def TheoremAGL : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) →
    ∀ (G : Type) [Group G] (Γ K : Subgroup G)
      (φ : K →* ∀ i, Matrix.GeneralLinearGroup (Fin (r i)) O),
    (∃ hU : IsStable (levelRep O r n ν K φ) (Delta O r n hn ν),
      ∃ E : AMFK O Γ K (resRep (levelRep O r n ν K φ) (Delta O r n hn ν) hU) ≃ₗ[O]
          formsIn Γ K (levelRep O r n ν K φ) (Delta O r n hn ν),
        ∀ f g, (E f : G → Nabla O r n ν) g = ((f : G → Delta O r n hn ν) g : Nabla O r n ν)) ∧
    (∀ f ∈ AMFK O Γ K (levelRep O r n ν K φ),
      (l : O) ^ exSum r n hn ν l • f ∈ formsIn Γ K (levelRep O r n ν K φ) (Delta O r n hn ν)) ∧
    (LemmaAZ → ∀ f ∈ AMFK O Γ K (levelRep O r n ν K φ),
      (l : O) ^ eSum r n ν l • f ∈ formsIn Γ K (levelRep O r n ν K φ) (Delta O r n hn ν))
def DeltaFree : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ),
    Antitone ν → Module.Free O (deltaIn O r n hn ν)
def TensorInj : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) →
    Function.Injective (PiTensorProduct.map fun i => (deltaIn O (r i) (n i) (hn i) (ν i)).subtype)
def ESumLogBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (ν : ∀ i, Fin (n i) → ℕ), (∀ i, Antitone (ν i)) →
    ∀ l : ℕ, l.Prime → ∀ (lo : ι → ℤ) (h : ι → ℕ),
    (∀ i a, lo i ≤ lamU (r i) (n i) (ν i) a ∧ lamU (r i) (n i) (ν i) a ≤ lo i + (h i : ℤ)) →
    ((eSum r n ν l : ℕ) : ℝ) * Real.log l ≤ ∑ i, ((r i).choose 2 : ℝ) * Real.log (h i) ∧
    ((∀ i, h i ≤ l) → eSum r n ν l = 0)
def TheoremARealLog : Prop :=
  LemmaAZ →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) → ∀ (lo : ι → ℤ) (h : ι → ℕ),
    (∀ i a, lo i ≤ lamU (r i) (n i) (ν i) a ∧ lamU (r i) (n i) (ν i) a ≤ lo i + (h i : ℤ)) →
    ((exSum r n hn ν l : ℕ) : ℝ) * Real.log l ≤ ∑ i, ((r i).choose 2 : ℝ) * Real.log (h i) ∧
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν)),
    ((sInf {J : ℕ | ∀ f ∈ AMFK O Γ K ρK,
        (l : O) ^ J • f ∈ formsIn Γ K ρK (Delta O r n hn ν)} : ℕ) : ℝ) * Real.log l ≤
      ∑ i, ((r i).choose 2 : ℝ) * Real.log (h i)
def ESumZero : Prop :=
  LemmaAZ →
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) →
    ∀ (ι : Type) [Fintype ι] (r n : ι → ℕ) (hn : ∀ i, n i ≤ r i) (ν : ∀ i, Fin (n i) → ℕ),
    (∀ i, Antitone (ν i)) → eSum r n ν l = 0 →
    (∀ i, dualWeyl O (r i) (n i) (ν i) = weyl O (r i) (n i) (hn i) (ν i)) ∧
    Delta O r n hn ν = ⊤ ∧
    ∀ (G : Type) [Group G] (Γ K : Subgroup G) (ρK : Representation O K (Nabla O r n ν)),
    formsIn Γ K ρK (Delta O r n hn ν) = AMFK O Γ K ρK ∧
    sInf {J : ℕ | ∀ f ∈ AMFK O Γ K ρK,
      (l : O) ^ J • f ∈ formsIn Γ K ρK (Delta O r n hn ν)} = 0
def ExZIndep : Prop :=
  ∀ (O O' : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [CharZero O] [CommRing O']
    [IsDomain O'] [IsLocalRing O'] [CharZero O'] (l : ℕ), l.Prime →
    ¬ IsUnit (l : O) → ¬ IsUnit (l : O') →
    ∀ (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ),
      sInf {e : ℕ | ∀ x ∈ dualWeyl O r n ν, (l : O) ^ e • x ∈ weyl O r n hn ν} =
        sInf {e : ℕ | ∀ x ∈ dualWeyl O' r n ν, (l : O') ^ e • x ∈ weyl O' r n hn ν}
end Formalism.CohomologicalDescent.RealLocalDeltaNabla


