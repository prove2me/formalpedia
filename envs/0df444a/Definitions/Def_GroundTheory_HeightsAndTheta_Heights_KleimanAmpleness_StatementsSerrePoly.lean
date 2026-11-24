-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:38.650104+00:00
-- url     : https://prove2.me/theorems/be4043c7-0dcc-4f5d-bae0-747fc1c18338
-- title:
--   Statements Serre Poly
-- statement:
--   Definitions and structural lemmas for Statements Serre Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/StatementsSerrePoly.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
def Cech.idRes (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] {n : ℕ}
    (U : Finset (Fin n)) : ∀ I J : Cell U, I.1 ⊆ J.1 → V →ₗ[R] V :=
  fun _ _ _ => LinearMap.id
section Laurent
variable (S : Type u) [CommRing S] (N : ℕ)
abbrev Laurent : Type u := (Fin (N + 1) → ℤ) →₀ S
def laurentExps (c : ℤ) (I : Finset (Fin (N + 1))) : Set (Fin (N + 1) → ℤ) :=
  {a | ∑ j, a j = c ∧ ∀ j ∉ I, 0 ≤ a j}
def laurentDeg (c : ℤ) (I : StdCell N) : Submodule S (Laurent S N) :=
  Finsupp.supported S S (laurentExps N c I.1)
def laurentCohom (i : ℕ) (c : ℤ) : Type u :=
  Cech.Hdeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
    (Cech.idRes S (Laurent S N) Finset.univ) i
instance (i : ℕ) (c : ℤ) : AddCommGroup (laurentCohom S N i c) :=
  inferInstanceAs (AddCommGroup (Cech.Hdeg _ _ _ _))
instance (i : ℕ) (c : ℤ) : Module S (laurentCohom S N i c) :=
  inferInstanceAs (Module S (Cech.Hdeg _ _ _ _))
def expToInt (e : Fin (N + 1) →₀ ℕ) : Fin (N + 1) → ℤ := fun j => (e j : ℤ)
def polyToLaurent : Poly S N →ₗ[S] Laurent S N where
  toFun p := Finsupp.mapDomain (expToInt N) (AddMonoidAlgebra.coeff p)
  map_add' p q := by
    change Finsupp.mapDomain _ (AddMonoidAlgebra.coeff p + AddMonoidAlgebra.coeff q) = _
    exact Finsupp.mapDomain_add
  map_smul' r p := by
    change Finsupp.mapDomain _ (r • AddMonoidAlgebra.coeff p) = _
    exact Finsupp.mapDomain_smul r _
end Laurent
def SerrePoly.Laurent.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (N : ℕ),
    Function.Injective (polyToLaurent S N) ∧
    (∀ c : ℤ, ((polyGraded S N).piece c).map (polyToLaurent S N) =
      Finsupp.supported S S (laurentExps N c ∅)) ∧
    ∃ ι : ∀ I : StdCell N, LocMod S N (Poly S N) I.1 →ₗ[S] Laurent S N,
      (∀ I, Function.Injective (ι I)) ∧
      (∀ (I J : StdCell N) (h : I.1 ⊆ J.1) (z : LocMod S N (Poly S N) I.1),
        ι J (locResS I J h z) = ι I z) ∧
      (∀ (I : StdCell N) (p : Poly S N), ι I (locMk (Poly S N) I.1 p) = polyToLaurent S N p) ∧
      ∀ (c : ℤ) (I : StdCell N), (degLoc (polyGraded S N) c I).map (ι I) = laurentDeg S N c I
def Cech.Transport.Statement : Prop :=
  ∀ (n : ℕ) (U : Finset (Fin n)) (R : Type u) [CommRing R]
    (G : Cell U → Type v) [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
    (G' : Cell U → Type w) [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
    (ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J) (ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J)
    (deg : ∀ I, Submodule R (G I)) (deg' : ∀ I, Submodule R (G' I)) (φ : ∀ I, G I →ₗ[R] G' I)
    (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (hdeg : ∀ I m, m ∈ deg I → φ I m ∈ deg' I),
    (∀ I, Function.Injective (φ I)) → (∀ I, (deg I).map (φ I) = deg' I) →
    ∀ i, Function.Bijective (Cech.mapHdeg deg deg' φ hφ hdeg i)
def Cech.Cone.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] (N : ℕ)
    (J : Finset (Fin (N + 1))),
    (∀ (W : Submodule R V) (i₀ : Fin (N + 1)), i₀ ∉ J → ∀ (i : ℕ)
      (z : Cech.Cochain (fun _ : StdCell N => V) (i + 1)),
      Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) (i + 1) z = 0 →
      (∀ I, z I ∈ W) → (∀ I, ¬ J ⊆ I.1.1 → z I = 0) →
      ∃ y : Cech.Cochain (fun _ : StdCell N => V) i, (∀ I, y I ∈ W) ∧ (∀ I, ¬ J ⊆ I.1.1 → y I = 0) ∧
        Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) i y = z) ∧
    (J.Nonempty → ∀ i₀ : Fin (N + 1), i₀ ∉ J → ∀ z : Cech.Cochain (fun _ : StdCell N => V) 0,
      Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0 →
      (∀ I, ¬ J ⊆ I.1.1 → z I = 0) → z = 0) ∧
    ∀ z : Cech.Cochain (fun _ : StdCell N => V) 0,
      Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0 → ∀ I K, z I = z K
def SerrePoly.LaurentCohom.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (N : ℕ),
    (∀ (i : ℕ) (c : ℤ), Module.Finite S (laurentCohom S N i c)) ∧
    (∀ c : ℤ, 0 ≤ c → ∀ i, 1 ≤ i → Subsingleton (laurentCohom S N i c)) ∧
    ∀ c : ℤ, 0 ≤ c → ∀ z : Cech.Cochain (fun _ : StdCell N => Laurent S N) 0,
      z ∈ Cech.cocyDeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
        (Cech.idRes S (Laurent S N) Finset.univ) 0 →
      ∃ f ∈ Finsupp.supported S S (laurentExps N c ∅), ∀ I, z I = f
section Hypotheses
end Hypotheses
end
end GroundTheory.Heights₂.Heights.Kleiman


