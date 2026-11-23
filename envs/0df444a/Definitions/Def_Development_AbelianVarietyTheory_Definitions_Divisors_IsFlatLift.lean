-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:56.637392+00:00
-- url     : https://prove2.me/theorems/bce0eb0e-e195-44ad-b24c-e5648fa739e6
-- title:
--   Is Flat Lift
-- statement:
--   Definitions and structural lemmas for Is Flat Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsFlatLift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
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
namespace GlobalTheory.DI
section Cochain
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
def delta (c : Finset ι → E) : Finset ι → E :=
  fun t => ∑ i ∈ t, cubeSign t i • c (t.erase i)
def Dtot (d : E →+ E) (c : Finset ι → E) : Finset ι → E :=
  fun t => delta c t + (-1 : ℤ) ^ t.card • d (c t)
omit [LinearOrder ι] in

def InCech (N : Finset ι → AddSubgroup E) (m : ℕ) (c : Finset ι → E) : Prop :=
  c ∅ = 0 ∧ (∀ s, c s ∈ N s) ∧ ∀ s, s.card ≠ m → c s = 0
def CechZero (N : Finset ι → AddSubgroup E) (b : ℕ) : Prop :=
  ∀ c, InCech N (b + 1) c → delta c = 0 → ∃ y, InCech N b y ∧ delta y = c
omit [LinearOrder ι] in

def InTot (T : ℕ → Finset ι → AddSubgroup E) (m : ℕ) (c : Finset ι → E) : Prop :=
  c ∅ = 0 ∧ (∀ q s, q + s.card = m → c s ∈ T q s) ∧ ∀ s, m < s.card → c s = 0
def HypZero (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E) (n : ℕ) : Prop :=
  ∀ c, InTot T (n + 1) c → Dtot d c = 0 → ∃ y, InTot T n y ∧ Dtot d y = c
structure CartierAt (d : E →+ E) (γ : E → E) (N T : ℕ → AddSubgroup E) : Prop where
  inj_zero : ∀ x ∈ N 0, γ x = 0 → x = 0
  inj_succ : ∀ a, ∀ x ∈ N (a + 1), ∀ z ∈ T a, γ x = d z → x = 0
  surj_zero : ∀ y ∈ T 0, d y = 0 → ∃ x ∈ N 0, y = γ x
  surj_succ : ∀ a, ∀ y ∈ T (a + 1), d y = 0 → ∃ x ∈ N (a + 1), ∃ z ∈ T a, y = γ x + d z
def cup (Φ : E → Finset ι → E) (c : Finset ι → E) : Finset ι → E :=
  fun u => ∑ j ∈ u, Φ (c (u.filter (· ≤ j))) (u.filter (j ≤ ·))
end Cochain
section Forms
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
structure IsOddDer (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) : Prop where
  mul : ∀ x y, d (x * y) = d x * y + CliffordAlgebra.involute x * d y
  sq : ∀ x, d (d x) = 0
structure IsExtD (k K : Type) [CommRing k] [CommRing K] [Algebra k K]
    (d : ExteriorAlgebra K Ω[K⁄k] →+ ExteriorAlgebra K Ω[K⁄k]) : Prop extends IsOddDer d where
  alg : ∀ a : K, d (algebraMap K _ a) = ExteriorAlgebra.ι K (KaehlerDifferential.D k K a)
def forms (B : Set K) (L : Set V) (q : ℕ) : AddSubgroup (ExteriorAlgebra K V) :=
  AddSubgroup.closure {x | ∃ b ∈ B, ∃ v : Fin q → V, (∀ k, v k ∈ L) ∧ x = b • ExteriorAlgebra.ιMulti K q v}
variable {ι : Type} [LinearOrder ι]
omit [LinearOrder ι] in

structure IsDatum (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) : Prop where
  f_smul : ∀ i (c : K) v, f i (c • v) = c ^ p • f i v
  h_smul : ∀ i j (c : K) v, h i j (c • v) = c ^ p * h i j v
  closed : ∀ i v, d (ExteriorAlgebra.ι K (f i v)) = 0
  dh : ∀ i j v, d (algebraMap K _ (h i j v)) = ExteriorAlgebra.ι K (f j v) - ExteriorAlgebra.ι K (f i v)
  cocycle : ∀ i j l v, h i j v + h j l v = h i l v
def Lop (f : ι → V →+ V) (h : ι → ι → V →+ K) (v : V) (y : Finset ι → ExteriorAlgebra K V) :
    Finset ι → ExteriorAlgebra K V := fun t =>
  if ht : t.Nonempty then
    (-1 : ℤ) ^ t.card • (ExteriorAlgebra.ι K (f (t.min' ht) v) * y t) +
      (if h2 : (t.erase (t.min' ht)).Nonempty then
        h (t.min' ht) ((t.erase (t.min' ht)).min' h2) v • y (t.erase (t.min' ht)) else 0)
  else 0
omit [LinearOrder ι] in

def oneC : Finset ι → ExteriorAlgebra K V := fun t => if t.card = 1 then 1 else 0
def prodL (f : ι → V →+ V) (h : ι → ι → V →+ K) (vs : List V) : Finset ι → ExteriorAlgebra K V :=
  vs.foldr (Lop f h) oneC
def alt (f : ι → V →+ V) (h : ι → ι → V →+ K) (a : ℕ) (v : Fin a → V) : Finset ι → ExteriorAlgebra K V :=
  ∑ σ : Equiv.Perm (Fin a), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • prodL f h (List.ofFn (v ∘ σ))
def IsPhi (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K)
    (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) : Prop :=
  ∀ (c : K) (a : ℕ) (v : Fin a → V), Φ (c • ExteriorAlgebra.ιMulti K a v) = c ^ p • alt f h a v
def IsGamma (p : ℕ) (f : V →+ V) (γ : ExteriorAlgebra K V →+* ExteriorAlgebra K V) : Prop :=
  (∀ c : K, γ (algebraMap K _ c) = algebraMap K _ (c ^ p)) ∧
    ∀ v, γ (ExteriorAlgebra.ι K v) = ExteriorAlgebra.ι K (f v)
end Forms
section Lift
variable {K Kt : Type} [CommRing K] [CommRing Kt]
structure IsFlatLift (p : ℕ) (π : Kt →+* K) : Prop where
  surj : Function.Surjective π
  ker : ∀ z, π z = 0 ↔ ∃ w, z = p * w
  ann : ∀ w, (p : Kt) * w = 0 ↔ π w = 0
def IsFrob (p : ℕ) (π : Kt →+* K) (F : Kt →+* Kt) : Prop := ∀ z, π (F z) = π z ^ p
def IsF (p : ℕ) (π : Kt →+* K) (F : Kt →+* Kt) (f : Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) : Prop :=
  (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ z w : Kt, F z = z ^ p + p * w →
    f (KaehlerDifferential.D ℤ K (π z)) =
      π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) + KaehlerDifferential.D ℤ K (π w)
def IsH (p : ℕ) (π : Kt →+* K) (F F' : Kt →+* Kt) (h : Ω[K⁄ℤ] →+ K) : Prop :=
  (∀ (c : K) v, h (c • v) = c ^ p * h v) ∧ ∀ z w : Kt, F' z = F z + p * w →
    h (KaehlerDifferential.D ℤ K (π z)) = π w
def LogLift {ι : Type} (p : ℕ) (π : Kt →+* K) (F : ι → Kt →+* Kt) (s : Finset ι) (A : Set K) (g : K) : Prop :=
  ∃ z, π z = g ∧ ∀ i ∈ s, ∃ w, π w ∈ A ∧ F i z = z ^ p * (1 + p * w)
end Lift
end GlobalTheory.DI


