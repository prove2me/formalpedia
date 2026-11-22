-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- name    : Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:19.777868+00:00
-- url     : https://prove2.me/theorems/9f91c9d7-162f-46c2-bdb7-f1535272e81c
-- title:
--   Branch Map
-- statement:
--   Definitions and structural lemmas for Branch Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/BranchMap.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace Formalism.BranchingDeterminantCap
def bmF {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (k a i : Fin n) : Module.End R M :=
  (if a = i then ((u + ((k : ℕ) : ℤ) : ℤ) : Module.End R M) else 0) - E a i
def bmM {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (α β : Fin n → Fin n) : Module.End R M :=
  (List.ofFn fun k => bmF E u k (α k) (β k)).prod
def bmPi {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) (β : Fin n → Fin n) : Module.End R M :=
  ∑ α : Equiv.Perm (Fin n), ((Equiv.Perm.sign α : ℤˣ) : ℤ) • bmM E u α β
def capDet {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
    (E : Fin n → Fin n → Module.End R M) (u : ℤ) : Module.End R M :=
  bmPi E u id
abbrev BP (R : Type*) [CommRing R] (n : ℕ) := MvPolynomial (Fin (n + 1) × Fin n) R
def bmE (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) : Derivation R (BP R n) (BP R n) :=
  mkDerivation R fun v => if v.2 = t ∧ v.1 ≠ Fin.last n then X (v.1, s) else 0
def bmZ (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) : Derivation R (BP R n) (BP R n) :=
  mkDerivation R fun v => if v.2 = t ∧ v.1 = Fin.last n then X (v.1, s) else 0
def bmEL (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) : Module.End R (BP R n) :=
  (bmE R n s t).toLinearMap
def bmZL (R : Type*) [CommRing R] (n : ℕ) (s t : Fin n) : Module.End R (BP R n) :=
  (bmZ R n s t).toLinearMap
def bmCap (R : Type*) [CommRing R] (n : ℕ) (u : ℤ) : Module.End R (BP R n) :=
  capDet (bmEL R n) u
def zW (n : ℕ) : Fin (n + 1) × Fin n → (Fin n → ℤ) :=
  fun v => if v.1 = Fin.last n then Pi.single v.2 1 else 0
def lastW (n : ℕ) : Fin (n + 1) × Fin n → ℕ := fun v => if v.1 = Fin.last n then 1 else 0
def omg {n : ℕ} (β : Fin n → ℤ) : ℤ := ∑ s : Fin n, ((((s : ℕ) : ℤ)) + 1) * β s
def zcomp (R : Type*) [CommRing R] (n : ℕ) (β : Fin n → ℤ) : Module.End R (BP R n) :=
  weightedHomogeneousComponent (zW n) β
def emb (R : Type*) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R →ₐ[R] BP R n :=
  rename fun v => (v.1.castSucc, v.2)
def zmon (R : Type*) [CommRing R] (n : ℕ) (b : Fin n → ℕ) : BP R n :=
  ∏ s : Fin n, X (Fin.last n, s) ^ b s
def bmChi {n : ℕ} (lam : Fin n → ℕ) (β : Fin n → ℤ) (u : ℤ) : ℤ :=
  ∏ j : Fin n, (u + ((j : ℕ) : ℤ) - ((lam j : ℤ) - β j))
def bmAdm {n : ℕ} (lam : Fin n → ℕ) (d : ℕ) (β : Fin n → ℤ) : Prop :=
  (∀ s, 0 ≤ β s) ∧ ∑ s, β s = (d : ℤ) ∧ Interlace (lamZ lam) (fun i => (lam i : ℤ) - β i)
def IsLow {R : Type*} [CommRing R] {n : ℕ} (D : ℤ) (L : BP R n) : Prop :=
  ∀ m ∈ L.support, omg (Finsupp.weight (zW n) m) < D
def bmLift (R : Type*) [CommRing R] (n : ℕ) (lam b : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R)
    (G : BP R n) : Prop :=
  G ∈ dualWeyl R (n + 1) n lam ∧ IsWeightedHomogeneous (lastW n) G (∑ s, b s) ∧
    IsLow (omg fun s => (b s : ℤ)) (G - zmon R n b * emb R n f)
def bmList {n : ℕ} (lam sg : Fin n → ℕ) : List ℤ :=
  (Finset.univ : Finset (Fin n)).toList.flatMap fun i =>
    ((rset (lamZ lam) (fun i => (sg i : ℤ)) i).erase (sg i : ℤ)).toList.map fun v => v - ((i : ℕ) : ℤ)
def bmZop (R : Type*) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) : Module.End R (BP R n) :=
  ((bmList lam sg).map (bmCap R n)).prod
def bmIL {n : ℕ} (lam sg : Fin n → ℕ) : Prop := ∀ i : Fin n, sg i ≤ lam i ∧ nuNext lam i ≤ sg i
def bmRho {n : ℕ} (lam sg : Fin n → ℕ) : Fin (n + 1) → ℕ :=
  fun a => if h : a.val < n then sg ⟨a.val, h⟩ else ∑ s, (lam s - sg s)
section bmAList
variable {A : Type*} [Ring A]
end bmAList
section bmACap
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap
section bmACap2
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap2
section bmACap3
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap3
def bmF_Fil {R : Type*} [CommRing R] {n : ℕ} (D : ℤ) (F : BP R n) : Prop :=
  ∀ m ∈ F.support, omg (Finsupp.weight (zW n) m) ≤ D
def bmG_D (R : Type*) [CommRing R] (n : ℕ) (s : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  if h : s ≤ n then lpMinor R s h h else 1
def bmW (R : Type*) [CommRing R] (n : ℕ) (lam : Fin n → ℕ) (d : ℕ) : Submodule R (BP R n) :=
  dualWeyl R (n + 1) n lam ⊓ weightedHomogeneousSubmodule R (lastW n) d
def bmRel (R : Type) [CommRing R] (n : ℕ) (lam sg : Fin n → ℕ) (f : ↥(dualWeyl R n n sg)) (G : BP R n) : Prop :=
  bmLift R n lam (fun s => lam s - sg s) (f : MvPolynomial (Fin n × Fin n) R) G
end Formalism.BranchingDeterminantCap


