-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_DepthPageFirstZetaFactorEqPrimePower
-- name    : Formalism_CoboundaryTransfers_GammaStableTransfers_DepthPageFirstZetaFactorEqPrimePower
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:04:34.297741+00:00
-- url     : https://prove2.me/theorems/9e8be68e-fdee-517d-86f0-f249e7b78d6d
-- title:
--   Depth Page First Zeta Factor Eq Prime Power
-- statement:
--   Definitions and structural lemmas for Depth Page First Zeta Factor Eq Prime Power, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/DepthPageFirstZetaFactorEqPrimePower.lean

import Definitions.Def_Formalism_CoboundaryTransfers_StatementBridge
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_FiniteCocyclesLeCocycles
import Theorems.Thm_P2M_Formalism_WachCohomologyFacts_PCoh____comm_26f0b5ea9b7b
import Theorems.Thm_P2M_Formalism_WachCohomologyFacts_PCoh_fD___5f81d7cb3ce3
import Theorems.Thm_P2M_Formalism_WachCohomologyFacts_PCoh_fD___83e0ac9c2344

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
open Formalism
namespace GammaInvariantLatticeLift
theorem gamma_invariant_lattice_lift {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D]
    [Module A D] [Module O D] [IsScalarTower O A D]
    (X Q v t : A) (γA : A →ₐ[O] A) (M : ℕ) (N : Submodule A D) (γ : D →ₗ[O] D)
    (hv : IsUnit v) (hvt : v = 1 + X * t) (hQ : γA Q = v * Q)
    (hbij : Function.Bijective (fun x : D => Q • x))
    (hsmul : ∀ (a : A) (x : D), γ (a • x) = γA a • γ x)
    (hN : ∀ x ∈ N, ∃ x' ∈ N, γ x - x = X • x') :
    ∀ y : D, Q ^ M • y ∈ N → ∃ y' : D, Q ^ M • y' ∈ N ∧ γ y - y = X • y' := by
  intro y hy
  have hit : ∀ k (x : D), (fun x : D => Q • x)^[k] x = Q ^ k • x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  have hbM : Function.Bijective (fun x : D => Q ^ M • x) := by
    have := hbij.iterate M
    convert this using 1
    funext x
    rw [hit]
  set w : A := ↑hv.unit⁻¹ with hw_def
  have hwv : w * v = 1 := hv.val_inv_mul
  have hw1 : w - 1 = X * (-(w * t)) := by
    have : w - 1 = w * (1 - v) := by rw [mul_sub, hwv, mul_one]
    rw [this, hvt]; ring
  obtain ⟨s, hs⟩ : X ∣ w ^ M - 1 := by
    have h1 := sub_dvd_pow_sub_pow w 1 M
    rw [one_pow] at h1
    exact (Dvd.intro _ hw1.symm).trans h1
  have hwM : w ^ M = 1 + X * s := by rw [← hs]; ring
  obtain ⟨n', hn'N, hn'⟩ := hN _ hy
  have e1 : (v * Q) ^ M • γ y = Q ^ M • y + X • n' := by
    rw [← hQ, ← map_pow, ← hsmul, ← hn']
    abel
  have key : Q ^ M • γ y = w ^ M • (Q ^ M • y + X • n') := by
    rw [← e1, smul_smul, mul_pow, ← mul_assoc, ← mul_pow, hwv, one_pow, one_mul]
  set m : D := s • (Q ^ M • y) + w ^ M • n' with hm_def
  have hmN : m ∈ N := N.add_mem (N.smul_mem _ hy) (N.smul_mem _ hn'N)
  have hQm : Q ^ M • (γ y - y) = X • m := by
    rw [smul_sub, key, hm_def, hwM]
    module
  obtain ⟨y', hy'⟩ := hbM.2 m
  refine ⟨y', ?_, ?_⟩
  · show Q ^ M • y' ∈ N
    have : Q ^ M • y' = m := hy'
    rw [this]; exact hmN
  · apply hbM.1
    show Q ^ M • (γ y - y) = Q ^ M • (X • y')
    have : Q ^ M • y' = m := hy'
    rw [hQm, smul_comm, this]
section Base
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
end Base
section Inst
variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : WachCohomologyFacts.Base O A} {E : WachCohomologyFacts.Amb B AA} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V] [IsScalarTower O A V]
theorem smul_eq_alg (a : A) (v : V) : a • v = algebraMap A AA a • v :=
  (algebraMap_smul AA a v).symm
theorem smul_bij (_E : WachCohomologyFacts.Amb B AA) (a : A) (ha : IsUnit (algebraMap A AA a)) :
    Function.Bijective (fun x : ZMod n → V => a • x) := by
  obtain ⟨u, hu⟩ := ha
  refine Function.bijective_iff_has_inverse.mpr ⟨fun x j => (↑u⁻¹ : AA) • x j, ?_, ?_⟩
  · intro x
    funext j
    show (↑u⁻¹ : AA) • (a • x j) = x j
    rw [smul_eq_alg (AA := AA) a (x j), ← hu, smul_smul, Units.inv_mul, one_smul]
  · intro x
    funext j
    show a • ((↑u⁻¹ : AA) • x j) = x j
    rw [smul_eq_alg (AA := AA) a, ← hu, smul_smul, Units.mul_inv, one_smul]
theorem Φ_smul (W : WachCohomologyFacts.WachDatum E n V) (a : A) (x : ZMod n → V) :
    W.Φ (a • x) = B.φ a • W.Φ x := by
  funext j
  show W.φ (j - 1) (a • x (j - 1)) = B.φ a • W.φ (j - 1) (x (j - 1))
  rw [smul_eq_alg (AA := AA) a, W.φ_smul, E.φ_ext, ← smul_eq_alg]
theorem Γ_smul (W : WachCohomologyFacts.WachDatum E n V) (a : A) (x : ZMod n → V) :
    W.Γ (a • x) = B.γ a • W.Γ x := by
  funext j
  show W.γ j (a • x j) = B.γ a • W.γ j (x j)
  rw [smul_eq_alg (AA := AA) a, W.γ_smul, E.γ_ext, ← smul_eq_alg]
theorem Γ_sub (W : WachCohomologyFacts.WachDatum E n V) :
    ∀ x ∈ Submodule.pi Set.univ W.N, ∃ x' ∈ Submodule.pi Set.univ W.N, W.Γ x - x = B.X • x' := by
  intro x hx
  rw [Submodule.mem_pi] at hx
  choose x' hx' he using fun j => W.γ_sub j (x j) (hx j (Set.mem_univ j))
  exact ⟨x', (Submodule.mem_pi).2 fun j _ => hx' j, funext fun j => he j⟩
theorem γq (B : WachCohomologyFacts.Base O A) : B.γ B.q = (1 + B.X * B.c) * B.q := by
  show B.γ (B.X + (B.ℓ : A)) = (1 + B.X * B.c) * (B.X + (B.ℓ : A))
  rw [map_add, map_natCast]
  linear_combination B.hγX
def toWach (W : WachCohomologyFacts.WachDatum E n V) (M : ℕ) (hc : IsUnit (1 + B.X * B.c))
    (hM : ∀ i, ∀ x ∈ W.N i, B.q ^ M • W.φ i x ∈ W.N (i + 1)) :
    WachMod (baseOfArchimedeanComponents B) M (ZMod n → V) where
  N := Submodule.pi Set.univ W.N
  φ := W.Φ
  γ := W.Γ
  φ_smul := Φ_smul W
  γ_smul := Γ_smul W
  comm := fun x => (WachCohomologyFacts.PCoh.ΓΦ_comm W x).symm
  X_inj := by
    intro x hx
    exact (smul_bij E B.X E.hX).1 (hx.trans (smul_zero _).symm)
  Q_bij := smul_bij E B.q E.hq
  φ_N := by
    intro x hx
    rw [Submodule.mem_pi] at hx ⊢
    intro j _
    have := hM (j - 1) (x (j - 1)) (hx (j - 1) (Set.mem_univ _))
    rw [sub_add_cancel] at this
    exact this
  γ_N := Γ_sub W
  γ_QN := gamma_invariant_lattice_lift B.X B.q (1 + B.X * B.c) B.c B.γ M (Submodule.pi Set.univ W.N) W.Γ hc rfl
    (γq B) (smul_bij E B.q E.hq) (Γ_smul W) (Γ_sub W)
end Inst
section Agree
variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : WachCohomologyFacts.Base O A} {E : WachCohomologyFacts.Amb B AA} {n : ℕ}
  {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V] [IsScalarTower O A V] {M : ℕ}
  (W' : WachMod (baseOfArchimedeanComponents B) M (ZMod n → V)) (W : WachCohomologyFacts.WachDatum E n V)
end Agree
section HomPart
variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA] {B : WachCohomologyFacts.Base O A} {E : WachCohomologyFacts.Amb B AA} {n : ℕ}
  {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁] [IsScalarTower O A V₁]
  {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂] [IsScalarTower O A V₂]
  {W₁ : WachCohomologyFacts.WachDatum E n V₁} {W₂ : WachCohomologyFacts.WachDatum E n V₂}
def fA (hm : WachCohomologyFacts.Hom W₁ W₂) : (ZMod n → V₁) →ₗ[A] (ZMod n → V₂) :=
  LinearMap.pi (fun j => (hm.f.restrictScalars A).comp (LinearMap.proj j))
theorem fA_apply (hm : WachCohomologyFacts.Hom W₁ W₂) (x : ZMod n → V₁) : fA hm x = hm.fD x := rfl
def toHom (hm : WachCohomologyFacts.Hom W₁ W₂) {M : ℕ}
    (W₁' : WachMod (baseOfArchimedeanComponents B) M (ZMod n → V₁)) (W₂' : WachMod (baseOfArchimedeanComponents B) M (ZMod n → V₂))
    (hN₁ : W₁'.N = Submodule.pi Set.univ W₁.N) (hφ₁ : ⇑W₁'.φ = ⇑W₁.Φ) (hγ₁ : ⇑W₁'.γ = ⇑W₁.Γ)
    (hN₂ : W₂'.N = Submodule.pi Set.univ W₂.N) (hφ₂ : ⇑W₂'.φ = ⇑W₂.Φ) (hγ₂ : ⇑W₂'.γ = ⇑W₂.Γ) :
    Hom W₁' W₂' where
  f := fA hm
  φ_comm := by
    intro x
    rw [congrFun hφ₁ x, congrFun hφ₂, fA_apply, fA_apply]
    exact WachCohomologyFacts.PCoh.fD_Φ hm x
  γ_comm := by
    intro x
    rw [congrFun hγ₁ x, congrFun hγ₂, fA_apply, fA_apply]
    exact WachCohomologyFacts.PCoh.fD_Γ hm x
  N_le := by
    intro x hx
    rw [hN₁, Submodule.mem_pi] at hx
    rw [hN₂, Submodule.mem_pi]
    intro j _
    exact hm.N_le j (x j) (hx j (Set.mem_univ j))
end HomPart
end GammaInvariantLatticeLift
end Formalism.CoboundaryTransfers


