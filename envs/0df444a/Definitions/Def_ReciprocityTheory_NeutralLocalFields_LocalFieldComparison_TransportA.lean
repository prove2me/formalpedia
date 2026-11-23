-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
-- name    : ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:56.196801+00:00
-- url     : https://prove2.me/theorems/e187488c-e71d-4ab9-96bd-ce169a3c267a
-- title:
--   Transport A
-- statement:
--   Definitions and structural lemmas for Transport A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/TransportA.lean

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
section Iso
variable {R : Type*} [CommRing R]
  {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (e : H ≃ₜ* G) (rho : Representation R G M) (rho' : Representation R H M)
  (hc : ∀ h m, rho (e h) m = rho' h m)
theorem continuous_coe_iso : Continuous ((e : H →* G)) := by
  exact e.continuous
theorem continuous_coe_iso_symm : Continuous ((e.symm : G →* H)) := by
  exact e.symm.continuous
include hc in
theorem compat_symm : ∀ g m, (LinearMap.id (R := R) (M := M)) (rho' ((e.symm : G →* H) g) m) =
    rho g (LinearMap.id (R := R) (M := M) m) := by
  intro g m
  rw [LinearMap.id_apply, LinearMap.id_apply, ← hc]
  congr 2
  exact e.apply_symm_apply g
include hc in
theorem invariants_eq_of_iso : H0 rho' = H0 rho := by
  ext m
  simp only [H0, Representation.mem_invariants]
  constructor
  · intro hH g
    have := hH ((e.symm : G →* H) g)
    rw [← hc] at this
    simpa using this
  · intro hH h
    rw [← hc]
    exact hH _
def equivH0OfIso : H0 rho ≃ₗ[R] H0 rho' := LinearEquiv.ofEq _ _ (invariants_eq_of_iso e rho rho' hc).symm
def equivH1OfIso : H1 rho ≃ₗ[R] H1 rho' :=
  LinearEquiv.ofLinear
    (pairH1DecompositionMap rho rho' (e : H →* G) (continuous_coe_iso e) LinearMap.id continuous_id hc)
    (pairH1DecompositionMap rho' rho (e.symm : G →* H) (continuous_coe_iso_symm e) LinearMap.id continuous_id
      (compat_symm e rho rho' hc))
    (Submodule.linearMap_qext _ (LinearMap.ext fun f => by
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1; apply Subtype.ext; funext g
      show f.1 (e.symm (e g)) = f.1 g
      rw [ContinuousMulEquiv.symm_apply_apply]))
    (Submodule.linearMap_qext _ (LinearMap.ext fun f => by
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1; apply Subtype.ext; funext g
      show f.1 (e (e.symm g)) = f.1 g
      rw [ContinuousMulEquiv.apply_symm_apply]))
def equivH2OfIso : H2 rho ≃ₗ[R] H2 rho' :=
  LinearEquiv.ofLinear
    (compatiblePairH2 rho rho' (e : H →* G) (continuous_coe_iso e) LinearMap.id continuous_id hc)
    (compatiblePairH2 rho' rho (e.symm : G →* H) (continuous_coe_iso_symm e) LinearMap.id continuous_id
      (compat_symm e rho rho' hc))
    (Submodule.linearMap_qext _ (LinearMap.ext fun f => by
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1; apply Subtype.ext; funext g
      show f.1 (e.symm (e g.1), e.symm (e g.2)) = f.1 g
      simp))
    (Submodule.linearMap_qext _ (LinearMap.ext fun f => by
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1; apply Subtype.ext; funext g
      show f.1 (e (e.symm g.1), e (e.symm g.2)) = f.1 g
      simp))
@[simp] theorem equivH0OfIso_apply (m : H0 rho) : (equivH0OfIso e rho rho' hc m).1 = m.1 := rfl
end Iso
section Degn
variable {R : Type*} [CommRing R]
  {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (rho : Representation R G M) (rho' : Representation R H M) (phi : H →* G)
  (hphi : Continuous phi) (hc : ∀ h m, rho (phi h) m = rho' h m)
theorem continuous_comp_pi (n : ℕ) (hphi : Continuous phi) :
    Continuous fun x : Fin n → H => phi ∘ x :=
  continuous_pi fun i => hphi.comp (continuous_apply i)
include hc in
theorem dn_comp (n : ℕ) (f : (Fin n → G) → M) (g : Fin (n + 1) → H) :
    dn rho' n (fun x => f (phi ∘ x)) g = dn rho n f (phi ∘ g) := by
  have hc' : ∀ j : Fin (n + 1),
      phi ∘ Fin.contractNth j (· * ·) g = Fin.contractNth j (· * ·) (phi ∘ g) := by
    intro j
    funext k
    simp only [Function.comp, Fin.contractNth]
    split_ifs <;> simp [map_mul]
  simp only [dn, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hc]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc' j]
include hphi hc in

def pairZn (n : ℕ) : Zn rho n →ₗ[R] Zn rho' n where
  toFun f := ⟨fun x => f.1 (phi ∘ x), by
    have hf : Continuous f.1 := (Submodule.mem_inf.1 f.2).1
    have hk := (Submodule.mem_inf.1 f.2).2
    rw [LinearMap.mem_ker] at hk
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · change Continuous _
      exact hf.comp (continuous_comp_pi phi n hphi)
    · rw [LinearMap.mem_ker]
      funext g
      rw [dn_comp rho rho' phi hc, hk]
      rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem pairZn_apply (n : ℕ) (f : Zn rho n) (x : Fin n → H) :
    (pairZn rho rho' phi hphi hc n f).1 x = f.1 (phi ∘ x) := rfl
include hphi hc in
theorem pairZn_mem_Bn (n : ℕ) (f : Zn rho n) (hf : f.1 ∈ Bn rho n) :
    (pairZn rho rho' phi hphi hc n f).1 ∈ Bn rho' n := by
  cases n with
  | zero =>
    change f.1 ∈ (⊥ : Submodule R ((Fin 0 → G) → M)) at hf
    change _ ∈ (⊥ : Submodule R ((Fin 0 → H) → M))
    rw [Submodule.mem_bot] at hf ⊢
    funext x
    rw [pairZn_apply, hf]
    rfl
  | succ n =>
    change f.1 ∈ (Cn rho n).map (dn rho n) at hf
    change _ ∈ (Cn rho' n).map (dn rho' n)
    obtain ⟨c, hcC, hcd⟩ := Submodule.mem_map.mp hf
    refine Submodule.mem_map.mpr ⟨fun x => c (phi ∘ x), ?_, ?_⟩
    · exact (show Continuous c from hcC).comp (continuous_comp_pi phi n hphi)
    · funext g
      rw [dn_comp rho rho' phi hc, hcd]
      rfl
def pairHn (n : ℕ) : Hn rho n →ₗ[R] Hn rho' n :=
  Submodule.mapQ _ _ (pairZn rho rho' phi hphi hc n) fun f hf =>
    pairZn_mem_Bn rho rho' phi hphi hc n f hf
end Degn
section IsoN
variable {R : Type*} [CommRing R]
  {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  (e : H ≃ₜ* G) (rho : Representation R G M) (rho' : Representation R H M)
  (hc : ∀ h m, rho (e h) m = rho' h m)
include hc in
theorem compat_symm' : ∀ g m, rho' ((e.symm : G →* H) g) m = rho g m := by
  intro g m
  rw [← hc]
  congr 2
  exact e.apply_symm_apply g
def isoHn (n : ℕ) : Hn rho n ≃ₗ[R] Hn rho' n :=
  LinearEquiv.ofLinear
    (pairHn rho rho' (e : H →* G) (continuous_coe_iso e) hc n)
    (pairHn rho' rho (e.symm : G →* H) (continuous_coe_iso_symm e) (compat_symm' e rho rho' hc) n)
    (Submodule.linearMap_qext _ (LinearMap.ext fun f => by
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1; apply Subtype.ext; funext g
      show f.1 (fun i => e.symm (e (g i))) = f.1 g
      simp))
    (Submodule.linearMap_qext _ (LinearMap.ext fun f => by
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1; apply Subtype.ext; funext g
      show f.1 (fun i => e (e.symm (g i))) = f.1 g
      simp))
end IsoN
section Bij
variable {R : Type*} [CommRing R] {A A' B B' C C' : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
  [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']
end Bij
section Cups
variable {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R] {G G' : Type}
  [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  (e : G ≃ₜ* G') (χ : G' →* Rˣ) (rho : Representation R G' M)
theorem twDual_compat : ∀ h φ, (twDual χ rho).comp (MonoidHom.id G') (e h) φ =
    (twDual (χ.comp (e : G →* G')) (rho.comp (e : G →* G'))).comp (MonoidHom.id G) h φ := by
  intro h φ
  show TDual.mk (((χ (e h) : Rˣ) : R) • ((φ : M →ₗ[R] R) ∘ₗ rho (e h)⁻¹)) =
    TDual.mk (((χ (e h) : Rˣ) : R) • ((φ : M →ₗ[R] R) ∘ₗ rho (e h⁻¹)))
  simp only [map_inv]
end Cups
end ReciprocityTheory.Neutral.Bridge


