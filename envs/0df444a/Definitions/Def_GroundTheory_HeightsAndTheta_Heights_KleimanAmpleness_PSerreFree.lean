-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:52.13572+00:00
-- url     : https://prove2.me/theorems/07370cd1-fe21-4a1c-bad1-611052f5b16c
-- title:
--   PSerre Free
-- statement:
--   Definitions and structural lemmas for PSerre Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreFree.lean

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
section FreeGraded
variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
omit [IsScalarTower S (Poly S N) M] in

theorem smul_mem_of_mem_polyGraded (𝓜 : GradedPMod S N M) {a c : ℤ} {p : Poly S N} {m : M}
    (hp : p ∈ (polyGraded S N).piece a) (hm : m ∈ 𝓜.piece c) : p • m ∈ 𝓜.piece (c + a) := by
  change p ∈ weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) a at hp
  rw [mem_weightedHomogeneousSubmodule] at hp
  rcases le_or_gt 0 a with ha | ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    refine 𝓜.smul_mem n c p m ?_ hm
    intro μ hμ
    have h := hp hμ
    simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one,
      nsmul_eq_mul] at h ⊢
    exact_mod_cast h
  · have hp0 : p = 0 := by
      by_contra hne
      obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hne
      have h := hp hμ
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_one] at h
      have : (0 : ℤ) ≤ ∑ i ∈ μ.support, (μ i : ℤ) := Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
      omega
    rw [hp0, zero_smul]
    exact zero_mem _
theorem locMap_locResS (f : M →ₗ[Poly S N] M') (I J : StdCell N) (h : I.1 ⊆ J.1)
    (x : LocMod S N M I.1) :
    (locMap f J.1).restrictScalars S (locResS I J h x) =
      locResS I J h ((locMap f I.1).restrictScalars S x) := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    change locMap f J.1 (locRes h _) = locRes h (locMap f I.1 _)
    rw [locRes_mk, locMap_mk, locMap_mk, locRes_mk]
theorem locMap_mem_degLoc {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M')
    (t : ℤ) (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) {c c' : ℤ}
    (hc : c' = c + t) (I : StdCell N) (x : LocMod S N M I.1) (hx : x ∈ degLoc 𝓜 c I) :
    (locMap f I.1).restrictScalars S x ∈ degLoc 𝓜' c' I := by
  refine Submodule.span_induction (p := fun x _ => (locMap f I.1).restrictScalars S x ∈
    degLoc 𝓜' c' I) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    refine Submodule.subset_span ⟨f m, s, a + t, e, hf a m hm, hs, by omega, ?_⟩
    exact locMap_mk f I.1 m s
  · simp
  · intro x y _ _ hx hy; simpa using add_mem hx hy
  · intro r x _ hx; simpa using Submodule.smul_mem _ r hx
def cohomMapShift {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M') (t : ℤ)
    (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) (i : ℕ) {c c' : ℤ}
    (hc : c' = c + t) : cohom 𝓜 i c →ₗ[S] cohom 𝓜' i c' :=
  Cech.mapHdeg (degLoc 𝓜 c) (degLoc 𝓜' c') (fun I => (locMap f I.1).restrictScalars S)
    (locMap_locResS f) (locMap_mem_degLoc f t hf hc) i
variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)
omit [IsScalarTower S (Poly S N) M] in

theorem coord_mem_piece (hb : ∀ j, b j ∈ 𝓜.piece (d j)) {a : ℤ} {m : M} (hm : m ∈ 𝓜.piece a)
    (j : Fin r) : b.coord j m ∈ (polyGraded S N).piece (a - d j) := by
  classical
  let _ := 𝓜.isInternal.chooseDecomposition
  let _ := (polyGraded S N).isInternal.chooseDecomposition

  have key : ∀ (k : Fin r) (p : Poly S N),
      (DirectSum.decompose 𝓜.piece (p • b k) a : M) =
        (DirectSum.decompose (polyGraded S N).piece p (a - d k) : Poly S N) • b k := by
    intro k p
    induction p using DirectSum.Decomposition.inductionOn (ℳ := (polyGraded S N).piece) with
    | zero => simp
    | @homogeneous e p =>
      have hpk : (p : Poly S N) • b k ∈ 𝓜.piece (d k + e) :=
        smul_mem_of_mem_polyGraded 𝓜 p.2 (hb k)
      by_cases he : d k + e = a
      · subst he
        rw [DirectSum.decompose_of_mem_same _ hpk, show d k + e - d k = e by omega,
          DirectSum.decompose_of_mem_same _ p.2]
      · rw [DirectSum.decompose_of_mem_ne _ hpk he,
          DirectSum.decompose_of_mem_ne _ p.2 (show e ≠ a - d k by omega), zero_smul]
    | add p q hp hq =>
      rw [add_smul, DirectSum.decompose_add, DirectSum.decompose_add, DirectSum.add_apply,
        DirectSum.add_apply, Submodule.coe_add, Submodule.coe_add, add_smul, hp, hq]
  have hsum : m = ∑ k, (DirectSum.decompose (polyGraded S N).piece (b.coord k m) (a - d k) :
      Poly S N) • b k := by
    conv_lhs => rw [← DirectSum.decompose_of_mem_same 𝓜.piece hm, ← b.sum_repr m]
    rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun k _ => key k _
  have hj : b.coord j m =
      (DirectSum.decompose (polyGraded S N).piece (b.coord j m) (a - d j) : Poly S N) := by
    conv_lhs => rw [hsum]
    rw [Module.Basis.coord_apply, ← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply]
  rw [hj]
  exact Submodule.coe_mem _
variable (hb : ∀ j, b j ∈ 𝓜.piece (d j))
include hb
def freeIncl (i : ℕ) (c : ℤ) (j : Fin r) : cohom (polyGraded S N) i (c - d j) →ₗ[S] cohom 𝓜 i c :=
  cohomMapShift (LinearMap.toSpanSingleton (Poly S N) M (b j)) (d j)
    (fun _ _ hp => by
      rw [LinearMap.toSpanSingleton_apply, add_comm]
      exact smul_mem_of_mem_polyGraded 𝓜 hp (hb j)) i (by ring)
def freeCoord (i : ℕ) (c : ℤ) (j : Fin r) : cohom 𝓜 i c →ₗ[S] cohom (polyGraded S N) i (c - d j) :=
  cohomMapShift (b.coord j) (-d j)
    (fun _ _ hm => by rw [← sub_eq_add_neg]; exact coord_mem_piece 𝓜 b d hb hm j) i (by ring)
omit [IsScalarTower S (Poly S N) M] in

theorem smul_basis_mem (c : ℤ) (j : Fin r) (p : (polyGraded S N).piece (c - d j)) :
    (p : Poly S N) • b j ∈ 𝓜.piece c := by
  have h := smul_mem_of_mem_polyGraded 𝓜 p.2 (hb j)
  rwa [show d j + (c - d j) = c by ring] at h
end FreeGraded
end
end GroundTheory.Heights₂.Heights.Kleiman


