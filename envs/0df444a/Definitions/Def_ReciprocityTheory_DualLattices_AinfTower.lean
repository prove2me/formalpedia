-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_AinfTower
-- name    : ReciprocityTheory_DualLattices_AinfTower
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:21:33.68892+00:00
-- url     : https://prove2.me/theorems/2df0be4f-6c73-4a17-bd85-2cd722bb3168
-- title:
--   Ainf Tower
-- statement:
--   Definitions and structural lemmas for Ainf Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/AinfTower.lean

import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAFull
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_O_local
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_ker_theta
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_root_pow
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_sepO
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_teich_eps
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_theta_surj
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_theta_xi
import Theorems.Thm_ReciprocityTheory_PGsh_Ainf_xi_nzd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
namespace ReciprocityTheory.PGsh
namespace Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
abbrev R0 (ε : PreTilt O p) := A p O ⧸ span {xi p O ε ^ 2}
abbrev Rn (n : ℕ) := O ⧸ span {(p : O) ^ (n + 1)}
abbrev R'n (ε : PreTilt O p) (n : ℕ) := R0 p O ε ⧸ span {(p : R0 p O ε) ^ (n + 1)}
lemma hpRn (n : ℕ) : (p : Rn p O n) ^ (n + 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) p, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _
lemma hpR' (ε : PreTilt O p) (n : ℕ) : (p : R'n p O ε n) ^ (n + 1) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk (span {(p : R0 p O ε) ^ (n + 1)})) p, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _
lemma Rn_local (hv : v.Integers O) (n : ℕ) : IsLocalRing (Rn p O n) := by
  haveI := O_local O hv
  haveI : Nontrivial (Rn p O n) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : (1 : O) ∈ span {(p : O) ^ (n + 1)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]; exact h.symm
    rw [Ideal.mem_span_singleton'] at h1
    obtain ⟨a, ha⟩ := h1
    exact (Fact.out : ¬IsUnit (p : O))
      ((isUnit_pow_iff (Nat.succ_ne_zero n)).1 (IsUnit.of_mul_eq_one_right a ha))
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
lemma one_add_unit {S : Type} [CommRing S] (a b : S) (hb : b * b = 0) : IsUnit (1 + a * b) := by
  exact IsUnit.of_mul_eq_one (1 - a * b) (by linear_combination (-a ^ 2) * hb)
variable (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)
include hv hε
def thetaBar : R0 p O ε →+* O :=
  Ideal.Quotient.lift _ (fontaineTheta O p) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, theta_xi p O hv ε hε, zero_pow two_ne_zero, mul_zero])
def algO : Algebra (R0 p O ε) O := (thetaBar p O hv ε hε).toAlgebra
def algRn (n : ℕ) : Algebra (R0 p O ε) (Rn p O n) :=
  ((Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})).comp (thetaBar p O hv ε hε)).toAlgebra
def piRing (n : ℕ) : R'n p O ε n →+* Rn p O n :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})).comp
    (thetaBar p O hv ε hε)) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast, hpRn, mul_zero])
lemma piRing_mk (n : ℕ) (a : A p O) :
    piRing p O hv ε hε n (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ a)) =
      Ideal.Quotient.mk _ (fontaineTheta O p a) := rfl
lemma piRing_surj (n : ℕ) : Function.Surjective (piRing p O hv ε hε n) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, rfl⟩ := theta_surj p O hv x
  exact ⟨_, piRing_mk p O hv ε hε n a⟩
def xiR (n : ℕ) : R'n p O ε n :=
  Ideal.Quotient.mk (span {(p : R0 p O ε) ^ (n + 1)}) (Ideal.Quotient.mk (span {xi p O ε ^ 2}) (xi p O ε))
lemma ker_pi (n : ℕ) : RingHom.ker (piRing p O hv ε hε n) = span {xiR p O ε n} := by
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [piRing_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨o, ho⟩ := hx
    obtain ⟨b, rfl⟩ := theta_surj p O hv o
    have hk : a - b * (p : A p O) ^ (n + 1) ∈ RingHom.ker (fontaineTheta O p) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast, ho, sub_self]
    rw [ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at hk
    obtain ⟨c, hc⟩ := hk
    have ha : a = c * xi p O ε + b * (p : A p O) ^ (n + 1) := by rw [hc]; ring
    rw [Ideal.mem_span_singleton']
    refine ⟨Ideal.Quotient.mk _ (Ideal.Quotient.mk _ c), ?_⟩
    rw [ha]
    simp only [xiR, map_add, map_mul, map_pow, map_natCast, hpR', mul_zero, add_zero]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, xiR, piRing_mk,
      theta_xi p O hv ε hε, map_zero]
lemma xi_sq' (n : ℕ) : xiR p O ε n * xiR p O ε n = 0 := by
  unfold xiR
  rw [← map_mul, ← map_mul]
  have h : (Ideal.Quotient.mk (span {xi p O ε ^ 2})) (xi p O ε * xi p O ε) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton'.2 ⟨1, by ring⟩)
  rw [h, map_zero]
lemma R'n_local (n : ℕ) : IsLocalRing (R'n p O ε n) := by
  haveI := Rn_local p O hv n
  haveI : Nontrivial (R'n p O ε n) := (piRing p O hv ε hε n).domain_nontrivial
  have key : ∀ a : R'n p O ε n, IsUnit (piRing p O hv ε hε n a) → IsUnit a := by
    intro a ha
    obtain ⟨u, hu⟩ := ha.exists_right_inv
    obtain ⟨u', rfl⟩ := piRing_surj p O hv ε hε n u
    have hk : a * u' - 1 ∈ RingHom.ker (piRing p O hv ε hε n) := by
      rw [RingHom.mem_ker, map_sub, map_mul, hu, map_one, sub_self]
    rw [ker_pi, Ideal.mem_span_singleton'] at hk
    obtain ⟨k, hk⟩ := hk
    have h1 : a * u' = 1 + k * xiR p O ε n := by rw [hk]; ring
    have h2 := one_add_unit k (xiR p O ε n) (xi_sq' p O hv ε hε n)
    rw [← h1] at h2
    exact isUnit_of_mul_isUnit_left h2
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun a => ?_)
  have h : piRing p O hv ε hε n a + piRing p O hv ε hε n (1 - a) = 1 := by
    rw [← map_add, add_sub_cancel, map_one]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h with h | h
  · exact Or.inl (key a h)
  · exact Or.inr (key _ h)
lemma ann' (n : ℕ) (a : R'n p O ε n) (ha : a * xiR p O ε n = 0) :
    a ∈ span {xiR p O ε n} := by
  haveI : IsDomain O := Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  have hp0 : (p : O) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h'
    exact hp.out.ne_zero (by exact_mod_cast h')
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  unfold xiR at ha
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at ha
  obtain ⟨d0, hd0⟩ := ha
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d0
  rw [← map_natCast (Ideal.Quotient.mk (span {xi p O ε ^ 2})) p, ← map_pow, ← map_mul,
    Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hd0
  obtain ⟨c, hc⟩ := hd0
  have h1 : fontaineTheta O p d * (p : O) ^ (n + 1) = 0 := by
    have h' := congrArg (fontaineTheta O p) hc
    simp only [map_mul, map_sub, map_pow, map_natCast, theta_xi p O hv ε hε] at h'
    linear_combination -h'
  have h2 : fontaineTheta O p d = 0 := (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ hp0)
  have h3 : d ∈ RingHom.ker (fontaineTheta O p) := h2
  rw [ker_theta p O hv ε hε, Ideal.mem_span_singleton'] at h3
  obtain ⟨e0, rfl⟩ := h3
  have h4 : (y - (e0 * (p : A p O) ^ (n + 1) - c * xi p O ε)) * xi p O ε = 0 := by
    linear_combination hc
  have h5 := xi_nzd p O hv ε hε _ h4
  rw [sub_eq_zero] at h5
  rw [h5, Ideal.mem_span_singleton']
  refine ⟨-(Ideal.Quotient.mk _ (Ideal.Quotient.mk _ c)), ?_⟩
  simp only [xiR, map_sub, map_mul, map_pow, map_natCast, hpR', mul_zero, zero_sub, neg_mul]
def zv (n : ℕ) : R'n p O ε n :=
  Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (teichmuller p (root p O ε (n + 1))))
def nuR (n : ℕ) : R'n p O ε n := Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (nu p O ε))
lemma zv_pow (n : ℕ) :
    zv p O ε n ^ p ^ (n + 1) = 1 + nuR p O ε n * xiR p O ε n := by
  unfold zv nuR xiR
  rw [← map_pow, ← map_pow, ← map_pow, root_pow, teich_eps p O hv ε hε, map_add, map_add, map_one,
    map_one, map_mul, map_mul]
lemma zv_unit (n : ℕ) : IsUnit (zv p O ε n) := by
  have hne : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  refine (isUnit_pow_iff hne).1 ?_
  rw [zv_pow p O hv ε hε n]
  exact one_add_unit _ _ (xi_sq' p O hv ε hε n)
def zetaV (n : ℕ) : O := fontaineTheta O p (teichmuller p (root p O ε (n + 1)))
lemma zeta_unit (n : ℕ) : IsUnit (zetaV p O ε n) := by
  have hne : p ^ (n + 1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have h : zetaV p O ε n ^ p ^ (n + 1) = 1 := by
    unfold zetaV
    rw [← map_pow, ← map_pow, root_pow, teich_eps p O hv ε hε, map_add, map_one, map_mul,
      theta_xi p O hv ε hε, mul_zero, add_zero]
  refine IsUnit.of_mul_eq_one (zetaV p O ε n ^ (p ^ (n + 1) - 1)) ?_
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hne), h]
def LO : LAlg (R0 p O ε) := { carrier := O, alg := algO p O hv ε hε, loc := O_local O hv }
def LR (n : ℕ) : LAlg (R0 p O ε) :=
  { carrier := Rn p O n, alg := algRn p O hv ε hε n, loc := Rn_local p O hv n }
def LR' (n : ℕ) : LAlg (R0 p O ε) := { carrier := R'n p O ε n, loc := R'n_local p O hv ε hε n }
lemma q_surj (n : ℕ) : Function.Surjective (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) := by
  exact Ideal.Quotient.mk_surjective
def ainfTower : ATower (R0 p O ε) p where
  O := LO p O hv ε hε
  R' n := LR' p O hv ε hε n
  R n := LR p O hv ε hε n
  π n := ⟨{ toRingHom := piRing p O hv ε hε n, commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (piRing_surj p O hv ε hε n)⟩
  q n := ⟨{ toRingHom := Ideal.Quotient.mk (span {(p : O) ^ (n + 1)}), commutes' := fun _ => rfl },
    TowerExample.isLocalHom_of_surj _ (q_surj p O hv ε hε n)⟩
  ξ n := xiR p O ε n
  surj n := piRing_surj p O hv ε hε n
  ker_eq n := ker_pi p O hv ε hε n
  ξ_sq n := xi_sq' p O hv ε hε n
  ann n a ha := ann' p O hv ε hε n a ha
  char n := by rw [Nat.cast_pow]; exact hpR' p O ε n
  sep a ha := sepO p O a fun n =>
    (Ideal.Quotient.eq_zero_iff_mem (I := span {(p : O) ^ (n + 1)})).1 (ha n)
  c := fontaineTheta O p (nu p O ε)
  cp n := nuR p O ε n
  cp_spec n := rfl
  zh n := (zv_unit p O hv ε hε n).unit
  zh_pow n := by rw [IsUnit.unit_spec]; exact zv_pow p O hv ε hε n
  ζ n := (zeta_unit p O hv ε hε n).unit
  ζ_spec n := by rw [IsUnit.unit_spec, IsUnit.unit_spec]; rfl
end Ainf
end ReciprocityTheory.PGsh


