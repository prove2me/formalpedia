-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:48:37.806945+00:00
-- url     : https://prove2.me/theorems/4efa73b0-f2b5-4bae-b2b5-b9fcc0ee95f3
-- title:
--   Connection Raising Constant Eq
-- statement:
--   Definitions and structural lemmas for Connection Raising Constant Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConnectionRaisingConstantEq.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
namespace Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
section Proj
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)
theorem pj_mul (ρ σ : M.Ty P) : proj κ ρ * proj κ σ = if ρ = σ then proj κ ρ else 0 := by
  unfold proj
  rw [← map_mul]
  split_ifs with h
  · subst h; congr 1; funext x; by_cases hx : x = ρ <;> simp [hx]
  · rw [← map_zero κ]; congr 1; funext x; by_cases hx : x = ρ <;> by_cases hy : x = σ <;> simp_all
theorem pj_idem (ρ : M.Ty P) : proj κ ρ * proj κ ρ = proj κ ρ := by simp [pj_mul]
theorem sum_pj : ∑ ρ, proj κ ρ = 1 := by
  unfold proj
  rw [← map_sum, ← map_one κ]; congr 1; funext x; simp
theorem xiA_xA {Y : ℂ} (h : Reg P Y) : xiA κ Y * xA κ Y = 1 := by
  unfold xA xiA; rw [← map_mul, ← map_one κ]; congr 1; funext ρ; simp [h ρ]
end Proj
section PF
variable {A : Type} [Ring A] [Algebra ℂ A]
def ev (p : A[X]) (Y : ℂ) : A := p.eval₂ (RingHom.id A) (algebraMap ℂ A Y)
def IsPF (f : ℂ → A) : Prop := ∃ p : A[X], ∀ Y, f Y = ev p Y
theorem cofinite_infinite {S : Set ℂ} (h : Sᶜ.Finite) : S.Infinite := by
  have := h.infinite_compl; simpa using this
end PF
section Types
open Formalism.FourierDecayAlt.M
theorem up_ne (P : M.Par) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {π π' : M.Ty P} (h : M.Up P l π π') : π ≠ π' := by
  rintro rfl
  have := h ⟨l - 1, by have := Finset.mem_Icc.1 hl; omega⟩
  have _hl' := Finset.mem_Icc.1 hl
  simp only at this; split_ifs at this with h' <;> omega
end Types
section Hyp
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
theorem H_kstar (h : SHyp P L0 QQ κ) (f : M.Ty P → ℂ) : star (κ f) = κ fun ρ => star (f ρ) :=
  h.2.2.2.2.2.2.1 f
theorem H_kops (h : SHyp P L0 QQ κ) (f : M.Ty P → ℂ) : ∀ g ∈ L0.ops, Commute (κ f) g :=
  h.2.2.2.2.2.2.2.1 f
theorem diagonal_entry_hypothesis (h : SHyp P L0 QQ κ) (Y : ℂ) : QQ Y 1 1 = L0.GG * xA κ Y := h.2.2.2.2.2.1 Y
theorem levelSubgroupAtPlace (h : SHyp P L0 QQ κ) (Y : ℂ) :
    QQ Y 1 0 * L0.ζ = L0.ζ * QQ Y 1 0 - QQ Y 1 1 ∧ QQ Y 1 1 * L0.ζ = L0.ζ * QQ Y 1 1 ∧
    QQ Y 0 1 * L0.ζ = L0.ζ * QQ Y 0 1 ∧ QQ Y 0 1 * L0.ζb = L0.ζb * QQ Y 0 1 + QQ Y 1 1 ∧
    QQ Y 1 0 * L0.ζb = L0.ζb * QQ Y 1 0 ∧ QQ Y 1 1 * L0.ζb = L0.ζb * QQ Y 1 1 :=
  h.2.2.2.2.2.2.2.2.2.1 Y
theorem H_crd (h : SHyp P L0 QQ κ) (Y : ℂ) (a b : Fin 2) : ∀ g ∈ L0.crdOps, Commute (QQ Y a b) g :=
  h.2.2.2.2.2.2.2.2.2.2 Y a b
theorem H_alg_star (h : SHyp P L0 QQ κ) (z : ℂ) : star (algebraMap ℂ A z) = algebraMap ℂ A (star z) := by
  have e : ∀ w : ℂ, algebraMap ℂ A w = κ (algebraMap ℂ (M.Ty P → ℂ) w) := fun w => (κ.commutes w).symm
  rw [e, e, H_kstar h]; rfl
end Hyp
section GlobalTheory
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (κ : (M.Ty P → ℂ) →ₐ[ℂ] A)
def GlobalTheory (R : M.Ty P → M.Ty P → Prop) (X : A) : Prop := ∀ σ τ, ¬ R τ σ → proj κ σ * X * proj κ τ = 0
end GlobalTheory
section Regular
theorem nreg_finite (P : M.Par) : {Y : ℂ | ¬ Reg P Y}.Finite := by
  have : {Y : ℂ | ¬ Reg P Y} ⊆ ⋃ ρ : M.Ty P, ⋃ i ∈ Icc 1 (P.k - 1), {-((M.rho P ρ i : ℝ) : ℂ)} := by
    intro Y hY
    simp only [Reg, not_forall, not_not, Set.mem_setOf_eq] at hY
    obtain ⟨ρ, hρ⟩ := hY
    unfold M.xC at hρ
    obtain ⟨i, hi, h0⟩ := Finset.prod_eq_zero_iff.1 hρ
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨ρ, i, hi, by linear_combination h0⟩
  refine Set.Finite.subset ?_ this
  exact Set.finite_iUnion fun ρ => Set.Finite.biUnion (Finset.finite_toSet _) fun i _ => Set.finite_singleton _
theorem reg_infinite (P : M.Par) : {Y : ℂ | Reg P Y}.Infinite := by
  apply cofinite_infinite
  simpa [Set.compl_setOf] using nreg_finite P
end Regular
section SB
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
def lowerBlockAlt (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (σ ρ : M.Ty P) (v : ℂ) : A :=
  proj κ σ * QQ v 1 0 * proj κ ρ
def regular_base_point : ℂ := Complex.I
def sb_K (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (l : ℕ) (ρ σ : M.Ty P) : A :=
  ((regular_base_point + ((M.rho P ρ l : ℝ) : ℂ) + 1) / M.xC P σ regular_base_point) • lowerBlockAlt κ QQ σ ρ regular_base_point
def sb_SS (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (l : ℕ) : A :=
  ∑ ρ : M.Ty P, ∑ σ : M.Ty P, if l ∈ Icc 1 (P.k - 1) ∧ M.Up P l ρ σ then sb_K κ QQ l ρ σ else 0
def sb_b (L0 : PreLevel A P.r) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (ρ : M.Ty P) : A :=
  L0.GGi * ((M.xC P ρ regular_base_point)⁻¹ • lowerBlockAlt κ QQ ρ ρ regular_base_point + regular_base_point • (L0.ζb * proj κ ρ))
end SB
section SN
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
end SN
section KatoClassHeckeEulerFactorRelation
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
def sn_hsh (P : M.Par) (l j : ℕ) (ρ : M.Ty P) (Y : ℂ) : ℂ :=
  ∏ i ∈ Icc 1 (P.k - 1) \ {l}, (Y + ((M.rho P ρ i : ℂ) + if i = j then 1 else 0))
end KatoClassHeckeEulerFactorRelation
section UnipotentMoveNumericalInequalities
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
end UnipotentMoveNumericalInequalities
section EpsilonZeroPos
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
def upperLeftTail (L : R.LevelData A P.r) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (SS : ℕ → A) (Y : ℂ) : A :=
  L.GG * xA κ Y * L.m0 Y * L.l0 Y + L.GG * L.m0 Y * L.GGi * Q.NFData.weightedSumBis (⟨L, κ, SS⟩ : Q.NFData P A) Y +
    Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * L.l0 Y
end EpsilonZeroPos
section SN5
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
end SN5
section SN6
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
def sn_e (P : M.Par) (τ : M.Ty P) (j : ℕ) (Y : ℂ) : ℂ :=
  (∏ i ∈ Icc 1 (P.k - 1) \ {j}, (Y + (M.rho P τ i : ℂ))) * ∏ i ∈ Icc 1 (P.k - 1) \ {j}, (Y + (1 + (M.rho P τ i : ℂ)))
end SN6
section SN7
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
end SN7
section SN8
end SN8
section SC
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
theorem sc_fc (L0 : PreLevel A P.r) {x y : A} (hx : x ∈ L0.fns) (hy : y ∈ L0.fns) : x * y = y * x :=
  L0.fns_comm x hx y hy
section Mem
variable (L0 : PreLevel A P.r)
theorem sc_mζ : L0.ζ ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mζb : L0.ζb ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mGGi : L0.GGi ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mc (l) : L0.c l ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mci (l) : L0.ci l ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mcb (l) : L0.cb l ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_mcbi (l) : L0.cbi l ∈ L0.fns := by simp [PreLevel.fns]
theorem sc_ops_of_fns {x : A} (hx : x ∈ L0.fns) : x ∈ L0.ops := by
  unfold PreLevel.ops; exact Or.inl (Or.inl hx)
theorem sc_mp (l) : L0.p l ∈ L0.ops := by unfold PreLevel.ops; exact Or.inl (Or.inr ⟨l, rfl⟩)
theorem sc_mpb (l) : L0.pb l ∈ L0.ops := by unfold PreLevel.ops; exact Or.inr ⟨l, rfl⟩
theorem sc_crd_c (l) : L0.c l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_ci (l) : L0.ci l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_cb (l) : L0.cb l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_cbi (l) : L0.cbi l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_p (l) : L0.p l ∈ L0.crdOps := by simp [PreLevel.crdOps]
theorem sc_crd_pb (l) : L0.pb l ∈ L0.crdOps := by simp [PreLevel.crdOps]
end Mem
section Core
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
theorem sc_kc (h : SHyp P L0 QQ κ) (f : M.Ty P → ℂ) {g : A} (hg : g ∈ L0.fns) : κ f * g = g * κ f :=
  (H_kops h f g (sc_ops_of_fns L0 hg)).eq
theorem sc_kops (h : SHyp P L0 QQ κ) (f : M.Ty P → ℂ) {g : A} (hg : g ∈ L0.ops) : κ f * g = g * κ f :=
  (H_kops h f g hg).eq
theorem sc_pc (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {g : A} (hg : g ∈ L0.ops) : proj κ ρ * g = g * proj κ ρ :=
  sc_kops h _ hg
theorem sc_pf (h : SHyp P L0 QQ κ) (ρ : M.Ty P) {g : A} (hg : g ∈ L0.fns) : proj κ ρ * g = g * proj κ ρ :=
  sc_kc h _ hg
theorem sc_crd_ops {g : A} (hg : g ∈ L0.crdOps) : g ∈ L0.ops ∧ L0.GGi * g = g * L0.GGi := by
  unfold PreLevel.crdOps at hg
  rcases hg with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
  · exact ⟨sc_ops_of_fns L0 (sc_mc L0 l), sc_fc L0 (sc_mGGi L0) (sc_mc L0 l)⟩
  · exact ⟨sc_ops_of_fns L0 (sc_mci L0 l), sc_fc L0 (sc_mGGi L0) (sc_mci L0 l)⟩
  · exact ⟨sc_ops_of_fns L0 (sc_mcb L0 l), sc_fc L0 (sc_mGGi L0) (sc_mcb L0 l)⟩
  · exact ⟨sc_ops_of_fns L0 (sc_mcbi L0 l), sc_fc L0 (sc_mGGi L0) (sc_mcbi L0 l)⟩
  · exact ⟨sc_mp L0 l, (L0.p_GGi l).symm⟩
  · exact ⟨sc_mpb L0 l, (L0.pb_GGi l).symm⟩
theorem sc_ldiag {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {Y : ℂ} (hY : Reg P Y) (ρ : M.Ty P) :
    proj κ ρ * lA L0 QQ κ Y * proj κ ρ = (b ρ - Y • (L0.ζb * L0.GGi)) * proj κ ρ := by
  have := hF Y hY ρ ρ
  rw [if_pos rfl, Finset.sum_eq_zero, add_zero] at this
  · exact this
  · intro l hl; rw [if_neg (fun hu => up_ne P hl hu rfl)]
theorem sc_Zp (h : SHyp P L0 QQ κ) (ρ : M.Ty P) :
    proj κ ρ * (L0.ζb * L0.GGi) = (L0.ζb * L0.GGi) * proj κ ρ := by
  rw [← mul_assoc, sc_pf h ρ (sc_mζb L0), mul_assoc, sc_pf h ρ (sc_mGGi L0), mul_assoc]
theorem sc_exreg (P : M.Par) : ∃ Y, Reg P Y := (reg_infinite P).nonempty
theorem sc_pbp (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) (ρ : M.Ty P) :
    proj κ ρ * b ρ * proj κ ρ = b ρ * proj κ ρ := by
  obtain ⟨Y, hY⟩ := sc_exreg P
  have e := sc_ldiag hF hY ρ
  have e2 : proj κ ρ * (proj κ ρ * lA L0 QQ κ Y * proj κ ρ) = proj κ ρ * lA L0 QQ κ Y * proj κ ρ := by
    rw [← mul_assoc, ← mul_assoc, pj_idem]
  rw [e] at e2
  have hZ := sc_Zp h ρ
  have e3a : proj κ ρ * (b ρ * proj κ ρ) = proj κ ρ * b ρ * proj κ ρ := (mul_assoc _ _ _).symm
  have e3b : proj κ ρ * ((L0.ζb * L0.GGi) * proj κ ρ) = (L0.ζb * L0.GGi) * proj κ ρ := by
    rw [← mul_assoc, hZ, mul_assoc, pj_idem]
  have e3 : proj κ ρ * ((b ρ - Y • (L0.ζb * L0.GGi)) * proj κ ρ) =
      proj κ ρ * b ρ * proj κ ρ - Y • ((L0.ζb * L0.GGi) * proj κ ρ) := by
    rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, e3a, e3b]
  rw [e3, sub_mul, smul_mul_assoc] at e2
  exact sub_left_inj.mp e2
def sc_B (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (b : M.Ty P → A) : A := ∑ ρ, proj κ ρ * b ρ * proj κ ρ
def sc_D (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (X : A) : A := ∑ ρ, proj κ ρ * X * proj κ ρ
theorem sc_B_eq (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {Y : ℂ}
    (hY : Reg P Y) : sc_B κ b = sc_D κ (lA L0 QQ κ Y) + Y • (L0.ζb * L0.GGi) := by
  unfold sc_B sc_D
  have : ∀ ρ, proj κ ρ * b ρ * proj κ ρ = proj κ ρ * lA L0 QQ κ Y * proj κ ρ + Y • ((L0.ζb * L0.GGi) * proj κ ρ) := by
    intro ρ; rw [sc_pbp h hF ρ, sc_ldiag hF hY ρ, sub_mul, smul_mul_assoc]; abel
  simp_rw [this, Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.mul_sum, sum_pj, mul_one]
theorem sc_D_comm {g : A} (hg : ∀ ρ, proj κ ρ * g = g * proj κ ρ) (X : A) :
    sc_D κ X * g = sc_D κ (X * g) ∧ g * sc_D κ X = sc_D κ (g * X) := by
  unfold sc_D
  constructor
  · rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun ρ _ => ?_; rw [mul_assoc, hg ρ]; noncomm_ring
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ρ _ => ?_; rw [← mul_assoc, ← mul_assoc, ← hg ρ]; noncomm_ring
theorem sc_lζ (h : SHyp P L0 QQ κ) {Y : ℂ} (hY : Reg P Y) : lA L0 QQ κ Y * L0.ζ = L0.ζ * lA L0 QQ κ Y - 1 := by
  unfold lA
  have h1 := (levelSubgroupAtPlace h Y).1
  have hx : xiA κ Y * L0.ζ = L0.ζ * xiA κ Y := sc_kc h _ (sc_mζ L0)
  have hg : L0.GGi * L0.ζ = L0.ζ * L0.GGi := sc_fc L0 (sc_mGGi L0) (sc_mζ L0)
  have hgx : L0.GGi * L0.GG = 1 := L0.GGi_GG
  calc xiA κ Y * L0.GGi * QQ Y 1 0 * L0.ζ = xiA κ Y * L0.GGi * (QQ Y 1 0 * L0.ζ) := by noncomm_ring
    _ = xiA κ Y * L0.GGi * (L0.ζ * QQ Y 1 0 - L0.GG * xA κ Y) := by rw [h1, diagonal_entry_hypothesis h]
    _ = (xiA κ Y * L0.GGi * L0.ζ) * QQ Y 1 0 - xiA κ Y * (L0.GGi * L0.GG) * xA κ Y := by noncomm_ring
    _ = L0.ζ * (xiA κ Y * L0.GGi * QQ Y 1 0) - 1 := by
        have key : xiA κ Y * L0.GGi * L0.ζ = L0.ζ * (xiA κ Y * L0.GGi) := by
          rw [mul_assoc, hg, ← mul_assoc, hx, mul_assoc]
        rw [hgx, mul_one, xiA_xA κ hY, key]; noncomm_ring
theorem sc_lζb (h : SHyp P L0 QQ κ) (Y : ℂ) : lA L0 QQ κ Y * L0.ζb = L0.ζb * lA L0 QQ κ Y := by
  unfold lA
  have h1 := (levelSubgroupAtPlace h Y).2.2.2.2.1
  have hx : xiA κ Y * L0.ζb = L0.ζb * xiA κ Y := sc_kc h _ (sc_mζb L0)
  have hg : L0.GGi * L0.ζb = L0.ζb * L0.GGi := sc_fc L0 (sc_mGGi L0) (sc_mζb L0)
  rw [mul_assoc, h1, ← mul_assoc, mul_assoc (xiA κ Y), hg, ← mul_assoc, hx, mul_assoc, mul_assoc, mul_assoc]
theorem sc_lcrd (h : SHyp P L0 QQ κ) (Y : ℂ) {g : A} (hg : g ∈ L0.crdOps) : lA L0 QQ κ Y * g = g * lA L0 QQ κ Y := by
  unfold lA
  obtain ⟨ho, hgi⟩ := sc_crd_ops hg
  have h1 := (H_crd h Y 1 0 g hg).eq
  have hx : xiA κ Y * g = g * xiA κ Y := sc_kops h _ ho
  rw [mul_assoc, h1, ← mul_assoc, mul_assoc (xiA κ Y), hgi, ← mul_assoc, hx, mul_assoc, mul_assoc, mul_assoc]
end Core
section Conn
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
theorem coordinate_commute_zeta {g : A} (hg : g ∈ L0.crdOps) : L0.ζb * g = g * L0.ζb ∧ L0.ζ * g = g * L0.ζ := by
  unfold PreLevel.crdOps at hg
  rcases hg with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩
  · exact ⟨sc_fc L0 (sc_mζb L0) (sc_mc L0 l), sc_fc L0 (sc_mζ L0) (sc_mc L0 l)⟩
  · exact ⟨sc_fc L0 (sc_mζb L0) (sc_mci L0 l), sc_fc L0 (sc_mζ L0) (sc_mci L0 l)⟩
  · exact ⟨sc_fc L0 (sc_mζb L0) (sc_mcb L0 l), sc_fc L0 (sc_mζ L0) (sc_mcb L0 l)⟩
  · exact ⟨sc_fc L0 (sc_mζb L0) (sc_mcbi L0 l), sc_fc L0 (sc_mζ L0) (sc_mcbi L0 l)⟩
  · exact ⟨(L0.p_ζb l).symm, (L0.p_ζ l).symm⟩
  · exact ⟨(L0.pb_ζb l).symm, (L0.pb_ζ l).symm⟩
theorem sc_Zc {g : A} (hb : L0.ζb * g = g * L0.ζb) (hi : L0.GGi * g = g * L0.GGi) :
    (L0.ζb * L0.GGi) * g = g * (L0.ζb * L0.GGi) := by
  rw [mul_assoc, hi, ← mul_assoc, hb, mul_assoc]
theorem sc_B_rel (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {g c : A}
    (hg : g ∈ L0.ops) (hZ : (L0.ζb * L0.GGi) * g = g * (L0.ζb * L0.GGi))
    (hl : ∀ Y, Reg P Y → lA L0 QQ κ Y * g = g * lA L0 QQ κ Y + c) (hD : sc_D κ c = c) :
    sc_B κ b * g = g * sc_B κ b + c := by
  obtain ⟨Y, hY⟩ := sc_exreg P
  obtain ⟨c1, c2⟩ := sc_D_comm (κ := κ) (fun ρ => sc_pc h ρ hg) (lA L0 QQ κ Y)
  have hsum : sc_D κ (g * lA L0 QQ κ Y + c) = sc_D κ (g * lA L0 QQ κ Y) + sc_D κ c := by
    unfold sc_D; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun ρ _ => ?_; noncomm_ring
  rw [sc_B_eq h hF hY, add_mul, c1, hl Y hY, hsum, hD, ← c2, smul_mul_assoc, hZ, mul_add, mul_smul_comm]
  abel
theorem sc_D_zero : sc_D κ (0 : A) = 0 := by unfold sc_D; simp
theorem sc_D_neg_one : sc_D κ (-1 : A) = -1 := by
  unfold sc_D; simp_rw [mul_neg, neg_mul, mul_one, pj_idem]; rw [Finset.sum_neg_distrib, sum_pj]
theorem sc_Bζ (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    sc_B κ b * L0.ζ = L0.ζ * sc_B κ b + (-1) :=
  sc_B_rel h hF (sc_ops_of_fns L0 (sc_mζ L0))
    (sc_Zc (sc_fc L0 (sc_mζb L0) (sc_mζ L0)) (sc_fc L0 (sc_mGGi L0) (sc_mζ L0)))
    (fun Y hY => by rw [sc_lζ h hY]; abel) sc_D_neg_one
theorem sc_Bζb (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    sc_B κ b * L0.ζb = L0.ζb * sc_B κ b + 0 :=
  sc_B_rel h hF (sc_ops_of_fns L0 (sc_mζb L0))
    (sc_Zc rfl (sc_fc L0 (sc_mGGi L0) (sc_mζb L0)))
    (fun Y _ => by rw [sc_lζb h Y, add_zero]) sc_D_zero
theorem sc_Bcrd (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {g : A}
    (hg : g ∈ L0.crdOps) : sc_B κ b * g = g * sc_B κ b + 0 :=
  sc_B_rel h hF (sc_crd_ops hg).1 (sc_Zc (coordinate_commute_zeta hg).1 (sc_crd_ops hg).2)
    (fun Y _ => by rw [sc_lcrd h Y hg, add_zero]) sc_D_zero
end Conn
section Nab
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
theorem sc_inv_rel {X a ai c : A} (h : X * a = a * X + c) (h1 : a * ai = 1) (h2 : ai * a = 1) :
    X * ai = ai * X - ai * c * ai := by
  calc X * ai = ai * a * X * ai := by rw [h2, one_mul]
    _ = ai * (X * a - c) * ai := by rw [h]; noncomm_ring
    _ = ai * X * (a * ai) - ai * c * ai := by noncomm_ring
    _ = _ := by rw [h1, mul_one]
theorem sc_N_eq (b : M.Ty P → A) :
    nabDef L0 κ b = -sc_B κ b - (1 / 2 : ℂ) • (L0.ζb * L0.GGi) := rfl
theorem sc_N_rel {b : M.Ty P → A} {g c : A} (hB : sc_B κ b * g = g * sc_B κ b + c)
    (hZ : (L0.ζb * L0.GGi) * g = g * (L0.ζb * L0.GGi)) : nabDef L0 κ b * g = g * nabDef L0 κ b - c := by
  rw [sc_N_eq, sub_mul, neg_mul, hB, smul_mul_assoc, hZ, mul_sub, mul_neg, mul_smul_comm]; abel
theorem sc_Nζ (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.ζ = L0.ζ * nabDef L0 κ b + 1 := by
  rw [sc_N_rel (sc_Bζ h hF) (sc_Zc (sc_fc L0 (sc_mζb L0) (sc_mζ L0)) (sc_fc L0 (sc_mGGi L0) (sc_mζ L0)))]; abel
theorem sc_Nζb (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.ζb = L0.ζb * nabDef L0 κ b := by
  rw [sc_N_rel (sc_Bζb h hF) (sc_Zc rfl (sc_fc L0 (sc_mGGi L0) (sc_mζb L0)))]; abel
theorem sc_Ncrd (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) {g : A}
    (hg : g ∈ L0.crdOps) : nabDef L0 κ b * g = g * nabDef L0 κ b := by
  rw [sc_N_rel (sc_Bcrd h hF hg) (sc_Zc (coordinate_commute_zeta hg).1 (sc_crd_ops hg).2)]; abel
theorem sc_NGG (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.GG = L0.GG * nabDef L0 κ b + L0.ζb := by
  have e1 := sc_Nζ h hF
  have e2 := sc_Nζb h hF
  have e3 : nabDef L0 κ b * algebraMap ℂ A L0.TT = algebraMap ℂ A L0.TT * nabDef L0 κ b := (Algebra.commutes _ _).symm
  rw [L0.GG_def]
  calc nabDef L0 κ b * (L0.ζ * L0.ζb - algebraMap ℂ A L0.TT)
      = (nabDef L0 κ b * L0.ζ) * L0.ζb - nabDef L0 κ b * algebraMap ℂ A L0.TT := by noncomm_ring
    _ = L0.ζ * (nabDef L0 κ b * L0.ζb) + L0.ζb - algebraMap ℂ A L0.TT * nabDef L0 κ b := by
        rw [e1, e3]; noncomm_ring
    _ = _ := by rw [e2]; noncomm_ring
theorem sc_NGGi (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.GGi = L0.GGi * nabDef L0 κ b - L0.ζb * L0.GGi * L0.GGi := by
  rw [sc_inv_rel (sc_NGG h hF) L0.GG_GGi L0.GGi_GG, sc_fc L0 (sc_mGGi L0) (sc_mζb L0)]
theorem sc_Nζi (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.ζi = L0.ζi * nabDef L0 κ b - L0.ζi * L0.ζi := by
  rw [sc_inv_rel (sc_Nζ h hF) L0.ζ_ζi L0.ζi_ζ, mul_one]
theorem sc_Nζbi (h : SHyp P L0 QQ κ) {b : M.Ty P → A} {SS : ℕ → A} (hF : SForm P L0 QQ κ b SS) :
    nabDef L0 κ b * L0.ζbi = L0.ζbi * nabDef L0 κ b := by
  rw [sc_inv_rel (a := L0.ζb) (c := 0) (by rw [sc_Nζb h hF, add_zero]) L0.ζb_ζbi L0.ζbi_ζb]; simp
theorem sc_inv_uniq {a b b' : A} (h1 : b * a = 1) (h2 : a * b' = 1) : b = b' := by
  calc b = b * (a * b') := by rw [h2, mul_one]
    _ = (b * a) * b' := by noncomm_ring
    _ = b' := by rw [h1, one_mul]
theorem sc_sζ (h : SHyp P L0 QQ κ) : star L0.ζ = L0.ζb := h.1
theorem sc_sζb (h : SHyp P L0 QQ κ) : star L0.ζb = L0.ζ := by rw [← sc_sζ h, star_star]
theorem sc_sζi (h : SHyp P L0 QQ κ) : star L0.ζi = L0.ζbi :=
  sc_inv_uniq (a := L0.ζb) (by rw [← sc_sζ h, ← star_mul, L0.ζ_ζi, star_one]) L0.ζb_ζbi
theorem sc_sζbi (h : SHyp P L0 QQ κ) : star L0.ζbi = L0.ζi := by rw [← sc_sζi h, star_star]
theorem sc_sGG (h : SHyp P L0 QQ κ) : star L0.GG = L0.GG := by
  rw [L0.GG_def, star_sub, star_mul, sc_sζ h, sc_sζb h, H_alg_star h, h.2.1]
theorem sc_sGGi (h : SHyp P L0 QQ κ) : star L0.GGi = L0.GGi :=
  sc_inv_uniq (a := L0.GG) (by rw [← sc_sGG h, ← star_mul, L0.GG_GGi, star_one]) L0.GG_GGi
theorem sc_sc (h : SHyp P L0 QQ κ) (l) : star (L0.c l) = L0.cb l := (h.2.2.1 l).1
theorem sc_sci (h : SHyp P L0 QQ κ) (l) : star (L0.ci l) = L0.cbi l := (h.2.2.1 l).2.1
theorem sc_sp (h : SHyp P L0 QQ κ) (l) : star (L0.p l) = -L0.pb l := (h.2.2.1 l).2.2
theorem sc_scb (h : SHyp P L0 QQ κ) (l) : star (L0.cb l) = L0.c l := by rw [← sc_sc h, star_star]
theorem sc_scbi (h : SHyp P L0 QQ κ) (l) : star (L0.cbi l) = L0.ci l := by rw [← sc_sci h, star_star]
theorem sc_spb (h : SHyp P L0 QQ κ) (l) : star (L0.pb l) = -L0.p l := by
  rw [← neg_neg (L0.pb l), ← sc_sp h, star_neg, star_star]
end Nab
section Nabs
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
theorem sc_Nsζb (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.ζb = L0.ζb * star (nabDef L0 κ b) - 1 := by
  have e := congrArg star (sc_Nζ h hF)
  rw [star_mul, star_add, star_mul, star_one, sc_sζ h] at e
  rw [e]; abel
theorem sc_Nsζbi (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.ζbi = L0.ζbi * star (nabDef L0 κ b) + L0.ζbi * L0.ζbi := by
  have e := congrArg star (sc_Nζi h hF)
  rw [star_mul, star_sub, star_mul, star_mul, sc_sζi h] at e
  rw [e]; abel
theorem sc_Nsζ (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.ζ = L0.ζ * star (nabDef L0 κ b) := by
  have e := congrArg star (sc_Nζb h hF)
  rw [star_mul, star_mul, sc_sζb h] at e
  exact e.symm
theorem sc_Nsζi (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.ζi = L0.ζi * star (nabDef L0 κ b) := by
  have e := congrArg star (sc_Nζbi h hF)
  rw [star_mul, star_mul, sc_sζbi h] at e
  exact e.symm
theorem sc_NsGG (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.GG = L0.GG * star (nabDef L0 κ b) - L0.ζ := by
  have e := congrArg star (sc_NGG h hF)
  rw [star_mul, star_add, star_mul, sc_sGG h, sc_sζb h] at e
  rw [e]; abel
theorem sc_NsGGi (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) :
    star (nabDef L0 κ b) * L0.GGi = L0.GGi * star (nabDef L0 κ b) + L0.ζ * L0.GGi * L0.GGi := by
  have e := congrArg star (sc_NGGi h hF)
  rw [star_mul, star_sub, star_mul, star_mul, star_mul, sc_sGGi h, sc_sζb h] at e
  have c1 : L0.GGi * L0.ζ = L0.ζ * L0.GGi := sc_fc L0 (sc_mGGi L0) (sc_mζ L0)
  have c : L0.GGi * (L0.GGi * L0.ζ) = L0.ζ * L0.GGi * L0.GGi := by
    calc L0.GGi * (L0.GGi * L0.ζ) = L0.GGi * (L0.ζ * L0.GGi) := by rw [c1]
      _ = (L0.GGi * L0.ζ) * L0.GGi := by noncomm_ring
      _ = _ := by rw [c1]
  rw [e, c]; abel
theorem sc_Ns_of {g g' : A} (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) (hg : g ∈ L0.crdOps)
    (hs : star g = g') : star (nabDef L0 κ b) * g' = g' * star (nabDef L0 κ b) := by
  have e := congrArg star (sc_Ncrd h hF hg)
  rw [star_mul, star_mul, hs] at e
  exact e.symm
def sc_L {r : ℕ} (L0 : PreLevel A r) (N Ns : A)
    (p_nab : ∀ l, L0.p l * N = N * L0.p l) (pb_nab : ∀ l, L0.pb l * N = N * L0.pb l)
    (p_nabs : ∀ l, L0.p l * Ns = Ns * L0.p l) (pb_nabs : ∀ l, L0.pb l * Ns = Ns * L0.pb l)
    (nab_ζ : N * L0.ζ = L0.ζ * N + 1) (nab_ζi : N * L0.ζi = L0.ζi * N - L0.ζi * L0.ζi)
    (nab_ζb : N * L0.ζb = L0.ζb * N) (nab_ζbi : N * L0.ζbi = L0.ζbi * N)
    (nab_GG : N * L0.GG = L0.GG * N + L0.ζb) (nab_GGi : N * L0.GGi = L0.GGi * N - L0.ζb * L0.GGi * L0.GGi)
    (nab_c : ∀ l, N * L0.c l = L0.c l * N) (nab_ci : ∀ l, N * L0.ci l = L0.ci l * N)
    (nab_cb : ∀ l, N * L0.cb l = L0.cb l * N) (nab_cbi : ∀ l, N * L0.cbi l = L0.cbi l * N)
    (nabs_ζb : Ns * L0.ζb = L0.ζb * Ns - 1) (nabs_ζbi : Ns * L0.ζbi = L0.ζbi * Ns + L0.ζbi * L0.ζbi)
    (nabs_ζ : Ns * L0.ζ = L0.ζ * Ns) (nabs_ζi : Ns * L0.ζi = L0.ζi * Ns)
    (nabs_GG : Ns * L0.GG = L0.GG * Ns - L0.ζ) (nabs_GGi : Ns * L0.GGi = L0.GGi * Ns + L0.ζ * L0.GGi * L0.GGi)
    (nabs_c : ∀ l, Ns * L0.c l = L0.c l * Ns) (nabs_ci : ∀ l, Ns * L0.ci l = L0.ci l * Ns)
    (nabs_cb : ∀ l, Ns * L0.cb l = L0.cb l * Ns) (nabs_cbi : ∀ l, Ns * L0.cbi l = L0.cbi l * Ns) :
    R.LevelData A r where
  p := L0.p
  pb := L0.pb
  c := L0.c
  ci := L0.ci
  cb := L0.cb
  cbi := L0.cbi
  ζ := L0.ζ
  ζi := L0.ζi
  ζb := L0.ζb
  ζbi := L0.ζbi
  GG := L0.GG
  GGi := L0.GGi
  nab := N
  nabs := Ns
  TT := L0.TT
  fns_comm := L0.fns_comm
  c_ci := L0.c_ci
  ci_c := L0.ci_c
  cb_cbi := L0.cb_cbi
  cbi_cb := L0.cbi_cb
  ζ_ζi := L0.ζ_ζi
  ζi_ζ := L0.ζi_ζ
  ζb_ζbi := L0.ζb_ζbi
  ζbi_ζb := L0.ζbi_ζb
  GG_GGi := L0.GG_GGi
  GGi_GG := L0.GGi_GG
  GG_def := L0.GG_def
  p_c := L0.p_c
  p_ci := L0.p_ci
  p_cb := L0.p_cb
  p_cbi := L0.p_cbi
  p_ζ := L0.p_ζ
  p_ζi := L0.p_ζi
  p_ζb := L0.p_ζb
  p_ζbi := L0.p_ζbi
  p_GG := L0.p_GG
  p_GGi := L0.p_GGi
  pb_cb := L0.pb_cb
  pb_cbi := L0.pb_cbi
  pb_c := L0.pb_c
  pb_ci := L0.pb_ci
  pb_ζ := L0.pb_ζ
  pb_ζi := L0.pb_ζi
  pb_ζb := L0.pb_ζb
  pb_ζbi := L0.pb_ζbi
  pb_GG := L0.pb_GG
  pb_GGi := L0.pb_GGi
  p_p := L0.p_p
  p_pb := L0.p_pb
  pb_pb := L0.pb_pb
  p_nab := p_nab
  pb_nab := pb_nab
  p_nabs := p_nabs
  pb_nabs := pb_nabs
  nab_ζ := nab_ζ
  nab_ζi := nab_ζi
  nab_ζb := nab_ζb
  nab_ζbi := nab_ζbi
  nab_GG := nab_GG
  nab_GGi := nab_GGi
  nab_c := nab_c
  nab_ci := nab_ci
  nab_cb := nab_cb
  nab_cbi := nab_cbi
  nabs_ζb := nabs_ζb
  nabs_ζbi := nabs_ζbi
  nabs_ζ := nabs_ζ
  nabs_ζi := nabs_ζi
  nabs_GG := nabs_GG
  nabs_GGi := nabs_GGi
  nabs_c := nabs_c
  nabs_ci := nabs_ci
  nabs_cb := nabs_cb
  nabs_cbi := nabs_cbi
def sc_LL (h : SHyp P L0 QQ κ) (hF : SForm P L0 QQ κ b SS) : R.LevelData A P.r :=
  sc_L L0 (nabDef L0 κ b) (star (nabDef L0 κ b))
    (fun l => (sc_Ncrd h hF (sc_crd_p L0 l)).symm) (fun l => (sc_Ncrd h hF (sc_crd_pb L0 l)).symm)
    (fun l => by
      have := sc_Ns_of h hF (sc_crd_pb L0 l) (sc_spb h l)
      rw [neg_mul, mul_neg] at this; exact (neg_inj.mp this).symm)
    (fun l => by
      have := sc_Ns_of h hF (sc_crd_p L0 l) (sc_sp h l)
      rw [neg_mul, mul_neg] at this; exact (neg_inj.mp this).symm)
    (sc_Nζ h hF) (sc_Nζi h hF) (sc_Nζb h hF) (sc_Nζbi h hF) (sc_NGG h hF) (sc_NGGi h hF)
    (fun l => sc_Ncrd h hF (sc_crd_c L0 l)) (fun l => sc_Ncrd h hF (sc_crd_ci L0 l))
    (fun l => sc_Ncrd h hF (sc_crd_cb L0 l)) (fun l => sc_Ncrd h hF (sc_crd_cbi L0 l))
    (sc_Nsζb h hF) (sc_Nsζbi h hF) (sc_Nsζ h hF) (sc_Nsζi h hF) (sc_NsGG h hF) (sc_NsGGi h hF)
    (fun l => sc_Ns_of h hF (sc_crd_cb L0 l) (sc_scb h l)) (fun l => sc_Ns_of h hF (sc_crd_cbi L0 l) (sc_scbi h l))
    (fun l => sc_Ns_of h hF (sc_crd_c L0 l) (sc_sc h l)) (fun l => sc_Ns_of h hF (sc_crd_ci L0 l) (sc_sci h l))
end Nabs
section T21
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
end T21
section T12
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
end T12
section NabSS
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
end NabSS
section NabsSS
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
end NabsSS
section Main
variable {L0 : PreLevel A P.r} {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
  {b : M.Ty P → A} {SS : ℕ → A}
end Main
end SC
end
end Formalism.FourierDecayAlt.P.NFx2
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


