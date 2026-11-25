-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_HomogeneousComponentMulForm
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:41:10.133898+00:00
-- url     : https://prove2.me/theorems/33f39a69-b1a6-4811-a03e-cf21c14f6845
-- title:
--   Homogeneous Component Mul Form
-- statement:
--   Definitions and structural lemmas for Homogeneous Component Mul Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/HomogeneousComponentMulForm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperQuotFiltSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PDomination
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
namespace SnapperQuotFilt
section Twist
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
def powsBundle : (t : ℕ) → (Fin t → LineBundle S x) → (Fin t → ℕ) → LineBundle S x
  | 0, _, _ => twistBundle S x 0
  | t + 1, L, n => (powsBundle t (fun j => L j.castSucc) (fun j => n j.castSucc)).tensorProd
      ((L (Fin.last t)).powBundle (n (Fin.last t)))
end Twist
section Tilde
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
omit [IsScalarTower S Ω E] in

def tildeFam (M : FinGradedSub (S := S) (x := x) E) : SubFamily S x E where
  toSubSystem := M.tildeSys 0
  mem_iff I J h y := by
    constructor
    · intro hy
      change y ∈ M.tilde 0 J at hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩ := hy
        obtain ⟨i, hi⟩ := I.2.1
        have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
        have hs0 := eval_ne_zero_of_mem_monos J hs
        have hX0 : aeval x (X i ^ e : Poly S N) ≠ 0 := by
          rw [map_pow, aeval_X]; exact pow_ne_zero _ hxi
        refine ⟨⟨aeval x s / aeval x (X i ^ e), s, X i ^ e, e, pow_mem (X_mem_monos hi) e, hse,
          isHomogeneous_X_pow i e, rfl⟩, ?_, ?_⟩
        · rw [isUnit_iff_exists_inv]
          refine ⟨⟨aeval x (X i ^ e) / aeval x s, X i ^ e, s, e, hs, isHomogeneous_X_pow i e, hse, rfl⟩, ?_⟩
          apply Subtype.ext
          change aeval x s / aeval x (X i ^ e) * (aeval x (X i ^ e) / aeval x s) = 1
          field_simp
        · change (aeval x s / aeval x (X i ^ e)) • ((aeval x s)⁻¹ • m) ∈ M.tilde 0 I
          rw [smul_smul, show aeval x s / aeval x (X i ^ e) * (aeval x s)⁻¹ = (aeval x (X i ^ e))⁻¹ by
            field_simp]
          exact Submodule.subset_span ⟨m, X i ^ e, a, e, pow_mem (X_mem_monos hi) e,
            isHomogeneous_X_pow i e, hm, hae, rfl⟩
      | zero => exact ⟨1, by simp, by rw [smul_zero]; exact Submodule.zero_mem _⟩
      | add y₁ y₂ _ _ h₁ h₂ =>
        obtain ⟨a₁, ha₁, h₁⟩ := h₁
        obtain ⟨a₂, ha₂, h₂⟩ := h₂
        refine ⟨a₁ * a₂, by rw [map_mul]; exact ha₁.mul ha₂, ?_⟩
        have : ((a₁ * a₂ : chartRing S x I) : Ω) • (y₁ + y₂) =
            a₂ • ((a₁ : Ω) • y₁) + a₁ • ((a₂ : Ω) • y₂) := by
          change ((a₁ : Ω) * a₂) • (y₁ + y₂) = (a₂ : Ω) • ((a₁ : Ω) • y₁) + (a₁ : Ω) • ((a₂ : Ω) • y₂)
          rw [smul_add, smul_smul, smul_smul, mul_comm (a₂ : Ω)]
        rw [this]
        exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
      | smul c z _ hz =>
        obtain ⟨a, ha, hz⟩ := hz
        obtain ⟨a', ha', hc⟩ := exists_isUnit_mul_mem h c
        refine ⟨a' * a, by rw [map_mul]; exact ha'.mul ha, ?_⟩
        have : ((a' * a : chartRing S x I) : Ω) • (c • z) =
            (⟨_, hc⟩ : chartRing S x I) • ((a : Ω) • z) := by
          change ((a' : Ω) * a) • ((c : Ω) • z) = ((a' : Ω) * c) • ((a : Ω) • z)
          rw [smul_smul, smul_smul, mul_assoc, mul_assoc, mul_comm (a : Ω)]
        rw [this]
        exact Submodule.smul_mem _ _ hz
    · rintro ⟨a, ⟨u, hu⟩, hay⟩
      have hJ := (M.tildeSys 0).mono I J h _ hay
      have hinv : ((↑u⁻¹ : chartRing S x J) : Ω) * (a : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul u)
        rw [hu] at this
        exact this
      have hy : y = (↑u⁻¹ : chartRing S x J) • ((a : Ω) • y) := by
        change y = ((↑u⁻¹ : chartRing S x J) : Ω) • ((a : Ω) • y)
        rw [smul_smul, hinv, one_smul]
      rw [hy]
      exact Submodule.smul_mem _ _ hJ
end Tilde
section Graded
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
def gsup (M M' : FinGradedSub (S := S) (x := x) E) : FinGradedSub (S := S) (x := x) E where
  piece c := M.piece c ⊔ M'.piece c
  smul_mem d c f m hf hm := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
    rw [smul_add]
    exact Submodule.add_mem_sup (M.smul_mem d c f a hf ha) (M'.smul_mem d c f b hf hb)
  fg := by
    obtain ⟨n, deg, gen, hmem, hspan⟩ := M.fg
    obtain ⟨n', deg', gen', hmem', hspan'⟩ := M'.fg
    refine ⟨n + n', Fin.append deg deg', Fin.append gen gen', fun j => ?_, fun c => ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [Fin.append_left, Fin.append_left]; exact Submodule.mem_sup_left (hmem j)
      · rw [Fin.append_right, Fin.append_right]; exact Submodule.mem_sup_right (hmem' j)
    · refine sup_le ((hspan c).trans (Submodule.span_mono ?_)) ((hspan' c).trans (Submodule.span_mono ?_))
      · rintro _ ⟨j, f, e, hf, he, rfl⟩
        exact ⟨Fin.castAdd n' j, f, e, hf, by rw [Fin.append_left]; exact he, by rw [Fin.append_left]⟩
      · rintro _ ⟨j, f, e, hf, he, rfl⟩
        exact ⟨Fin.natAdd n j, f, e, hf, by rw [Fin.append_right]; exact he, by rw [Fin.append_right]⟩
def gmul (M : FinGradedSub (S := S) (x := x) E) {s : ℕ} (h : Fin s → Poly S N) (d : Fin s → ℕ) :
    FinGradedSub (S := S) (x := x) E where
  piece c := Submodule.span S {z | ∃ (l : Fin s) (b : ℤ) (m : E), m ∈ M.piece b ∧ b + d l = c ∧
    z = aeval x (h l) • m}
  smul_mem e c f m hf hm := by
    induction hm using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨l, b, m, hm, hb, rfl⟩ := hz
      refine Submodule.subset_span ⟨l, b + e, aeval x f • m, M.smul_mem e b f m hf hm, by rw [← hb]; ring, ?_⟩
      rw [smul_comm]
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz
  fg := by
    obtain ⟨n, deg, gen, hmem, hspan⟩ := M.fg
    let q : Fin (s * n) ≃ Fin s × Fin n := finProdFinEquiv.symm
    refine ⟨s * n, fun k => deg (q k).2 + d (q k).1, fun k => aeval x (h (q k).1) • gen (q k).2,
      fun k => Submodule.subset_span ⟨(q k).1, deg (q k).2, gen (q k).2, hmem _, rfl, rfl⟩, fun c => ?_⟩
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, b, m, hm, hb, rfl⟩
    have key : ∀ z, z ∈ Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ),
        f.IsHomogeneous e ∧ (e : ℤ) + deg j = b ∧ z = aeval x f • gen j} →
        aeval x (h l) • z ∈ Submodule.span S {z | ∃ (k : Fin (s * n)) (f : Poly S N) (e : ℕ),
          f.IsHomogeneous e ∧ (e : ℤ) + (deg (q k).2 + d (q k).1) = c ∧
            z = aeval x f • aeval x (h (q k).1) • gen (q k).2} := fun z hz => by
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨j, f, e, hf, he, rfl⟩ := hz
        refine Submodule.subset_span ⟨q.symm (l, j), f, e, hf, ?_, ?_⟩
        · rw [Equiv.apply_symm_apply]; rw [← hb, ← he]; ring
        · rw [Equiv.apply_symm_apply, smul_comm]
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
      | smul r z _ hz => rw [smul_comm]; exact Submodule.smul_mem _ r hz
    exact key m (hspan b hm)
end Graded
end SnapperQuotFilt
end
end GroundTheory.Heights₂.Heights.Kleiman


