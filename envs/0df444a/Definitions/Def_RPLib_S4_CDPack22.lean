-- Prove2me | Definitions.Def_RPLib_S4_CDPack22
-- name    : RPLib_S4_CDPack22
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:31:39.267928+00:00
-- url     : https://prove2.me/theorems/84445b82-4fe9-4b89-a69f-24946a845ed2
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 22 of 71
-- statement:
--   Part 22 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CupDuality_ParZ`: S4-CurveDuality O9-1: dual bases of parabolic homomorphisms; the block over `ℤ/N` from the right kernel
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack21
import Definitions.Def_RPLib_S4_CDPack07

/-!
# Curve-duality library package, part 22 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CupDuality_ParZ`: S4-CurveDuality O9-1: dual bases of parabolic homomorphisms; the block over `ℤ/N` from the right kernel
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CupDuality_ParZ =====
section

/-!
# S4-CurveDuality O9-1: dual bases of parabolic homomorphisms; the block over `ℤ/N` from the right kernel

`exists_dualBasis`: an additive `(ℤ/N)^r ≃ P` onto a group `P` of homomorphisms `Γ → ℤ/N` gives `χ_i = Ψ(δ_i)`
with dual elements `e_j ∈ Γ` (`χ_i(e_j) = δ_ij`) spanning `P` (the evaluation `Γ → (ℤ/N)^r` is onto: a character
of `(ℤ/N)^r` killing its image is a relation among the `χ_i`). `parabolic_of_rightKer`: with such a dual basis
of the parabolic homomorphisms, a zero right kernel of `constPair` over `ℤ/N` makes the intersection matrix
injective, hence invertible over the finite ring `ℤ/N`, so the parabolic block is perfect.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh Matrix

noncomputable section

section Basis

variable {N : ℕ} [NeZero N] {Γ : Type*} [Group Γ] {r : ℕ}

/-- The standard vector `δ_i`. -/
def stdV (i : Fin r) : Fin r → ZMod N := fun j => if i = j then 1 else 0

theorem addHom_apply_sum {B : Type*} [AddCommGroup B] [Module (ZMod N) B] (f : (Fin r → ZMod N) →+ B)
    (v : Fin r → ZMod N) : f v = ∑ i, v i • f (stdV i) :=
  LinearMap.pi_apply_eq_sum_univ (f.toZModLinearMap N) v

variable (P : AddSubgroup (Γ → ZMod N)) (Ψ : (Fin r → ZMod N) ≃+ P)

/-- `χ_i := Ψ(δ_i)`. -/
def chiOf (i : Fin r) : Γ → ZMod N := (Ψ (stdV i) : Γ → ZMod N)

theorem chiOf_mem (i : Fin r) : chiOf P Ψ i ∈ P := (Ψ (stdV i)).2

theorem psi_apply (v : Fin r → ZMod N) (g : Γ) : (Ψ v : Γ → ZMod N) g = ∑ i, v i * chiOf P Ψ i g :=
  addHom_apply_sum ((Pi.evalAddMonoidHom (fun _ : Γ => ZMod N) g).comp (P.subtype.comp Ψ.toAddMonoidHom)) v

theorem exists_dual (hP : ∀ y ∈ P, ∀ a b : Γ, y (a * b) = y a + y b) (j : Fin r) :
    ∃ g : Γ, ∀ i, chiOf P Ψ i g = if i = j then 1 else 0 := by
  classical
  have hmul : ∀ i (a b : Γ), chiOf P Ψ i (a * b) = chiOf P Ψ i a + chiOf P Ψ i b :=
    fun i => hP _ (chiOf_mem P Ψ i)
  have hone : ∀ i, chiOf P Ψ i 1 = 0 := fun i => by
    have h := hmul i 1 1
    rw [mul_one] at h
    exact left_eq_add.mp h
  have hinv : ∀ i (a : Γ), chiOf P Ψ i a⁻¹ = -chiOf P Ψ i a := fun i a => by
    have h := hmul i a⁻¹ a
    rw [inv_mul_cancel, hone] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  let R : AddSubgroup (Fin r → ZMod N) :=
    { carrier := Set.range fun g : Γ => fun i => chiOf P Ψ i g
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, funext fun i => hmul i a b⟩
      zero_mem' := ⟨1, funext fun i => hone i⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a⁻¹, funext fun i => hinv i a⟩ }
  by_contra hne
  simp only [not_exists] at hne
  have hmem : (fun i => if i = j then (1 : ZMod N) else 0) ∉ R := by
    rintro ⟨g, hg⟩
    exact hne g fun i => congrFun hg i
  have hN : ∀ a : (Fin r → ZMod N) ⧸ R, N • a = 0 := by
    intro a
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective a
    have hv : N • v = 0 := funext fun i => by
      rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rfl
    rw [← QuotientAddGroup.mk_nsmul, hv, QuotientAddGroup.mk_zero]
  have hne0 : (QuotientAddGroup.mk (fun i => if i = j then (1 : ZMod N) else 0) :
      (Fin r → ZMod N) ⧸ R) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact hmem
  obtain ⟨ψ, hψ⟩ := exists_zmod_hom_ne_zero hN hne0
  let ψ' : (Fin r → ZMod N) →+ ZMod N := ψ.comp (QuotientAddGroup.mk' R)
  let c : Fin r → ZMod N := fun i => ψ' (stdV i)
  have hc : Ψ c = 0 := by
    apply Subtype.ext
    funext g
    have h0 : ψ' (fun i => chiOf P Ψ i g) = 0 := by
      show ψ (QuotientAddGroup.mk (fun i => chiOf P Ψ i g)) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 (show (fun i => chiOf P Ψ i g) ∈ R from ⟨g, rfl⟩), map_zero]
    have h1 := addHom_apply_sum ψ' (fun i => chiOf P Ψ i g)
    rw [h0] at h1
    rw [AddSubgroup.coe_zero, Pi.zero_apply, psi_apply, h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc0 : c = 0 := Ψ.injective (hc.trans (map_zero Ψ).symm)
  apply hψ
  show ψ' (fun i => if i = j then (1 : ZMod N) else 0) = 0
  rw [addHom_apply_sum ψ']
  exact Finset.sum_eq_zero fun i _ => by
    rw [show ψ' (stdV i) = 0 from congrFun hc0 i, smul_zero]

theorem span_of_dual (e : Fin r → Γ) (he : ∀ i j, chiOf P Ψ i (e j) = if i = j then 1 else 0)
    {y : Γ → ZMod N} (hy : y ∈ P) (g : Γ) : y g = ∑ i, y (e i) * chiOf P Ψ i g := by
  classical
  have hv : ∀ x, y x = ∑ i, (Ψ.symm ⟨y, hy⟩) i * chiOf P Ψ i x := fun x => by
    rw [← psi_apply, AddEquiv.apply_symm_apply]
  have he' : ∀ j, y (e j) = (Ψ.symm ⟨y, hy⟩) j := fun j => by
    rw [hv, Finset.sum_eq_single j (fun i _ hij => by rw [he, if_neg hij, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), he, if_pos rfl, mul_one]
  rw [hv]
  exact Finset.sum_congr rfl fun i _ => by rw [he']

/-- **Dual basis.** `χ_i = Ψ(δ_i)` has dual elements `e_j ∈ Γ` and spans `P` in coordinates `y(e_i)`. -/
theorem exists_dualBasis (hP : ∀ y ∈ P, ∀ a b : Γ, y (a * b) = y a + y b) :
    ∃ e : Fin r → Γ, (∀ i j, chiOf P Ψ i (e j) = if i = j then 1 else 0) ∧
      ∀ y ∈ P, ∀ g, y g = ∑ i, y (e i) * chiOf P Ψ i g := by
  choose e he using exists_dual P Ψ hP
  exact ⟨e, fun i j => he j i, fun y hy g => span_of_dual P Ψ e (fun i j => he j i) hy g⟩

end Basis

section Perf

variable {N : ℕ} [NeZero N] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Γ : Subgroup G} [Γ.Normal] {S : Type} [Fintype S] [Nonempty S] {I : S → Subgroup G}
  {t : (s : S) → ↥(Γ ⊓ I s)} {r : ℕ} {χ : Fin r → Γ → ZMod N} {e : Fin r → Γ}

/-- **O9 over `ℤ/N`.** With a dual basis of the parabolic homomorphisms, a zero right kernel of `constPair`
(`InR d → d = 0`) makes the parabolic block perfect. -/
theorem parabolic_of_rightKer {σ0 : Representation (ZMod N) G (ZMod N)}
    (H0 : CupHyp (Representation.trivial (ZMod N) G (ZMod N)) σ0 σ0 (LinearMap.mul (ZMod N) (ZMod N)) Γ)
    (D0 : ConstData σ0 Γ I t) (hχ : ∀ i, IsParHom (InBdry I) (χ i))
    (hδ : ∀ i j, χ i (e j) = if i = j then 1 else 0)
    (hspan : ∀ y : Γ → ZMod N, IsParHom (InBdry I) y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    (hR : ∀ d : Γ → ZMod N, InR H0 D0 d → d = 0) :
    (pairQuotSub (constPair H0 D0) _ _ (constPair_h0 H0 D0)).IsPerfPair := by
  classical
  obtain ⟨U, hU⟩ : ∃ U : Fin r → Fin r → Γ → ZMod N, IsPrimFam χ U := by
    choose U hU using fun i j => exists_prim H0
      (mem_Z1_of_isParHom (σ := Representation.trivial (ZMod N) G (ZMod N)) (fun _ _ => rfl) (hχ i))
      (mem_Z1_of_isParHom D0.triv (hχ j))
    refine ⟨U, fun i j => ⟨(hU i j).1, fun g h => ?_⟩⟩
    have := (hU i j).2 g h
    simpa only [cupCochain, LinearMap.mul_apply', D0.triv] using this
  have hid : (lamMat t U).map (RingHom.id (ZMod N)) = lamMat t U := Matrix.ext fun _ _ => rfl
  have hlin : ∀ μ, (lamMat t U) *ᵥ μ = 0 → μ = 0 := by
    intro μ hμ
    have hpair : ∀ l, pairQuotSub (constPair H0 D0) _ _ (constPair_h0 H0 D0)
        (eL (RingHom.id _) hχ hδ hspan l) (eR (RingHom.id _) D0.triv hχ hδ hspan μ) = 0 := by
      intro l
      rw [pair_eLR (RingHom.id _) H0 D0 hχ hδ hspan hU l μ, hid, toLinearMap₂'_eq_dot,
        ← dotProduct_mulVec, hμ, dotProduct_zero]
    have hd : InR H0 D0 (parHomL (RingHom.id (ZMod N)) χ μ) := by
      refine ⟨(parZ1 (RingHom.id _) D0.triv hχ μ).2, fun s g hg => (parHomL_isParHom hχ μ).2.2 g ⟨s, hg⟩,
        fun z => ?_⟩
      obtain ⟨l, hl⟩ := (eL (RingHom.id _) hχ hδ hspan).surjective (Submodule.Quotient.mk z)
      have h := hpair l
      rw [hl, pairQuotSub_apply, eR_coe] at h
      exact h
    have h0 := hR _ hd
    funext j
    have h1 := congrFun h0 (e j)
    rw [parHomL_e hδ] at h1
    exact h1
  have hinj : Function.Injective (lamMat t U).mulVec := fun a b hab =>
    sub_eq_zero.1 (hlin _ (by rw [mulVec_sub, hab, sub_self]))
  obtain ⟨u, hu⟩ := Matrix.mulVec_surjective_iff_isUnit.1 (Finite.injective_iff_surjective.1 hinj)
  have hBA : (↑u⁻¹ : Matrix (Fin r) (Fin r) (ZMod N)) * lamMat t U = 1 := by
    rw [← hu]
    exact u.inv_mul
  have hAB : lamMat t U * (↑u⁻¹ : Matrix (Fin r) (Fin r) (ZMod N)) = 1 := by
    rw [← hu]
    exact u.mul_inv
  have hM := isPerfPair_toLinearMap₂' hBA hAB
  refine LinearMap.IsPerfPair.congr (p := Matrix.toLinearMap₂' (ZMod N) (lamMat t U))
    (eM := (eL (RingHom.id _) hχ hδ hspan).symm) (eN := (eR (RingHom.id _) D0.triv hχ hδ hspan).symm)
    (q := _) ?_
  refine LinearMap.ext fun l => LinearMap.ext fun μ => ?_
  have := pair_eLR (RingHom.id (ZMod N)) H0 D0 hχ hδ hspan hU l μ
  rw [hid] at this
  exact this

end Perf

end

end CupDuality
end RamanujanPetersson

end


