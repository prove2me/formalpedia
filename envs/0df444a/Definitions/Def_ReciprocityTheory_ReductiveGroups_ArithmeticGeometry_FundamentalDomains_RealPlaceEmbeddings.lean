-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:20.864674+00:00
-- url     : https://prove2.me/theorems/cb371d25-a41e-4ba8-9f0b-ab63ff471747
-- title:
--   Real Place Embeddings
-- statement:
--   Definitions and structural lemmas for Real Place Embeddings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealPlaceEmbeddings.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TraceIntegralBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace RealPlaceEmbeddings
open NumberField Module Submodule
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
instance finite_int : Module.Finite ℤ X.Λ := by
  have : Module.Finite (𝓞 E) X.Λ := Module.Finite.iff_fg.mpr X.Λ_fg
  exact Module.Finite.trans (𝓞 E) X.Λ
instance free_int : Module.Free ℤ X.Λ := inferInstance
noncomputable def zb : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ := Module.finBasis ℤ X.Λ
theorem smul_mem_spanQ (α : E) {l : Fin r → E} (hl : l ∈ X.Λ) :
    α • l ∈ span ℚ (X.Λ : Set (Fin r → E)) := by
  have hα : α = ∑ k, (integralBasis E).repr α k • integralBasis E k :=
    ((integralBasis E).sum_repr α).symm
  rw [hα, Finset.sum_smul]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [smul_assoc]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [integralBasis_apply]
  exact X.Λ.smul_of_tower_mem (RingOfIntegers.basis E k) hl
theorem spanQ_eq_top {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    span ℚ (Set.range fun i => (g i : Fin r → E)) = ⊤ := by
  set S := span ℚ (Set.range fun i => (g i : Fin r → E)) with hS
  have hΛ : ∀ l ∈ X.Λ, l ∈ S := by
    intro l hl
    have h1 : (⟨l, hl⟩ : X.Λ) = ∑ i, g.repr ⟨l, hl⟩ i • g i := (g.sum_repr ⟨l, hl⟩).symm
    have h2 : l = ∑ i, ((g.repr ⟨l, hl⟩ i : ℤ) : ℚ) • (g i : Fin r → E) := by
      refine (congrArg Subtype.val h1).trans ?_
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul]
      rfl
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspanΛ : span ℚ (X.Λ : Set (Fin r → E)) ≤ S := Submodule.span_le.mpr fun l hl => hΛ l hl
  have hE : ∀ α : E, ∀ w ∈ S, α • w ∈ S := by
    intro α w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hspanΛ (smul_mem_spanQ X α (g i).2)
    | zero => simp
    | add y z _ _ hy hz => rw [smul_add]; exact S.add_mem hy hz
    | smul q y _ hy => rw [smul_comm]; exact S.smul_mem q hy
  refine eq_top_iff.mpr ?_
  rintro v -
  have hv : v ∈ span E (X.Λ : Set (Fin r → E)) := by rw [X.Λ_span]; trivial
  induction hv using Submodule.span_induction with
  | mem y hy => exact hΛ y hy
  | zero => exact S.zero_mem
  | add y z _ _ hy hz => exact S.add_mem hy hz
  | smul α y _ hy => exact hE α y hy
theorem linIndQ {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) :
    LinearIndependent ℚ fun i => (g i : Fin r → E) := by
  have hZ : LinearIndependent ℤ fun i => (g i : Fin r → E) :=
    g.linearIndependent.map' (X.Λ.toAddSubgroup.subtype.toIntLinearMap)
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  exact (LinearIndependent.iff_fractionRing ℤ ℚ).mp hZ
noncomputable def qb {ι : Type} [Fintype ι] (g : Basis ι ℤ X.Λ) : Basis ι ℚ (Fin r → E) :=
  Basis.mk (linIndQ X g) (spanQ_eq_top X g).ge
noncomputable def plc (τ : X.Ψ) : TraceIntegralBasis.CP E :=
  ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩
open scoped Classical in

noncomputable def Tm : TraceIntegralBasis.VS E →ₗ[ℝ] (X.Ψ → ℂ) where
  toFun z τ := if (plc X τ).1.embedding = τ.1 then z (plc X τ) else conj (z (plc X τ))
  map_add' z z' := by
    funext τ
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    funext τ
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul]
noncomputable def Ja (a : Fin r) : (X.Ψ → ℂ) →ₗ[ℝ] (X.Ψ → Fin r → ℂ) where
  toFun z τ b := if b = a then z τ else 0
  map_add' z z' := by
    funext τ b
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c z := by
    funext τ b
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp
end RealPlaceEmbeddings
end ReciprocityTheory.ChartRestriction.G.FD


