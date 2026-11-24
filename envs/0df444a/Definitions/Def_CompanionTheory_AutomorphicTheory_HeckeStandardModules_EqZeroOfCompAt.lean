-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
-- name    : CompanionTheory_AutomorphicTheory_HeckeStandardModules_EqZeroOfCompAt
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:00.859511+00:00
-- url     : https://prove2.me/theorems/70122564-7cfa-4501-9b0b-a514182b5701
-- title:
--   Eq Zero Of Comp At
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Comp At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/HeckeStandardModules/EqZeroOfCompAt.lean

import Definitions.Def_ReciprocityTheory_Automorphisms_SplitCoeAlgebraMap
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsIntegerUnitSplitPlaceConjugatePrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Theorems.Thm_GlobalTheory_SplitSep_exists_sep
import Theorems.Thm_GlobalTheory_tensor_decomp_eq_zero
import Theorems.Thm_GlobalTheory_tensor_exists_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut TensorProduct
noncomputable section
namespace CompanionTheory.Split
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => maximalRealSubfield L
open Classical in

def sgl (v : HeightOneSpectrum (𝓞 L⁺)) (r : v.adicCompletion L⁺) : AFplus L :=
  ⟨Pi.single (M := fun w : HeightOneSpectrum (𝓞 L⁺) => w.adicCompletion L⁺) v r, by
    refine Filter.mem_of_superset (Set.finite_singleton v).compl_mem_cofinite fun w hw => ?_
    have hw' : w ≠ v := hw
    simp only [Set.mem_setOf_eq, Pi.single_eq_of_ne hw']
    exact zero_mem _⟩
theorem sgl_same (v : HeightOneSpectrum (𝓞 L⁺)) (r : v.adicCompletion L⁺) : sgl v r v = r := by
  classical
  exact Pi.single_eq_same (M := fun w : HeightOneSpectrum (𝓞 L⁺) => w.adicCompletion L⁺) v r
theorem sgl_ne (v : HeightOneSpectrum (𝓞 L⁺)) (r : v.adicCompletion L⁺) {w} (hw : w ≠ v) : sgl v r w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 L⁺) => w.adicCompletion L⁺) hw r
theorem compAt_tmul (v : HeightOneSpectrum (𝓞 L⁺)) (x : L) (a : AFplus L) :
    compAt L v (x ⊗ₜ[L⁺] a) = x ⊗ₜ[L⁺] (a v) := rfl
theorem proj_tmul (s : SplitPlace L) (x : L) (a : AFplus L) : s.proj (x ⊗ₜ[L⁺] a) = s.i x * a s.v := rfl
theorem conj_tmul (x : L) (a : AFplus L) : conjAL L (x ⊗ₜ[L⁺] a) = IsCMField.complexConj L x ⊗ₜ[L⁺] a := rfl
theorem exists_basis (e : L) (he : IsCMField.complexConj L e ≠ e) :
    ∃ b : Module.Basis (Fin 2) L⁺ L, b 0 = 1 ∧ b 1 = e := by
  have hli : LinearIndependent L⁺ ![(1 : L), e] := by
    rw [LinearIndependent.pair_iff' one_ne_zero]
    rintro a rfl
    exact he (by rw [← Algebra.algebraMap_eq_smul_one, AlgEquiv.commutes])
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli (by
    rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two]), ?_, ?_⟩ <;> simp
theorem eq_zero_of_compAt (z : AL L) (hz : ∀ v, compAt L v z = 0) : z = 0 := by
  let b : Module.Basis (Fin 2) L⁺ L := Module.finBasisOfFinrankEq _ _ (Algebra.IsQuadraticExtension.finrank_eq_two L⁺ L)
  obtain ⟨A, B, rfl⟩ := GlobalTheory.tensor_exists_decomp b z
  have h : ∀ w, A w = 0 ∧ B w = 0 := fun w => GlobalTheory.tensor_decomp_eq_zero b _ _ (by
    have := hz w
    rwa [map_add, compAt_tmul, compAt_tmul] at this)
  rw [show A = 0 from DFunLike.ext _ _ fun w => (h w).1, show B = 0 from DFunLike.ext _ _ fun w => (h w).2]
  simp
variable (s : SplitPlace L)
theorem exists_ne : ∃ e : L, s.i (IsCMField.complexConj L e) ≠ s.i e := by
  obtain ⟨e, h1, h2⟩ := GlobalTheory.SplitSep.exists_sep L s
  exact ⟨e, fun h => by rw [h, h1] at h2; exact lt_irrefl _ h2⟩
theorem eq_zero_of_proj {z : AL L} (hz : ∀ w, w ≠ s.v → compAt L w z = 0) (h1 : s.proj z = 0)
    (h2 : s.proj (conjAL L z) = 0) : z = 0 := by
  obtain ⟨e, he⟩ := exists_ne s
  obtain ⟨b, hb0, hb1⟩ := exists_basis e fun h => he (by rw [h])
  refine eq_zero_of_compAt z fun w => ?_
  rcases eq_or_ne w s.v with rfl | hw
  · obtain ⟨A, B, rfl⟩ := GlobalTheory.tensor_exists_decomp b z
    rw [hb0, hb1] at *
    rw [map_add, proj_tmul, proj_tmul, map_one] at h1
    rw [map_add, conj_tmul, conj_tmul, map_add, proj_tmul, proj_tmul, map_one, map_one] at h2
    have hB : B s.v = 0 := (mul_eq_zero.1 (show (s.i (IsCMField.complexConj L e) - s.i e) * B s.v = 0 by
      linear_combination h2 - h1)).resolve_left (sub_ne_zero.2 he)
    have hA : A s.v = 0 := by simpa [hB] using h1
    rw [map_add, compAt_tmul, compAt_tmul, hA, hB, tmul_zero, tmul_zero, add_zero]
  · exact hz w hw
theorem exists_pair (a b : s.v.adicCompletion L⁺) :
    ∃ z : AL L, (∀ w, w ≠ s.v → compAt L w z = 0) ∧ s.proj z = a ∧ s.proj (conjAL L z) = b := by
  obtain ⟨e, he⟩ := exists_ne s
  have hd := sub_ne_zero.2 he
  set β := (b - a) / (s.i (IsCMField.complexConj L e) - s.i e) with hβ
  refine ⟨(1 : L) ⊗ₜ[L⁺] sgl s.v (a - s.i e * β) + e ⊗ₜ[L⁺] sgl s.v β, fun w hw => ?_, ?_, ?_⟩
  · rw [map_add, compAt_tmul, compAt_tmul, sgl_ne _ _ hw, sgl_ne _ _ hw, tmul_zero, tmul_zero, add_zero]
  · rw [map_add, proj_tmul, proj_tmul, sgl_same, sgl_same, map_one]
    ring
  · rw [map_add, conj_tmul, conj_tmul, map_add, proj_tmul, proj_tmul, sgl_same, sgl_same, map_one, map_one]
    have := div_mul_cancel₀ (b - a) hd
    linear_combination this
theorem compAt_conj {w : HeightOneSpectrum (𝓞 L⁺)} {z : AL L} (h : compAt L w z = 0) : compAt L w (conjAL L z) = 0 := by
  have : ∀ z : AL L, compAt L w (conjAL L z) =
      Algebra.TensorProduct.map (IsCMField.complexConj L).toAlgHom (AlgHom.id L⁺ _) (compAt L w z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x a => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this, h, map_zero]
abbrev ent (x : GA L n) : Matrix (Fin n) (Fin n) (AL L) := x.1
theorem ent_inv (x : GA L n) (i j : Fin n) : ent x⁻¹ i j = conjAL L (ent x j i) := by
  have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
    Units.inv_eq_of_mul_eq_one_right x.2
  exact congrFun (congrFun h1 i) j
theorem loc_apply (x : GA L n) (i j : Fin n) :
    (s.loc n x : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j = s.proj (ent x i j) := rfl
def Gv (n : ℕ) (T : Set (HeightOneSpectrum (𝓞 L⁺))) : Subgroup (GA L n) :=
  ⨅ w, ⨅ _ : w ∉ T, ((Matrix.GeneralLinearGroup.map (compAt L w)).comp (GA L n).subtype).ker
theorem mem_Gv {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x : GA L n} : x ∈ Gv n T ↔ TrivOutside T x := by
  simp only [Gv, Subgroup.mem_iInf, MonoidHom.mem_ker, TrivOutside, Units.ext_iff]
  rfl
instance Gv_normal (T : Set (HeightOneSpectrum (𝓞 L⁺))) : (Gv (L := L) n T).Normal :=
  Subgroup.normal_iInf_normal fun _ => Subgroup.normal_iInf_normal fun _ => inferInstance
theorem sub_one_supp {v : HeightOneSpectrum (𝓞 L⁺)} {x : GA L n} (hx : TrivOutside {v} x) (i j : Fin n) {w}
    (hw : w ≠ v) : compAt L w (ent x i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0 := by
  rw [map_sub, show compAt L w (ent x i j) = _ from congrFun (congrFun (hx w hw) i) j]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]
theorem map_one_apply {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (i j : Fin n) :
    φ ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) S) i j := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]
theorem one_apply_symm {R : Type*} [CommRing R] (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) j i := by
  simp [Matrix.one_apply, eq_comm]
theorem eq_one_of_loc {x : GA L n} (hx : TrivOutside {s.v} x) (h : s.loc n x = 1) : x = 1 := by
  have h' : s.loc n x⁻¹ = 1 := by rw [map_inv, h, inv_one]
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_proj s (fun w => sub_one_supp hx i j) ?_ ?_)))
  · show s.proj (ent x i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0
    rw [map_sub, ← loc_apply, h, map_one_apply]
    exact sub_self _
  · show s.proj (conjAL L (ent x i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j)) = 0
    rw [map_sub, map_sub, ← ent_inv, ← loc_apply, h', map_one_apply, map_one_apply, one_apply_symm]
    exact sub_self _
theorem exists_loc (g : GL (Fin n) (s.v.adicCompletion L⁺)) : ∃ x : GA L n, TrivOutside {s.v} x ∧ s.loc n x = g := by
  choose Z h0 h1 h2 using fun i j : Fin n => exists_pair s
    ((g : Matrix (Fin n) (Fin n) _) i j - (1 : Matrix (Fin n) (Fin n) _) i j)
    (((g⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) j i - (1 : Matrix (Fin n) (Fin n) _) i j)
  set X : Matrix (Fin n) (Fin n) (AL L) := 1 + Matrix.of Z with hX
  have e0 : ∀ w, w ≠ s.v → X.map (compAt L w) = 1 := fun w hw => Matrix.ext fun i j => by
    rw [Matrix.map_apply, hX, Matrix.add_apply, map_add, Matrix.of_apply, h0 i j w hw, add_zero, map_one_apply]
  have e0' : ∀ w, w ≠ s.v → (conjT (conjAL L) X).map (compAt L w) = 1 := fun w hw => Matrix.ext fun i j => by
    show compAt L w (conjAL L (X j i)) = _
    rw [hX, Matrix.add_apply, map_add, map_add, Matrix.of_apply, compAt_conj (h0 j i w hw), add_zero, map_one_apply,
      map_one_apply, one_apply_symm]
  have e1 : X.map s.proj = g := Matrix.ext fun i j => by
    rw [Matrix.map_apply, hX, Matrix.add_apply, map_add, Matrix.of_apply, h1, map_one_apply, add_sub_cancel]
  have e2 : (conjT (conjAL L) X).map s.proj = (g⁻¹ : GL (Fin n) _) := Matrix.ext fun i j => by
    show s.proj (conjAL L (X j i)) = _
    rw [hX, Matrix.add_apply, map_add, map_add, Matrix.of_apply, h2, map_one_apply, map_one_apply, add_sub_cancel]
  have e3 : (X * conjT (conjAL L) X).map s.proj = 1 := by rw [Matrix.map_mul, e1, e2, Units.mul_inv]
  have hU : X * conjT (conjAL L) X = 1 := Matrix.ext fun i j => sub_eq_zero.1 (eq_zero_of_proj s (fun w hw => by
      rw [map_sub, ← Matrix.map_apply (f := compAt L w), Matrix.map_mul, e0 w hw, e0' w hw, one_mul, map_one_apply, sub_self])
    (by rw [map_sub, ← Matrix.map_apply (f := s.proj), e3, map_one_apply, sub_self]) (by
      have : conjAL L ((X * conjT (conjAL L) X) i j) = (X * conjT (conjAL L) X) j i := by
        show conjT (conjAL L) (X * conjT (conjAL L) X) j i = _
        rw [conjT_mul, conjT_conjT _ (conjAL_conjAL L)]
      rw [map_sub, map_sub, this, ← Matrix.map_apply (f := s.proj), e3, map_one_apply, map_one_apply, one_apply_symm,
        sub_self]))
  exact ⟨⟨⟨X, _, hU, mul_eq_one_comm.1 hU⟩, hU⟩, e0, Units.ext e1⟩
abbrev KL (n : ℕ) : Subgroup (GL (Fin n) (s.v.adicCompletion L⁺)) :=
  Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring
def locEquiv (n : ℕ) : Gv (L := L) n {s.v} ≃* GL (Fin n) (s.v.adicCompletion L⁺) :=
  MulEquiv.ofBijective ((s.loc n).comp (Gv n {s.v}).subtype)
    ⟨(injective_iff_map_eq_one _).2 fun x h => Subtype.ext (eq_one_of_loc s (mem_Gv.1 x.2) h), fun g =>
      let ⟨x, hx, e⟩ := exists_loc s g
      ⟨⟨x, mem_Gv.2 hx⟩, e⟩⟩
def emb (n : ℕ) : GL (Fin n) (s.v.adicCompletion L⁺) →* GA L n :=
  (Gv n {s.v}).subtype.comp (locEquiv s n).symm.toMonoidHom
end CompanionTheory.Split


