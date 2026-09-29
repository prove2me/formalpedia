-- Prove2me | solution 1 for AutomorphicForm.exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/adb38731-70f2-5bda-9730-deefcf8d047b

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_AutomorphicForm_heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_AdelicDock_finEmbed_localEmbed_comm_of_ne
import Theorems.Thm_AutomorphicForm_le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Module
p2m_export "Module" "support Finite.of_basis finrank Free End.mul_apply mk finrank_mul_finrank End finBasis finite_of_finrank_pos End.one_apply End.mem_eigenspace_iff Basis"
namespace End
p2m_export "Module.End" "mul_apply eigenspace one_apply mem_eigenspace_iff"
namespace EigenData
p2m_open "Module.End Module"

variable {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module k E]

section Trace

private theorem finiteDimensional_of_trace_ne_zero {M : Type*} [AddCommGroup M] [Module k M]
    (f : Module.End k M) (h : LinearMap.trace k M f ≠ 0) : FiniteDimensional k M := by
  classical
  by_contra hM
  apply h
  have hne : ¬∃ s : Finset M, Nonempty (Module.Basis s k M) :=
    fun ⟨s, ⟨b⟩⟩ => hM (Module.Finite.of_basis b)
  rw [LinearMap.trace, dif_neg hne, LinearMap.zero_apply]

private theorem trace_eq_trace_restrict [FiniteDimensional k E] (f : Module.End k E)
    (W : Submodule k E) (hW : ∀ x, f x ∈ W) :
    LinearMap.trace k E f = LinearMap.trace k W (f.restrict fun x _ => hW x) := by
  have h : f.restrict (fun x (_ : x ∈ W) => hW x) = f.codRestrict W hW ∘ₗ W.subtype :=
    LinearMap.ext fun _ => rfl
  calc LinearMap.trace k E f = LinearMap.trace k E (W.subtype ∘ₗ f.codRestrict W hW) := by
        rw [LinearMap.subtype_comp_codRestrict]
    _ = LinearMap.trace k W (f.codRestrict W hW ∘ₗ W.subtype) := LinearMap.trace_comp_comm' _ _
    _ = LinearMap.trace k W (f.restrict fun x _ => hW x) := by rw [h]

private theorem trace_eq_sum_trace_restrict_of_mapsTo [FiniteDimensional k E] {α : Type*}
    [Fintype α] [DecidableEq α] (A : α → Submodule k E) (h : DirectSum.IsInternal A)
    (σ : α → Option α) (f : Module.End k E) (hf : ∀ a b, σ a = some b → ∀ x ∈ A a, f x ∈ A b)
    (hf0 : ∀ a, σ a = none → ∀ x ∈ A a, f x = 0) :
    LinearMap.trace k E f =
      ∑ a : {a // σ a = some a}, LinearMap.trace k (A a.1) (f.restrict (hf a.1 a.1 a.2)) := by
  classical
  let v : ∀ a, Module.Basis (Fin (Module.finrank k (A a))) k (A a) :=
    fun a => Module.finBasis k (A a)
  have hdiag : ∀ a (j : Fin (Module.finrank k (A a))),
      (h.collectedBasis v).repr (f (h.collectedBasis v ⟨a, j⟩)) ⟨a, j⟩ =
        if ha : σ a = some a then
          (v a).repr ⟨f (h.collectedBasis v ⟨a, j⟩), hf a a ha _ (h.collectedBasis_mem v ⟨a, j⟩)⟩ j
        else 0 := by
    intro a j
    by_cases ha : σ a = some a
    · rw [dif_pos ha]
      exact h.collectedBasis_repr_of_mem v _
    · rw [dif_neg ha]
      rcases hσ : σ a with _ | b
      · rw [hf0 a hσ _ (h.collectedBasis_mem v ⟨a, j⟩), map_zero, Finsupp.zero_apply]
      · have hba : b ≠ a := fun hba => ha (hba ▸ hσ)
        exact h.collectedBasis_repr_of_mem_ne v hba (hf a b hσ _ (h.collectedBasis_mem v ⟨a, j⟩))
  have htr : ∀ a (ha : σ a = some a),
      LinearMap.trace k (A a) (f.restrict (hf a a ha)) =
        ∑ j, (v a).repr ⟨f (h.collectedBasis v ⟨a, j⟩),
          hf a a ha _ (h.collectedBasis_mem v ⟨a, j⟩)⟩ j := by
    intro a ha
    rw [LinearMap.trace_eq_matrix_trace k (v a)]
    simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.restrict_apply,
      DirectSum.IsInternal.collectedBasis_coe]
  rw [LinearMap.trace_eq_matrix_trace k (h.collectedBasis v)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [Fintype.sum_sigma, ← Fintype.sum_subtype_add_sum_subtype (fun a => σ a = some a)]
  have hzero : ∑ a : {a // ¬σ a = some a}, ∑ j : Fin (Module.finrank k (A a.1)),
      (h.collectedBasis v).repr (f (h.collectedBasis v ⟨a.1, j⟩)) ⟨a.1, j⟩ = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun j _ => ?_
    rw [hdiag a.1 j, dif_neg a.2]
  rw [hzero, add_zero]
  refine Fintype.sum_congr _ _ fun a => ?_
  rw [htr a.1 a.2]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [hdiag a.1 j, dif_pos a.2]

end Trace

section Pieces

variable {ι : Type*} (T : ι → Module.End k E)

private def piece (χ : ι → k) : Submodule k E := ⨅ i, (T i).eigenspace (χ i)

variable {T}

private theorem mem_piece {χ : ι → k} {x : E} : x ∈ piece T χ ↔ ∀ i, T i x = χ i • x := by
  simp only [piece, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

private theorem sub_apply_of_mem_piece {χ : ι → k} {x : E} (hx : x ∈ piece T χ) (i : ι) (c : k) :
    (T i - c • (1 : Module.End k E)) x = (χ i - c) • x := by
  rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, (mem_piece.mp hx) i, sub_smul]

private theorem exists_separating (χ₀ : ι → k) (t : Finset (ι → k)) (ht : χ₀ ∉ t) :
    ∃ q : Module.End k E, (∀ χ ∈ t, ∀ x ∈ piece T χ, q x = 0) ∧
      (∃ c : k, c ≠ 0 ∧ ∀ x ∈ piece T χ₀, q x = c • x) ∧
      ∀ V : Submodule k E, (∀ i, ∀ v ∈ V, T i v ∈ V) → ∀ v ∈ V, q v ∈ V := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    exact ⟨1, fun χ hχ => absurd hχ (Finset.notMem_empty χ), ⟨1, one_ne_zero, fun x _ => by
      rw [Module.End.one_apply, one_smul]⟩, fun V _ v hv => by rwa [Module.End.one_apply]⟩
  | insert χ t hχt ih =>
    obtain ⟨q, hq0, ⟨c, hc, hqc⟩, hqV⟩ := ih fun h => ht (Finset.mem_insert_of_mem h)
    have hne : χ ≠ χ₀ := fun h => ht (h ▸ Finset.mem_insert_self χ t)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    refine ⟨q * (T i - χ i • 1), ?_, ⟨c * (χ₀ i - χ i),
      mul_ne_zero hc (sub_ne_zero.mpr (Ne.symm hi)), ?_⟩, ?_⟩
    · intro χ' hχ' x hx
      rw [Module.End.mul_apply, sub_apply_of_mem_piece hx i (χ i), map_smul]
      rcases Finset.mem_insert.mp hχ' with rfl | hχ't
      · rw [sub_self, zero_smul]
      · rw [hq0 χ' hχ't x hx, smul_zero]
    · intro x hx
      rw [Module.End.mul_apply, sub_apply_of_mem_piece hx i (χ i), map_smul, hqc x hx, smul_smul,
        mul_comm]
    · intro V hV v hv
      rw [Module.End.mul_apply]
      refine hqV V hV _ ?_
      rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact V.sub_mem (hV i v hv) (V.smul_mem _ hv)

private theorem piece_iSupIndep : iSupIndep (piece T) := by
  classical
  intro χ₀
  rw [Submodule.disjoint_def]
  intro x hx hx'
  rw [iSup_subtype'] at hx'
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx'
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hs
  obtain ⟨q, hq0, ⟨c, hc, hqc⟩, -⟩ := exists_separating (T := T) χ₀ (s.image fun χ => χ.1)
    (fun h => by
      obtain ⟨χ, -, hχ⟩ := Finset.mem_image.mp h
      exact χ.2 hχ)
  have h1 : q x = 0 := by
    rw [← hμ, map_sum]
    refine Finset.sum_eq_zero fun χ hχ => hq0 χ.1 (Finset.mem_image_of_mem _ hχ) _ ?_
    exact (μ χ).2
  rw [hqc x hx] at h1
  exact (smul_eq_zero.mp h1).resolve_left hc

private theorem exists_sum_eq_of_mem (V : Submodule k E) (hV : ∀ i, ∀ v ∈ V, T i v ∈ V)
    (s : Finset (ι → k)) {v : E} (hv : v ∈ V) (hvs : v ∈ ⨆ χ ∈ s, piece T χ) :
    ∃ p : (ι → k) → E, (∀ χ ∈ s, p χ ∈ V ∧ p χ ∈ piece T χ) ∧ (∑ χ ∈ s, p χ) = v := by
  classical
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hvs
  refine ⟨fun χ => (μ χ : E), fun χ₀ hχ₀ => ⟨?_, (μ χ₀).2⟩, hμ⟩
  obtain ⟨q, hq0, ⟨c, hc, hqc⟩, hqV⟩ :=
    exists_separating (T := T) χ₀ (s.erase χ₀) (s.notMem_erase χ₀)
  have h1 : q v = c • (μ χ₀ : E) := by
    rw [← hμ, map_sum, ← Finset.add_sum_erase s _ hχ₀, hqc _ (μ χ₀).2, Finset.sum_eq_zero,
      add_zero]
    intro χ hχ
    exact hq0 χ hχ _ (μ χ).2
  have h2 : (μ χ₀ : E) = c⁻¹ • q v := by rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  show (μ χ₀ : E) ∈ V
  rw [h2]
  exact V.smul_mem _ (hqV V hV v hv)

private theorem mem_biSup_of_mem_piece {β : Type*} (Q : β → Submodule k E) (d : β → ι → k)
    (hQ : ∀ b, Q b ≤ piece T (d b)) (F : Finset β) {χ₀ : ι → k} {x : E} (hx : x ∈ piece T χ₀)
    (hxF : x ∈ ⨆ b ∈ F, Q b) : x ∈ ⨆ (b) (_ : b ∈ F) (_ : d b = χ₀), Q b := by
  classical
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hxF
  obtain ⟨q, hq0, ⟨c, hc, hqc⟩, -⟩ :=
    exists_separating (T := T) χ₀ ((F.image d).erase χ₀) (Finset.notMem_erase χ₀ _)
  have hsplit : q x = c • ∑ b ∈ F.filter (fun b => d b = χ₀), (μ b : E) := by
    rw [← hμ, map_sum, Finset.smul_sum,
      ← Finset.sum_filter_add_sum_filter_not F (fun b => d b = χ₀),
      Finset.sum_eq_zero (s := F.filter fun b => ¬d b = χ₀) ?_, add_zero]
    · refine Finset.sum_congr rfl fun b hb => hqc _ ?_
      exact (Finset.mem_filter.mp hb).2 ▸ hQ b (μ b).2
    · intro b hb
      obtain ⟨hbF, hbd⟩ := Finset.mem_filter.mp hb
      exact hq0 (d b) (Finset.mem_erase.mpr ⟨hbd, Finset.mem_image_of_mem d hbF⟩) _ (hQ b (μ b).2)
  have hx' : x = ∑ b ∈ F.filter (fun b => d b = χ₀), (μ b : E) :=
    smul_right_injective E hc ((hqc x hx).symm.trans hsplit)
  rw [hx']
  refine Submodule.sum_mem _ fun b hb => ?_
  obtain ⟨hbF, hbd⟩ := Finset.mem_filter.mp hb
  exact Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hbF
    (Submodule.mem_iSup_of_mem hbd (μ b).2))

private theorem eq_zero_of_smul_eq_smul {x : E} {a b : k} (h : a • x = b • x) (hab : a ≠ b) :
    x = 0 := by
  rw [← sub_eq_zero, ← sub_smul] at h
  exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hab)

private theorem finite_ne_bot {β : Type*} (V : Submodule k E) [FiniteDimensional k V]
    (Q : β → Submodule k E) (hQ : iSupIndep Q) (hQV : ∀ b, Q b ≤ V) :
    {b | Q b ≠ ⊥}.Finite := by
  have hx : ∀ b : {b // Q b ≠ ⊥}, ∃ x ∈ Q b.1, x ≠ 0 := fun b => (Submodule.ne_bot_iff _).mp b.2
  choose x hxQ hx0 using hx
  have hli : LinearIndependent k x :=
    (hQ.comp Subtype.val_injective).linearIndependent _ hxQ hx0
  let y : {b // Q b ≠ ⊥} → V := fun b => ⟨x b, hQV _ (hxQ b)⟩
  have hy : LinearIndependent k y := LinearIndependent.of_comp V.subtype hli
  have hfin : Finite {b // Q b ≠ ⊥} := hy.finite_of_isNoetherian
  exact @Set.toFinite β {b | Q b ≠ ⊥} hfin

end Pieces

end Module.End.EigenData
namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

open IsDedekindDomain
open scoped Pointwise

section LevelPart

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

open scoped Classical in

private noncomputable def primeExponent (w : HeightOneSpectrum R) (N : Ideal R) : ℕ :=
  (Associates.mk w.asIdeal).count (Associates.mk N).factors

private noncomputable def supportedPart (N : Ideal R) (S : Finset (HeightOneSpectrum R)) : Ideal R :=
  ∏ w ∈ S, w.asIdeal ^ primeExponent w N

private theorem pow_dvd_iff_le_primeExponent {w : HeightOneSpectrum R} {N : Ideal R} (hN : N ≠ ⊥) (k : ℕ) :
    w.asIdeal ^ k ∣ N ↔ k ≤ primeExponent w N := by
  classical
  rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow, primeExponent]
  exact Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 (show N ≠ 0 from hN))
    (Associates.irreducible_mk.2 w.irreducible)

private theorem pow_primeExponent_dvd {w : HeightOneSpectrum R} {N : Ideal R} (hN : N ≠ ⊥) :
    w.asIdeal ^ primeExponent w N ∣ N :=
  (pow_dvd_iff_le_primeExponent hN _).2 le_rfl

private theorem isMaximal_asIdeal (w : HeightOneSpectrum R) : w.asIdeal.IsMaximal :=
  Ideal.IsPrime.isMaximal w.isPrime w.ne_bot

private theorem isCoprime_pow_pow {w w' : HeightOneSpectrum R} (h : w ≠ w') (m n : ℕ) :
    IsCoprime (w.asIdeal ^ m) (w'.asIdeal ^ n) :=
  (Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne (isMaximal_asIdeal w) (isMaximal_asIdeal w')
    (fun hEq => h (HeightOneSpectrum.ext hEq)))).pow

private theorem supportedPart_dvd {N : Ideal R} (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum R)) :
    supportedPart N S ∣ N :=
  Finset.prod_dvd_of_coprime
    (fun w _ w' _ h => show IsCoprime (w.asIdeal ^ primeExponent w N) (w'.asIdeal ^ primeExponent w' N) from
      isCoprime_pow_pow h _ _)
    (fun _ _ => pow_primeExponent_dvd hN)

private theorem supportedPart_ne_bot {N : Ideal R} (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum R)) :
    supportedPart N S ≠ ⊥ := by
  intro h
  have hdvd := supportedPart_dvd hN S
  rw [h] at hdvd
  exact hN (le_bot_iff.1 (Ideal.dvd_iff_le.1 hdvd))

private theorem pow_primeExponent_dvd_supportedPart {N : Ideal R} {S : Finset (HeightOneSpectrum R)}
    {w : HeightOneSpectrum R} (hw : w ∈ S) : w.asIdeal ^ primeExponent w N ∣ supportedPart N S :=
  Finset.dvd_prod_of_mem (fun w => w.asIdeal ^ primeExponent w N) hw

private theorem mem_of_dvd_supportedPart {N : Ideal R} {S : Finset (HeightOneSpectrum R)}
    {w : HeightOneSpectrum R} (h : w.asIdeal ∣ supportedPart N S) : w ∈ S := by
  obtain ⟨w', hw'S, hdvd⟩ := w.prime.exists_mem_finset_dvd h
  have h1 : w'.asIdeal ≤ w.asIdeal := Ideal.dvd_iff_le.1 (w.prime.dvd_of_dvd_pow hdvd)
  have h2 : w'.asIdeal = w.asIdeal := (isMaximal_asIdeal w').eq_of_le w.isPrime.ne_top h1
  have h3 : w' = w := HeightOneSpectrum.ext h2
  rw [← h3]
  exact hw'S

private theorem primeExponent_supportedPart {N : Ideal R} (hN : N ≠ ⊥) {S : Finset (HeightOneSpectrum R)}
    {w : HeightOneSpectrum R} (hw : w ∈ S) : primeExponent w (supportedPart N S) = primeExponent w N := by
  classical
  apply le_antisymm
  · unfold primeExponent
    exact Associates.count_le_count_of_le (Associates.mk_ne_zero.2 (show N ≠ 0 from hN))
      (Associates.irreducible_mk.2 w.irreducible) (Associates.mk_le_mk_iff_dvd.2 (supportedPart_dvd hN S))
  · exact (pow_dvd_iff_le_primeExponent (supportedPart_ne_bot hN S) _).1 (pow_primeExponent_dvd_supportedPart hw)

private theorem not_dvd_supportedPart_of_not_mem {N : Ideal R} {S : Finset (HeightOneSpectrum R)}
    {w : HeightOneSpectrum R} (hw : w ∉ S) : ¬ w.asIdeal ∣ supportedPart N S :=
  fun h => hw (mem_of_dvd_supportedPart h)

end LevelPart

section PrimeDegree

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

private theorem finiteDimensional_of_finrank_prime (hdeg : (Module.finrank K L).Prime) :
    FiniteDimensional K L :=
  Module.finite_of_finrank_pos hdeg.pos

private theorem natCard_aut_dvd_finrank [FiniteDimensional K L] :
    Nat.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
  refine ⟨Module.finrank K (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))), ?_⟩
  rw [mul_comm, ← Subgroup.card_top (G := L ≃ₐ[K] L),
    ← IntermediateField.finrank_fixedField_eq_card (⊤ : Subgroup (L ≃ₐ[K] L))]
  exact (Module.finrank_mul_finrank K (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L).symm

private theorem natCard_aut_eq_finrank_of_ne_one (hdeg : (Module.finrank K L).Prime) {σ : L ≃ₐ[K] L}
    (hσ : σ ≠ 1) : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
  haveI := finiteDimensional_of_finrank_prime hdeg
  rcases (Nat.dvd_prime hdeg).1 natCard_aut_dvd_finrank with h1 | h
  · exfalso
    haveI : Subsingleton (L ≃ₐ[K] L) := (Nat.card_eq_one_iff_unique.1 h1).1
    exact hσ (Subsingleton.elim _ _)
  · exact h

private theorem isGalois_of_finrank_prime_of_ne_one (hdeg : (Module.finrank K L).Prime) {σ : L ≃ₐ[K] L}
    (hσ : σ ≠ 1) : IsGalois K L := by
  haveI := finiteDimensional_of_finrank_prime hdeg
  exact IsGalois.of_card_aut_eq_finrank K L (natCard_aut_eq_finrank_of_ne_one hdeg hσ)

private theorem exists_pow_eq_of_finrank_prime (hdeg : (Module.finrank K L).Prime) {σ : L ≃ₐ[K] L}
    (hσ : σ ≠ 1) (τ : L ≃ₐ[K] L) : ∃ n : ℕ, σ ^ n = τ := by
  haveI := finiteDimensional_of_finrank_prime hdeg
  haveI : Fact (Module.finrank K L).Prime := ⟨hdeg⟩
  have htop : Subgroup.zpowers σ = ⊤ :=
    zpowers_eq_top_of_prime_card (natCard_aut_eq_finrank_of_ne_one hdeg hσ) hσ
  have hτ : τ ∈ Subgroup.zpowers σ := htop ▸ Subgroup.mem_top τ
  rw [← (isOfFinOrder_of_finite σ).mem_powers_iff_mem_zpowers] at hτ
  exact (Submonoid.mem_powers_iff τ σ).1 hτ

variable [NumberField K] [NumberField L]

private theorem isGaloisGroup_ringOfIntegers (hdeg : (Module.finrank K L).Prime) {σ : L ≃ₐ[K] L}
    (hσ : σ ≠ 1) : IsGaloisGroup (L ≃ₐ[K] L) (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) := by
  haveI := isGalois_of_finrank_prime_of_ne_one hdeg hσ
  exact IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) K L

private theorem exists_smul_asIdeal_eq (hdeg : (Module.finrank K L).Prime) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (w w' : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : w.under (NumberField.RingOfIntegers K) = w'.under (NumberField.RingOfIntegers K)) :
    ∃ τ : L ≃ₐ[K] L, τ • w.asIdeal = w'.asIdeal := by
  haveI := finiteDimensional_of_finrank_prime hdeg
  haveI := isGaloisGroup_ringOfIntegers hdeg hσ
  haveI := w.isPrime
  haveI := w'.isPrime
  have hu : w.asIdeal.under (NumberField.RingOfIntegers K) = w'.asIdeal.under (NumberField.RingOfIntegers K) := by
    have := congrArg HeightOneSpectrum.asIdeal h
    simpa using this
  haveI : w.asIdeal.LiesOver (w.asIdeal.under (NumberField.RingOfIntegers K)) := ⟨rfl⟩
  haveI : w'.asIdeal.LiesOver (w.asIdeal.under (NumberField.RingOfIntegers K)) := ⟨hu⟩
  exact Ideal.exists_smul_eq_of_isGaloisGroup (w.asIdeal.under (NumberField.RingOfIntegers K)) w.asIdeal w'.asIdeal
    (L ≃ₐ[K] L)

private theorem exists_pow_smul_asIdeal_eq (hdeg : (Module.finrank K L).Prime) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (w w' : HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : w.under (NumberField.RingOfIntegers K) = w'.under (NumberField.RingOfIntegers K)) :
    ∃ n : ℕ, (σ ^ n) • w.asIdeal = w'.asIdeal := by
  obtain ⟨τ, hτ⟩ := exists_smul_asIdeal_eq hdeg hσ w w' h
  obtain ⟨n, rfl⟩ := exists_pow_eq_of_finrank_prime hdeg hσ τ
  exact ⟨n, hτ⟩

end PrimeDegree

section RefinedGlue

open NumberField NumberField.AdelicLevel
open scoped NumberField.PlaceTransport

section Bounds

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

private theorem idealBound_supportedPart_of_mem {N : Ideal R} (hN : N ≠ ⊥) {S : Finset (HeightOneSpectrum R)}
    {w : HeightOneSpectrum R} (hw : w ∈ S) : idealBound R (supportedPart N S) w = idealBound R N w := by
  have h := primeExponent_supportedPart hN hw
  unfold primeExponent at h
  rw [idealBound_of_ne_bot (supportedPart_ne_bot hN S), idealBound_of_ne_bot hN, h]

private theorem idealBound_supportedPart_of_not_mem {N : Ideal R} (hN : N ≠ ⊥) {S : Finset (HeightOneSpectrum R)}
    {w : HeightOneSpectrum R} (hw : w ∉ S) : idealBound R (supportedPart N S) w = 1 :=
  idealBound_eq_one_of_not_dvd (supportedPart_ne_bot hN S) (not_dvd_supportedPart_of_not_mem hw)

private theorem ne_bot_of_dvd {M N : Ideal R} (hN : N ≠ ⊥) (hMN : M ∣ N) : M ≠ ⊥ := by
  rintro rfl
  exact hN (le_bot_iff.1 (Ideal.dvd_iff_le.1 hMN))

private theorem idealBound_le_idealBound_of_dvd {M N : Ideal R} (hN : N ≠ ⊥) (hMN : M ∣ N) (v : HeightOneSpectrum R) :
    idealBound R N v ≤ idealBound R M v := by
  classical
  rw [idealBound_of_ne_bot hN, idealBound_of_ne_bot (ne_bot_of_dvd hN hMN), WithZero.exp_le_exp]
  have h : (Associates.mk v.asIdeal).count (Associates.mk M).factors
      ≤ (Associates.mk v.asIdeal).count (Associates.mk N).factors :=
    Associates.count_le_count_of_le (Associates.mk_ne_zero.2 (show N ≠ 0 from hN))
      (Associates.irreducible_mk.2 v.irreducible) (Associates.mk_le_mk_iff_dvd.2 hMN)
  omega

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

private theorem idealBall_subset_idealBall_of_dvd {M N : Ideal R} (hN : N ≠ ⊥) (hMN : M ∣ N) :
    idealBall R K N ⊆ idealBall R K M :=
  fun _ hx v => (hx v).trans (idealBound_le_idealBound_of_dvd hN hMN v)

private theorem isLevelOneMatrix_of_dvd {M N : Ideal R} (hN : N ≠ ⊥) (hMN : M ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing R K)} (hm : IsLevelOneMatrix R K N m) : IsLevelOneMatrix R K M m :=
  ⟨⟨hm.integral, idealBall_subset_idealBall_of_dvd K hN hMN hm.lowerLeft⟩,
    idealBall_subset_idealBall_of_dvd K hN hMN hm.lowerRight⟩

private theorem finiteLevelOne_le_finiteLevelOne_of_dvd {M N : Ideal R} (hN : N ≠ ⊥) (hMN : M ∣ N) :
    finiteLevelOne R K N ≤ finiteLevelOne R K M :=
  fun _ hg => ⟨isLevelOneMatrix_of_dvd K hN hMN hg.1, isLevelOneMatrix_of_dvd K hN hMN hg.2⟩

private theorem levelOne_le_levelOne_of_dvd {M N : Ideal R} (hN : N ≠ ⊥) (hMN : M ∣ N) :
    levelOne R K N ≤ levelOne R K M := by
  unfold levelOne
  exact Subgroup.comap_mono (finiteLevelOne_le_finiteLevelOne_of_dvd K hN hMN)

end Bounds

section RefinedPrimes

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

open scoped Classical in

private noncomputable def primesOverFinset (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (SL : Finset (HeightOneSpectrum (𝓞 L))) : Finset (HeightOneSpectrum (𝓞 L)) :=
  SL.filter fun w => w.under (𝓞 K) ∈ SK

omit [NumberField K] [NumberField L] in
private theorem mem_primesOverFinset_iff {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {SL : Finset (HeightOneSpectrum (𝓞 L))} (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ SK → w ∈ SL)
    (w : HeightOneSpectrum (𝓞 L)) :
    w ∈ primesOverFinset SK SL ↔ w.under (𝓞 K) ∈ SK := by
  classical
  unfold primesOverFinset
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hSL w h, h⟩⟩

omit [NumberField K] [NumberField L] in
private theorem primesOverFinset_subset (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (SL : Finset (HeightOneSpectrum (𝓞 L))) :
    primesOverFinset SK SL ⊆ SL := by
  classical
  unfold primesOverFinset
  exact Finset.filter_subset _ _

omit [NumberField K] [NumberField L] in
private theorem toRingEquiv_algebraMap (σ : L ≃ₐ[K] L) (k : 𝓞 K) :
    (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) (algebraMap (𝓞 K) (𝓞 L) k)
      = algebraMap (𝓞 K) (𝓞 L) k :=
  RingOfIntegers.ext (σ.commutes (k : K))

private theorem comap_comap_eq_of_fix {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (e : B →+* B)
    (he : ∀ a : A, e (algebraMap A B a) = algebraMap A B a) (P : Ideal B) :
    Ideal.comap (algebraMap A B) (Ideal.comap e P) = Ideal.comap (algebraMap A B) P := by
  rw [Ideal.comap_comap]
  congr 1
  exact RingHom.ext he

private def algEquivOfRingEquiv {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (e : B ≃+* B)
    (he : ∀ a : A, e (algebraMap A B a) = algebraMap A B a) : B ≃ₐ[A] B :=
  AlgEquiv.ofRingEquiv (f := e) he

private theorem inertiaDeg_map_of_fix {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (e : B ≃+* B)
    (he : ∀ a : A, e (algebraMap A B a) = algebraMap A B a) (p : Ideal A) (P : Ideal B) :
    p.inertiaDeg' (Ideal.map (e : B →+* B) P) = p.inertiaDeg' P :=
  Ideal.inertiaDeg_map_eq p P (algEquivOfRingEquiv e he)

private theorem absNorm_map_ringEquiv {B : Type*} [CommRing B] [Nontrivial B] [IsDedekindDomain B] [Module.Free ℤ B]
    (e : B ≃+* B) (I : Ideal B) : Ideal.absNorm (Ideal.map (e : B →+* B) I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (Ideal.map (e : B →+* B) I) e rfl).toEquiv).symm

omit [NumberField K] [NumberField L] in

private theorem under_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).under (𝓞 K) = w.under (𝓞 K) := by
  refine HeightOneSpectrum.ext ?_
  show Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) (σ • w).asIdeal = Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal
  rw [NumberField.PlaceTransport.smul_asIdeal]
  exact comap_comap_eq_of_fix _ (toRingEquiv_algebraMap σ⁻¹) _

omit [NumberField K] [NumberField L] in
private theorem inertiaDeg_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    ((σ • w).under (𝓞 K)).asIdeal.inertiaDeg' (σ • w).asIdeal = (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal := by
  rw [under_smul, NumberField.PlaceTransport.smul_asIdeal_eq_map]
  exact inertiaDeg_map_of_fix _ (toRingEquiv_algebraMap σ) _ _

omit [NumberField K] in
private theorem absNorm_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (σ • w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map]
  exact absNorm_map_ringEquiv _ _

omit [NumberField K] [NumberField L] in

private theorem asIdeal_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : (σ • w).asIdeal = σ • w.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, Ideal.pointwise_smul_def]
  exact congrArg (fun f : 𝓞 L →+* 𝓞 L => Ideal.map f w.asIdeal) (RingHom.ext fun _ => rfl)

omit [NumberField K] [NumberField L] in
private theorem smul_mem_primesOverFinset_iff {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {SL : Finset (HeightOneSpectrum (𝓞 L))} (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ SK → w ∈ SL)
    (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) : σ • w ∈ primesOverFinset SK SL ↔ w ∈ primesOverFinset SK SL := by
  rw [mem_primesOverFinset_iff hSL, mem_primesOverFinset_iff hSL, under_smul]

private theorem exists_pow_smul_eq (hdeg : (Module.finrank K L).Prime) {σ : L ≃ₐ[K] L} (hσ : σ ≠ 1)
    (w w' : HeightOneSpectrum (𝓞 L)) (h : w.under (𝓞 K) = w'.under (𝓞 K)) : ∃ n : ℕ, (σ ^ n) • w = w' := by
  obtain ⟨n, hn⟩ := exists_pow_smul_asIdeal_eq hdeg hσ w w' h
  exact ⟨n, HeightOneSpectrum.ext (by rw [asIdeal_smul, hn])⟩

private theorem eq_of_under_eq_of_forall_smul_eq {X : Type*} (hdeg : (Module.finrank K L).Prime) {σ : L ≃ₐ[K] L}
    (hσ : σ ≠ 1) {S : Finset (HeightOneSpectrum (𝓞 L))} (hS : ∀ w : HeightOneSpectrum (𝓞 L), σ • w ∈ S ↔ w ∈ S)
    {d : HeightOneSpectrum (𝓞 L) → X} (hd : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → d (σ • w) = d w)
    {w w' : HeightOneSpectrum (𝓞 L)} (hw : w ∉ S) (h : w.under (𝓞 K) = w'.under (𝓞 K)) : d w = d w' := by
  obtain ⟨n, rfl⟩ := exists_pow_smul_eq hdeg hσ w w' h
  have key : ∀ m : ℕ, (σ ^ m) • w ∉ S ∧ d ((σ ^ m) • w) = d w := by
    intro m
    induction m with
    | zero => exact ⟨by simpa using hw, by simp⟩
    | succ m ih =>
      rw [pow_succ', mul_smul]
      exact ⟨fun hmem => ih.1 ((hS _).1 hmem), (hd _ ih.1).trans ih.2⟩
  exact ((key n).2).symm

end RefinedPrimes

end RefinedGlue

end AutomorphicForm.TwistedTraceRefinement
namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

noncomputable section

open NumberField NumberField.AdelicLevel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.AutomorphicForm AdelicDock IsDedekindDomain UnramifiedWhittaker"
open scoped TensorProduct TensorProduct.RightActions

section OnePlace

variable {L : Type} [Field L] [NumberField L]

private def placeAt (w : HeightOneSpectrum (𝓞 L)) : GL (Fin 2) (w.adicCompletion L) →* AdelicGL2 (𝓞 L) L :=
  (finEmbed (𝓞 L) L).comp (localEmbed (𝓞 L) L w)

variable (w : HeightOneSpectrum (𝓞 L))

private theorem glArch_placeAt (m : GL (Fin 2) (w.adicCompletion L)) : glArch (𝓞 L) L (placeAt w m) = 1 :=
  glArch_finEmbed (𝓞 L) L _

private theorem finComponent_glFin_placeAt_self (m : GL (Fin 2) (w.adicCompletion L)) :
    finComponent (𝓞 L) L w (glFin (𝓞 L) L (placeAt w m)) = m := by
  show finComponent (𝓞 L) L w (glFin (𝓞 L) L (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m))) = m
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem finComponent_glFin_placeAt_of_ne (m : GL (Fin 2) (w.adicCompletion L)) {w' : HeightOneSpectrum (𝓞 L)}
    (h : w' ≠ w) : finComponent (𝓞 L) L w' (glFin (𝓞 L) L (placeAt w m)) = 1 := by
  show finComponent (𝓞 L) L w' (glFin (𝓞 L) L (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 L) L w m h]

variable {w}

private theorem adelicGL2_ext {a b : AdelicGL2 (𝓞 L) L} (h₁ : glArch (𝓞 L) L a = glArch (𝓞 L) L b)
    (h₂ : ∀ w' : HeightOneSpectrum (𝓞 L),
      finComponent (𝓞 L) L w' (glFin (𝓞 L) L a) = finComponent (𝓞 L) L w' (glFin (𝓞 L) L b)) : a = b := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  refine Prod.ext ?_ ?_
  · have h := congrArg
      (fun g : GL (Fin 2) (InfiniteAdeleRing L) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j) h₁
    simpa only [glArch_apply] using h
  · refine FiniteAdeleRing.ext L fun w' => ?_
    have h := congrArg
      (fun g : GL (Fin 2) (w'.adicCompletion L) => (g : Matrix (Fin 2) (Fin 2) (w'.adicCompletion L)) i j) (h₂ w')
    simpa only [finComponent_apply, glFin_apply] using h

private theorem placeAt_mul_eq_mul_placeAt (m : GL (Fin 2) (w.adicCompletion L)) {y : AdelicGL2 (𝓞 L) L}
    (hy : finComponent (𝓞 L) L w (glFin (𝓞 L) L y) = 1) : placeAt w m * y = y * placeAt w m := by
  refine adelicGL2_ext ?_ fun w' => ?_
  · simp only [map_mul, glArch_placeAt, one_mul, mul_one]
  · simp only [map_mul]
    by_cases h : w' = w
    · subst h
      rw [finComponent_glFin_placeAt_self, hy, mul_one, one_mul]
    · rw [finComponent_glFin_placeAt_of_ne w m h, one_mul, mul_one]

private theorem finComponent_glFin_mul_inv_placeAt (x : AdelicGL2 (𝓞 L) L) :
    finComponent (𝓞 L) L w (glFin (𝓞 L) L (x * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)))⁻¹)) = 1 := by
  simp only [map_mul, map_inv, finComponent_glFin_placeAt_self, mul_inv_cancel]

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 L)} (hb : idealBound (𝓞 L) N w = 1)
    (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) (hM : ∀ i j, M i j ∈ w.adicCompletionIntegers L) :
    IsLocalLevelOne (𝓞 L) L w N M :=
  ⟨hM, by rw [hb]; exact hM 1 0, by rw [hb]; exact sub_mem (hM 1 1) (one_mem _)⟩

private theorem placeAt_mem_of_integral {N : Ideal (𝓞 L)} (hb : idealBound (𝓞 L) N w = 1)
    (m : GL (Fin 2) (w.adicCompletion L))
    (hm : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L)
    (hm' : ∀ i j, ((m⁻¹ : GL (Fin 2) (w.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L) :
    placeAt w m ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m) ∈ levelOne (𝓞 L) L N
    rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    exact ⟨isLocalLevelOne_of_integral hb _ hm, isLocalLevelOne_of_integral hb _ hm'⟩
  · show glArch (𝓞 L) L (placeAt w m) = 1
    exact glArch_placeAt w m

private theorem finComponent_integral_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) (i j : Fin 2) :
    (finComponent (𝓞 L) L w (glFin (𝓞 L) L k) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L := by
  rw [finComponent_apply]
  have h : (glFin (𝓞 L) L k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j ∈
      AdelicLevel.integralFiniteAdeles (𝓞 L) L :=
    (mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp hk)).1.integral i j
  exact h w

private theorem finComponent_inv_integral_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) (i j : Fin 2) :
    (((finComponent (𝓞 L) L w (glFin (𝓞 L) L k))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L := by
  rw [← map_inv, ← map_inv]
  exact finComponent_integral_of_mem_levelOne (inv_mem hk) i j

end OnePlace

section Dictionary

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

private theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v (semiLocalEval K L v a) w = AdelicLevel.finAdeleEval (𝓞 L) L w.1 a := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w' : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w'.1 a)) w =
    AdelicLevel.finAdeleEval (𝓞 L) L w.1 a
  rw [AlgEquiv.apply_symm_apply]

private theorem forall_of_mem_semiLocalIntegers (t : L ⊗[K] v.adicCompletion K) (ht : t ∈ semiLocalIntegers K L v)
    (w : v.Extension (𝓞 L)) : semiLocalHomeomorph K L v t w ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi] at ht
  exact ht w

end Dictionary

section SemiLocalGlue

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem mem_semiLocalIntegers_of_forall (v : HeightOneSpectrum (𝓞 K)) (t : L ⊗[K] v.adicCompletion K)
    (ht : ∀ w : v.Extension (𝓞 L), semiLocalHomeomorph K L v t w ∈ w.1.adicCompletionIntegers L) :
    t ∈ semiLocalIntegers K L v := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
  exact ht

private theorem semiLocalEval_eq_of_forall (v : HeightOneSpectrum (𝓞 K)) {a b : FiniteAdeleRing (𝓞 L) L}
    (h : ∀ w : v.Extension (𝓞 L), a w.1 = b w.1) : semiLocalEval K L v a = semiLocalEval K L v b := by
  apply (semiLocalHomeomorph K L v).injective
  funext w
  rw [semiLocalHomeomorph_semiLocalEval, semiLocalHomeomorph_semiLocalEval, finAdeleEval_apply, finAdeleEval_apply]
  exact h w

private theorem semiLocalEval_mem_of_forall (v : HeightOneSpectrum (𝓞 K)) {a : FiniteAdeleRing (𝓞 L) L}
    (h : ∀ w : v.Extension (𝓞 L), a w.1 ∈ w.1.adicCompletionIntegers L) :
    semiLocalEval K L v a ∈ semiLocalIntegers K L v := by
  refine mem_semiLocalIntegers_of_forall v _ fun w => ?_
  rw [semiLocalHomeomorph_semiLocalEval, finAdeleEval_apply]
  exact h w

private theorem semiLocalComponent_coe_apply (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))
    (i j : Fin 2) :
    (semiLocalComponent K L v x : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j
      = semiLocalEval K L v ((x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) :=
  rfl

private theorem semiLocalComponent_eq_of_forall (v : HeightOneSpectrum (𝓞 K))
    {x y : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (h : ∀ w : v.Extension (𝓞 L), finComponent (𝓞 L) L w.1 x = finComponent (𝓞 L) L w.1 y) :
    semiLocalComponent K L v x = semiLocalComponent K L v y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [semiLocalComponent_coe_apply, semiLocalComponent_coe_apply]
  refine semiLocalEval_eq_of_forall v fun w => ?_
  have hw := congrArg
    (fun g : GL (Fin 2) (w.1.adicCompletion L) => (g : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j) (h w)
  simpa only [finComponent_apply] using hw

private theorem semiLocalComponent_mem_of_forall (v : HeightOneSpectrum (𝓞 K))
    {x : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hx : ∀ w : v.Extension (𝓞 L), ∀ i j,
      (finComponent (𝓞 L) L w.1 x : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j ∈ w.1.adicCompletionIntegers L)
    (hx' : ∀ w : v.Extension (𝓞 L), ∀ i j,
      (finComponent (𝓞 L) L w.1 x⁻¹ : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) i j
        ∈ w.1.adicCompletionIntegers L) :
    semiLocalComponent K L v x ∈ semiLocalIntegralSet K L v := by
  unfold semiLocalIntegralSet
  refine mem_integralUnitsSet.mpr ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [semiLocalComponent_coe_apply]
    exact semiLocalEval_mem_of_forall v fun w => by simpa only [finComponent_apply] using hx w i j
  · rw [← map_inv (semiLocalComponent K L v) x, semiLocalComponent_coe_apply]
    exact semiLocalEval_mem_of_forall v fun w => by simpa only [finComponent_apply] using hx' w i j

omit [NumberField L] in
private theorem add_mem_semiLocalIntegers (v : HeightOneSpectrum (𝓞 K)) {s t : L ⊗[K] v.adicCompletion K}
    (hs : s ∈ semiLocalIntegers K L v) (ht : t ∈ semiLocalIntegers K L v) : s + t ∈ semiLocalIntegers K L v := by
  obtain ⟨s', rfl⟩ := hs
  obtain ⟨t', rfl⟩ := ht
  exact ⟨s' + t', map_add _ _ _⟩

omit [NumberField L] in
private theorem mul_mem_semiLocalIntegers (v : HeightOneSpectrum (𝓞 K)) {s t : L ⊗[K] v.adicCompletion K}
    (hs : s ∈ semiLocalIntegers K L v) (ht : t ∈ semiLocalIntegers K L v) : s * t ∈ semiLocalIntegers K L v := by
  obtain ⟨s', rfl⟩ := hs
  obtain ⟨t', rfl⟩ := ht
  exact ⟨s' * t', map_mul _ _ _⟩

omit [NumberField L] in
private theorem coe_mul_mem_of_mem (v : HeightOneSpectrum (𝓞 K)) {a b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (ha : ∀ i j, (a : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈ semiLocalIntegers K L v)
    (hb : ∀ i j, (b : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j ∈ semiLocalIntegers K L v)
    (i j : Fin 2) :
    ((a * b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j
      ∈ semiLocalIntegers K L v := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem_semiLocalIntegers v (mul_mem_semiLocalIntegers v (ha i 0) (hb 0 j))
    (mul_mem_semiLocalIntegers v (ha i 1) (hb 1 j))

omit [NumberField L] in

private theorem mul_mem_semiLocalIntegralSet (v : HeightOneSpectrum (𝓞 K))
    {a b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)} (ha : a ∈ semiLocalIntegralSet K L v)
    (hb : b ∈ semiLocalIntegralSet K L v) : a * b ∈ semiLocalIntegralSet K L v := by
  unfold semiLocalIntegralSet at ha hb ⊢
  obtain ⟨ha₁, ha₂⟩ := mem_integralUnitsSet.mp ha
  obtain ⟨hb₁, hb₂⟩ := mem_integralUnitsSet.mp hb
  refine mem_integralUnitsSet.mpr ⟨coe_mul_mem_of_mem v ha₁ hb₁, ?_⟩
  rw [mul_inv_rev]
  exact coe_mul_mem_of_mem v hb₂ ha₂

end SemiLocalGlue

section LevelTransfer

variable {L : Type} [Field L] [NumberField L]

private theorem isLocalLevelOne_finComponent_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) (w : HeightOneSpectrum (𝓞 L)) :
    IsLocalLevelOne (𝓞 L) L w N (finComponent (𝓞 L) L w (glFin (𝓞 L) L k)) := by
  have h := (mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp hk)).1
  refine ⟨finComponent_integral_of_mem_levelOne hk, ?_, ?_⟩
  · rw [finComponent_apply]
    exact h.lowerLeft w
  · have h1 := h.lowerRight w
    rw [coe_sub_apply, coe_one_apply] at h1
    rw [finComponent_apply]
    exact h1

private theorem isLocalLevelOne_of_idealBound_eq {N N₀ : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N₀ w = idealBound (𝓞 L) N w) {m : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)}
    (hm : IsLocalLevelOne (𝓞 L) L w N₀ m) : IsLocalLevelOne (𝓞 L) L w N m :=
  ⟨hm.integral, by rw [← hb]; exact hm.lowerLeft, by rw [← hb]; exact hm.lowerRight⟩

private theorem placeAt_finComponent_mem {N N₀ : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N₀ w = idealBound (𝓞 L) N w) {u : AdelicGL2 (𝓞 L) L} (hu : u ∈ levelOne (𝓞 L) L N₀) :
    placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u)) ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w _) ∈ levelOne (𝓞 L) L N
    rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    refine ⟨isLocalLevelOne_of_idealBound_eq hb (isLocalLevelOne_finComponent_of_mem_levelOne hu w), ?_⟩
    rw [← map_inv, ← map_inv]
    exact isLocalLevelOne_of_idealBound_eq hb (isLocalLevelOne_finComponent_of_mem_levelOne (inv_mem hu) w)
  · show glArch (𝓞 L) L (placeAt w _) = 1
    exact glArch_placeAt w _

private theorem finComponent_inv_placeAt_mul_self (w : HeightOneSpectrum (𝓞 L)) (u : AdelicGL2 (𝓞 L) L) :
    finComponent (𝓞 L) L w (glFin (𝓞 L) L ((placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u)))⁻¹ * u)) = 1 := by
  simp only [map_mul, map_inv, finComponent_glFin_placeAt_self, inv_mul_cancel]

private theorem finComponent_inv_placeAt_mul_of_ne (w : HeightOneSpectrum (𝓞 L)) (u : AdelicGL2 (𝓞 L) L)
    {w' : HeightOneSpectrum (𝓞 L)} (h : w' ≠ w) :
    finComponent (𝓞 L) L w' (glFin (𝓞 L) L ((placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u)))⁻¹ * u))
      = finComponent (𝓞 L) L w' (glFin (𝓞 L) L u) := by
  rw [map_mul, map_mul, map_inv, map_inv, finComponent_glFin_placeAt_of_ne w _ h, inv_one, one_mul]

private theorem placeEmbed_map_mem_of_idealBound_eq_one {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N w = 1) (kv : GL (Fin 2) (w.adicCompletionIntegers L)) :
    placeEmbed L w
        (Matrix.GeneralLinearGroup.map (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) kv) ∈
      levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  show placeAt w _ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L
  refine placeAt_mem_of_integral hb _ (fun i j => ?_) (fun i j => ?_)
  · show ((kv i j : w.adicCompletionIntegers L) : w.adicCompletion L) ∈ w.adicCompletionIntegers L
    exact (kv i j).2
  · show ((kv⁻¹ i j : w.adicCompletionIntegers L) : w.adicCompletion L) ∈ w.adicCompletionIntegers L
    exact (kv⁻¹ i j).2

end LevelTransfer

section Discharge

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem finComponent_integral_of_ne_zero {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w.under (𝓞 K) ∉ SK) (x : AdelicGL2 (𝓞 L) L) (hx : φ x ≠ 0) :
      (∀ i j, (finComponent (𝓞 L) L w (glFin (𝓞 L) L x) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
          w.adicCompletionIntegers L) ∧
      (∀ i j, (((finComponent (𝓞 L) L w (glFin (𝓞 L) L x))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L)
    := by
  obtain ⟨φa, φf, φS, -, -, -, -, h₅, h₆⟩ := hφ.1.2
  have hf : φf (glFin (𝓞 L) L x) ≠ 0 := fun h0 => hx (by rw [h₆ x, h0, mul_zero])
  have hmem : semiLocalComponent K L (w.under (𝓞 K)) (glFin (𝓞 L) L x) ∈
      semiLocalIntegralSet K L (w.under (𝓞 K)) := by
    by_contra hc
    exact hf (h₅ _ ⟨w.under (𝓞 K), hw, hc⟩)
  unfold semiLocalIntegralSet at hmem
  obtain ⟨hm, hm'⟩ := mem_integralUnitsSet.mp hmem

  let wE : {w' : HeightOneSpectrum (𝓞 L) // w'.under (𝓞 K) = w.under (𝓞 K)} := ⟨w, rfl⟩
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h : semiLocalHomeomorph K L (w.under (𝓞 K))
        (semiLocalEval K L (w.under (𝓞 K))
          ((glFin (𝓞 L) L x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)) wE ∈
        w.adicCompletionIntegers L :=
      forall_of_mem_semiLocalIntegers K L (w.under (𝓞 K)) _ (hm i j) wE
    rw [semiLocalHomeomorph_semiLocalEval] at h
    exact h
  · have hm'' := hm' i j
    rw [← map_inv (semiLocalComponent K L (w.under (𝓞 K))) (glFin (𝓞 L) L x)] at hm''
    have h : semiLocalHomeomorph K L (w.under (𝓞 K))
        (semiLocalEval K L (w.under (𝓞 K))
          ((((glFin (𝓞 L) L x)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)) wE ∈
        w.adicCompletionIntegers L :=
      forall_of_mem_semiLocalIntegers K L (w.under (𝓞 K)) _ hm'' wE
    rw [semiLocalHomeomorph_semiLocalEval] at h
    rw [← map_inv (finComponent (𝓞 L) L w) (glFin (𝓞 L) L x)]
    exact h

end Discharge

section Conv

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem rightConv_mul_eq_of_tier {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) (u : AdelicGL2 (𝓞 L) L → ℂ)
    (g : AdelicGL2 (𝓞 L) L) {k : AdelicGL2 (𝓞 L) L} (hk : k ∈ U) :
    rightConv L u φ (g * k) = rightConv L u φ g := by
  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply L u φ g k]
  have hφk : (fun y => φ (k⁻¹ * y)) = φ := funext fun y => (hφ.1.1 k⁻¹ (inv_mem hk) y).1
  rw [hφk]

end Conv

section Invariance

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem finFactor_mul_eq {S : Finset (HeightOneSpectrum (𝓞 K))}
    {φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    {φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ}
    (h₄ : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
      (∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) →
        φf h = ∏ v ∈ S, φS v (semiLocalComponent K L v h))
    (h₅ : ∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
      (∃ v ∉ S, semiLocalComponent K L v h ∉ semiLocalIntegralSet K L v) → φf h = 0)
    {c : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)} (hc₁ : ∀ v ∈ S, semiLocalComponent K L v c = 1)
    (hc₂ : ∀ v : HeightOneSpectrum (𝓞 K), semiLocalComponent K L v c ∈ semiLocalIntegralSet K L v)
    (hc₃ : ∀ v : HeightOneSpectrum (𝓞 K), semiLocalComponent K L v c⁻¹ ∈ semiLocalIntegralSet K L v)
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : φf (h * c) = φf h ∧ φf (c * h) = φf h := by
  classical
  have hright : ∀ v : HeightOneSpectrum (𝓞 K),
      semiLocalComponent K L v (h * c) ∈ semiLocalIntegralSet K L v ↔
        semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v := by
    intro v
    constructor
    · intro hm
      have hh : h = h * c * c⁻¹ := (mul_inv_cancel_right h c).symm
      rw [hh, map_mul]
      exact mul_mem_semiLocalIntegralSet v hm (hc₃ v)
    · intro hm
      rw [map_mul]
      exact mul_mem_semiLocalIntegralSet v hm (hc₂ v)
  have hleft : ∀ v : HeightOneSpectrum (𝓞 K),
      semiLocalComponent K L v (c * h) ∈ semiLocalIntegralSet K L v ↔
        semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v := by
    intro v
    constructor
    · intro hm
      have hh : h = c⁻¹ * (c * h) := (inv_mul_cancel_left c h).symm
      rw [hh, map_mul]
      exact mul_mem_semiLocalIntegralSet v (hc₃ v) hm
    · intro hm
      rw [map_mul]
      exact mul_mem_semiLocalIntegralSet v (hc₂ v) hm
  by_cases hint : ∀ v, v ∉ S → semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v
  · have hint₁ : ∀ v, v ∉ S → semiLocalComponent K L v (h * c) ∈ semiLocalIntegralSet K L v :=
      fun v hv => (hright v).2 (hint v hv)
    have hint₂ : ∀ v, v ∉ S → semiLocalComponent K L v (c * h) ∈ semiLocalIntegralSet K L v :=
      fun v hv => (hleft v).2 (hint v hv)
    rw [h₄ h hint, h₄ (h * c) hint₁, h₄ (c * h) hint₂]
    refine ⟨Finset.prod_congr rfl fun v hv => ?_, Finset.prod_congr rfl fun v hv => ?_⟩
    · rw [map_mul, hc₁ v hv, mul_one]
    · rw [map_mul, hc₁ v hv, one_mul]
  · obtain ⟨v, hv⟩ := not_forall.mp hint
    obtain ⟨hvS, hvn⟩ := Classical.not_imp.mp hv
    rw [h₅ h ⟨v, hvS, hvn⟩, h₅ (h * c) ⟨v, hvS, fun hm => hvn ((hright v).1 hm)⟩,
      h₅ (c * h) ⟨v, hvS, fun hm => hvn ((hleft v).1 hm)⟩]
    exact ⟨rfl, rfl⟩

private theorem apply_mul_eq_of_forall_finComponent_eq_one {tys : ArchTypeFamily L}
    {U : Subgroup (AdelicGL2 (𝓞 L) L)} {S : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U S φ) {M : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (htriv : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ S → finComponent (𝓞 L) L w (glFin (𝓞 L) L k) = 1)
    (g : AdelicGL2 (𝓞 L) L) : φ (k * g) = φ g ∧ φ (g * k) = φ g := by
  obtain ⟨φa, φf, φS, -, -, -, h₄, h₅, h₆⟩ := hφ.1.2
  obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_inf.mp hk
  have harch : glArch (𝓞 L) L k = 1 := (mem_finiteAdelicGL2Subgroup_iff L k).mp hk₂
  have hc₁ : ∀ v ∈ S, semiLocalComponent K L v (glFin (𝓞 L) L k) = 1 := by
    intro v hv
    rw [← map_one (semiLocalComponent K L v)]
    refine semiLocalComponent_eq_of_forall v fun w => ?_
    rw [map_one]
    refine htriv w.1 ?_
    rw [w.2]
    exact hv
  have hc₂ : ∀ v : HeightOneSpectrum (𝓞 K),
      semiLocalComponent K L v (glFin (𝓞 L) L k) ∈ semiLocalIntegralSet K L v := fun v =>
    semiLocalComponent_mem_of_forall v (fun w i j => finComponent_integral_of_mem_levelOne hk₁ i j)
      (fun w i j => by rw [map_inv]; exact finComponent_inv_integral_of_mem_levelOne hk₁ i j)
  have hc₃ : ∀ v : HeightOneSpectrum (𝓞 K),
      semiLocalComponent K L v (glFin (𝓞 L) L k)⁻¹ ∈ semiLocalIntegralSet K L v := by
    intro v
    exact semiLocalComponent_mem_of_forall v
      (fun w i j => by rw [map_inv]; exact finComponent_inv_integral_of_mem_levelOne hk₁ i j)
      (fun w i j => by rw [inv_inv]; exact finComponent_integral_of_mem_levelOne hk₁ i j)
  obtain ⟨hf₁, hf₂⟩ := finFactor_mul_eq h₄ h₅ hc₁ hc₂ hc₃ (glFin (𝓞 L) L g)
  constructor
  · rw [h₆ (k * g), h₆ g, map_mul, map_mul, harch, one_mul, hf₂]
  · rw [h₆ (g * k), h₆ g, map_mul, map_mul, harch, mul_one, hf₁]

end Invariance

section Refinement

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem exists_eq_mul_of_ne_zero {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) {w : HeightOneSpectrum (𝓞 L)} (hw : w.under (𝓞 K) ∉ SK)
    {M : Ideal (𝓞 L)} (hb : idealBound (𝓞 L) M w = 1) (z : AdelicGL2 (𝓞 L) L) (hz : φ z ≠ 0) :
    ∃ z₁ z₂ : AdelicGL2 (𝓞 L) L, z = z₁ * z₂ ∧ z₂ ∈ levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L ∧
      ∀ xv : GL (Fin 2) (w.adicCompletion L), z₁ * placeEmbed L w xv = placeEmbed L w xv * z₁ := by
  obtain ⟨hm, hm'⟩ := finComponent_integral_of_ne_zero hφ hw z hz
  refine ⟨z * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L z)))⁻¹,
    placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L z)), (inv_mul_cancel_right z _).symm,
    placeAt_mem_of_integral hb _ hm hm', fun xv => ?_⟩
  show z * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L z)))⁻¹ * placeAt w xv
    = placeAt w xv * (z * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L z)))⁻¹)
  exact (placeAt_mul_eq_mul_placeAt xv (finComponent_glFin_mul_inv_placeAt z)).symm

private theorem exists_eq_mul_of_mem {SL' : Finset (HeightOneSpectrum (𝓞 L))} {N N₀ : Ideal (𝓞 L)}
    (hle : levelOne (𝓞 L) L N ≤ levelOne (𝓞 L) L N₀)
    (hb : ∀ w ∈ SL', idealBound (𝓞 L) N₀ w = idealBound (𝓞 L) N w) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ∀ u ∈ levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L,
      (∀ w ∈ SL', w ∉ T → finComponent (𝓞 L) L w (glFin (𝓞 L) L u) = 1) →
        ∃ u₁ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
          ∃ u₂ ∈ levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L,
            u = u₁ * u₂ ∧ ∀ w ∈ SL', finComponent (𝓞 L) L w (glFin (𝓞 L) L u₂) = 1 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro u hu htriv
    exact ⟨1, one_mem _, u, hu, (one_mul u).symm, fun w hw => htriv w hw (Finset.notMem_empty w)⟩
  | insert w T hwT ih =>
    intro u hu htriv
    by_cases hwS : w ∈ SL'
    · have hp : placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u))
          ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
        placeAt_finComponent_mem (hb w hwS) (Subgroup.mem_inf.mp hu).1
      have hp₀ : placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u))
          ∈ levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L :=
        inf_le_inf_right _ hle hp
      have htriv' : ∀ w' ∈ SL', w' ∉ T →
          finComponent (𝓞 L) L w' (glFin (𝓞 L) L ((placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u)))⁻¹ * u))
            = 1 := by
        intro w' hw' hw'T
        by_cases hww : w' = w
        · rw [hww]
          exact finComponent_inv_placeAt_mul_self w u
        · rw [finComponent_inv_placeAt_mul_of_ne w u hww]
          exact htriv w' hw' fun hmem => (Finset.mem_insert.mp hmem).elim hww hw'T
      obtain ⟨u₁, hu₁, u₂, hu₂, hsplit, htriv₂⟩ := ih _ (mul_mem (inv_mem hp₀) hu) htriv'
      refine ⟨placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u)) * u₁, mul_mem hp hu₁, u₂, hu₂, ?_, htriv₂⟩
      rw [mul_assoc, ← hsplit, mul_inv_cancel_left]
    · refine ih u hu fun w' hw' hw'T => htriv w' hw' fun hmem => ?_
      exact (Finset.mem_insert.mp hmem).elim (fun h => hwS (by rw [← h]; exact hw')) hw'T

private theorem isBiInvariantUnder_of_refined {tys : ArchTypeFamily L} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {SL' : Finset (HeightOneSpectrum (𝓞 L))} {N N₀ : Ideal (𝓞 L)} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (hle : levelOne (𝓞 L) L N ≤ levelOne (𝓞 L) L N₀)
    (hb : ∀ w ∈ SL', idealBound (𝓞 L) N₀ w = idealBound (𝓞 L) N w)
    (hcover : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ SK → w ∈ SL') :
    IsBiInvariantUnder L (levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L) φ := by
  intro u hu g
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl, htriv⟩ := exists_eq_mul_of_mem hle hb SL' u hu fun w hw hw' => absurd hw hw'
  have h₁ := hφ.1.1 u₁ hu₁
  have h₂ := apply_mul_eq_of_forall_finComponent_eq_one hφ hu₂ fun w hw => htriv w (hcover w hw)
  constructor
  · rw [mul_assoc, (h₁ (u₂ * g)).1, (h₂ g).1]
  · rw [← mul_assoc, (h₂ (g * u₁)).2, (h₁ g).2]

private theorem isUnitFactorizableAboveOfType_of_refined {tys : ArchTypeFamily L}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {SL' : Finset (HeightOneSpectrum (𝓞 L))} {N N₀ : Ideal (𝓞 L)}
    {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (hle : levelOne (𝓞 L) L N ≤ levelOne (𝓞 L) L N₀)
    (hb : ∀ w ∈ SL', idealBound (𝓞 L) N₀ w = idealBound (𝓞 L) N w)
    (hcover : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ SK → w ∈ SL') :
    IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L) SK φ :=
  ⟨⟨isBiInvariantUnder_of_refined hφ hle hb hcover, hφ.1.2⟩, hφ.2⟩

private theorem rightConv_mul_eq_of_refined {tys : ArchTypeFamily L} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {SL' : Finset (HeightOneSpectrum (𝓞 L))} {N N₀ : Ideal (𝓞 L)} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (hle : levelOne (𝓞 L) L N ≤ levelOne (𝓞 L) L N₀)
    (hb : ∀ w ∈ SL', idealBound (𝓞 L) N₀ w = idealBound (𝓞 L) N w)
    (hcover : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ SK → w ∈ SL') (u : AdelicGL2 (𝓞 L) L → ℂ)
    (g : AdelicGL2 (𝓞 L) L) {k : AdelicGL2 (𝓞 L) L} (hk : k ∈ levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L) :
    rightConv L u φ (g * k) = rightConv L u φ g :=
  rightConv_mul_eq_of_tier (isUnitFactorizableAboveOfType_of_refined hφ hle hb hcover) u g hk

end Refinement

end

end AutomorphicForm.TwistedTraceRefinement
namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

open NumberField NumberField.AdelicLevel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.AutomorphicForm IsDedekindDomain UnramifiedWhittaker"

section Hecke

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem isHeckeCosetSystem_comp_equiv {G : Type} [Group G] {U : Subgroup G} {g : G} {ι κ : Type}
    {reps : ι → G} (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (e : κ ≃ ι) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset i := h.mem_doubleCoset (e i)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  mk_injective := h.mk_injective.comp e.injective

private theorem card_option_residue (w : HeightOneSpectrum (𝓞 L)) :
    Nonempty (Fin (Ideal.absNorm w.asIdeal + 1) ≃ Option (𝓞 L ⧸ w.asIdeal)) := by
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (Option (𝓞 L ⧸ w.asIdeal)) = Ideal.absNorm w.asIdeal + 1 := by
    rw [Fintype.card_option, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact ⟨(Fintype.equivFinOfCardEq hcard).symm⟩

private theorem not_dvd_of_idealBound_eq_one {M : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) M w = 1) : ¬ w.asIdeal ∣ M := by
  classical
  intro hdvd
  by_cases hM : M = ⊥
  · rw [hM, idealBound_bot] at hb
    exact zero_ne_one hb
  · rw [idealBound_of_ne_bot hM, WithZero.exp_eq_one, neg_eq_zero, Nat.cast_eq_zero] at hb
    exact (Associates.count_ne_zero_iff_dvd (show M ≠ 0 from hM) w.irreducible).mpr hdvd hb

private theorem exists_cosetFamily (w : HeightOneSpectrum (𝓞 L)) :
    ∃ r : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L,
      (∀ M : Ideal (𝓞 L), ¬ w.asIdeal ∣ M →
        HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (heckeGen (𝓞 L) L w) r) ∧
      ∀ i, ∃ m : GL (Fin 2) (w.adicCompletion L), r i = placeEmbed L w m := by
  obtain ⟨ϖ, hϖ0, -, -, sec, -, hall⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen L w
  obtain ⟨e⟩ := card_option_residue w
  exact ⟨_ ∘ e, fun M hM => isHeckeCosetSystem_comp_equiv (hall M hM) e, fun i => ⟨_, rfl⟩⟩

private noncomputable def cosetFamily (w : HeightOneSpectrum (𝓞 L)) :
    Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L :=
  (exists_cosetFamily w).choose

private theorem isHeckeCosetSystem_cosetFamily (w : HeightOneSpectrum (𝓞 L)) {M : Ideal (𝓞 L)}
    (hM : ¬ w.asIdeal ∣ M) :
    HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w)
      (cosetFamily w) :=
  (exists_cosetFamily w).choose_spec.1 M hM

private theorem isHeckeCosetSystem_cosetFamily_of_idealBound_eq_one (w : HeightOneSpectrum (𝓞 L)) {M : Ideal (𝓞 L)}
    (hb : idealBound (𝓞 L) M w = 1) :
    HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w)
      (cosetFamily w) :=
  isHeckeCosetSystem_cosetFamily w (not_dvd_of_idealBound_eq_one hb)

private theorem exists_cosetFamily_eq_placeEmbed (w : HeightOneSpectrum (𝓞 L))
    (i : Fin (Ideal.absNorm w.asIdeal + 1)) :
    ∃ m : GL (Fin 2) (w.adicCompletion L), cosetFamily w i = placeEmbed L w m :=
  (exists_cosetFamily w).choose_spec.2 i

private theorem isHeckeCosetEigenfunctionAt_iff_forall {M : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hM : ¬ w.asIdeal ∣ M) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, u (g * k) = u g) (c : ℂ) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w)
        w u c
      ↔ ∀ g : AdelicGL2 (𝓞 L) L, SmoothCusp.heckeCosetSum L (cosetFamily w) u g = c * u g := by
  constructor
  · rintro ⟨reps, hsys, heig⟩ g
    rw [← heig g]
    exact HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys (isHeckeCosetSystem_cosetFamily w hM) hu g
  · intro h
    exact ⟨cosetFamily w, isHeckeCosetSystem_cosetFamily w hM, h⟩

private theorem isHeckeCosetSystem_mul_left {G : Type} [Group G] {U : Subgroup G} {g : G} {ι : Type} {reps : ι → G}
    (h : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) {k : G} (hk : k ∈ U) :
    HeckeIntegralSeam.IsHeckeCosetSystem U g fun i => k * reps i where
  mem_doubleCoset i := by
    obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.mp (h.mem_doubleCoset i)
    exact HeckePair.mem_doubleCoset_iff.mpr ⟨k * a, mul_mem hk ha, b, hb, by rw [← hab]; simp only [mul_assoc]⟩
  covers x hx := by
    have hx' : k⁻¹ * x ∈ HeckePair.doubleCoset U g := by
      obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.mp hx
      exact HeckePair.mem_doubleCoset_iff.mpr
        ⟨k⁻¹ * a, mul_mem (inv_mem hk) ha, b, hb, by rw [← hab]; simp only [mul_assoc]⟩
    obtain ⟨i, hi⟩ := h.covers (k⁻¹ * x) hx'
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hi
  mk_injective i j hij := by
    apply h.mk_injective
    change (QuotientGroup.mk (k * reps i) : G ⧸ U) = QuotientGroup.mk (k * reps j) at hij
    change (QuotientGroup.mk (reps i) : G ⧸ U) = QuotientGroup.mk (reps j)
    rw [QuotientGroup.eq] at hij ⊢
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hij

private theorem heckeCosetSum_cosetFamily_mul_eq {M : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hM : ¬ w.asIdeal ∣ M) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L, u (g * k) = u g)
    (g : AdelicGL2 (𝓞 L) L) {k : AdelicGL2 (𝓞 L) L} (hk : k ∈ levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) :
    SmoothCusp.heckeCosetSum L (cosetFamily w) u (g * k) = SmoothCusp.heckeCosetSum L (cosetFamily w) u g := by
  have h := HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem (isHeckeCosetSystem_cosetFamily w hM)
    (isHeckeCosetSystem_mul_left (isHeckeCosetSystem_cosetFamily w hM) hk) hu g
  simp only [← mul_assoc] at h
  exact h

end Hecke

end AutomorphicForm.TwistedTraceRefinement
namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
namespace TwistLevel
p2m_open "AutomorphicForm"

noncomputable section

open NumberField NumberField.AdelicLevel
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.AutomorphicForm"
open scoped NumberField.PlaceTransport

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in

private theorem idealBound_map_smul (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L)) :
    idealBound (𝓞 L) (Ideal.map
        ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N)
        (σ • w)
      = idealBound (𝓞 L) N w := by
  by_cases h0 : N = ⊥
  · subst h0
    rw [Ideal.map_bot, idealBound_bot, idealBound_bot]
  have h0' : Ideal.map ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N ≠ ⊥ :=
    fun h => h0 ((Ideal.map_eq_bot_iff_of_injective
      (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ).injective).1 h)
  have hbound : ∀ (M : Ideal (𝓞 L)), M ≠ ⊥ → ∀ (P : HeightOneSpectrum (𝓞 L)) (k : ℕ),
      k ≤ (Associates.mk P.asIdeal).count (Associates.mk M).factors ↔ M ≤ P.asIdeal ^ k := fun M hM P k => by
    rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 hM)
        (Associates.irreducible_mk.2 P.irreducible),
      ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]
  have hσ : ∀ k : ℕ, Ideal.map
      ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N
        ≤ (σ • w).asIdeal ^ k ↔ N ≤ w.asIdeal ^ k := fun k => by
    rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, ← Ideal.map_pow,
      Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv]
    exact Ideal.comap_le_comap_iff_of_surjective
      (f := (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ).symm) (RingEquiv.surjective _) _ _
  have hc : (Associates.mk (σ • w).asIdeal).count (Associates.mk (Ideal.map
      ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N)).factors
      = (Associates.mk w.asIdeal).count (Associates.mk N).factors :=
    le_antisymm ((hbound _ h0 _ _).2 ((hσ _).1 ((hbound _ h0' _ _).1 le_rfl)))
      ((hbound _ h0' _ _).2 ((hσ _).2 ((hbound _ h0 _ _).1 le_rfl)))
  rw [idealBound_of_ne_bot h0', idealBound_of_ne_bot h0, hc]

private theorem act_snd_mem_integralFiniteAdeles (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L}
    (hx : x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
  refine fun w' => ?_
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ x (smul_inv_smul σ w'),
    NumberField.PlaceTransport.transport_mem_adicCompletionIntegers_iff]
  exact hx _

private theorem act_snd_mem_idealBall_map (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L))
    {x : AdeleRing (𝓞 L) L} (hx : x.2 ∈ idealBall (𝓞 L) L N) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).2
      ∈ idealBall (𝓞 L) L (Ideal.map
          ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N) := by
  refine fun w' => ?_
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ x (smul_inv_smul σ w'),
    NumberField.PlaceTransport.valued_transport]
  have h := idealBound_map_smul σ N (σ⁻¹ • w')
  rw [smul_inv_smul] at h
  exact (hx _).trans h.symm.le

private theorem act_fst_eq_zero (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L} (hx : x.1 = 0) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 = 0 := by
  funext w'
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x (smul_inv_smul σ w'), hx]
  exact map_zero _

private theorem act_fst_eq_one (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L} (hx : x.1 = 1) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 = 1 := by
  funext w'
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x (smul_inv_smul σ w'), hx]
  exact map_one _

private theorem isLevelOneMatrix_glFin_sigmaAdelicAct (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L))
    {g : GL (Fin 2) (AdeleRing (𝓞 L) L)}
    (hg : IsLevelOneMatrix (𝓞 L) L N
      (glFin (𝓞 L) L g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :
    IsLevelOneMatrix (𝓞 L) L (Ideal.map
        ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N)
      (glFin (𝓞 L) L (sigmaAdelicAct K L (M4aHerbrand.GenuineDescent.genuineDescentDatum K L) σ g) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) where
  integral i j :=
    act_snd_mem_integralFiniteAdeles σ (x := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j)
      (hg.integral i j)
  lowerLeft :=
    act_snd_mem_idealBall_map σ N
      (x := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0) hg.lowerLeft
  lowerRight := by
    have h := act_snd_mem_idealBall_map σ N
      (x := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 - 1) hg.lowerRight
    rwa [map_sub, map_one] at h

private theorem sigmaAdelicAct_mem_levelOne_inf_finiteAdelicGL2Subgroup
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L))
    {g : GL (Fin 2) (AdeleRing (𝓞 L) L)}
    (hg : g ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) :
    sigmaAdelicAct K L D σ g
      ∈ levelOne (𝓞 L) L (Ideal.map
          ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N)
        ⊓ finiteAdelicGL2Subgroup L := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  obtain ⟨hlev, harch⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨h₁, h₂⟩ := mem_finiteLevelOne_iff.1 (mem_levelOne_iff.1 hlev)
  refine Subgroup.mem_inf.2 ⟨mem_levelOne_iff.2 (mem_finiteLevelOne_iff.2 ⟨?_, ?_⟩), ?_⟩
  · exact isLevelOneMatrix_glFin_sigmaAdelicAct σ N h₁
  · rw [← map_inv, ← map_inv]
    refine isLevelOneMatrix_glFin_sigmaAdelicAct σ N ?_
    rw [map_inv]
    exact h₂
  · rw [mem_finiteAdelicGL2Subgroup_iff] at harch ⊢
    have hentry : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1
        = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j := by
      intro i j
      have h := glArch_apply (𝓞 L) L g i j
      rw [harch, Units.val_one] at h
      exact h.symm
    refine Units.ext ?_
    rw [Units.val_one]
    ext i j
    rw [glArch_apply, Matrix.one_apply]
    have h := hentry i j
    rw [Matrix.one_apply] at h
    split_ifs at h ⊢ with hij
    · exact act_fst_eq_one σ h
    · exact act_fst_eq_zero σ h

end

end AutomorphicForm.TwistedTraceRefinement.TwistLevel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicVolume
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain MeasureTheory HeckeIntegralSeam
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.AutomorphicForm AutomorphicForm.SmoothCusp"
open scoped NumberField.PlaceTransport

section

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem unitsAct_coe (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((Dsc.unitsAct σ z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = Dsc.act σ (z : AdeleRing (𝓞 L) L) := rfl

end

section

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem act_inv_act (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L Dsc σ⁻¹ (sigmaAdelicAct K L Dsc σ g) = g := by
  have h := sigmaAdelicAct_mul K L Dsc σ⁻¹ σ
  rw [inv_mul_cancel, sigmaAdelicAct_one] at h
  exact (DFunLike.congr_fun h g).symm

private theorem act_act_inv (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L Dsc σ (sigmaAdelicAct K L Dsc σ⁻¹ g) = g := by
  have h := sigmaAdelicAct_mul K L Dsc σ σ⁻¹
  rw [mul_inv_cancel, sigmaAdelicAct_one] at h
  exact (DFunLike.congr_fun h g).symm

private theorem act_entry (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L Dsc σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
      = Dsc.act σ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j g

private theorem sigmaSectionActOn_apply (σ : L ≃ₐ[K] L) (u : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    sigmaSectionActOn K L Dsc σ u g = u (sigmaAdelicAct K L Dsc σ g) := rfl

private theorem act_centralScalar (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L Dsc σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (Dsc.unitsAct σ z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [act_entry]
  by_cases hij : i = j
  · subst hij
    rw [centralScalar_apply_eq, centralScalar_apply_eq, unitsAct_coe]
  · rw [centralScalar_apply_ne _ hij, centralScalar_apply_ne _ hij, map_zero]

end

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem act_snd_mem_integralFiniteAdeles (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L}
    (hx : x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
  refine fun w' => ?_
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ x (smul_inv_smul σ w'),
    NumberField.PlaceTransport.transport_mem_adicCompletionIntegers_iff]
  exact hx _

private theorem act_fst_eq_zero (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L} (hx : x.1 = 0) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 = 0 := by
  funext w'
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x (smul_inv_smul σ w'), hx]
  exact map_zero _

private theorem act_fst_eq_one (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L} (hx : x.1 = 1) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 = 1 := by
  funext w'
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x (smul_inv_smul σ w'), hx]
  exact map_one _

end

section

variable {G : Type*} [Group G] {U : Subgroup G}

private theorem doubleCoset_mul_of_mem {g k : G} (hk : k ∈ U) :
    HeckePair.doubleCoset U (g * k) = HeckePair.doubleCoset U g := by
  ext x
  rw [HeckePair.mem_doubleCoset_iff, HeckePair.mem_doubleCoset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, k * b, U.mul_mem hk hb, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, k⁻¹ * b, U.mul_mem (U.inv_mem hk) hb, by group⟩

private theorem cosetSystem_of_doubleCoset_eq {g g' : G}
    (hgg : HeckePair.doubleCoset U g' = HeckePair.doubleCoset U g) {ι : Type*} {reps : ι → G}
    (h : IsHeckeCosetSystem U g' reps) : IsHeckeCosetSystem U g reps where
  mem_doubleCoset i := hgg ▸ h.mem_doubleCoset i
  covers x hx := h.covers x (hgg ▸ hx)
  mk_injective := h.mk_injective

private theorem cosetSystem_of_mul_mem {g k : G} (hk : k ∈ U) {ι : Type*} {reps : ι → G}
    (h : IsHeckeCosetSystem U (g * k) reps) : IsHeckeCosetSystem U g reps :=
  cosetSystem_of_doubleCoset_eq (doubleCoset_mul_of_mem hk) h

private theorem cosetSystem_comp_equiv {g : G} {ι ι' : Type*} {reps : ι → G} (h : IsHeckeCosetSystem U g reps)
    (e : ι' ≃ ι) : IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset i := h.mem_doubleCoset (e i)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa only [Function.comp, Equiv.apply_symm_apply] using hi⟩
  mk_injective i j hij := e.injective (h.mk_injective hij)

private theorem cosetSystem_map_of_mem_iff {g : G} {ι : Type*} {reps : ι → G} (h : IsHeckeCosetSystem U g reps)
    (U' : Subgroup G) (α : G ≃* G) (hU : ∀ x : G, α x ∈ U' ↔ x ∈ U) :
    IsHeckeCosetSystem U' (α g) (fun i => α (reps i)) where
  mem_doubleCoset i := by
    obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.mp (h.mem_doubleCoset i)
    exact HeckePair.mem_doubleCoset_iff.mpr
      ⟨α a, (hU a).mpr ha, α b, (hU b).mpr hb, by rw [← map_mul, ← map_mul, hab]⟩
  covers x hx := by
    obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    have hy : α.symm x ∈ HeckePair.doubleCoset U g := by
      refine HeckePair.mem_doubleCoset_iff.mpr ⟨α.symm a, ?_, α.symm b, ?_, ?_⟩
      · rw [← hU, MulEquiv.apply_symm_apply]; exact ha
      · rw [← hU, MulEquiv.apply_symm_apply]; exact hb
      · apply α.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hab]
    obtain ⟨i, hi⟩ := h.covers _ hy
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    have h2 := (hU _).mpr hi
    rwa [map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
  mk_injective i j hij := by
    apply h.mk_injective
    simp only at hij ⊢
    rw [QuotientGroup.eq] at hij ⊢
    rw [← map_inv, ← map_mul, hU] at hij
    exact hij

end

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def genIndexEquiv (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    Fin (Ideal.absNorm w.asIdeal + 1) ≃ Fin (Ideal.absNorm (σ • w).asIdeal + 1) :=
  finCongr (by rw [absNorm_smul])

end

section Action

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private def actEquiv (σ : L ≃ₐ[K] L) : AdelicGL2 (𝓞 L) L ≃* AdelicGL2 (𝓞 L) L where
  toFun := sigmaAdelicAct K L Dsc σ
  invFun := sigmaAdelicAct K L Dsc σ⁻¹
  left_inv := act_inv_act Dsc σ
  right_inv := act_act_inv Dsc σ
  map_mul' := map_mul _

omit [NumberField K] in
private theorem actEquiv_apply
    (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) : actEquiv Dsc σ g = sigmaAdelicAct K L Dsc σ g := rfl

omit [NumberField K] in
private theorem det_act (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (sigmaAdelicAct K L Dsc σ g) = Dsc.unitsAct σ (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unitsAct_coe, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two, Matrix.det_fin_two, act_entry, act_entry, act_entry, act_entry, map_sub, map_mul, map_mul]

private def tUnit (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂) (t : (w₁.adicCompletion L)ˣ) :
    (w₂.adicCompletion L)ˣ :=
  Units.map ((NumberField.PlaceTransport.transport σ h : w₁.adicCompletion L →+* w₂.adicCompletion L) :
    w₁.adicCompletion L →* w₂.adicCompletion L) t

omit [NumberField K] in
private theorem coe_tUnit
    (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂) (t : (w₁.adicCompletion L)ˣ) :
    ((tUnit σ h t : (w₂.adicCompletion L)ˣ) : w₂.adicCompletion L)
      = NumberField.PlaceTransport.transport σ h (t : w₁.adicCompletion L) := rfl

omit [NumberField K] in
private theorem valued_tUnit
    (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂) (t : (w₁.adicCompletion L)ˣ) :
    Valued.v ((tUnit σ h t : (w₂.adicCompletion L)ˣ) : w₂.adicCompletion L) = Valued.v (t : w₁.adicCompletion L) := by
  rw [coe_tUnit, NumberField.PlaceTransport.valued_transport]

private theorem act_heckeGenAt (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂)
    (t : (w₁.adicCompletion L)ˣ) :
    sigmaAdelicAct K L Dsc σ (heckeGenAt (𝓞 L) L w₁ t) = heckeGenAt (𝓞 L) L w₂ (tUnit σ h t) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : Dsc = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  subst h
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [act_entry]
  refine Prod.ext ?_ ?_
  · rw [heckeGenAt_fst]
    have h1 := heckeGenAt_fst t i j
    rw [Matrix.one_apply] at h1 ⊢
    split_ifs at h1 ⊢ with hij
    · exact act_fst_eq_one σ h1
    · exact act_fst_eq_zero σ h1
  · refine FiniteAdeleRing.ext L fun v' => ?_
    by_cases hv : v' = σ • w₁
    · subst hv
      rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ (rfl : σ • w₁ = σ • w₁),
        heckeGenAt_snd_apply_self, heckeGenAt_snd_apply_self]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        fin_cases i
        · exact (coe_tUnit σ rfl t).symm
        · exact map_one _
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, map_zero]
    · have hne : σ⁻¹ • v' ≠ w₁ := fun hh => hv (by rw [← hh, smul_inv_smul])
      rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ (smul_inv_smul σ v'),
        heckeGenAt_snd_apply_of_ne t hne, heckeGenAt_snd_apply_of_ne (tUnit σ rfl t) hv, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs
      · exact map_one _
      · exact map_zero _

private theorem act_heckeGen (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂) :
    ∃ s : (w₂.adicCompletion L)ˣ, Valued.v (s : w₂.adicCompletion L) = 1 ∧
      sigmaAdelicAct K L Dsc σ (heckeGen (𝓞 L) L w₁) = heckeGen (𝓞 L) L w₂ * heckeGenAt (𝓞 L) L w₂ s := by
  refine ⟨(uniformizerUnit L w₂)⁻¹ * tUnit σ h (uniformizerUnit L w₁), ?_, ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, valued_tUnit, valued_uniformizerUnit,
      valued_uniformizerUnit, inv_mul_cancel₀ WithZero.exp_ne_zero]
  · unfold heckeGen
    rw [act_heckeGenAt Dsc σ h, ← map_mul, mul_inv_cancel_left]

end Action

section Level

variable {L : Type} [Field L] [NumberField L]

private abbrev UN (L : Type) [Field L] [NumberField L] (N : Ideal (𝓞 L)) : Subgroup (AdelicGL2 (𝓞 L) L) :=
  levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L

private theorem glArch_heckeGenAt (v : HeightOneSpectrum (𝓞 L)) (s : (v.adicCompletion L)ˣ) :
    glArch (𝓞 L) L (heckeGenAt (𝓞 L) L v s) = 1 := by
  refine Units.ext ?_
  rw [Units.val_one]
  ext i j
  rw [glArch_apply, heckeGenAt_fst]

private theorem heckeGenAt_mem_UN (N : Ideal (𝓞 L)) {v : HeightOneSpectrum (𝓞 L)} {s : (v.adicCompletion L)ˣ}
    (hs : Valued.v (s : v.adicCompletion L) = 1) : heckeGenAt (𝓞 L) L v s ∈ UN L N := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h := heckeGenAt_inv_mul_heckeGenAt_mem_levelOne (R := 𝓞 L) (K := L) (v := v) 1 s
      (by rw [Units.val_one, map_one, hs]) N
    rwa [map_one, inv_one, one_mul] at h
  · exact (mem_finiteAdelicGL2Subgroup_iff L _).mpr (glArch_heckeGenAt v s)

private theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) : Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(a : A), 1]).det = a
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_heckeGenAt (v : HeightOneSpectrum (𝓞 L)) (s : (v.adicCompletion L)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L v s) = Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v s) :=
  det_diagOne _

private theorem localUnit_mem_integralFiniteAdeles {v : HeightOneSpectrum (𝓞 L)} {s : (v.adicCompletion L)ˣ}
    (hs : Valued.v (s : v.adicCompletion L) = 1) :
    ((localUnit (𝓞 L) L v s : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
  intro w
  classical
  by_cases hw : w = v
  · subst hw
    rw [localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers, hs]
  · rw [localUnit_apply_of_ne (𝓞 L) L v s hw]; exact one_mem _

private theorem localUnit_sub_one_mem_idealBall
    {N : Ideal (𝓞 L)} {v : HeightOneSpectrum (𝓞 L)} (hb : idealBound (𝓞 L) N v = 1)
    {s : (v.adicCompletion L)ˣ} (hs : Valued.v (s : v.adicCompletion L) = 1) :
    ((localUnit (𝓞 L) L v s : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) - 1 ∈ idealBall (𝓞 L) L N := by
  intro w
  rw [coe_sub_apply, coe_one_apply]
  by_cases hw : w = v
  · subst hw
    rw [localUnit_apply_self, hb]
    exact (Valuation.map_sub _ _ _).trans (max_le (le_of_eq hs) (le_of_eq (map_one _)))
  · rw [localUnit_apply_of_ne (𝓞 L) L v s hw, sub_self, map_zero]
    exact zero_le'

private theorem coe_units_map_finIncl_snd (z : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ((Units.map (finIncl (𝓞 L) L) z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2
      = (z : FiniteAdeleRing (𝓞 L) L) := rfl

private theorem coe_units_map_finIncl_fst (z : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ((Units.map (finIncl (𝓞 L) L) z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := rfl

private theorem isLevelOneMatrix_glFin_centralScalar {N : Ideal (𝓞 L)} {v : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N v = 1) {s : (v.adicCompletion L)ˣ} (hs : Valued.v (s : v.adicCompletion L) = 1) :
    IsLevelOneMatrix (𝓞 L) L N
      (glFin (𝓞 L) L (centralScalar (𝓞 L) L (Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v s))) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) := by
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · by_cases hij : i = j
    · subst hij
      rw [glFin_apply, centralScalar_apply_eq, coe_units_map_finIncl_snd]
      exact localUnit_mem_integralFiniteAdeles hs
    · rw [glFin_apply, centralScalar_apply_ne _ hij]
      exact zero_mem_integralFiniteAdeles
  · rw [glFin_apply, centralScalar_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    exact zero_mem_idealBall N
  · rw [glFin_apply, centralScalar_apply_eq, coe_units_map_finIncl_snd]
    exact localUnit_sub_one_mem_idealBall hb hs

private theorem glArch_centralScalar_units_map_finIncl (z : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    glArch (𝓞 L) L (centralScalar (𝓞 L) L (Units.map (finIncl (𝓞 L) L) z)) = 1 := by
  refine Units.ext ?_
  rw [Units.val_one]
  ext i j
  rw [glArch_apply]
  by_cases hij : i = j
  · subst hij
    rw [centralScalar_apply_eq, coe_units_map_finIncl_fst, Matrix.one_apply_eq]
  · rw [centralScalar_apply_ne _ hij, Matrix.one_apply_ne hij]
    rfl

private theorem centralScalar_det_heckeGenAt_mem_UN {N : Ideal (𝓞 L)} {v : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N v = 1) {s : (v.adicCompletion L)ˣ} (hs : Valued.v (s : v.adicCompletion L) = 1) :
    centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L v s)) ∈ UN L N := by
  rw [det_heckeGenAt]
  have hsi : Valued.v ((s⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]
  refine Subgroup.mem_inf.mpr ⟨mem_levelOne_iff.mpr ?_,
    (mem_finiteAdelicGL2Subgroup_iff L _).mpr (glArch_centralScalar_units_map_finIncl _)⟩
  show _ ∧ _
  refine ⟨isLevelOneMatrix_glFin_centralScalar hb hs, ?_⟩
  rw [← map_inv, ← map_inv, ← map_inv, ← map_inv]
  exact isLevelOneMatrix_glFin_centralScalar hb hsi

end Level

section Transport

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

omit [NumberField K] in
private theorem actEquiv_inv_mem_iff_of_transport (σ : L ≃ₐ[K] L) {U U' : Subgroup (AdelicGL2 (𝓞 L) L)}
    (hdown : ∀ x ∈ U, sigmaAdelicAct K L Dsc σ⁻¹ x ∈ U') (hup : ∀ x ∈ U', sigmaAdelicAct K L Dsc σ x ∈ U)
    (x : AdelicGL2 (𝓞 L) L) : actEquiv Dsc σ⁻¹ x ∈ U' ↔ x ∈ U := by
  rw [actEquiv_apply]
  refine ⟨fun hx => ?_, hdown x⟩
  have h := hup _ hx
  rwa [act_act_inv] at h

omit [NumberField K] in
private theorem heckeCosetSum_twist (σ : L ≃ₐ[K] L) {n m : ℕ} (reps : Fin m → AdelicGL2 (𝓞 L) L) (e : Fin n ≃ Fin m)
    (u : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    heckeCosetSum L (fun i => sigmaAdelicAct K L Dsc σ⁻¹ (reps (e i))) (sigmaSectionActOn K L Dsc σ u) g
      = heckeCosetSum L reps u (sigmaAdelicAct K L Dsc σ g) := by
  unfold heckeCosetSum
  rw [← e.sum_comp fun j => u (sigmaAdelicAct K L Dsc σ g * reps j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  show u (sigmaAdelicAct K L Dsc σ (g * sigmaAdelicAct K L Dsc σ⁻¹ (reps (e i))))
    = u (sigmaAdelicAct K L Dsc σ g * reps (e i))
  rw [map_mul, act_act_inv]

private theorem isHeckeCosetEigenfunctionAt_twist_of_transport (σ : L ≃ₐ[K] L) (N N' : Ideal (𝓞 L))
    (hdown : ∀ x ∈ UN L N, sigmaAdelicAct K L Dsc σ⁻¹ x ∈ UN L N')
    (hup : ∀ x ∈ UN L N', sigmaAdelicAct K L Dsc σ x ∈ UN L N) {u : AdelicGL2 (𝓞 L) L → ℂ}
    {w : HeightOneSpectrum (𝓞 L)} {c : ℂ}
    (h : IsHeckeCosetEigenfunctionAt L (UN L N) (heckeGen (𝓞 L) L (σ • w)) (σ • w) u c) :
    IsHeckeCosetEigenfunctionAt L (UN L N') (heckeGen (𝓞 L) L w) w (sigmaSectionActOn K L Dsc σ u) c := by
  obtain ⟨reps, hsys, hsum⟩ := h
  obtain ⟨s, hs, hgen⟩ := act_heckeGen Dsc σ⁻¹ (inv_smul_smul σ w)
  refine ⟨fun i => sigmaAdelicAct K L Dsc σ⁻¹ (reps (genIndexEquiv σ w i)), ?_, fun g => ?_⟩
  · have hs' := cosetSystem_comp_equiv (cosetSystem_map_of_mem_iff hsys (UN L N') (actEquiv Dsc σ⁻¹)
      (actEquiv_inv_mem_iff_of_transport Dsc σ hdown hup)) (genIndexEquiv σ w)
    rw [actEquiv_apply, hgen] at hs'
    exact cosetSystem_of_mul_mem (heckeGenAt_mem_UN N' hs) hs'
  · rw [heckeCosetSum_twist, hsum, sigmaSectionActOn_apply]

private theorem central_eigen_twist (σ : L ≃ₐ[K] L) {N : Ideal (𝓞 L)} {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ UN L N, u (g * k) = u g) {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N (σ • w) = 1) {b : ℂ}
    (h : ∀ g : AdelicGL2 (𝓞 L) L,
      u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (σ • w))) * g) = b * u g)
    (g : AdelicGL2 (𝓞 L) L) :
    sigmaSectionActOn K L Dsc σ u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * g)
      = b * sigmaSectionActOn K L Dsc σ u g := by
  obtain ⟨s, hs, hgen⟩ := act_heckeGen Dsc σ (rfl : σ • w = σ • w)
  rw [sigmaSectionActOn_apply, sigmaSectionActOn_apply, map_mul, act_centralScalar, ← det_act, hgen, map_mul, map_mul,
    mul_assoc, h, ← mul_centralScalar_comm, hlev _ _ (centralScalar_det_heckeGenAt_mem_UN hb hs)]

end Transport

section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

omit [NumberField K] in
private theorem cNorm_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    HeckeEigensystem.cNorm (σ • w) = HeckeEigensystem.cNorm w := by
  unfold HeckeEigensystem.cNorm
  rw [absNorm_smul]

omit [NumberField K] in
private theorem toRawCentral_b_smul (σ : L ≃ₐ[K] L) {SL : Finset (HeightOneSpectrum (𝓞 L))} {Ψ : HeckeEigensystem L ℂ}
    (hfib : ∀ 𝔓₁ ∉ SL, ∀ 𝔓₂ ∉ SL, 𝔓₁.under (𝓞 K) = 𝔓₂.under (𝓞 K) →
      (𝔓₁.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₁.asIdeal = (𝔓₂.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₂.asIdeal →
      Ψ.a 𝔓₁ = Ψ.a 𝔓₂ ∧ Ψ.b 𝔓₁ = Ψ.b 𝔓₂)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ SL) (hw' : σ • w ∉ SL) :
    Ψ.a (σ • w) = Ψ.a w ∧ Ψ.toRawCentral.b (σ • w) = Ψ.toRawCentral.b w := by
  obtain ⟨ha, hb⟩ := hfib (σ • w) hw' w hw (under_smul σ w) (inertiaDeg_smul σ w)
  refine ⟨ha, ?_⟩
  rw [HeckeEigensystem.toRawCentral_b, HeckeEigensystem.toRawCentral_b, cNorm_smul, hb]

end

end

end AutomorphicForm.TwistedTraceRefinement
namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
namespace TwistLevel
p2m_open "AutomorphicForm"

open NumberField NumberField.AdelicLevel
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.AutomorphicForm"
open scoped NumberField.PlaceTransport

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in

private theorem level_map_map_inv (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) :
    Ideal.map ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L)
        (Ideal.map ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ⁻¹ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N)
      = N := by
  rw [Ideal.map_map]
  convert Ideal.map_id N using 2
  ext x
  simp only [RingHom.comp_apply, RingHom.coe_coe, MulSemiringAction.toRingEquiv_apply, RingHom.id_apply]
  rw [smul_inv_smul]

end AutomorphicForm.TwistedTraceRefinement.TwistLevel

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

section TwistGlue

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain MeasureTheory
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.AutomorphicForm AutomorphicForm.SmoothCusp HeckeIntegralSeam UnramifiedWhittaker"
open scoped NumberField.PlaceTransport

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private abbrev twistLevel (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) : Ideal (𝓞 L) :=
  Ideal.map ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ⁻¹ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N

private theorem act_inv_mem_UN_twistLevel (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) :
    ∀ x ∈ UN L N, sigmaAdelicAct K L Dsc σ⁻¹ x ∈ UN L (twistLevel σ N) :=
  fun _ hx => TwistLevel.sigmaAdelicAct_mem_levelOne_inf_finiteAdelicGL2Subgroup Dsc σ⁻¹ N hx

private theorem act_mem_UN_of_mem_twistLevel (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L)) :
    ∀ x ∈ UN L (twistLevel σ N), sigmaAdelicAct K L Dsc σ x ∈ UN L N := by
  intro x hx
  have h := TwistLevel.sigmaAdelicAct_mem_levelOne_inf_finiteAdelicGL2Subgroup Dsc σ (twistLevel σ N) hx
  rwa [TwistLevel.level_map_map_inv σ N] at h

omit [NumberField K] in

private theorem idealBound_twistLevel_eq_one (σ : L ≃ₐ[K] L) {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N (σ • w) = 1) : idealBound (𝓞 L) (twistLevel σ N) w = 1 := by
  have h := TwistLevel.idealBound_map_smul σ⁻¹ N (σ • w)
  rwa [inv_smul_smul, hb] at h

private theorem sigmaSectionActOn_mul_eq_of_mem_twistLevel (σ : L ≃ₐ[K] L) {N : Ideal (𝓞 L)}
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hlev : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ UN L N, u (g * k) = u g) :
    ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ UN L (twistLevel σ N),
      sigmaSectionActOn K L Dsc σ u (g * k) = sigmaSectionActOn K L Dsc σ u g := by
  intro g k hk
  rw [sigmaSectionActOn_apply, sigmaSectionActOn_apply, map_mul]
  exact hlev _ _ (act_mem_UN_of_mem_twistLevel Dsc σ N k hk)

omit [NumberField K] in

private theorem integrable_sigmaSectionActOn_mul (σ : L ≃ₐ[K] L) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hcont : Continuous u) {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (g : AdelicGL2 (𝓞 L) L) :
    Integrable (fun z => sigmaSectionActOn K L Dsc σ u (g * z) * φ z) (adelicGLHaar (Fin 2) (𝓞 L) L) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  have htw : Continuous (sigmaSectionActOn K L Dsc σ u) := continuous_sigmaSectionActOn K L Dsc σ hcont
  exact ((htw.comp (continuous_const.mul continuous_id)).mul hφ).integrable_of_hasCompactSupport hφc.mul_left

private theorem heckeCosetSum_twistedConvOp_eq (σ : L ≃ₐ[K] L) {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N (σ • w) = 1) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ UN L N, u (g * k) = u g) (hcont : Continuous u) {a : ℂ}
    (heig : IsHeckeCosetEigenfunctionAt L (UN L N) (heckeGen (𝓞 L) L (σ • w)) (σ • w) u a)
    {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {reps : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L}
    (hfam : ∀ M : Ideal (𝓞 L), idealBound (𝓞 L) M w = 1 → IsHeckeCosetSystem (UN L M) (heckeGen (𝓞 L) L w) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) (w.adicCompletion L), reps j = placeEmbed L w m)
    (hplace : ∀ M : Ideal (𝓞 L), idealBound (𝓞 L) M w = 1 → ∀ kv : GL (Fin 2) (w.adicCompletionIntegers L),
      placeEmbed L w (Matrix.GeneralLinearGroup.map
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) kv) ∈ UN L M)
    (hsupp : ∀ M : Ideal (𝓞 L), idealBound (𝓞 L) M w = 1 → ∀ z : AdelicGL2 (𝓞 L) L, φ z ≠ 0 →
      ∃ z₁ z₂ : AdelicGL2 (𝓞 L) L, z = z₁ * z₂ ∧ z₂ ∈ UN L M ∧
        ∀ xv : GL (Fin 2) (w.adicCompletion L), z₁ * placeEmbed L w xv = placeEmbed L w xv * z₁) :
    ∀ g : AdelicGL2 (𝓞 L) L,
      heckeCosetSum L reps (twistedConvOp K L Dsc σ φ u) g = a * twistedConvOp K L Dsc σ φ u g := by
  have hb' : idealBound (𝓞 L) (twistLevel σ N) w = 1 := idealBound_twistLevel_eq_one σ hb
  have heig' : IsHeckeCosetEigenfunctionAt L (UN L (twistLevel σ N)) (heckeGen (𝓞 L) L w) w
      (sigmaSectionActOn K L Dsc σ u) a :=
    isHeckeCosetEigenfunctionAt_twist_of_transport Dsc σ N (twistLevel σ N)
      (act_inv_mem_UN_twistLevel Dsc σ N) (act_mem_UN_of_mem_twistLevel Dsc σ N) heig
  have h := AutomorphicForm.heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps L w (UN L (twistLevel σ N))
    (hplace _ hb') reps (hfam _ hb') hpure (sigmaSectionActOn K L Dsc σ u)
    (sigmaSectionActOn_mul_eq_of_mem_twistLevel Dsc σ hlev) a heig' φ (hsupp _ hb')
    (integrable_sigmaSectionActOn_mul Dsc σ hcont hφ hφc) (n := 1) (fun _ => 1) (fun _ => 1)
    (fun _ xv => by rw [one_mul, mul_one])
  obtain ⟨-, h₂, -⟩ := h
  intro g
  show heckeCosetSum L reps (rightConv L (sigmaSectionActOn K L Dsc σ u) φ) g
    = a * rightConv L (sigmaSectionActOn K L Dsc σ u) φ g
  simpa using h₂ g

private theorem twistedConvOp_centralScalar_mul (σ : L ≃ₐ[K] L) {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N (σ • w) = 1) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ UN L N, u (g * k) = u g) {b : ℂ}
    (hcen : ∀ g : AdelicGL2 (𝓞 L) L,
      u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (σ • w))) * g) = b * u g)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    twistedConvOp K L Dsc σ φ u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * g)
      = b * twistedConvOp K L Dsc σ φ u g := by
  have htw := central_eigen_twist Dsc σ hlev hb hcen
  simp only [twistedConvOp_apply, rightConv_apply]
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [mul_assoc, htw, mul_assoc]

private theorem twistedConvOp_eigenData_of_isIsotypicCuspFormAt (σ : L ≃ₐ[K] L) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (ξ : (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).Z →* ℂˣ)
    {N : Ideal (𝓞 L)} {S : Finset (HeightOneSpectrum (𝓞 L))} {π : HeckeEigensystem L ℂ}
    {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : IsIsotypicCuspFormAt L (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξ N S π u)
    {w : HeightOneSpectrum (𝓞 L)} (hσw : σ • w ∉ S) (hb : idealBound (𝓞 L) N (σ • w) = 1)
    {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    {reps : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L}
    (hfam : ∀ M : Ideal (𝓞 L), idealBound (𝓞 L) M w = 1 → IsHeckeCosetSystem (UN L M) (heckeGen (𝓞 L) L w) reps)
    (hpure : ∀ j, ∃ m : GL (Fin 2) (w.adicCompletion L), reps j = placeEmbed L w m)
    (hplace : ∀ M : Ideal (𝓞 L), idealBound (𝓞 L) M w = 1 → ∀ kv : GL (Fin 2) (w.adicCompletionIntegers L),
      placeEmbed L w (Matrix.GeneralLinearGroup.map
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) kv) ∈ UN L M)
    (hsupp : ∀ M : Ideal (𝓞 L), idealBound (𝓞 L) M w = 1 → ∀ z : AdelicGL2 (𝓞 L) L, φ z ≠ 0 →
      ∃ z₁ z₂ : AdelicGL2 (𝓞 L) L, z = z₁ * z₂ ∧ z₂ ∈ UN L M ∧
        ∀ xv : GL (Fin 2) (w.adicCompletion L), z₁ * placeEmbed L w xv = placeEmbed L w xv * z₁) :
    (∀ g : AdelicGL2 (𝓞 L) L,
        heckeCosetSum L reps (twistedConvOp K L Dsc σ φ u) g = π.a (σ • w) * twistedConvOp K L Dsc σ φ u g) ∧
      (∀ g : AdelicGL2 (𝓞 L) L,
        twistedConvOp K L Dsc σ φ u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * g)
          = π.toRawCentral.b (σ • w) * twistedConvOp K L Dsc σ φ u g) :=
  ⟨heckeCosetSum_twistedConvOp_eq Dsc σ hb hu.level_invariant hu.continuous (hu.hecke_eigen _ hσw) hφ hφc hfam
      hpure hplace hsupp,
    twistedConvOp_centralScalar_mul Dsc σ hb hu.level_invariant (hu.central_eigen _ hσw) φ⟩

end TwistGlue

end AutomorphicForm.TwistedTraceRefinement
namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

section GenuineMembers

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.AutomorphicForm"

variable {L : Type} [Field L] [NumberField L]

private theorem isSmoothCuspAutomorphicFnAt_of_mem_isotypicCuspSubmodule (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (ξ : (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).Z →* ℂˣ)
    (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξ N S Ψ) :
    IsSmoothCuspAutomorphicFnAt L (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξ u := by
  have hle : isotypicCuspSubmodule L (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξ N S Ψ ≤
      AutomorphicForm.CuspidalSpectrum.cuspMemberSubmodule L ΦL ξ :=
    Submodule.span_le.2 fun φ hφ => by
      have h : IsIsotypicCuspFormAt L _ ξ N S Ψ φ := hφ
      exact ⟨h.smoothCusp, h.continuous⟩
  exact (hle hu).1

end GenuineMembers

end AutomorphicForm.TwistedTraceRefinement
namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

noncomputable section

open NumberField NumberField.AdelicLevel
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.AutomorphicForm AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum IsDedekindDomain"
open UnramifiedWhittaker

section Cut

variable {L : Type} [Field L] [NumberField L]

private theorem commute_placeEmbed_rowIsometryInclAt₀ (w : HeightOneSpectrum (𝓞 L))
    (m : GL (Fin 2) (w.adicCompletion L)) (v : InfinitePlace L) (k : rowIsometrySubgroup₀ v.Completion) :
    Commute (placeEmbed L w m) (rowIsometryInclAt₀ L v k) := by
  show placeAt w m * rowIsometryInclAt₀ L v k = rowIsometryInclAt₀ L v k * placeAt w m
  exact placeAt_mul_eq_mul_placeAt m (by rw [glFin_rowIsometryInclAt₀, map_one])

private theorem rightTranslate_placeEmbed_mem_archCutSubmodule (tys : ArchTypeFamily L) {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : f ∈ archCutSubmodule L tys) (w : HeightOneSpectrum (𝓞 L)) (m : GL (Fin 2) (w.adicCompletion L)) :
    rightTranslate L (placeEmbed L w m) f ∈ archCutSubmodule L tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro v
  have key : ∀ i : Fin (tys.card v),
      (archTypeSubmoduleAt L v (tys.rep v i)).map (rightRegular L (placeEmbed L w m))
        ≤ archTypeSubmoduleAt L v (tys.rep v i) := by
    intro i f₁ hf₁
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf₁
    exact comp_mul_mem_typeSubmodule_of_commute hf₀ _ fun k => commute_placeEmbed_rowIsometryInclAt₀ w m v k
  have hmap : (⨆ i, archTypeSubmoduleAt L v (tys.rep v i)).map (rightRegular L (placeEmbed L w m))
      ≤ ⨆ i, archTypeSubmoduleAt L v (tys.rep v i) := by
    rw [Submodule.map_iSup]
    exact iSup_mono key
  exact hmap (Submodule.mem_map_of_mem (hf v))

end Cut

section Translate

variable {L : Type} [Field L] [NumberField L]

private theorem isCuspidalFn_rightTranslate {Q G : Type} {_ : MeasurableSpace Q} [Group G]
    (μ : MeasureTheory.Measure Q) (n : Q → G) {f : G → ℂ} (hf : IsCuspidalFn μ n f) (r : G) :
    IsCuspidalFn μ n fun x => f (x * r) := by
  intro g
  have h := hf (g * r)
  simp only [constantTerm, constantTermIntegrand, mul_assoc] at h ⊢
  exact h

private theorem isKfSmooth_rightTranslate {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : IsKfSmooth L f) {r : AdelicGL2 (𝓞 L) L}
    (hr : r ∈ finiteAdelicGL2Subgroup L) : IsKfSmooth L (rightTranslate L r f) := by
  rw [isKfSmooth_iff] at hf ⊢
  exact hf.smul (⟨r, hr⟩ : finiteAdelicGL2Subgroup L)

private theorem det_centralScalar_eq (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z) = z * z := by
  refine Units.ext ?_
  show Matrix.det (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L)) = (z : AdeleRing (𝓞 L) L) * z
  simp
  exact pow_two _

private theorem rightTranslate_mem_contMemberSubmodule {α β : ℝ} {ΦL : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ : IsSlabFundamentalDomain L α β ΦL) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : u ∈ contMemberSubmodule L ΦL ξ) (r : AdelicGL2 (𝓞 L) L) :
    rightTranslate L r u ∈ contMemberSubmodule L ΦL ξ := by
  have hpos : 0 < (NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det r))⁻¹ :=
    inv_pos.mpr (NumberField.TateGlobal.ideleNorm_pos _)
  obtain ⟨z, -, hz⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one L _ (Real.sqrt_pos.mpr hpos)
  have hnorm : NumberField.TateGlobal.ideleNorm L
      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z * r)) = 1 := by
    rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, det_centralScalar_eq, NumberField.TateGlobal.ideleNorm_mul, hz,
      Real.mul_self_sqrt hpos.le, inv_mul_cancel₀ (NumberField.TateGlobal.ideleNorm_pos _).ne']
  have hmem := (CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one L hΦ 0 ξ u u
    hu hu (centralScalar (𝓞 L) L z * r) hnorm).1
  have hu' : u ∈ memberSubmodule L ΦL ξ ∧ Continuous u := hu
  have hcentral : IsLsXiFunction (𝓞 L) L ⊤ ξ u := ((isAutomorphicFnAt_fdPins_iff L ΦL ξ u).mp hu'.1).1
  have hcent : ∀ g : AdelicGL2 (𝓞 L) L,
      u (centralScalar (𝓞 L) L z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u g :=
    hcentral.central_transform ⟨z, Subgroup.mem_top z⟩
  have hrewrite : rightTranslate L r u
      = (((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))⁻¹ • rightTranslate L (centralScalar (𝓞 L) L z * r) u := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, rightTranslate_apply, rightTranslate_apply, ← mul_assoc,
      SiegelCovering.mul_centralScalar_comm, mul_assoc, hcent, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), one_mul]
  rw [hrewrite]
  exact (contMemberSubmodule L ΦL ξ).smul_mem _ hmem

private theorem rightTranslate_mem_cuspMemberSubmodule {α β : ℝ} {ΦL : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ : IsSlabFundamentalDomain L α β ΦL) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : u ∈ cuspMemberSubmodule L ΦL ξ) {r : AdelicGL2 (𝓞 L) L}
    (hr : r ∈ finiteAdelicGL2Subgroup L) : rightTranslate L r u ∈ cuspMemberSubmodule L ΦL ξ := by
  have hu' : IsSmoothCuspAutomorphicFnAt L (fdPins L ΦL) ξ u ∧ Continuous u := hu
  obtain ⟨⟨⟨hauto, hcusp⟩, hsmooth⟩, hcont⟩ := hu'
  have hmem : rightTranslate L r u ∈ memberSubmodule L ΦL ξ ∧ Continuous (rightTranslate L r u) :=
    rightTranslate_mem_contMemberSubmodule hΦ ξ (show u ∈ memberSubmodule L ΦL ξ ∧ Continuous u from ⟨hauto, hcont⟩) r
  show IsSmoothCuspAutomorphicFnAt L (fdPins L ΦL) ξ (rightTranslate L r u) ∧ Continuous (rightTranslate L r u)
  exact ⟨⟨⟨hmem.1, isCuspidalFn_rightTranslate _ _ hcusp r⟩, isKfSmooth_rightTranslate hsmooth hr⟩, hmem.2⟩

end Translate

section Sum

variable {L : Type} [Field L] [NumberField L]

private theorem placeEmbed_mem_finiteAdelicGL2Subgroup (w : HeightOneSpectrum (𝓞 L))
    (m : GL (Fin 2) (w.adicCompletion L)) :
    placeEmbed L w m ∈ finiteAdelicGL2Subgroup L :=
  (mem_finiteAdelicGL2Subgroup_iff L _).mpr (glArch_placeAt w m)

private theorem heckeCosetSum_eq_sum_rightTranslate {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 L) L)
    (u : AdelicGL2 (𝓞 L) L → ℂ) :
    (fun g => SmoothCusp.heckeCosetSum L reps u g) = ∑ i, rightTranslate L (reps i) u := by
  funext g
  simp only [SmoothCusp.heckeCosetSum, Finset.sum_apply, rightTranslate_apply]

private theorem heckeCosetSum_cosetFamily_mem_archCutSubmodule (tys : ArchTypeFamily L) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ archCutSubmodule L tys) (w : HeightOneSpectrum (𝓞 L)) :
    (fun g => SmoothCusp.heckeCosetSum L (cosetFamily w) u g) ∈ archCutSubmodule L tys := by
  rw [heckeCosetSum_eq_sum_rightTranslate]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨m, hm⟩ := exists_cosetFamily_eq_placeEmbed w i
  rw [hm]
  exact rightTranslate_placeEmbed_mem_archCutSubmodule tys hu w m

private theorem heckeCosetSum_cosetFamily_mem_cuspMemberSubmodule {α β : ℝ} {ΦL : Set (AdelicGL2 (𝓞 L) L)}
    (hΦ : IsSlabFundamentalDomain L α β ΦL) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : u ∈ cuspMemberSubmodule L ΦL ξ) (w : HeightOneSpectrum (𝓞 L)) :
    (fun g => SmoothCusp.heckeCosetSum L (cosetFamily w) u g) ∈ cuspMemberSubmodule L ΦL ξ := by
  rw [heckeCosetSum_eq_sum_rightTranslate]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨m, hm⟩ := exists_cosetFamily_eq_placeEmbed w i
  rw [hm]
  exact rightTranslate_mem_cuspMemberSubmodule hΦ ξ hu (placeEmbed_mem_finiteAdelicGL2Subgroup w m)

private theorem cosetFamily_mul_comm {v w : HeightOneSpectrum (𝓞 L)} (hvw : v ≠ w)
    (i : Fin (Ideal.absNorm v.asIdeal + 1)) (j : Fin (Ideal.absNorm w.asIdeal + 1)) :
    cosetFamily v i * cosetFamily w j = cosetFamily w j * cosetFamily v i := by
  obtain ⟨x, hx⟩ := exists_cosetFamily_eq_placeEmbed v i
  obtain ⟨y, hy⟩ := exists_cosetFamily_eq_placeEmbed w j
  rw [hx, hy]
  exact AdelicDock.finEmbed_localEmbed_comm_of_ne hvw x y

private theorem heckeCosetSum_cosetFamily_of_heckeCosetSum_eq {v w : HeightOneSpectrum (𝓞 L)} (hvw : v ≠ w)
    (u : AdelicGL2 (𝓞 L) L → ℂ) {c : ℂ} (hc : ∀ g, SmoothCusp.heckeCosetSum L (cosetFamily v) u g = c * u g)
    (g : AdelicGL2 (𝓞 L) L) :
    SmoothCusp.heckeCosetSum L (cosetFamily v) (fun g' => SmoothCusp.heckeCosetSum L (cosetFamily w) u g') g
      = c * SmoothCusp.heckeCosetSum L (cosetFamily w) u g := by
  simp only [SmoothCusp.heckeCosetSum] at hc ⊢
  rw [Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hc (g * cosetFamily w i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, cosetFamily_mul_comm hvw, ← mul_assoc]

private theorem heckeCosetSum_cosetFamily_mul_left_eq (w : HeightOneSpectrum (𝓞 L)) (u : AdelicGL2 (𝓞 L) L → ℂ)
    {z : AdelicGL2 (𝓞 L) L} {b : ℂ} (hb : ∀ g, u (z * g) = b * u g) (g : AdelicGL2 (𝓞 L) L) :
    SmoothCusp.heckeCosetSum L (cosetFamily w) u (z * g) = b * SmoothCusp.heckeCosetSum L (cosetFamily w) u g := by
  simp only [SmoothCusp.heckeCosetSum, Finset.mul_sum, mul_assoc, hb]

private theorem heckeCosetSum_cosetFamily_mem_isotypicCuspSubmodule_and_mem_archCutSubmodule {α β : ℝ}
    {ΦL : Set (AdelicGL2 (𝓞 L) L)} (hΦ : IsSlabFundamentalDomain L α β ΦL)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) {N N₀ : Ideal (𝓞 L)}
    (hle : levelOne (𝓞 L) L N ≤ levelOne (𝓞 L) L N₀) {S : Finset (HeightOneSpectrum (𝓞 L))}
    (hS : ∀ v : HeightOneSpectrum (𝓞 L), v ∉ S → ¬ v.asIdeal ∣ N) (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    {w : HeightOneSpectrum (𝓞 L)} (hwS : w ∈ S) (hw₀ : ¬ w.asIdeal ∣ N₀) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ cuspMemberSubmodule L ΦL ξ) (hut : u ∈ archCutSubmodule L tys)
    (hu₀ : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L, u (g * k) = u g)
    (hscal : ∀ v : HeightOneSpectrum (𝓞 L), v ∉ S →
      ∀ g : AdelicGL2 (𝓞 L) L, SmoothCusp.heckeCosetSum L (cosetFamily v) u g = Ψ.a v * u g)
    (hcent : ∀ v : HeightOneSpectrum (𝓞 L), v ∉ S → ∀ g : AdelicGL2 (𝓞 L) L,
      u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) * g) = Ψ.toRawCentral.b v * u g) :
    ((fun g => SmoothCusp.heckeCosetSum L (cosetFamily w) u g) ∈ isotypicCuspSubmodule L (fdPins L ΦL) ξ N S Ψ) ∧
      ((fun g => SmoothCusp.heckeCosetSum L (cosetFamily w) u g) ∈ archCutSubmodule L tys) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L,
        SmoothCusp.heckeCosetSum L (cosetFamily w) u (g * k) = SmoothCusp.heckeCosetSum L (cosetFamily w) u g) := by
  have hinv : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L,
      SmoothCusp.heckeCosetSum L (cosetFamily w) u (g * k) = SmoothCusp.heckeCosetSum L (cosetFamily w) u g :=
    fun g k hk => heckeCosetSum_cosetFamily_mul_eq hw₀ hu₀ g hk
  have hinvN : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      SmoothCusp.heckeCosetSum L (cosetFamily w) u (g * k) = SmoothCusp.heckeCosetSum L (cosetFamily w) u g :=
    fun g k hk => hinv g k (inf_le_inf_right _ hle hk)
  have hT : IsSmoothCuspAutomorphicFnAt L (fdPins L ΦL) ξ (fun g => SmoothCusp.heckeCosetSum L (cosetFamily w) u g) ∧
      Continuous (fun g => SmoothCusp.heckeCosetSum L (cosetFamily w) u g) :=
    heckeCosetSum_cosetFamily_mem_cuspMemberSubmodule hΦ ξ hu w
  refine ⟨?_, heckeCosetSum_cosetFamily_mem_archCutSubmodule tys hut w, hinv⟩
  refine IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule ?_
  refine { smoothCusp := hT.1, continuous := hT.2, level_invariant := hinvN, hecke_eigen := ?_, central_eigen := ?_ }
  · intro v hv
    refine (isHeckeCosetEigenfunctionAt_iff_forall (hS v hv) hinvN _).mpr fun g => ?_
    exact heckeCosetSum_cosetFamily_of_heckeCosetSum_eq (fun h => hv (by rw [h]; exact hwS)) u (hscal v hv) g
  · intro v hv g
    exact heckeCosetSum_cosetFamily_mul_left_eq w u (hcent v hv) g

end Sum

end

end AutomorphicForm.TwistedTraceRefinement

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

section TraceLayer

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private theorem isStableLinearOn_of_le {V V₀ : Submodule ℂ M} {T : M → M}
    (hV : IsStableLinearOn V T) (hle : V₀ ≤ V) (hmaps : ∀ u ∈ V₀, T u ∈ V₀) :
    IsStableLinearOn V₀ T where
  mapsTo := hmaps
  map_add u hu w hw := hV.map_add u (hle hu) w (hle hw)
  map_smul c u hu := hV.map_smul c u (hle hu)

private theorem traceOn_eq_traceOn_of_le {V V₀ : Submodule ℂ M} [FiniteDimensional ℂ V]
    {T : M → M}
    (hV : IsStableLinearOn V T) (hle : V₀ ≤ V) (himage : ∀ u ∈ V, T u ∈ V₀)
    (hV₀ : IsStableLinearOn V₀ T) : traceOn V T hV = traceOn V₀ T hV₀ := by
  let W : Submodule ℂ V := V₀.comap V.subtype
  have hW : ∀ x : V, hV.toEnd x ∈ W := fun x => himage x x.2
  let e : W ≃ₗ[ℂ] V₀ := Submodule.comapSubtypeEquivOfLe hle
  have hconj : hV₀.toEnd = e.conj (hV.toEnd.restrict fun x _ => hW x) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rfl
  rw [traceOn_eq, traceOn_eq, Module.End.EigenData.trace_eq_trace_restrict hV.toEnd W hW, hconj,
    LinearMap.trace_conj']

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem isInternal_comap_subtype {V₀ : Submodule ℂ M} (P : α → Submodule ℂ M)
    (hind : iSupIndep P) (hle : ∀ a, P a ≤ V₀) (hsup : V₀ ≤ ⨆ a, P a) :
    DirectSum.IsInternal fun a => (P a).comap V₀.subtype := by
  classical
  refine DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top ?_ ?_
  · intro a
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hxM : (x : M) ∈ ⨆ (b) (_ : b ≠ a), P b := by
      have hmem : (x : M) ∈ (⨆ (b) (_ : b ≠ a), (P b).comap V₀.subtype).map V₀.subtype :=
        Submodule.mem_map_of_mem hx'
      rw [Submodule.map_iSup] at hmem
      have hle : (⨆ b, ((⨆ (_ : b ≠ a), (P b).comap V₀.subtype).map V₀.subtype)) ≤
          ⨆ (b) (_ : b ≠ a), P b := by
        refine iSup_mono fun b => ?_
        rw [Submodule.map_iSup]
        exact iSup_mono fun _ => Submodule.map_comap_le _ _
      exact hle hmem
    exact Subtype.ext ((Submodule.disjoint_def.mp (hind a)) x hx hxM)
  · rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hcov : (⨆ a, P a) ≤ ⨆ a ∈ (Finset.univ : Finset α), P a :=
      iSup_le fun a => le_iSup₂ (f := fun a (_ : a ∈ (Finset.univ : Finset α)) => P a) a
        (Finset.mem_univ a)
    have hx' : x ∈ ⨆ a ∈ (Finset.univ : Finset α), P a := hcov (hsup hx)
    obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hx'
    have hmem : ∀ a, (⟨(μ a : M), hle a (μ a).2⟩ : V₀) ∈ (P a).comap V₀.subtype :=
      fun a => (μ a).2
    have : (⟨x, hx⟩ : V₀) = ∑ a, ⟨(μ a : M), hle a (μ a).2⟩ := by
      refine Subtype.ext ?_
      rw [Submodule.coe_sum]
      exact hμ.symm
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a (hmem a)

private theorem trace_restrict_comap_eq_traceOn {V₀ : Submodule ℂ M} {T : M → M}
    (hV₀ : IsStableLinearOn V₀ T) (P : Submodule ℂ M) (hle : P ≤ V₀)
    (hP : IsStableLinearOn P T)
    (hres : ∀ x ∈ P.comap V₀.subtype, hV₀.toEnd x ∈ P.comap V₀.subtype) :
    LinearMap.trace ℂ (P.comap V₀.subtype) (hV₀.toEnd.restrict hres) = traceOn P T hP := by
  let e : P.comap V₀.subtype ≃ₗ[ℂ] P := Submodule.comapSubtypeEquivOfLe hle
  have hconj : hP.toEnd = e.conj (hV₀.toEnd.restrict hres) := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rfl
  rw [traceOn_eq, hconj, LinearMap.trace_conj']

private theorem traceOn_eq_sum_traceOn {V₀ : Submodule ℂ M} [FiniteDimensional ℂ V₀]
    {T : M → M} (hV₀ : IsStableLinearOn V₀ T) (P : α → Submodule ℂ M) (hind : iSupIndep P)
    (hle : ∀ a, P a ≤ V₀) (hsup : V₀ ≤ ⨆ a, P a) (σ : α → Option α)
    (hT : ∀ a b, σ a = some b → ∀ x ∈ P a, T x ∈ P b)
    (hT0 : ∀ a, σ a = none → ∀ x ∈ P a, T x = 0)
    (hP : ∀ a, σ a = some a → IsStableLinearOn (P a) T) :
    traceOn V₀ T hV₀ =
      ∑ a : {a // σ a = some a}, traceOn (P a.1) T (hP a.1 a.2) := by
  classical
  have hint := isInternal_comap_subtype P hind hle hsup
  have hf : ∀ a b, σ a = some b → ∀ x ∈ (P a).comap V₀.subtype,
      hV₀.toEnd x ∈ (P b).comap V₀.subtype := fun a b hab x hx => hT a b hab x hx
  have hf0 : ∀ a, σ a = none → ∀ x ∈ (P a).comap V₀.subtype, hV₀.toEnd x = 0 :=
    fun a ha x hx => Subtype.ext (hT0 a ha x hx)
  rw [traceOn_eq, Module.End.EigenData.trace_eq_sum_trace_restrict_of_mapsTo
    (fun a => (P a).comap V₀.subtype) hint σ hV₀.toEnd hf hf0]
  refine Fintype.sum_congr _ _ fun a => ?_
  exact trace_restrict_comap_eq_traceOn hV₀ (P a.1) (hle a.1) (hP a.1 a.2) _

private theorem exists_finset_cover {β : Type*} {V₀ : Submodule ℂ M} [FiniteDimensional ℂ V₀]
    (P : β → Submodule ℂ M) (R : Set β) (hind : iSupIndep fun c : R => P c.1)
    (hincl : ∀ b ∈ R, P b ≤ V₀) (hcov : V₀ ≤ ⨆ (b : β) (_ : b ∈ R), P b) :
    ∃ C : Finset β, (∀ b ∈ C, b ∈ R) ∧ iSupIndep (fun a : C => P a.1) ∧
      (∀ a : C, P a.1 ≤ V₀) ∧ V₀ ≤ ⨆ a : C, P a.1 := by
  classical
  have hfin : {c : R | P c.1 ≠ ⊥}.Finite :=
    Module.End.EigenData.finite_ne_bot V₀ (fun c : R => P c.1) hind fun c => hincl c.1 c.2
  set C : Finset β := hfin.toFinset.image Subtype.val with hC
  have hCR : ∀ b ∈ C, b ∈ R := by
    intro b hb
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hb
    exact c.2
  have hmemC : ∀ b ∈ R, P b ≠ ⊥ → b ∈ C := fun b hb hbot =>
    Finset.mem_image.mpr ⟨⟨b, hb⟩, hfin.mem_toFinset.mpr hbot, rfl⟩
  refine ⟨C, hCR, ?_, fun a => hincl a.1 (hCR a.1 a.2), ?_⟩
  · exact hind.comp (f := fun a : C => (⟨a.1, hCR a.1 a.2⟩ : R)) fun a a' h =>
      Subtype.ext (by have h' := Subtype.ext_iff.mp h; exact h')
  · have hle : (⨆ (b : β) (_ : b ∈ R), P b) ≤ ⨆ a : C, P a.1 := by
      refine iSup₂_le fun b hb => ?_
      by_cases hbot : P b = ⊥
      · rw [hbot]
        exact bot_le
      · exact le_iSup (fun a : C => P a.1) ⟨b, hmemC b hb hbot⟩
    exact hcov.trans hle

private theorem traceOn_eq_sum_traceOn_attach {β : Type*} {V₀ : Submodule ℂ M}
    [FiniteDimensional ℂ V₀] {T : M → M} (hV₀ : IsStableLinearOn V₀ T) (C : Finset β)
    (P : β → Submodule ℂ M) (hind : iSupIndep fun a : C => P a.1) (hle : ∀ a : C, P a.1 ≤ V₀)
    (hsup : V₀ ≤ ⨆ a : C, P a.1) (σ : C → Option C)
    (hT : ∀ a b, σ a = some b → ∀ x ∈ P a.1, T x ∈ P b.1)
    (hT0 : ∀ a, σ a = none → ∀ x ∈ P a.1, T x = 0)
    (hP : ∀ a, σ a = some a → IsStableLinearOn (P a.1) T) :
    ∃ C₀ : Finset β, (∀ b ∈ C₀, ∃ h : b ∈ C, σ ⟨b, h⟩ = some ⟨b, h⟩) ∧
      ∀ hC₀ : ∀ b ∈ C₀, IsStableLinearOn (P b) T,
        traceOn V₀ T hV₀ = ∑ b ∈ C₀.attach, traceOn (P b.1) T (hC₀ b.1 b.2) := by
  classical
  have hsum := traceOn_eq_sum_traceOn hV₀ (fun a : C => P a.1) hind hle hsup σ hT hT0 hP
  set C₀ : Finset β := (Finset.univ.filter fun a : C => σ a = some a).image Subtype.val with hC₀
  have hfix_iff : ∀ b : β, b ∈ C₀ ↔ ∃ h : b ∈ C, σ ⟨b, h⟩ = some ⟨b, h⟩ := by
    intro b
    simp only [hC₀, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.2, ha⟩
    · rintro ⟨h, ha⟩
      exact ⟨⟨b, h⟩, ha, rfl⟩
  refine ⟨C₀, fun b hb => (hfix_iff b).mp hb, fun hC₀' => ?_⟩
  rw [hsum]
  exact Finset.sum_bij' (fun a _ => ⟨a.1.1, (hfix_iff a.1.1).mpr ⟨a.1.2, a.2⟩⟩)
    (fun x _ => ⟨⟨x.1, ((hfix_iff x.1).mp x.2).fst⟩, ((hfix_iff x.1).mp x.2).snd⟩)
    (fun a _ => Finset.mem_attach _ _) (fun x _ => Finset.mem_univ _)
    (fun a _ => Subtype.ext (Subtype.ext rfl)) (fun x _ => Subtype.ext rfl) fun a _ => rfl

end TraceLayer

end AutomorphicForm.TwistedTraceRefinement

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain

section Operators

variable {L : Type} [Field L] [NumberField L]

private noncomputable def rightInvariants (U : Subgroup (AdelicGL2 (𝓞 L) L)) :
    Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) where
  carrier := {u | ∀ g : AdelicGL2 (𝓞 L) L, ∀ x ∈ U, u (g * x) = u g}
  add_mem' {u v} hu hv g x hx := by simp only [Pi.add_apply, hu g x hx, hv g x hx]
  zero_mem' _ _ _ := rfl
  smul_mem' c {u} hu g x hx := by simp only [Pi.smul_apply, hu g x hx]

private theorem mem_rightInvariants_iff {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {u : AdelicGL2 (𝓞 L) L → ℂ} :
    u ∈ rightInvariants U ↔ ∀ g : AdelicGL2 (𝓞 L) L, ∀ x ∈ U, u (g * x) = u g :=
  Iff.rfl

private noncomputable def cosetOp {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 L) L) :
    Module.End ℂ (AdelicGL2 (𝓞 L) L → ℂ) where
  toFun u g := SmoothCusp.heckeCosetSum L reps u g
  map_add' u v := by
    funext g
    simp only [SmoothCusp.heckeCosetSum, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c u := by
    funext g
    simp only [SmoothCusp.heckeCosetSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      RingHom.id_apply]

private theorem cosetOp_apply {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 L) L)
    (u : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    cosetOp reps u g = SmoothCusp.heckeCosetSum L reps u g :=
  rfl

private noncomputable def leftOp (z : AdelicGL2 (𝓞 L) L) :
    Module.End ℂ (AdelicGL2 (𝓞 L) L → ℂ) where
  toFun u g := u (z * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem leftOp_apply (z : AdelicGL2 (𝓞 L) L) (u : AdelicGL2 (𝓞 L) L → ℂ)
    (g : AdelicGL2 (𝓞 L) L) : leftOp z u g = u (z * g) :=
  rfl

private noncomputable def centralAt (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L)
    (w : HeightOneSpectrum (𝓞 L)) : AdelicGL2 (𝓞 L) L :=
  centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (gen w))

private noncomputable def fullFamily (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L)
    (fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L)
    (S' : Finset (HeightOneSpectrum (𝓞 L))) :
    ({w // w ∉ S'} ⊕ {w // w ∉ S'}) → Module.End ℂ (AdelicGL2 (𝓞 L) L → ℂ) :=
  Sum.elim (fun w => cosetOp (fam w.1)) (fun w => leftOp (centralAt gen w.1))

private noncomputable def fullData (S' : Finset (HeightOneSpectrum (𝓞 L)))
    (π : HeckeEigensystem L ℂ) : ({w // w ∉ S'} ⊕ {w // w ∉ S'}) → ℂ :=
  Sum.elim (fun w => π.a w.1) (fun w => π.toRawCentral.b w.1)

private noncomputable def redFamily (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L)
    (fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L)
    (S S' : Finset (HeightOneSpectrum (𝓞 L))) :
    ({w // w ∉ S'} ⊕ {w // w ∉ S}) → Module.End ℂ (AdelicGL2 (𝓞 L) L → ℂ) :=
  Sum.elim (fun w => cosetOp (fam w.1)) (fun w => leftOp (centralAt gen w.1))

private noncomputable def redData (S S' : Finset (HeightOneSpectrum (𝓞 L)))
    (π : HeckeEigensystem L ℂ) : ({w // w ∉ S'} ⊕ {w // w ∉ S}) → ℂ :=
  Sum.elim (fun w => π.a w.1) (fun w => π.toRawCentral.b w.1)

private theorem mem_piece_fullFamily_iff
    {gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L}
    {fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L}
    {S' : Finset (HeightOneSpectrum (𝓞 L))} {π : HeckeEigensystem L ℂ}
    {u : AdelicGL2 (𝓞 L) L → ℂ} :
    u ∈ Module.End.EigenData.piece (fullFamily gen fam S') (fullData S' π) ↔
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ S' → ∀ g : AdelicGL2 (𝓞 L) L,
        SmoothCusp.heckeCosetSum L (fam w) u g = π.a w * u g) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ S' → ∀ g : AdelicGL2 (𝓞 L) L,
        u (centralAt gen w * g) = π.toRawCentral.b w * u g) := by
  rw [Module.End.EigenData.mem_piece, Sum.forall]
  refine and_congr ⟨fun h w hw g => ?_, fun h w => ?_⟩ ⟨fun h w hw g => ?_, fun h w => ?_⟩
  · exact congrFun (h ⟨w, hw⟩) g
  · exact funext fun g => h w.1 w.2 g
  · exact congrFun (h ⟨w, hw⟩) g
  · exact funext fun g => h w.1 w.2 g

private theorem mem_piece_redFamily_iff
    {gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L}
    {fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L}
    {S S' : Finset (HeightOneSpectrum (𝓞 L))} {π : HeckeEigensystem L ℂ}
    {u : AdelicGL2 (𝓞 L) L → ℂ} :
    u ∈ Module.End.EigenData.piece (redFamily gen fam S S') (redData S S' π) ↔
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ S' → ∀ g : AdelicGL2 (𝓞 L) L,
        SmoothCusp.heckeCosetSum L (fam w) u g = π.a w * u g) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → ∀ g : AdelicGL2 (𝓞 L) L,
        u (centralAt gen w * g) = π.toRawCentral.b w * u g) := by
  rw [Module.End.EigenData.mem_piece, Sum.forall]
  refine and_congr ⟨fun h w hw g => ?_, fun h w => ?_⟩ ⟨fun h w hw g => ?_, fun h w => ?_⟩
  · exact congrFun (h ⟨w, hw⟩) g
  · exact funext fun g => h w.1 w.2 g
  · exact congrFun (h ⟨w, hw⟩) g
  · exact funext fun g => h w.1 w.2 g

private theorem piece_fullFamily_le_piece_redFamily
    (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L)
    (fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L)
    {S S' : Finset (HeightOneSpectrum (𝓞 L))} (hS : S' ⊆ S) (π : HeckeEigensystem L ℂ) :
    Module.End.EigenData.piece (fullFamily gen fam S') (fullData S' π) ≤
      Module.End.EigenData.piece (redFamily gen fam S S') (redData S S' π) := by
  intro u hu
  obtain ⟨ha, hb⟩ := mem_piece_fullFamily_iff.mp hu
  exact mem_piece_redFamily_iff.mpr ⟨ha, fun w hw => hb w fun h => hw (hS h)⟩

end Operators

section ScalarAction

variable {L : Type} [Field L] [NumberField L]

private theorem isotypicCuspSubmodule_le_eigenspace_cosetOp (pins : CarrierPins L)
    (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (Ψ : HeckeEigensystem L ℂ) {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ S)
    {reps : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L}
    (hreps : HeckeIntegralSeam.IsHeckeCosetSystem (pins.U N) (pins.gen w) reps) :
    isotypicCuspSubmodule L pins ξ N S Ψ ≤ (cosetOp reps).eigenspace (Ψ.a w) := by
  rw [isotypicCuspSubmodule, Submodule.span_le]
  intro u hu
  have hu' : IsIsotypicCuspFormAt L pins ξ N S Ψ u := hu
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
  obtain ⟨reps₀, hsys₀, heig₀⟩ := hu'.hecke_eigen w hw
  funext g
  rw [cosetOp_apply, Pi.smul_apply, smul_eq_mul, ← heig₀ g]
  exact HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys₀ hreps
    (fun g x hx => hu'.level_invariant g x hx) g

private theorem isotypicCuspSubmodule_le_eigenspace_leftOp (pins : CarrierPins L)
    (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (Ψ : HeckeEigensystem L ℂ) {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ S) :
    isotypicCuspSubmodule L pins ξ N S Ψ ≤ (leftOp (centralAt pins.gen w)).eigenspace
      (Ψ.toRawCentral.b w) := by
  rw [isotypicCuspSubmodule, Submodule.span_le]
  intro u hu
  have hu' : IsIsotypicCuspFormAt L pins ξ N S Ψ u := hu
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
  funext g
  rw [leftOp_apply, Pi.smul_apply, smul_eq_mul]
  exact hu'.central_eigen w hw g

private theorem isotypicCuspSubmodule_inf_le_piece_fullFamily (pins : CarrierPins L)
    (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L)))
    (π : HeckeEigensystem L ℂ) (W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L)
    (hfam : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      HeckeIntegralSeam.IsHeckeCosetSystem (pins.U N) (pins.gen w) (fam w)) :
    isotypicCuspSubmodule L pins ξ N S π ⊓ W ≤
      Module.End.EigenData.piece (fullFamily pins.gen fam S) (fullData S π) := by
  intro u hu
  rw [Module.End.EigenData.mem_piece]
  rintro (⟨w, hw⟩ | ⟨w, hw⟩)
  · exact Module.End.mem_eigenspace_iff.mp
      (isotypicCuspSubmodule_le_eigenspace_cosetOp pins ξ N S π hw (hfam w hw) hu.1)
  · exact Module.End.mem_eigenspace_iff.mp
      (isotypicCuspSubmodule_le_eigenspace_leftOp pins ξ N S π hw hu.1)

end ScalarAction

section RefinedSubspace

variable {L : Type} [Field L] [NumberField L]

private theorem mapsTo_inf_rightInvariants {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)}
    {T : (AdelicGL2 (𝓞 L) L → ℂ) → (AdelicGL2 (𝓞 L) L → ℂ)} (hV : ∀ u ∈ V, T u ∈ V)
    {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    (hT : ∀ u : AdelicGL2 (𝓞 L) L → ℂ, ∀ g : AdelicGL2 (𝓞 L) L, ∀ x ∈ U, T u (g * x) = T u g) :
    ∀ u ∈ V, T u ∈ V ⊓ rightInvariants U :=
  fun u hu => Submodule.mem_inf.mpr ⟨hV u hu, fun g x hx => hT u g x hx⟩

private theorem heckeCosetSum_eq_of_mem_rightInvariants {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {gv : AdelicGL2 (𝓞 L) L} {n : ℕ} {reps reps' : Fin n → AdelicGL2 (𝓞 L) L}
    (hreps : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps)
    (hreps' : HeckeIntegralSeam.IsHeckeCosetSystem U gv reps')
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : u ∈ rightInvariants U) (g : AdelicGL2 (𝓞 L) L) :
    SmoothCusp.heckeCosetSum L reps' u g = SmoothCusp.heckeCosetSum L reps u g :=
  HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hreps hreps' hu g

end RefinedSubspace

section Refinement

variable {L : Type} [Field L] [NumberField L]

private noncomputable abbrev lvPins (D : Set (AdelicGL2 (𝓞 L) L)) : CarrierPins L :=
  productionPinsOf L D (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)

private theorem inf_rightInvariants_le_iSup (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (D : Set (AdelicGL2 (𝓞 L) L))
    (hDs : D ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hD : IsFundamentalDomain (globalPoints (𝓞 L) L).range D
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (N N₀ : Ideal (𝓞 L)) (hN₀ : N₀ ≠ ⊥)
    (S S' : Finset (HeightOneSpectrum (𝓞 L)))
    (hN₀S' : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N₀ → w ∈ S')
    (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L)
    (hfamN : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      HeckeIntegralSeam.IsHeckeCosetSystem ((lvPins D).U N) ((lvPins D).gen w) (fam w))
    (hfamN₀ : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S' →
      HeckeIntegralSeam.IsHeckeCosetSystem ((lvPins D).U N₀) ((lvPins D).gen w) (fam w))
    (hgen : ∀ u ∈ isotypicCuspSubmodule L (lvPins D) ξ N S Ψ,
      IsSmoothCuspAutomorphicFnAt L (lvPins D) ξ u)
    (hstabS : ∀ w ∈ S, w ∉ S' →
      ∀ u ∈ (isotypicCuspSubmodule L (lvPins D) ξ N S Ψ ⊓ archCutSubmodule L tys) ⊓
          rightInvariants ((lvPins D).U N₀),
        cosetOp (fam w) u ∈ (isotypicCuspSubmodule L (lvPins D) ξ N S Ψ ⊓ archCutSubmodule L tys) ⊓
          rightInvariants ((lvPins D).U N₀))
    [FiniteDimensional ℂ
      ↥(isotypicCuspSubmodule L (lvPins D) ξ N S Ψ ⊓ archCutSubmodule L tys)] :
    (isotypicCuspSubmodule L (lvPins D) ξ N S Ψ ⊓ archCutSubmodule L tys) ⊓
        rightInvariants ((lvPins D).U N₀) ≤
      ⨆ (π : HeckeEigensystem L ℂ) (_ : π ∈ cuspClasses L (lvPins D) ξ N₀ S'),
        isotypicCuspSubmodule L (lvPins D) ξ N₀ S' π ⊓ archCutSubmodule L tys := by
  set V := isotypicCuspSubmodule L (lvPins D) ξ N S Ψ ⊓ archCutSubmodule L tys with hV
  refine
    le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem
      L α β hα hαβ D hDs hD ξ N₀ hN₀ S' hN₀S' tys (V ⊓ rightInvariants ((lvPins D).U N₀))
      ?_ inferInstance ?_
  · intro x hx
    obtain ⟨hxV, hxU⟩ := Submodule.mem_inf.mp hx
    exact ⟨hgen x (Submodule.mem_inf.mp hxV).1, continuous_of_mem_isotypicCuspSubmodule_inf L x hxV,
      mem_rightInvariants_iff.mp hxU, (Submodule.mem_inf.mp hxV).2⟩
  · intro v hv reps hsys x hx
    obtain ⟨hxV, hxU⟩ := Submodule.mem_inf.mp hx
    have hsum : SmoothCusp.heckeCosetSum L reps x = cosetOp (fam v) x := by
      funext g
      rw [cosetOp_apply]
      exact heckeCosetSum_eq_of_mem_rightInvariants (hfamN₀ v hv) hsys hxU g
    rw [hsum]
    by_cases hvS : v ∈ S
    · exact hstabS v hvS hv x hx
    · have hsmul : cosetOp (fam v) x = Ψ.a v • x :=
        Module.End.mem_eigenspace_iff.mp
          (isotypicCuspSubmodule_le_eigenspace_cosetOp (lvPins D) ξ N S Ψ hvS (hfamN v hvS)
            (Submodule.mem_inf.mp hxV).1)
      rw [hsmul]
      exact Submodule.smul_mem _ _ hx

end Refinement

section StablePieces

variable {k : Type*} [Field k] {E : Type*} [AddCommGroup E] [Module k E] {ι : Type*}
  {T : ι → Module.End k E}

private theorem apply_mem_biSup_of_le_piece {β : Type*} (Q : β → Submodule k E) (d : β → ι → k)
    (hQ : ∀ b, Q b ≤ Module.End.EigenData.piece T (d b)) (F : Finset β) (i : ι) {x : E}
    (hx : x ∈ ⨆ b ∈ F, Q b) : T i x ∈ ⨆ b ∈ F, Q b := by
  classical
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hx
  rw [← hμ, map_sum]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hb' : T i (μ b : E) = d b i • (μ b : E) :=
    (Module.End.EigenData.mem_piece.mp (hQ b (μ b).2)) i
  rw [hb']
  exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem hb (μ b).2))

end StablePieces

section Components

variable {L : Type} [Field L] [NumberField L]

private theorem redFamily_apply_mem (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ)
    (N N₀ : Ideal (𝓞 L)) (S S' : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    (W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L)
    (hfamN : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      HeckeIntegralSeam.IsHeckeCosetSystem (pins.U N) (pins.gen w) (fam w))
    (hstabS : ∀ w ∈ S, w ∉ S' →
      ∀ u ∈ (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀),
        cosetOp (fam w) u ∈ (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀))
    (i : {w // w ∉ S'} ⊕ {w // w ∉ S}) :
    ∀ u ∈ (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀),
      redFamily pins.gen fam S S' i u ∈
        (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀) := by
  intro u hu
  have huI : u ∈ isotypicCuspSubmodule L pins ξ N S Ψ :=
    (Submodule.mem_inf.mp (Submodule.mem_inf.mp hu).1).1
  rcases i with ⟨w, hw⟩ | ⟨w, hw⟩
  · show cosetOp (fam w) u ∈ _
    by_cases hwS : w ∈ S
    · exact hstabS w hwS hw u hu
    · rw [Module.End.mem_eigenspace_iff.mp
        (isotypicCuspSubmodule_le_eigenspace_cosetOp pins ξ N S Ψ hwS (hfamN w hwS) huI)]
      exact Submodule.smul_mem _ _ hu
  · show leftOp (centralAt pins.gen w) u ∈ _
    rw [Module.End.mem_eigenspace_iff.mp
      (isotypicCuspSubmodule_le_eigenspace_leftOp pins ξ N S Ψ hw huI)]
    exact Submodule.smul_mem _ _ hu

private theorem eq_zero_of_mem_piece_redFamily (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 L)) (S S' : Finset (HeightOneSpectrum (𝓞 L))) (hS : S' ⊆ S)
    (Ψ : HeckeEigensystem L ℂ)
    (fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L)
    (hfamN : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      HeckeIntegralSeam.IsHeckeCosetSystem (pins.U N) (pins.gen w) (fam w))
    {χ : ({w // w ∉ S'} ⊕ {w // w ∉ S}) → ℂ}
    (hχ : ¬ ∀ w : HeightOneSpectrum (𝓞 L), ∀ hw : w ∉ S,
      χ (Sum.inl ⟨w, fun h => hw (hS h)⟩) = Ψ.a w ∧ χ (Sum.inr ⟨w, hw⟩) = Ψ.toRawCentral.b w)
    {x : AdelicGL2 (𝓞 L) L → ℂ} (hxI : x ∈ isotypicCuspSubmodule L pins ξ N S Ψ)
    (hx : x ∈ Module.End.EigenData.piece (redFamily pins.gen fam S S') χ) : x = 0 := by
  push Not at hχ
  obtain ⟨w, hw, hne⟩ := hχ
  have hpc := Module.End.EigenData.mem_piece.mp hx
  by_cases ha : χ (Sum.inl ⟨w, fun h => hw (hS h)⟩) = Ψ.a w
  · have hb : χ (Sum.inr ⟨w, hw⟩) ≠ Ψ.toRawCentral.b w := hne ha
    refine Module.End.EigenData.eq_zero_of_smul_eq_smul ?_ hb
    rw [← hpc (Sum.inr ⟨w, hw⟩)]
    exact Module.End.mem_eigenspace_iff.mp
      (isotypicCuspSubmodule_le_eigenspace_leftOp pins ξ N S Ψ hw hxI)
  · refine Module.End.EigenData.eq_zero_of_smul_eq_smul ?_ ha
    rw [← hpc (Sum.inl ⟨w, fun h => hw (hS h)⟩)]
    exact Module.End.mem_eigenspace_iff.mp
      (isotypicCuspSubmodule_le_eigenspace_cosetOp pins ξ N S Ψ hw (hfamN w hw) hxI)

private theorem refines_of_redData_eq {S S' : Finset (HeightOneSpectrum (𝓞 L))} (hS : S' ⊆ S)
    {Ψ π : HeckeEigensystem L ℂ}
    (h : ∀ w : HeightOneSpectrum (𝓞 L), ∀ hw : w ∉ S,
      redData S S' π (Sum.inl ⟨w, fun h => hw (hS h)⟩) = Ψ.a w ∧
        redData S S' π (Sum.inr ⟨w, hw⟩) = Ψ.toRawCentral.b w) :
    ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → π.a w = Ψ.a w ∧ π.b w = Ψ.b w := by
  intro w hw
  obtain ⟨ha, hb⟩ := h w hw
  refine ⟨ha, ?_⟩
  have hb' : (HeckeEigensystem.cNorm w)⁻¹ * π.b w = (HeckeEigensystem.cNorm w)⁻¹ * Ψ.b w := hb
  exact mul_left_cancel₀ (inv_ne_zero (HeckeEigensystem.cNorm_ne_zero w)) hb'

end Components

section RefiningCover

variable {L : Type} [Field L] [NumberField L]

private theorem inf_rightInvariants_le_iSup_refining (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ)
    (N N₀ : Ideal (𝓞 L)) (S S' : Finset (HeightOneSpectrum (𝓞 L))) (hS : S' ⊆ S)
    (Ψ : HeckeEigensystem L ℂ) (W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L)
    (hfamN : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      HeckeIntegralSeam.IsHeckeCosetSystem (pins.U N) (pins.gen w) (fam w))
    (hfamN₀ : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S' →
      HeckeIntegralSeam.IsHeckeCosetSystem (pins.U N₀) (pins.gen w) (fam w))
    (hstabS : ∀ w ∈ S, w ∉ S' →
      ∀ u ∈ (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀),
        cosetOp (fam w) u ∈ (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀))
    (hcover : (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀) ≤
      ⨆ (π : HeckeEigensystem L ℂ) (_ : π ∈ cuspClasses L pins ξ N₀ S'),
        isotypicCuspSubmodule L pins ξ N₀ S' π ⊓ W) :
    (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀) ≤
      ⨆ (π : HeckeEigensystem L ℂ) (_ : π ∈ cuspClasses L pins ξ N₀ S' ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → π.a w = Ψ.a w ∧ π.b w = Ψ.b w),
        isotypicCuspSubmodule L pins ξ N₀ S' π ⊓ W := by
  classical
  intro v hv
  set V₀ := (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀) with hV₀
  set P : HeckeEigensystem L ℂ → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) :=
    fun π => isotypicCuspSubmodule L pins ξ N₀ S' π ⊓ W with hP
  set C := cuspClasses L pins ξ N₀ S' with hC
  have h1 : v ∈ ⨆ c : C, P c.1 := by
    rw [iSup_subtype'']
    exact hcover hv
  obtain ⟨F, hF⟩ := Submodule.mem_iSup_iff_exists_finset.mp h1
  have hQ : ∀ c : C, P c.1 ≤ Module.End.EigenData.piece (redFamily pins.gen fam S S')
      (redData S S' c.1) := fun c =>
    (isotypicCuspSubmodule_inf_le_piece_fullFamily pins ξ N₀ S' c.1 W fam hfamN₀).trans
      (piece_fullFamily_le_piece_redFamily pins.gen fam hS c.1)
  set s : Finset (({w // w ∉ S'} ⊕ {w // w ∉ S}) → ℂ) := F.image fun c => redData S S' c.1
    with hs
  have hles : (⨆ c ∈ F, P c.1) ≤
      ⨆ χ ∈ s, Module.End.EigenData.piece (redFamily pins.gen fam S S') χ :=
    iSup₂_le fun c hc => (hQ c).trans
      (le_iSup₂ (f := fun χ (_ : χ ∈ s) =>
        Module.End.EigenData.piece (redFamily pins.gen fam S S') χ)
        (redData S S' c.1) (Finset.mem_image_of_mem _ hc))
  have hVs : ∀ i, ∀ x ∈ V₀ ⊓ ⨆ c ∈ F, P c.1,
      redFamily pins.gen fam S S' i x ∈ V₀ ⊓ ⨆ c ∈ F, P c.1 := fun i x hx =>
    Submodule.mem_inf.mpr
      ⟨redFamily_apply_mem pins ξ N N₀ S S' Ψ W fam hfamN hstabS i x (Submodule.mem_inf.mp hx).1,
        apply_mem_biSup_of_le_piece (fun c : C => P c.1) (fun c => redData S S' c.1) hQ F i
          (Submodule.mem_inf.mp hx).2⟩
  obtain ⟨p, hp, hsum⟩ := Module.End.EigenData.exists_sum_eq_of_mem
    (T := redFamily pins.gen fam S S') (V₀ ⊓ ⨆ c ∈ F, P c.1) hVs s
    (Submodule.mem_inf.mpr ⟨hv, hF⟩) (hles hF)
  rw [← hsum]
  refine Submodule.sum_mem _ fun χ hχ => ?_
  obtain ⟨hpV, hpχ⟩ := hp χ hχ
  obtain ⟨hpV₀, hpF⟩ := Submodule.mem_inf.mp hpV
  by_cases hmatch : ∀ w : HeightOneSpectrum (𝓞 L), ∀ hw : w ∉ S,
      χ (Sum.inl ⟨w, fun h => hw (hS h)⟩) = Ψ.a w ∧ χ (Sum.inr ⟨w, hw⟩) = Ψ.toRawCentral.b w
  · have hmem := Module.End.EigenData.mem_biSup_of_mem_piece
      (T := redFamily pins.gen fam S S') (fun c : C => P c.1) (fun c => redData S S' c.1) hQ F
      hpχ hpF
    have hle : (⨆ (c : C) (_ : c ∈ F) (_ : redData S S' c.1 = χ), P c.1) ≤
        ⨆ (π : HeckeEigensystem L ℂ) (_ : π ∈ C ∧
          ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → π.a w = Ψ.a w ∧ π.b w = Ψ.b w), P π := by
      refine iSup_le fun c => iSup_le fun _ => iSup_le fun hcχ => ?_
      have href : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → c.1.a w = Ψ.a w ∧ c.1.b w = Ψ.b w := by
        refine refines_of_redData_eq hS fun w hw => ?_
        rw [hcχ]
        exact hmatch w hw
      exact le_iSup_of_le c.1 (le_iSup_of_le ⟨c.2, href⟩ le_rfl)
    exact hle hmem
  · have hzero : p χ = 0 :=
      eq_zero_of_mem_piece_redFamily pins ξ N S S' hS Ψ fam hfamN hmatch
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hpV₀).1).1 hpχ
    rw [hzero]
    exact Submodule.zero_mem _

end RefiningCover

section BlockDecomposition

variable {L : Type} [Field L] [NumberField L]

private theorem eq_of_fullData_eq {pins : CarrierPins L} {ξ : pins.Z →* ℂˣ} {N₀ : Ideal (𝓞 L)}
    {S' : Finset (HeightOneSpectrum (𝓞 L))} {π π' : HeckeEigensystem L ℂ}
    (hπ : π ∈ cuspClasses L pins ξ N₀ S') (hπ' : π' ∈ cuspClasses L pins ξ N₀ S')
    (h : fullData S' π = fullData S' π') : π = π' := by
  refine eq_of_mem_cuspClasses hπ hπ' fun w hw => ?_
  have ha : π.a w = π'.a w := congrFun h (Sum.inl ⟨w, hw⟩)
  have hb : (HeckeEigensystem.cNorm w)⁻¹ * π.b w =
      (HeckeEigensystem.cNorm w)⁻¹ * π'.b w := congrFun h (Sum.inr ⟨w, hw⟩)
  exact ⟨ha, mul_left_cancel₀ (inv_ne_zero (HeckeEigensystem.cNorm_ne_zero w)) hb⟩

private theorem exists_finset_traceOn_eq_sum_traceOn (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ)
    (N N₀ : Ideal (𝓞 L)) (S S' : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    (W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (fam : ∀ w : HeightOneSpectrum (𝓞 L), Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L)
    (hfamN₀ : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S' →
      HeckeIntegralSeam.IsHeckeCosetSystem (pins.U N₀) (pins.gen w) (fam w))
    (T : (AdelicGL2 (𝓞 L) L → ℂ) → (AdelicGL2 (𝓞 L) L → ℂ))
    (hVT : IsStableLinearOn (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) T)
    (hTV₀ : ∀ u ∈ isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W,
      T u ∈ (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀))
    [FiniteDimensional ℂ ↥(isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W)]
    (R : Set (HeckeEigensystem L ℂ)) (hR : R ⊆ cuspClasses L pins ξ N₀ S')
    (hcov : (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀) ≤
      ⨆ (π : HeckeEigensystem L ℂ) (_ : π ∈ R), isotypicCuspSubmodule L pins ξ N₀ S' π ⊓ W)
    (hincl : ∀ π ∈ R, isotypicCuspSubmodule L pins ξ N₀ S' π ⊓ W ≤
      (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) ⊓ rightInvariants (pins.U N₀))
    (tw : HeckeEigensystem L ℂ → HeckeEigensystem L ℂ)
    (hT : ∀ π ∈ R, ∀ u ∈ isotypicCuspSubmodule L pins ξ N₀ S' π ⊓ W,
      T u ∈ Module.End.EigenData.piece (fullFamily pins.gen fam S') (fullData S' (tw π))) :
    ∃ C : Finset (HeckeEigensystem L ℂ), (↑C : Set (HeckeEigensystem L ℂ)) ⊆ R ∧
      (∀ Ψ' ∈ C, fullData S' (tw Ψ') = fullData S' Ψ') ∧
      (∀ Ψ' ∈ C, ∀ u ∈ isotypicCuspSubmodule L pins ξ N₀ S' Ψ' ⊓ W,
        T u ∈ isotypicCuspSubmodule L pins ξ N₀ S' Ψ' ⊓ W) ∧
      ∀ hC : ∀ Ψ' ∈ C, IsStableLinearOn (isotypicCuspSubmodule L pins ξ N₀ S' Ψ' ⊓ W) T,
        traceOn (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W) T hVT =
          ∑ Ψ' ∈ C.attach, traceOn (isotypicCuspSubmodule L pins ξ N₀ S' Ψ'.1 ⊓ W) T (hC Ψ'.1 Ψ'.2) := by
  classical
  set V := isotypicCuspSubmodule L pins ξ N S Ψ ⊓ W with hV
  set V₀ := V ⊓ rightInvariants (pins.U N₀) with hV₀
  set P : HeckeEigensystem L ℂ → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) :=
    fun π => isotypicCuspSubmodule L pins ξ N₀ S' π ⊓ W with hP

  have hPpiece : ∀ π : HeckeEigensystem L ℂ,
      P π ≤ Module.End.EigenData.piece (fullFamily pins.gen fam S') (fullData S' π) := fun π =>
    isotypicCuspSubmodule_inf_le_piece_fullFamily pins ξ N₀ S' π W fam hfamN₀
  have hinj : ∀ c c' : R, fullData S' c.1 = fullData S' c'.1 → c = c' := fun c c' h =>
    Subtype.ext (eq_of_fullData_eq (hR c.2) (hR c'.2) h)
  have hind : iSupIndep fun c : R => P c.1 :=
    ((Module.End.EigenData.piece_iSupIndep (T := fullFamily pins.gen fam S')).comp
      (f := fun c : R => fullData S' c.1) fun c c' h => hinj c c' h).mono fun c => hPpiece c.1

  obtain ⟨C, hCR, hindC, hleC, hsupC⟩ :=
    exists_finset_cover (V₀ := V₀) P R hind (fun π hπ => hincl π hπ) hcov
  have hsupC' : (⨆ a : C, P a.1) ≤ ⨆ a ∈ (Finset.univ : Finset C), P a.1 :=
    iSup_le fun a => le_iSup₂ (f := fun a (_ : a ∈ (Finset.univ : Finset C)) => P a.1) a
      (Finset.mem_univ a)

  set f : C → Option C := fun a =>
    if h : ∃ b : C, fullData S' b.1 = fullData S' (tw a.1) then some h.choose else none with hf
  have hf_some : ∀ a b : C, f a = some b → fullData S' b.1 = fullData S' (tw a.1) := by
    intro a b hab
    simp only [hf] at hab
    by_cases h : ∃ b : C, fullData S' b.1 = fullData S' (tw a.1)
    · rw [dif_pos h] at hab
      rw [← Option.some.inj hab]
      exact h.choose_spec
    · rw [dif_neg h] at hab
      cases hab
  have hf_none : ∀ a : C, f a = none → ∀ b : C, fullData S' b.1 ≠ fullData S' (tw a.1) := by
    intro a ha b hb
    simp only [hf] at ha
    by_cases h : ∃ b : C, fullData S' b.1 = fullData S' (tw a.1)
    · rw [dif_pos h] at ha
      cases ha
    · exact h ⟨b, hb⟩

  have hTimg : ∀ a : C, ∀ x ∈ P a.1, T x ∈ ⨆ (b : C) (_ : b ∈ (Finset.univ : Finset C))
      (_ : fullData S' b.1 = fullData S' (tw a.1)), P b.1 := by
    intro a x hx
    have hTx := hT a.1 (hCR a.1 a.2) x hx
    have hTV : T x ∈ V₀ := hTV₀ x (Submodule.mem_inf.mp (hleC a hx)).1
    exact Module.End.EigenData.mem_biSup_of_mem_piece (T := fullFamily pins.gen fam S')
      (fun b : C => P b.1) (fun b => fullData S' b.1) (fun b => hPpiece b.1) Finset.univ hTx
      (hsupC' (hsupC hTV))
  have hTs : ∀ a b : C, f a = some b → ∀ x ∈ P a.1, T x ∈ P b.1 := by
    intro a b hab x hx
    have hle : (⨆ (b' : C) (_ : b' ∈ (Finset.univ : Finset C))
        (_ : fullData S' b'.1 = fullData S' (tw a.1)), P b'.1) ≤ P b.1 := by
      refine iSup_le fun b' => iSup_le fun _ => iSup_le fun hb' => ?_
      have hRb := hinj ⟨b'.1, hCR b'.1 b'.2⟩ ⟨b.1, hCR b.1 b.2⟩ (hb'.trans (hf_some a b hab).symm)
      have hbb : b' = b := Subtype.ext (by have h' := Subtype.ext_iff.mp hRb; exact h')
      rw [hbb]
    exact hle (hTimg a x hx)
  have hT0 : ∀ a : C, f a = none → ∀ x ∈ P a.1, T x = 0 := by
    intro a ha x hx
    have hle : (⨆ (b' : C) (_ : b' ∈ (Finset.univ : Finset C))
        (_ : fullData S' b'.1 = fullData S' (tw a.1)), P b'.1) ≤ ⊥ :=
      iSup_le fun b' => iSup_le fun _ => iSup_le fun hb' => absurd hb' (hf_none a ha b')
    exact (Submodule.mem_bot ℂ).mp (hle (hTimg a x hx))
  have hV₀T : IsStableLinearOn V₀ T :=
    isStableLinearOn_of_le hVT inf_le_left fun u hu => hTV₀ u (Submodule.mem_inf.mp hu).1
  have hPT : ∀ a : C, f a = some a → IsStableLinearOn (P a.1) T := fun a ha =>
    isStableLinearOn_of_le hVT ((hleC a).trans inf_le_left) (hTs a a ha)
  have htr : traceOn V T hVT = traceOn V₀ T hV₀T :=
    traceOn_eq_traceOn_of_le hVT inf_le_left hTV₀ hV₀T

  obtain ⟨Cfix, hfix, hsum⟩ :=
    traceOn_eq_sum_traceOn_attach hV₀T C P hindC hleC hsupC f hTs hT0 hPT
  refine ⟨Cfix, fun Ψ' hΨ' => hCR Ψ' (hfix Ψ' hΨ').fst, fun Ψ' hΨ' => ?_, fun Ψ' hΨ' => ?_,
    fun hCst => ?_⟩
  · obtain ⟨h, ha⟩ := hfix Ψ' hΨ'
    exact (hf_some ⟨Ψ', h⟩ ⟨Ψ', h⟩ ha).symm
  · obtain ⟨h, ha⟩ := hfix Ψ' hΨ'
    exact hTs ⟨Ψ', h⟩ ⟨Ψ', h⟩ ha
  · rw [htr]
    exact hsum hCst

end BlockDecomposition

end AutomorphicForm.TwistedTraceRefinement

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsBiInvariantUnder IsIsotypicCuspFormAt isotypicCuspSubmodule IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule cuspClasses eq_of_mem_cuspClasses IsStableLinearOn traceOn traceOn_eq continuous_sigmaSectionActOn twistedConvOp twistedConvOp_apply twistedConvOp_smul twistedConvOp_add isStableLinearOn_twistedConvOp twistedConvTraceOn_eq_traceOn comp_mul_mem_typeSubmodule_of_commute rowIsometryInclAt₀ archTypeSubmoduleAt ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff glFin_rowIsometryInclAt₀ continuous_of_mem_isotypicCuspSubmodule_inf twistedCutTrace twistedCutTrace_eq mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt constantTermIntegrand constantTerm IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.cNorm_ne_zero HeckeEigensystem.toRawCentral_b SmoothCusp.heckeCosetSum SmoothCusp.IsHeckeCosetEigenfunctionAt HeckeEigensystem SiegelCovering.mul_centralScalar_comm rightConv rightConv_apply sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul rowIsometrySubgroup₀ CuspidalSpectrum.IsSlabFundamentalDomain CuspidalSpectrum.cuspMemberSubmodule rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one le_iSup_isotypicCuspSubmodule_inf_archCutSubmodule_of_finiteDimensional_of_forall_heckeCosetSum_mem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd"
namespace TwistedTraceRefinement
p2m_open "AutomorphicForm"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped NumberField.PlaceTransport

section Concrete

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private noncomputable def twistTable (σ : L ≃ₐ[K] L) (π : HeckeEigensystem L ℂ) :
    HeckeEigensystem L ℂ where
  level := π.level
  level_ne_bot := π.level_ne_bot
  a := fun w => π.a (σ • w)
  b := fun w => π.b (σ • w)

omit [NumberField K] in
private theorem twistTable_a (σ : L ≃ₐ[K] L) (π : HeckeEigensystem L ℂ) (w : HeightOneSpectrum (𝓞 L)) :
    (twistTable σ π).a w = π.a (σ • w) :=
  rfl

omit [NumberField K] in
private theorem twistTable_toRawCentral_b (σ : L ≃ₐ[K] L) (π : HeckeEigensystem L ℂ)
    (w : HeightOneSpectrum (𝓞 L)) :
    (twistTable σ π).toRawCentral.b w = π.toRawCentral.b (σ • w) := by
  show (HeckeEigensystem.cNorm w)⁻¹ * π.b (σ • w) = (HeckeEigensystem.cNorm (σ • w))⁻¹ * π.b (σ • w)
  rw [HeckeEigensystem.cNorm, HeckeEigensystem.cNorm, absNorm_smul]

omit [NumberField K] in

private theorem fullData_twistTable_eq_iff (σ : L ≃ₐ[K] L) (S' : Finset (HeightOneSpectrum (𝓞 L)))
    (π : HeckeEigensystem L ℂ) :
    fullData S' (twistTable σ π) = fullData S' π ↔
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S' → π.a (σ • w) = π.a w ∧ π.b (σ • w) = π.b w := by
  constructor
  · intro h w hw
    have ha : π.a (σ • w) = π.a w := congrFun h (Sum.inl ⟨w, hw⟩)
    have hb : (HeckeEigensystem.cNorm w)⁻¹ * π.b (σ • w) =
        (HeckeEigensystem.cNorm w)⁻¹ * π.b w := congrFun h (Sum.inr ⟨w, hw⟩)
    exact ⟨ha, mul_left_cancel₀ (inv_ne_zero (HeckeEigensystem.cNorm_ne_zero w)) hb⟩
  · intro h
    funext i
    rcases i with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact (h w hw).1
    · show (HeckeEigensystem.cNorm w)⁻¹ * π.b (σ • w) = (HeckeEigensystem.cNorm w)⁻¹ * π.b w
      rw [(h w hw).2]

private theorem isotypicCuspSubmodule_inf_le_refined (D : Set (AdelicGL2 (𝓞 L) L))
    (ξ : (lvPins D).Z →* ℂˣ) {N N₀ : Ideal (𝓞 L)} (hN : N ≠ ⊥) (hN₀N : N₀ ∣ N)
    {S S' : Finset (HeightOneSpectrum (𝓞 L))} (hS : S' ⊆ S)
    (hNS : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ S)
    (hN₀S' : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N₀ → w ∈ S')
    (Ψ : HeckeEigensystem L ℂ) {π : HeckeEigensystem L ℂ}
    (href : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S → π.a w = Ψ.a w ∧ π.b w = Ψ.b w)
    (W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)) :
    isotypicCuspSubmodule L (lvPins D) ξ N₀ S' π ⊓ W ≤
      (isotypicCuspSubmodule L (lvPins D) ξ N S Ψ ⊓ W) ⊓ rightInvariants ((lvPins D).U N₀) := by
  have hUle : (lvPins D).U N ≤ (lvPins D).U N₀ :=
    inf_le_inf_right (finiteAdelicGL2Subgroup L) (levelOne_le_levelOne_of_dvd L hN hN₀N)
  have hgen : ∀ u : AdelicGL2 (𝓞 L) L → ℂ, IsIsotypicCuspFormAt L (lvPins D) ξ N₀ S' π u →
      IsIsotypicCuspFormAt L (lvPins D) ξ N S Ψ u := by
    intro u h
    refine
      { smoothCusp := h.smoothCusp
        continuous := h.continuous
        level_invariant := fun g x hx => h.level_invariant g x (hUle hx)
        hecke_eigen := fun w hwS => ?_
        central_eigen := fun w hwS g => ?_ }
    · have hw' : w ∉ S' := fun hw => hwS (hS hw)
      have hwN : ¬ w.asIdeal ∣ N := fun hw => hwS (hNS w hw)
      have hwN₀ : ¬ w.asIdeal ∣ N₀ := fun hw => hw' (hN₀S' w hw)
      have h1 := (isHeckeCosetEigenfunctionAt_iff_forall hwN₀ h.level_invariant (π.a w)).mp
        (h.hecke_eigen w hw')
      rw [(href w hwS).1] at h1
      exact (isHeckeCosetEigenfunctionAt_iff_forall hwN
        (fun g x hx => h.level_invariant g x (hUle hx)) (Ψ.a w)).mpr h1
    · have hw' : w ∉ S' := fun hw => hwS (hS hw)
      have hb : π.toRawCentral.b w = Ψ.toRawCentral.b w := by
        show (HeckeEigensystem.cNorm w)⁻¹ * π.b w = (HeckeEigensystem.cNorm w)⁻¹ * Ψ.b w
        rw [(href w hwS).2]
      rw [← hb]
      exact h.central_eigen w hw' g
  intro u hu
  obtain ⟨huπ, huW⟩ := Submodule.mem_inf.mp hu
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, huW⟩, ?_⟩
  · have hle : isotypicCuspSubmodule L (lvPins D) ξ N₀ S' π ≤
        isotypicCuspSubmodule L (lvPins D) ξ N S Ψ := by
      rw [isotypicCuspSubmodule, Submodule.span_le]
      intro v hv
      exact Submodule.subset_span (hgen v hv)
    exact hle huπ
  · have hle : isotypicCuspSubmodule L (lvPins D) ξ N₀ S' π ≤ rightInvariants ((lvPins D).U N₀) := by
      rw [isotypicCuspSubmodule, Submodule.span_le]
      intro v hv
      have hv' : IsIsotypicCuspFormAt L (lvPins D) ξ N₀ S' π v := hv
      exact mem_rightInvariants_iff.mpr hv'.level_invariant
    exact hle huπ

private theorem twistedConvOp_mem_piece_fullFamily (Dd : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L) (D : Set (AdelicGL2 (𝓞 L) L)) (ξ : (lvPins D).Z →* ℂˣ) {N₀ : Ideal (𝓞 L)}
    {S' : Finset (HeightOneSpectrum (𝓞 L))} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    (hS'σ : ∀ w : HeightOneSpectrum (𝓞 L), σ • w ∈ S' ↔ w ∈ S')
    (hS'K : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ S' ↔ HeightOneSpectrum.under (𝓞 K) w ∈ SK)
    (hb₀ : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S' → idealBound (𝓞 L) N₀ w = 1)
    {tys : ArchTypeFamily L} {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tys
      (levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (π : HeckeEigensystem L ℂ) (W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)) :
    ∀ u ∈ isotypicCuspSubmodule L (lvPins D) ξ N₀ S' π ⊓ W,
      twistedConvOp K L Dd σ φ u ∈
        Module.End.EigenData.piece (fullFamily (lvPins D).gen (fun w => cosetFamily w) S')
          (fullData S' (twistTable σ π)) := by
  intro u hu
  have huπ : u ∈ isotypicCuspSubmodule L (lvPins D) ξ N₀ S' π := (Submodule.mem_inf.mp hu).1
  rw [isotypicCuspSubmodule] at huπ
  refine Submodule.span_induction
    (p := fun u _ => twistedConvOp K L Dd σ φ u ∈
      Module.End.EigenData.piece (fullFamily (lvPins D).gen (fun w => cosetFamily w) S')
        (fullData S' (twistTable σ π))) ?_ ?_ ?_ ?_ huπ
  · intro u₀ hu₀
    have h : IsIsotypicCuspFormAt L (lvPins D) ξ N₀ S' π u₀ := hu₀
    refine mem_piece_fullFamily_iff.mpr ⟨fun w hw g => ?_, fun w hw g => ?_⟩
    · have hσw : σ • w ∉ S' := fun h' => hw ((hS'σ w).mp h')
      have hwK : HeightOneSpectrum.under (𝓞 K) w ∉ SK := fun h' => hw ((hS'K w).mpr h')
      rw [twistTable_a]
      exact (twistedConvOp_eigenData_of_isIsotypicCuspFormAt Dd σ D ξ h hσw (hb₀ (σ • w) hσw) hφ hφc
        (fun M hb => isHeckeCosetSystem_cosetFamily_of_idealBound_eq_one w hb)
        (exists_cosetFamily_eq_placeEmbed w)
        (fun M hb kv => placeEmbed_map_mem_of_idealBound_eq_one hb kv)
        (fun M hb z hz => exists_eq_mul_of_ne_zero hφt hwK hb z hz)).1 g
    · have hσw : σ • w ∉ S' := fun h' => hw ((hS'σ w).mp h')
      have hwK : HeightOneSpectrum.under (𝓞 K) w ∉ SK := fun h' => hw ((hS'K w).mpr h')
      rw [twistTable_toRawCentral_b]
      exact (twistedConvOp_eigenData_of_isIsotypicCuspFormAt Dd σ D ξ h hσw (hb₀ (σ • w) hσw) hφ hφc
        (fun M hb => isHeckeCosetSystem_cosetFamily_of_idealBound_eq_one w hb)
        (exists_cosetFamily_eq_placeEmbed w)
        (fun M hb kv => placeEmbed_map_mem_of_idealBound_eq_one hb kv)
        (fun M hb z hz => exists_eq_mul_of_ne_zero hφt hwK hb z hz)).2 g
  · have h0 : twistedConvOp K L Dd σ φ 0 = 0 := by
      rw [show (0 : AdelicGL2 (𝓞 L) L → ℂ) = (0 : ℂ) • (0 : AdelicGL2 (𝓞 L) L → ℂ) from
        (zero_smul ℂ _).symm, twistedConvOp_smul, zero_smul, zero_smul]
    show twistedConvOp K L Dd σ φ 0 ∈ _
    rw [h0]
    exact Submodule.zero_mem _
  · intro x y hx hy hpx hpy
    rw [twistedConvOp_add K L Dd σ hφ hφc (continuous_of_mem_isotypicCuspSubmodule hx)
      (continuous_of_mem_isotypicCuspSubmodule hy)]
    exact Submodule.add_mem _ hpx hpy
  · intro c x hx hpx
    rw [twistedConvOp_smul]
    exact Submodule.smul_mem _ c hpx

end Concrete

end AutomorphicForm.TwistedTraceRefinement

open scoped NumberField.PlaceTransport in
open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime.AutomorphicForm AutomorphicForm.TwistedTraceRefinement in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆
      {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 L)) (tysL : ArchTypeFamily L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφt : IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : twistedCutTrace K L D σ
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc ≠ 0) :
    ∃ (SL' : Finset (HeightOneSpectrum (𝓞 L))) (N₀ : Ideal (𝓞 L)) (C : Finset (HeckeEigensystem L ℂ)),
      (∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL' ↔ HeightOneSpectrum.under (𝓞 K) w ∈ SK) ∧
      (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N₀ → w ∈ SL') ∧
      IsUnitFactorizableAboveOfType K L tysL (levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L) SK φ ∧
      (∀ Ψ' ∈ C,
        Ψ' ∈ cuspClasses L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N₀ SL' ∧
        (∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → Ψ'.a w = Ψ.a w ∧ Ψ'.b w = Ψ.b w) ∧
        (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL' → w' ∉ SL' →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' →
            (Ψ'.a w, Ψ'.b w) = (Ψ'.a w', Ψ'.b w'))) ∧
      twistedCutTrace K L D σ
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc =
        ∑ Ψ' ∈ C, twistedCutTrace K L D σ
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N₀ SL' Ψ' tysL φ hφ hφc := by
  classical

  obtain ⟨hmaps, hVne⟩ := mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero K L D hΨ
  have hst := isStableLinearOn_twistedConvOp K L D σ (continuous_of_mem_isotypicCuspSubmodule_inf L)
    hφ hφc hmaps
  have htr : twistedCutTrace K L D σ
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ tysL φ hφ hφc =
      traceOn _ _ hst := by
    rw [twistedCutTrace_eq, twistedConvTraceOn_eq_traceOn K L D σ _ hφ hφc hmaps]
  have hΨ' : traceOn _ _ hst ≠ 0 := by
    rw [← htr]
    exact hΨ
  haveI := Module.End.EigenData.finiteDimensional_of_trace_ne_zero hst.toEnd hΨ'

  have hNbot : N ≠ ⊥ := by
    rintro rfl
    apply hVne
    rw [isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf L ΦL (adelicBox L) ξL SL Ψ, bot_inf_eq]
  have hNS : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL := by
    intro w hw
    by_contra hwS
    apply hVne
    rw [isotypicCuspSubmodule_productionPinsOf_levelOne_eq_bot_of_dvd L w ΦL (adelicBox L) ξL N SL Ψ
      hwS hw, bot_inf_eq]

  let SL' : Finset (HeightOneSpectrum (𝓞 L)) := primesOverFinset SK SL
  have hSL'K : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL' ↔ HeightOneSpectrum.under (𝓞 K) w ∈ SK :=
    mem_primesOverFinset_iff hSL
  have hSL'sub : SL' ⊆ SL := primesOverFinset_subset SK SL
  have hσSL' : ∀ w : HeightOneSpectrum (𝓞 L), σ • w ∈ SL' ↔ w ∈ SL' :=
    smul_mem_primesOverFinset_iff hSL σ
  have hcovK : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∈ SK → w ∈ SL' :=
    fun w h => (hSL'K w).mpr h
  let N₀ : Ideal (𝓞 L) := supportedPart N SL'
  have hN₀bot : N₀ ≠ ⊥ := supportedPart_ne_bot hNbot SL'
  have hN₀N : N₀ ∣ N := supportedPart_dvd hNbot SL'
  have hN₀S' : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N₀ → w ∈ SL' :=
    fun w hw => mem_of_dvd_supportedPart hw
  have hb₀ : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL' → idealBound (𝓞 L) N₀ w = 1 :=
    fun w hw => idealBound_supportedPart_of_not_mem hNbot hw
  have hbS' : ∀ w ∈ SL', idealBound (𝓞 L) N₀ w = idealBound (𝓞 L) N w :=
    fun w hw => idealBound_supportedPart_of_mem hNbot hw
  have hle : levelOne (𝓞 L) L N ≤ levelOne (𝓞 L) L N₀ := levelOne_le_levelOne_of_dvd L hNbot hN₀N
  have hΦd : AutomorphicForm.CuspidalSpectrum.IsSlabFundamentalDomain L α β ΦL := ⟨hα, hαβ, hΦs, hΦ⟩

  have h3 : IsUnitFactorizableAboveOfType K L tysL
      (levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L) SK φ :=
    isUnitFactorizableAboveOfType_of_refined hφt hle hbS' hcovK

  have hTinv : ∀ u : AdelicGL2 (𝓞 L) L → ℂ, ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L,
        twistedConvOp K L D σ φ u (g * k) = twistedConvOp K L D σ φ u g := fun u g k hk => by
    rw [twistedConvOp_apply]
    exact rightConv_mul_eq_of_refined hφt hle hbS' hcovK _ g hk
  have hTV₀ := mapsTo_inf_rightInvariants hmaps
    (U := (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).U N₀) hTinv

  have hfamN : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
        (heckeGen (𝓞 L) L w) (cosetFamily w) :=
    fun w hw => isHeckeCosetSystem_cosetFamily w fun h => hw (hNS w h)
  have hfamN₀ : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL' →
      HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 L) L N₀ ⊓ finiteAdelicGL2Subgroup L)
        (heckeGen (𝓞 L) L w) (cosetFamily w) :=
    fun w hw => isHeckeCosetSystem_cosetFamily w fun h => hw (hN₀S' w h)

  have hstabS : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL → w ∉ SL' →
      ∀ u ∈ (isotypicCuspSubmodule L (lvPins ΦL) ξL N SL Ψ ⊓ archCutSubmodule L tysL) ⊓
        rightInvariants ((lvPins ΦL).U N₀),
        cosetOp (cosetFamily w) u ∈ (isotypicCuspSubmodule L (lvPins ΦL) ξL N SL Ψ ⊓
          archCutSubmodule L tysL) ⊓ rightInvariants ((lvPins ΦL).U N₀) := by
    intro w hwS hwS' u hu
    obtain ⟨hu₁, hri⟩ := Submodule.mem_inf.mp hu
    obtain ⟨hiso, hcut⟩ := Submodule.mem_inf.mp hu₁
    have hscal : ∀ v : HeightOneSpectrum (𝓞 L), v ∉ SL →
        ∀ g : AdelicGL2 (𝓞 L) L, SmoothCusp.heckeCosetSum L (cosetFamily v) u g = Ψ.a v * u g := by
      intro v hv g
      have h := congrFun (Module.End.mem_eigenspace_iff.mp
        (isotypicCuspSubmodule_le_eigenspace_cosetOp (lvPins ΦL) ξL N SL Ψ hv (hfamN v hv) hiso)) g
      simpa only [cosetOp_apply, Pi.smul_apply, smul_eq_mul] using h
    have hcent : ∀ v : HeightOneSpectrum (𝓞 L), v ∉ SL → ∀ g : AdelicGL2 (𝓞 L) L,
        u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L v)) * g) =
          Ψ.toRawCentral.b v * u g := by
      intro v hv g
      have h := congrFun (Module.End.mem_eigenspace_iff.mp
        (isotypicCuspSubmodule_le_eigenspace_leftOp (lvPins ΦL) ξL N SL Ψ hv hiso)) g
      first
        | simpa only [leftOp_apply, centralAt, Pi.smul_apply, smul_eq_mul] using h
        | (simpa only [leftOp_apply, centralAt, Pi.smul_apply, smul_eq_mul] using (h :)) | (simpa [Function.comp_def] using h) | exact h | (have h__ := h; (try simp only [leftOp_apply, centralAt, Pi.smul_apply, smul_eq_mul] at h__); (try simp only [leftOp_apply, centralAt, Pi.smul_apply, smul_eq_mul]); exact h__)
    obtain ⟨h₁, h₂, h₃⟩ :=
      heckeCosetSum_cosetFamily_mem_isotypicCuspSubmodule_and_mem_archCutSubmodule hΦd ξL hle
        (fun v hv h => hv (hNS v h)) Ψ tysL hwS (fun h => hwS' (hN₀S' w h))
        (show u ∈ AutomorphicForm.CuspidalSpectrum.cuspMemberSubmodule L ΦL ξL from
          ⟨isSmoothCuspAutomorphicFnAt_of_mem_isotypicCuspSubmodule ΦL ξL N SL Ψ hiso,
            continuous_of_mem_isotypicCuspSubmodule hiso⟩)
        hcut (mem_rightInvariants_iff.mp hri) hscal hcent
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨h₁, h₂⟩, mem_rightInvariants_iff.mpr h₃⟩

  have hcov₁ := inf_rightInvariants_le_iSup α β hα hαβ ΦL hΦs hΦ ξL N N₀ hN₀bot SL SL' hN₀S' Ψ tysL
    (fun w => cosetFamily w) hfamN hfamN₀
    (fun u hu => isSmoothCuspAutomorphicFnAt_of_mem_isotypicCuspSubmodule ΦL ξL N SL Ψ hu) hstabS
  have hcov₂ := inf_rightInvariants_le_iSup_refining (lvPins ΦL) ξL N N₀ SL SL' hSL'sub Ψ
    (archCutSubmodule L tysL) (fun w => cosetFamily w) hfamN hfamN₀ hstabS hcov₁

  obtain ⟨C, hCR, hCfix, hCmaps, hCsum⟩ := exists_finset_traceOn_eq_sum_traceOn (lvPins ΦL) ξL N N₀
    SL SL' Ψ (archCutSubmodule L tysL) (fun w => cosetFamily w) hfamN₀ (twistedConvOp K L D σ φ) hst hTV₀
    {π | π ∈ cuspClasses L (lvPins ΦL) ξL N₀ SL' ∧
      ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL → π.a w = Ψ.a w ∧ π.b w = Ψ.b w}
    (fun π hπ => hπ.1) hcov₂
    (fun π hπ => isotypicCuspSubmodule_inf_le_refined ΦL ξL hNbot hN₀N hSL'sub hNS hN₀S' Ψ hπ.2
      (archCutSubmodule L tysL))
    (twistTable σ)
    (fun π _ => twistedConvOp_mem_piece_fullFamily D σ ΦL ξL hσSL' hSL'K hb₀ hφ hφc h3 π
      (archCutSubmodule L tysL))

  refine ⟨SL', N₀, C, hSL'K, hN₀S', h3, fun Ψ' hΨ' => ⟨(hCR hΨ').1, (hCR hΨ').2, ?_⟩, ?_⟩
  ·
    intro w w' hw _ hunder
    have hfix := (fullData_twistTable_eq_iff σ SL' Ψ').mp (hCfix Ψ' hΨ')
    exact eq_of_under_eq_of_forall_smul_eq (X := ℂ × ℂ) hdeg hσ hσSL'
      (d := fun w => (Ψ'.a w, Ψ'.b w)) (fun w hw => Prod.ext (hfix w hw).1 (hfix w hw).2) hw hunder
  ·
    refine htr.trans ?_
    rw [← Finset.sum_attach C]
    refine (hCsum fun Ψ' hΨ' => isStableLinearOn_twistedConvOp K L D σ
      (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ hφc (hCmaps Ψ' hΨ')).trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    exact ((twistedCutTrace_eq K L D σ (lvPins ΦL) ξL N₀ SL' x.1 tysL φ hφ hφc).trans
      (twistedConvTraceOn_eq_traceOn K L D σ (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ hφc
        (hCmaps x.1 x.2))).symm

end S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_twistedCutTrace_eq_sum_twistedCutTrace_of_isFundamentalDomain_of_prime (solution)
