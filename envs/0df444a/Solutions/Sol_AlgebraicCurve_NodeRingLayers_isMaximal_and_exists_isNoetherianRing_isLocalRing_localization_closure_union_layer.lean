-- Prove2me | solution 1 for AlgebraicCurve.NodeRingLayers.isMaximal_and_exists_isNoetherianRing_isLocalRing_localization_closure_union_layer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/54961d96-1735-5faf-a1e6-08d7fd4be7ae

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeRingLayers_isMaximal_and_exists_isNoetherianRing_isLocalRing_localization_closure_union_layer

set_option autoImplicit false

open IsLocalRing

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {L : Type} [Field L] {F : Type} [Field F] [Algebra L F]

    (C' : Subring L) [IsDomain ↥C'] [IsDiscreteValuationRing ↥C'] (ϖ' : ↥C') (hϖ'irr : Irreducible ϖ')

    (N₀ : Subring F) [IsLocalRing ↥N₀] [IsNoetherianRing ↥N₀]
    (hC'N₀ : ∀ c : L, c ∈ C' → algebraMap L F c ∈ N₀)
    (hconst : ∀ g : ↥N₀, ∃ (o : ↥C') (h : algebraMap L F (o : L) ∈ N₀), ¬ IsUnit (g - ⟨_, h⟩))
    (hlin : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥N₀), LinearIndependent ↥C' c →
      ∑ i, c i • ((a i : ↥N₀) : F) = 0 → ∀ i, a i = 0)
    (hϖ'N₀ : ¬ IsUnit (⟨algebraMap L F ((ϖ' : ↥C') : L), hC'N₀ _ ϖ'.2⟩ : ↥N₀))
    (hdim : 2 ≤ ringKrullDim ↥N₀)

    (C'' : Subring L) (hC'C'' : C' ≤ C'') [IsDomain ↥C''] [IsDiscreteValuationRing ↥C''] (ϖ'' : ↥C'') (hϖ''irr : Irreducible ϖ'')
    (e : ℕ) (he : 1 ≤ e) (hϖe : ∃ v : L, v ∈ C'' ∧ v⁻¹ ∈ C'' ∧ ((ϖ' : ↥C') : L) = v * ((ϖ'' : ↥C'') : L) ^ e)
    (R : Subring L) (hC'R : C' ≤ R) (hRC'' : R ≤ C'')
    (hRfin : letI : Algebra ↥C' ↥R := (Subring.inclusion hC'R).toAlgebra; Module.Finite ↥C' ↥R)
    (hloc : ∀ c : L, c ∈ C'' → ∃ r s : L, r ∈ R ∧ s ∈ R ∧ s ≠ 0 ∧ s⁻¹ ∈ C'' ∧ c * s = r)

    (T'' : Subring F) (hT'' : T'' = Subring.closure ((N₀ : Set F) ∪ {f : F | ∃ c : L, c ∈ C'' ∧ f = algebraMap L F c}))
    (𝔐 : Ideal ↥T'')
    (h𝔐 : 𝔐 = Ideal.span ({t : ↥T'' | ∃ f : ↥N₀, ¬ IsUnit f ∧ (t : F) = (f : F)} ∪
      {t : ↥T'' | (t : F) = algebraMap L F ((ϖ'' : ↥C'') : L)}))
    :
    𝔐.IsMaximal ∧
    ∃ (TL : Subring F), (∀ f : F, f ∈ TL ↔ ∃ a b : ↥T'', b ∉ 𝔐 ∧ f * (b : F) = (a : F)) ∧
    ∃ (_ : IsNoetherianRing ↥TL) (_ : IsLocalRing ↥TL) (hle : N₀ ≤ TL),

      (∀ f : ↥N₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion hle f)) ∧

      (∀ g : ↥TL, ∃ (o : ↥C'') (h : algebraMap L F (o : L) ∈ TL), ¬ IsUnit (g - ⟨_, h⟩)) ∧

      (∀ hϖ'' : algebraMap L F ((ϖ'' : ↥C'') : L) ∈ TL,
        maximalIdeal ↥TL ≤ (maximalIdeal ↥N₀).map (Subring.inclusion hle) ⊔ Ideal.span {⟨_, hϖ''⟩}) ∧
      2 ≤ ringKrullDim ↥TL := by
  classical

  set ι : L →+* F := algebraMap L F with hιdef
  have hιinj : Function.Injective ι := (algebraMap L F).injective
  haveI : IsPrincipalIdealRing ↥C' := inferInstance
  have hmC' : maximalIdeal ↥C' = Ideal.span {ϖ'} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').mp hϖ'irr
  have hmC'' : maximalIdeal ↥C'' = Ideal.span {ϖ''} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ'').mp hϖ''irr

  let j : ↥C' →+* ↥N₀ :=
    { toFun := fun c => ⟨ι (c : L), hC'N₀ _ c.2⟩
      map_one' := Subtype.ext (by simp [hιdef])
      map_mul' := fun a b => Subtype.ext (by simp [hιdef])
      map_zero' := Subtype.ext (by simp [hιdef])
      map_add' := fun a b => Subtype.ext (by simp [hιdef]) }
  have hj : ∀ c : ↥C', ((j c : ↥N₀) : F) = ι (c : L) := fun _ => rfl

  obtain ⟨v, hvC, hvinv, hϖv⟩ := hϖe
  have hϖ'C'' : (⟨(ϖ' : ↥C') , hC'C'' ϖ'.2⟩ : ↥C'') ∈ maximalIdeal ↥C'' := by
    rw [hmC'', Ideal.mem_span_singleton']
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    refine ⟨⟨v, hvC⟩ * ϖ'' ^ e', Subtype.ext ?_⟩
    show (v * (ϖ'' : L) ^ e') * (ϖ'' : L) = ((ϖ' : ↥C') : L)
    rw [hϖv, pow_succ, mul_assoc]

  letI algC'R : Algebra ↥C' ↥R := (Subring.inclusion hC'R).toAlgebra
  haveI : Module.Finite ↥C' ↥R := hRfin
  haveI : FaithfulSMul ↥C' ↥R :=
    (faithfulSMul_iff_algebraMap_injective ↥C' ↥R).mpr (fun a b h =>
      Subtype.ext (congrArg (fun x : ↥R => (x : L)) h :))
  haveI : Module.IsTorsionFree ↥C' ↥R := inferInstance
  haveI : Module.Free ↥C' ↥R := Module.free_of_finite_type_torsion_free'
  let bR := Module.finBasis ↥C' ↥R
  set m : ℕ := Module.finrank ↥C' ↥R with hmdef
  have halgC'R : ∀ c : ↥C', ((algebraMap ↥C' ↥R c : ↥R) : L) = (c : L) := fun _ => rfl

  have hsumR : ∀ r : ↥R, (r : L) = ∑ i, ((bR.repr r i : ↥C') : L) * ((bR i : ↥R) : L) := by
    intro r
    have h := congrArg (fun x : ↥R => (x : L)) (bR.sum_repr r)
    simp only [AddSubmonoidClass.coe_finsetSum, Algebra.smul_def, Subring.coe_mul] at h
    exact h.symm

  set R' : Subring F := Subring.closure ((N₀ : Set F) ∪ {f : F | ∃ r : L, r ∈ R ∧ f = ι r}) with hR'def
  have hN₀R' : N₀ ≤ R' := fun f hf => Subring.subset_closure (Or.inl hf)
  have hιR' : ∀ r : L, r ∈ R → ι r ∈ R' := fun r hr => Subring.subset_closure (Or.inr ⟨r, hr, rfl⟩)
  letI algN₀R' : Algebra ↥N₀ ↥R' := (Subring.inclusion hN₀R').toAlgebra
  have halgN₀R' : ∀ n : ↥N₀, ((algebraMap ↥N₀ ↥R' n : ↥R') : F) = (n : F) := fun _ => rfl
  haveI : IsScalarTower ↥N₀ ↥R' ↥R' := IsScalarTower.right
  let w : Fin m → ↥R' := fun i => ⟨ι ((bR i : ↥R) : L), hιR' _ (bR i).2⟩
  have hw : ∀ i, ((w i : ↥R') : F) = ι ((bR i : ↥R) : L) := fun _ => rfl

  have hιr : ∀ r : ↥R, (⟨ι (r : L), hιR' _ r.2⟩ : ↥R') = ∑ i, j (bR.repr r i) • w i := by
    intro r
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    show ι (r : L) = ∑ i, (((j (bR.repr r i)) • w i : ↥R') : F)
    simp only [Algebra.smul_def, Subring.coe_mul, halgN₀R', hj, hw, ← map_mul, ← map_sum]
    exact congrArg ι (hsumR r)

  have hbL : LinearIndependent ↥C' (fun i => ((bR i : ↥R) : L)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h2 : (∑ i, g i • bR i : ↥R) = 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, ← hg]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Algebra.smul_def, Subring.coe_mul, Algebra.smul_def]
      rfl
    exact (Fintype.linearIndependent_iff.mp bR.linearIndependent) g h2

  have hwli : LinearIndependent ↥N₀ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (fun x : ↥R' => (x : F)) hg
    simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero] at h1
    refine hlin m (fun i => ((bR i : ↥R) : L)) g hbL ?_ i
    rw [← h1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.smul_def]
    show ι _ * _ = (((algebraMap ↥N₀ ↥R' (g i)) * w i : ↥R') : F)
    rw [Subring.coe_mul, halgN₀R', hw, mul_comm]

  have hwmul : ∀ i k, w i * w k ∈ Submodule.span ↥N₀ (Set.range w) := by
    intro i k
    have : w i * w k = ⟨ι (((bR i * bR k : ↥R)) : L), hιR' _ (bR i * bR k).2⟩ := by
      apply Subtype.ext; show ι _ * ι _ = ι _; rw [← map_mul]; rfl
    rw [this, hιr]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hspanmul : ∀ x ∈ Submodule.span ↥N₀ (Set.range w), ∀ y ∈ Submodule.span ↥N₀ (Set.range w),
      x * y ∈ Submodule.span ↥N₀ (Set.range w) := by
    intro x hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hwmul i k
      | zero => rw [zero_mul]; exact Submodule.zero_mem _
      | add x x' _ _ hx hx' => rw [add_mul]; exact Submodule.add_mem _ hx hx'
      | smul n x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hx
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ hy hy' => rw [mul_add]; exact Submodule.add_mem _ hy hy'
    | smul n y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
  have hone : (1 : ↥R') ∈ Submodule.span ↥N₀ (Set.range w) := by
    have : (1 : ↥R') = ⟨ι ((1 : ↥R) : L), hιR' _ (1 : ↥R).2⟩ := Subtype.ext (by simp)
    rw [this, hιr]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hwspan : ⊤ ≤ Submodule.span ↥N₀ (Set.range w) := by
    rintro ⟨y, hy⟩ -
    have hy' := hy
    rw [hR'def] at hy'
    induction hy' using Subring.closure_induction with
    | mem f hf =>
      rcases hf with hf | ⟨r, hr, rfl⟩
      · have : (⟨f, hy⟩ : ↥R') = (⟨f, hf⟩ : ↥N₀) • (1 : ↥R') := Subtype.ext (by
          show f = (((algebraMap ↥N₀ ↥R' ⟨f, hf⟩) * 1 : ↥R') : F); rw [mul_one]; rfl)
        rw [this]; exact Submodule.smul_mem _ _ hone
      · have : (⟨ι r, hy⟩ : ↥R') = ⟨ι ((⟨r, hr⟩ : ↥R) : L), hιR' _ hr⟩ := rfl
        rw [this, hιr]
        exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
    | zero => exact (Submodule.span ↥N₀ (Set.range w)).zero_mem
    | one => exact hone
    | add a b ha hb iha ihb =>
      have : (⟨a + b, hy⟩ : ↥R') = ⟨a, hR'def ▸ ha⟩ + ⟨b, hR'def ▸ hb⟩ := rfl
      rw [this]; exact Submodule.add_mem _ (iha _) (ihb _)
    | neg a ha iha =>
      have : (⟨-a, hy⟩ : ↥R') = -⟨a, hR'def ▸ ha⟩ := rfl
      rw [this]; exact Submodule.neg_mem _ (iha _)
    | mul a b ha hb iha ihb =>
      have : (⟨a * b, hy⟩ : ↥R') = ⟨a, hR'def ▸ ha⟩ * ⟨b, hR'def ▸ hb⟩ := rfl
      rw [this]; exact hspanmul _ (iha _) _ (ihb _)
  let bw : Module.Basis (Fin m) ↥N₀ ↥R' := Module.Basis.mk hwli hwspan
  have hbw : ∀ i, bw i = w i := fun i => Module.Basis.mk_apply hwli hwspan i
  haveI : Module.Finite ↥N₀ ↥R' := Module.Finite.of_basis bw
  haveI : Module.Free ↥N₀ ↥R' := Module.Free.of_basis bw
  haveI : IsNoetherianRing ↥R' := Algebra.FiniteType.isNoetherianRing ↥N₀ ↥R'

  have hjunit : ∀ c : ↥C', IsUnit (j c) ↔ IsUnit c := by
    intro c
    refine ⟨fun hu => ?_, fun hu => hu.map j⟩
    by_contra hc
    have hcm : c ∈ maximalIdeal ↥C' := hc
    rw [hmC', Ideal.mem_span_singleton'] at hcm
    obtain ⟨d, rfl⟩ := hcm
    rw [map_mul] at hu
    exact hϖ'N₀ (isUnit_of_mul_isUnit_right hu)
  let jbar : ↥C' →+* (↥N₀ ⧸ maximalIdeal ↥N₀) := (Ideal.Quotient.mk (maximalIdeal ↥N₀)).comp j
  have hjbar_surj : Function.Surjective jbar := by
    intro g
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨o, ho, hgo⟩ := hconst g
    refine ⟨o, ?_⟩
    show Ideal.Quotient.mk _ (j o) = Ideal.Quotient.mk _ g
    rw [Ideal.Quotient.eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    have : (j o : ↥N₀) - g = -(g - ⟨_, ho⟩) := by rw [neg_sub]; rfl
    rw [this, IsUnit.neg_iff]
    exact hgo
  have hjbar_ker : ∀ c : ↥C', c ∈ RingHom.ker jbar ↔ c ∈ maximalIdeal ↥C' := by
    intro c
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, hjunit]
    rfl
  let e₀ := RingHom.quotientKerEquivOfSurjective hjbar_surj
  have he₀ : ∀ c : ↥C', e₀ (Ideal.Quotient.mk _ c) = Ideal.Quotient.mk _ (j c) := fun c => rfl
  let resC'' : ↥C' →+* ResidueField ↥C'' := (IsLocalRing.residue ↥C'').comp (Subring.inclusion hC'C'')
  have hreskill : ∀ c ∈ RingHom.ker jbar, resC'' c = 0 := by
    intro c hc
    rw [hjbar_ker, hmC', Ideal.mem_span_singleton'] at hc
    obtain ⟨d, rfl⟩ := hc
    show IsLocalRing.residue ↥C'' (Subring.inclusion hC'C'' (d * ϖ')) = 0
    rw [IsLocalRing.residue_eq_zero_iff, map_mul]
    exact Ideal.mul_mem_left _ _ hϖ'C''
  let μ : ↥N₀ →+* ResidueField ↥C'' :=
    (Ideal.Quotient.lift (RingHom.ker jbar) resC'' hreskill).comp
      (e₀.symm.toRingHom.comp (Ideal.Quotient.mk (maximalIdeal ↥N₀)))
  have hμj : ∀ c : ↥C', μ (j c) = IsLocalRing.residue ↥C'' (Subring.inclusion hC'C'' c) := by
    intro c
    show Ideal.Quotient.lift (RingHom.ker jbar) resC'' hreskill (e₀.symm (Ideal.Quotient.mk _ (j c))) = _
    rw [← he₀, RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]
    rfl
  have hμnu : ∀ g : ↥N₀, ¬ IsUnit g → μ g = 0 := by
    intro g hg
    show Ideal.Quotient.lift (RingHom.ker jbar) resC'' hreskill (e₀.symm (Ideal.Quotient.mk _ g)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (by exact hg), map_zero, map_zero]

  letI modk : Module ↥N₀ (ResidueField ↥C'') := Module.compHom _ μ
  have hsmulk : ∀ (n : ↥N₀) (x : ResidueField ↥C''), n • x = μ n * x := fun _ _ => rfl
  let incl'' : ↥R →+* ↥C'' := Subring.inclusion hRC''
  have hincl'' : ∀ r : ↥R, ((incl'' r : ↥C'') : L) = (r : L) := fun _ => rfl
  let β : Fin m → ResidueField ↥C'' := fun i => IsLocalRing.residue ↥C'' (incl'' (bR i))
  let θₗ : ↥R' →ₗ[↥N₀] ResidueField ↥C'' := bw.constr ℕ β
  have hθw : ∀ i, θₗ (w i) = β i := fun i => by rw [← hbw]; exact bw.constr_basis ℕ β i
  have hθsmul : ∀ (n : ↥N₀) (y : ↥R'), θₗ (n • y) = μ n * θₗ y := fun n y => by rw [map_smul, hsmulk]

  have hsumC'' : ∀ r : ↥R, incl'' r = ∑ i, Subring.inclusion hC'C'' (bR.repr r i) * incl'' (bR i) := by
    intro r
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [Subring.coe_mul, hincl'']
    exact hsumR r
  have hθιr : ∀ r : ↥R, θₗ ⟨ι (r : L), hιR' _ r.2⟩ = IsLocalRing.residue ↥C'' (incl'' r) := by
    intro r
    rw [hιr, map_sum, hsumC'', map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hθsmul, hμj, hθw, map_mul]

  have hmemspan : ∀ y : ↥R', y ∈ Submodule.span ↥N₀ (Set.range w) := fun y => hwspan Submodule.mem_top
  have hwι : ∀ i, w i = ⟨ι ((bR i : ↥R) : L), hιR' _ (bR i).2⟩ := fun _ => rfl
  have hθmulι : ∀ (r : ↥R) (y : ↥R'),
      θₗ (⟨ι (r : L), hιR' _ r.2⟩ * y) = IsLocalRing.residue ↥C'' (incl'' r) * θₗ y := by
    intro r y
    induction hmemspan y using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      have : (⟨ι (r : L), hιR' _ r.2⟩ : ↥R') * w k = ⟨ι ((r * bR k : ↥R) : L), hιR' _ (r * bR k).2⟩ :=
        Subtype.ext (by show ι _ * ι _ = ι _; rw [← map_mul]; rfl)
      rw [this, hθιr, hθw, map_mul, map_mul]
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add y y' _ _ hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | smul n y _ hy => rw [mul_smul_comm, hθsmul, hθsmul, hy]; ring
  have hθmul : ∀ x y : ↥R', θₗ (x * y) = θₗ x * θₗ y := by
    intro x y
    induction hmemspan x using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [hwι, hθmulι, hθιr]
    | zero => rw [zero_mul, map_zero, zero_mul]
    | add x x' _ _ hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
    | smul n x _ hx => rw [smul_mul_assoc, hθsmul, hθsmul, hx, mul_assoc]
  have hθone : θₗ 1 = 1 := by
    have : (1 : ↥R') = ⟨ι ((1 : ↥R) : L), hιR' _ (1 : ↥R).2⟩ := Subtype.ext (by simp)
    rw [this, hθιr, map_one, map_one]
  let θ : ↥R' →+* ResidueField ↥C'' :=
    { toFun := θₗ, map_one' := hθone, map_mul' := hθmul, map_zero' := map_zero θₗ, map_add' := map_add θₗ }
  have hθ : ∀ y, θ y = θₗ y := fun _ => rfl

  have hconstT'' : ∀ c : L, c ∈ C'' → ι c ∈ T'' := fun c hc => by
    rw [hT'']; exact Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩)
  have hN₀T'' : N₀ ≤ T'' := fun f hf => by rw [hT'']; exact Subring.subset_closure (Or.inl hf)
  have hR'T'' : R' ≤ T'' := by
    rw [hR'def]
    refine Subring.closure_le.mpr ?_
    rintro f (hf | ⟨r, hr, rfl⟩)
    · exact hN₀T'' hf
    · exact hconstT'' r (hRC'' hr)
  letI algR'T'' : Algebra ↥R' ↥T'' := (Subring.inclusion hR'T'').toAlgebra
  have halgR'T'' : ∀ y : ↥R', ((algebraMap ↥R' ↥T'' y : ↥T'') : F) = (y : F) := fun _ => rfl
  let S₀ : Submonoid ↥R' :=
    { carrier := {y | ∃ s : L, s ∈ R ∧ s ≠ 0 ∧ s⁻¹ ∈ C'' ∧ (y : F) = ι s}
      one_mem' := ⟨1, R.one_mem, one_ne_zero, by rw [inv_one]; exact C''.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨s, hs, hs0, hsi, ha⟩ ⟨t, ht, ht0, hti, hb⟩
        exact ⟨s * t, R.mul_mem hs ht, mul_ne_zero hs0 ht0, by rw [mul_inv]; exact C''.mul_mem hsi hti,
          by rw [Subring.coe_mul, ha, hb, map_mul]⟩ }
  have hS₀T : ∀ t : F, t ∈ T'' → ∃ (a : ↥R') (s : ↥S₀), t * (s : ↥R') = (a : F) := by
    intro t ht
    rw [hT''] at ht
    induction ht using Subring.closure_induction with
    | mem f hf =>
      rcases hf with hf | ⟨c, hc, rfl⟩
      · exact ⟨⟨f, hN₀R' hf⟩, 1, by simp⟩
      · obtain ⟨r, s, hr, hs, hs0, hsi, hcs⟩ := hloc c hc
        exact ⟨⟨ι r, hιR' r hr⟩, ⟨⟨ι s, hιR' s hs⟩, s, hs, hs0, hsi, rfl⟩, by
          show ι c * ι s = ι r; rw [← map_mul, hcs]⟩
    | zero => exact ⟨0, 1, by simp⟩
    | one => exact ⟨1, 1, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨x, s, hx⟩ := iha
      obtain ⟨y, t, hy⟩ := ihb
      refine ⟨x * (t : ↥R') + y * (s : ↥R'), s * t, ?_⟩
      simp only [Submonoid.coe_mul, Subring.coe_mul, Subring.coe_add]
      rw [← hx, ← hy]; ring
    | neg a _ iha =>
      obtain ⟨x, s, hx⟩ := iha
      exact ⟨-x, s, by rw [Subring.coe_neg, ← hx]; ring⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨x, s, hx⟩ := iha
      obtain ⟨y, t, hy⟩ := ihb
      refine ⟨x * y, s * t, ?_⟩
      simp only [Submonoid.coe_mul, Subring.coe_mul]
      rw [← hx, ← hy]; ring
  haveI hlocT : IsLocalization S₀ ↥T'' :=
    { map_units := by
        rintro ⟨y, s, hs, hs0, hsi, hy⟩
        refine isUnit_iff_exists_inv.mpr ⟨⟨ι s⁻¹, hconstT'' _ hsi⟩, Subtype.ext ?_⟩
        show (y : F) * ι s⁻¹ = 1
        rw [hy, ← map_mul, mul_inv_cancel₀ hs0, map_one]
      surj := fun t => by
        obtain ⟨a, s, h⟩ := hS₀T (t : F) t.2
        exact ⟨(a, s), Subtype.ext h⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        have : (x : F) = (y : F) := congrArg (fun z : ↥T'' => (z : F)) h
        rw [Subtype.ext this]⟩ }
  haveI : IsNoetherianRing ↥T'' := IsLocalization.isNoetherianRing S₀ ↥T'' inferInstance

  have hθS : ∀ y : ↥S₀, IsUnit (θ (y : ↥R')) := by
    rintro ⟨y, s, hs, hs0, hsi, hy⟩
    have hyeq : (y : ↥R') = ⟨ι ((⟨s, hs⟩ : ↥R) : L), hιR' _ hs⟩ := Subtype.ext hy
    show IsUnit (θ y)
    rw [hθ, hyeq, hθιr]
    exact IsUnit.map _ (isUnit_iff_exists_inv.mpr ⟨⟨s⁻¹, hsi⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩)
  let Θ : ↥T'' →+* ResidueField ↥C'' := IsLocalization.lift (M := S₀) hθS
  have hΘR' : ∀ y : ↥R', Θ (algebraMap ↥R' ↥T'' y) = θ y := fun y => IsLocalization.lift_eq hθS y
  have hΘιr : ∀ (r : L) (hr : r ∈ R), Θ ⟨ι r, hconstT'' r (hRC'' hr)⟩ = IsLocalRing.residue ↥C'' ⟨r, hRC'' hr⟩ := by
    intro r hr
    have : (⟨ι r, hconstT'' r (hRC'' hr)⟩ : ↥T'') = algebraMap ↥R' ↥T'' ⟨ι r, hιR' r hr⟩ := rfl
    rw [this, hΘR', hθ]
    exact hθιr ⟨r, hr⟩
  have hΘconst : ∀ (c : L) (hc : c ∈ C''), Θ ⟨ι c, hconstT'' c hc⟩ = IsLocalRing.residue ↥C'' ⟨c, hc⟩ := by
    intro c hc
    obtain ⟨r, s, hr, hs, hs0, hsi, hcs⟩ := hloc c hc
    have hsu : IsUnit (IsLocalRing.residue ↥C'' ⟨s, hRC'' hs⟩) :=
      IsUnit.map _ (isUnit_iff_exists_inv.mpr ⟨⟨s⁻¹, hsi⟩, Subtype.ext (mul_inv_cancel₀ hs0)⟩)
    refine hsu.mul_left_injective ?_
    have h1 : (⟨ι c, hconstT'' c hc⟩ * ⟨ι s, hconstT'' s (hRC'' hs)⟩ : ↥T'') = ⟨ι r, hconstT'' r (hRC'' hr)⟩ :=
      Subtype.ext (by show ι c * ι s = ι r; rw [← map_mul, hcs])
    have h2 : ((⟨c, hc⟩ : ↥C'') * ⟨s, hRC'' hs⟩) = ⟨r, hRC'' hr⟩ := Subtype.ext hcs
    show Θ ⟨ι c, _⟩ * IsLocalRing.residue ↥C'' ⟨s, _⟩ = IsLocalRing.residue ↥C'' ⟨c, hc⟩ * IsLocalRing.residue ↥C'' ⟨s, _⟩
    calc Θ ⟨ι c, hconstT'' c hc⟩ * IsLocalRing.residue ↥C'' ⟨s, hRC'' hs⟩
        = Θ ⟨ι c, hconstT'' c hc⟩ * Θ ⟨ι s, hconstT'' s (hRC'' hs)⟩ := by rw [hΘιr s hs]
      _ = Θ ⟨ι r, hconstT'' r (hRC'' hr)⟩ := by rw [← map_mul, h1]
      _ = IsLocalRing.residue ↥C'' ⟨r, hRC'' hr⟩ := hΘιr r hr
      _ = IsLocalRing.residue ↥C'' ⟨c, hc⟩ * IsLocalRing.residue ↥C'' ⟨s, hRC'' hs⟩ := by rw [← map_mul, h2]
  have hΘN₀ : ∀ (f : F) (hf : f ∈ N₀), Θ ⟨f, hN₀T'' hf⟩ = μ ⟨f, hf⟩ := by
    intro f hf
    have : (⟨f, hN₀T'' hf⟩ : ↥T'') = algebraMap ↥R' ↥T'' (algebraMap ↥N₀ ↥R' ⟨f, hf⟩) := rfl
    rw [this, hΘR', hθ, Algebra.algebraMap_eq_smul_one, hθsmul, hθone, mul_one]
  have hΘsurj : Function.Surjective Θ := by
    intro x
    obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
    exact ⟨⟨ι (c : L), hconstT'' _ c.2⟩, hΘconst _ c.2⟩

  have hϖ''T'' : ι ((ϖ'' : ↥C'') : L) ∈ T'' := hconstT'' _ ϖ''.2
  have hΘϖ'' : Θ ⟨ι ((ϖ'' : ↥C'') : L), hϖ''T''⟩ = 0 := by
    rw [hΘconst _ ϖ''.2, IsLocalRing.residue_eq_zero_iff, hmC'']
    exact Ideal.mem_span_singleton_self _
  have h𝔐le : 𝔐 ≤ RingHom.ker Θ := by
    rw [h𝔐, Ideal.span_le]
    rintro t (⟨f, hfu, htf⟩ | htϖ)
    · have : t = ⟨(f : F), hN₀T'' f.2⟩ := Subtype.ext htf
      rw [SetLike.mem_coe, RingHom.mem_ker, this, hΘN₀ _ f.2]
      exact hμnu _ (by simpa using hfu)
    · have : t = ⟨_, hϖ''T''⟩ := Subtype.ext htϖ
      rw [SetLike.mem_coe, RingHom.mem_ker, this, hΘϖ'']

  have hmod : ∀ t : F, t ∈ T'' → ∃ (c : L) (hc : c ∈ C'') (hm : t - ι c ∈ T''), (⟨t - ι c, hm⟩ : ↥T'') ∈ 𝔐 := by
    intro t ht
    rw [hT''] at ht
    induction ht using Subring.closure_induction with
    | mem f hf =>
      rcases hf with hf | ⟨c, hc, rfl⟩
      · obtain ⟨o, ho, hgo⟩ := hconst ⟨f, hf⟩
        refine ⟨(o : L), hC'C'' o.2, T''.sub_mem (hN₀T'' hf) (hconstT'' _ (hC'C'' o.2)), ?_⟩
        rw [h𝔐]
        exact Ideal.subset_span (Or.inl ⟨⟨f, hf⟩ - ⟨_, ho⟩, hgo, rfl⟩)
      · have hm : ι c - ι c ∈ T'' := by rw [sub_self]; exact T''.zero_mem
        refine ⟨c, hc, hm, ?_⟩
        have : (⟨ι c - ι c, hm⟩ : ↥T'') = 0 := Subtype.ext (sub_self _)
        rw [this]; exact 𝔐.zero_mem
    | zero =>
      have hm : (0 : F) - ι 0 ∈ T'' := by rw [map_zero, sub_zero]; exact T''.zero_mem
      refine ⟨0, C''.zero_mem, hm, ?_⟩
      have : (⟨0 - ι 0, hm⟩ : ↥T'') = 0 := Subtype.ext (by simp)
      rw [this]; exact 𝔐.zero_mem
    | one =>
      have hm : (1 : F) - ι 1 ∈ T'' := by rw [map_one, sub_self]; exact T''.zero_mem
      refine ⟨1, C''.one_mem, hm, ?_⟩
      have : (⟨1 - ι 1, hm⟩ : ↥T'') = 0 := Subtype.ext (by simp)
      rw [this]; exact 𝔐.zero_mem
    | add a b ha hb iha ihb =>
      obtain ⟨c, hc, hm1, h1⟩ := iha
      obtain ⟨d, hd, hm2, h2⟩ := ihb
      have hm : a + b - ι (c + d) ∈ T'' := by
        have : a + b - ι (c + d) = (a - ι c) + (b - ι d) := by rw [map_add]; ring
        rw [this]; exact T''.add_mem hm1 hm2
      refine ⟨c + d, C''.add_mem hc hd, hm, ?_⟩
      have : (⟨a + b - ι (c + d), hm⟩ : ↥T'') = ⟨a - ι c, hm1⟩ + ⟨b - ι d, hm2⟩ :=
        Subtype.ext (by show a + b - ι (c + d) = (a - ι c) + (b - ι d); rw [map_add]; ring)
      rw [this]; exact 𝔐.add_mem h1 h2
    | neg a ha iha =>
      obtain ⟨c, hc, hm1, h1⟩ := iha
      have hm : -a - ι (-c) ∈ T'' := by
        have : -a - ι (-c) = -(a - ι c) := by rw [map_neg]; ring
        rw [this]; exact T''.neg_mem hm1
      refine ⟨-c, C''.neg_mem hc, hm, ?_⟩
      have : (⟨-a - ι (-c), hm⟩ : ↥T'') = -⟨a - ι c, hm1⟩ :=
        Subtype.ext (by show -a - ι (-c) = -(a - ι c); rw [map_neg]; ring)
      rw [this]; exact 𝔐.neg_mem_iff.mpr h1
    | mul a b ha hb iha ihb =>
      obtain ⟨c, hc, hm1, h1⟩ := iha
      obtain ⟨d, hd, hm2, h2⟩ := ihb
      have ha' : a ∈ T'' := by rw [hT'']; exact ha
      have hm : a * b - ι (c * d) ∈ T'' := by
        have : a * b - ι (c * d) = a * (b - ι d) + (a - ι c) * ι d := by rw [map_mul]; ring
        rw [this]
        exact T''.add_mem (T''.mul_mem ha' hm2) (T''.mul_mem hm1 (hconstT'' d hd))
      refine ⟨c * d, C''.mul_mem hc hd, hm, ?_⟩
      have : (⟨a * b - ι (c * d), hm⟩ : ↥T'') =
          ⟨a, ha'⟩ * ⟨b - ι d, hm2⟩ + ⟨a - ι c, hm1⟩ * ⟨ι d, hconstT'' d hd⟩ :=
        Subtype.ext (by show a * b - ι (c * d) = a * (b - ι d) + (a - ι c) * ι d; rw [map_mul]; ring)
      rw [this]
      exact 𝔐.add_mem (𝔐.mul_mem_left _ h2) (𝔐.mul_mem_right _ h1)
  have hkerle : RingHom.ker Θ ≤ 𝔐 := by
    intro t ht
    obtain ⟨c, hc, hm, hcm⟩ := hmod (t : F) t.2
    have hsplit : t = ⟨(t : F) - ι c, hm⟩ + ⟨ι c, hconstT'' c hc⟩ := Subtype.ext (by simp)
    have hc0 : IsLocalRing.residue ↥C'' ⟨c, hc⟩ = 0 := by
      rw [← hΘconst c hc]
      have := congrArg Θ hsplit
      rw [map_add, (RingHom.mem_ker).mp ht, (RingHom.mem_ker).mp (h𝔐le hcm), zero_add] at this
      exact this.symm
    rw [IsLocalRing.residue_eq_zero_iff, hmC'', Ideal.mem_span_singleton'] at hc0
    obtain ⟨d, hd⟩ := hc0
    have hιc : (⟨ι c, hconstT'' c hc⟩ : ↥T'') ∈ 𝔐 := by
      have : (⟨ι c, hconstT'' c hc⟩ : ↥T'') = ⟨ι (d : L), hconstT'' _ d.2⟩ * ⟨ι ((ϖ'' : ↥C'') : L), hϖ''T''⟩ :=
        Subtype.ext (by
          show ι c = ι (d : L) * ι ((ϖ'' : ↥C'') : L)
          rw [← map_mul]; congr 1; exact (congrArg Subtype.val hd).symm)
      rw [this, h𝔐]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inr rfl))
    rw [hsplit]
    exact 𝔐.add_mem hcm hιc
  have h𝔐ker : 𝔐 = RingHom.ker Θ := le_antisymm h𝔐le hkerle
  have h𝔐max : 𝔐.IsMaximal := by rw [h𝔐ker]; exact RingHom.ker_isMaximal_of_surjective Θ hΘsurj

  haveI h𝔐prime : 𝔐.IsPrime := h𝔐max.isPrime
  have h𝔐ne : 𝔐 ≠ ⊤ := h𝔐max.ne_top
  have hone𝔐 : (1 : ↥T'') ∉ 𝔐 := fun h => h𝔐ne ((Ideal.eq_top_iff_one 𝔐).mpr h)
  let TLs : Subring F :=
    { carrier := {f | ∃ a b : ↥T'', b ∉ 𝔐 ∧ f * (b : F) = (a : F)}
      mul_mem' := by
        rintro f g ⟨a, b, hb, hf⟩ ⟨a', b', hb', hg⟩
        refine ⟨a * a', b * b', fun h => (h𝔐prime.mem_or_mem h).elim hb hb', ?_⟩
        rw [Subring.coe_mul, Subring.coe_mul, ← hf, ← hg]; ring
      one_mem' := ⟨1, 1, hone𝔐, by simp⟩
      add_mem' := by
        rintro f g ⟨a, b, hb, hf⟩ ⟨a', b', hb', hg⟩
        refine ⟨a * b' + a' * b, b * b', fun h => (h𝔐prime.mem_or_mem h).elim hb hb', ?_⟩
        rw [Subring.coe_mul, Subring.coe_add, Subring.coe_mul, Subring.coe_mul, ← hf, ← hg]; ring
      zero_mem' := ⟨0, 1, hone𝔐, by simp⟩
      neg_mem' := by
        rintro f ⟨a, b, hb, hf⟩
        exact ⟨-a, b, hb, by rw [Subring.coe_neg, ← hf]; ring⟩ }
  have hTLs : ∀ f : F, f ∈ TLs ↔ ∃ a b : ↥T'', b ∉ 𝔐 ∧ f * (b : F) = (a : F) := fun _ => Iff.rfl
  have hT''TL : T'' ≤ TLs := fun f hf => ⟨⟨f, hf⟩, 1, hone𝔐, by simp⟩
  have hle : N₀ ≤ TLs := hN₀T''.trans hT''TL
  letI algTTL : Algebra ↥T'' ↥TLs := (Subring.inclusion hT''TL).toAlgebra
  have halgTTL : ∀ t : ↥T'', ((algebraMap ↥T'' ↥TLs t : ↥TLs) : F) = (t : F) := fun _ => rfl
  have hb0 : ∀ b : ↥T'', b ∉ 𝔐 → (b : F) ≠ 0 := by
    intro b hb h0
    apply hb
    have : b = 0 := Subtype.ext h0
    rw [this]; exact 𝔐.zero_mem
  haveI hlocTL : IsLocalization.AtPrime ↥TLs 𝔐 :=
    { map_units := by
        rintro ⟨b, hb⟩
        have hb' : b ∉ 𝔐 := hb
        refine isUnit_iff_exists_inv.mpr ⟨⟨(b : F)⁻¹, 1, b, hb', ?_⟩, Subtype.ext ?_⟩
        · rw [inv_mul_cancel₀ (hb0 b hb')]; simp
        · show (b : F) * (b : F)⁻¹ = 1
          exact mul_inv_cancel₀ (hb0 b hb')
      surj := by
        rintro ⟨f, a, b, hb, hf⟩
        exact ⟨(a, ⟨b, hb⟩), Subtype.ext hf⟩
      exists_of_eq := fun {x y} h => ⟨1, by
        have : (x : F) = (y : F) := congrArg (fun z : ↥TLs => (z : F)) h
        rw [Subtype.ext this]⟩ }
  haveI : IsNoetherianRing ↥TLs := IsLocalization.isNoetherianRing 𝔐.primeCompl ↥TLs inferInstance
  haveI hTLloc : IsLocalRing ↥TLs := IsLocalization.AtPrime.isLocalRing ↥TLs 𝔐
  have hmemmax : ∀ t : ↥T'', algebraMap ↥T'' ↥TLs t ∈ maximalIdeal ↥TLs ↔ t ∈ 𝔐 :=
    fun t => IsLocalization.AtPrime.to_map_mem_maximal_iff ↥TLs 𝔐 t

  have hlocal : ∀ f : ↥N₀, ¬ IsUnit f → ¬ IsUnit (Subring.inclusion hle f) := by
    intro f hf
    have h1 : (⟨(f : F), hN₀T'' f.2⟩ : ↥T'') ∈ 𝔐 := by
      rw [h𝔐]; exact Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩)
    have h2 : Subring.inclusion hle f = algebraMap ↥T'' ↥TLs ⟨(f : F), hN₀T'' f.2⟩ := rfl
    rw [h2]
    exact (IsLocalRing.mem_maximalIdeal _).mp ((hmemmax _).mpr h1)

  have hconst𝔐 : ∀ (c : L) (hc : c ∈ C''), (⟨c, hc⟩ : ↥C'') ∈ maximalIdeal ↥C'' →
      (⟨ι c, hconstT'' c hc⟩ : ↥T'') ∈ 𝔐 := by
    intro c hc hcm
    rw [h𝔐ker, RingHom.mem_ker, hΘconst c hc, IsLocalRing.residue_eq_zero_iff]
    exact hcm

  have hres : ∀ g : ↥TLs, ∃ (o : ↥C'') (h : algebraMap L F (o : L) ∈ TLs), ¬ IsUnit (g - ⟨_, h⟩) := by
    intro g
    obtain ⟨a, b, hb, hgb⟩ := g.2
    obtain ⟨ca, hca, hma, h𝔐a⟩ := hmod (a : F) a.2
    obtain ⟨cb, hcb, hmb, h𝔐b⟩ := hmod (b : F) b.2
    have hcbu : (⟨cb, hcb⟩ : ↥C'') ∉ maximalIdeal ↥C'' := by
      intro hcbm
      apply hb
      have : b = ⟨(b : F) - ι cb, hmb⟩ + ⟨ι cb, hconstT'' cb hcb⟩ := Subtype.ext (by simp)
      rw [this]
      exact 𝔐.add_mem h𝔐b (hconst𝔐 cb hcb hcbm)
    have hcbunit : IsUnit (⟨cb, hcb⟩ : ↥C'') := by by_contra h; exact hcbu h
    obtain ⟨cbi, hcbi⟩ := isUnit_iff_exists_inv.mp hcbunit
    let o : ↥C'' := ⟨ca, hca⟩ * cbi
    have hoT : ι (o : L) ∈ T'' := hconstT'' _ o.2
    refine ⟨o, hT''TL hoT, ?_⟩
    have hcb0 : cb ≠ 0 := fun h => by
      have : (⟨cb, hcb⟩ : ↥C'') = 0 := Subtype.ext h
      rw [this, zero_mul] at hcbi; exact zero_ne_one hcbi
    have hcbi' : (cbi : L) = cb⁻¹ := by
      have := congrArg Subtype.val hcbi
      simp only [Subring.coe_mul, Subring.coe_one] at this
      exact (eq_inv_of_mul_eq_one_right this)
    have hnum : a - b * ⟨ι (o : L), hoT⟩ ∈ 𝔐 := by
      have : a - b * ⟨ι (o : L), hoT⟩ =
          ⟨(a : F) - ι ca, hma⟩ - ⟨(b : F) - ι cb, hmb⟩ * ⟨ι (o : L), hoT⟩ := Subtype.ext (by
        show (a : F) - b * ι (o : L) = ((a : F) - ι ca) - ((b : F) - ι cb) * ι (o : L)
        have ho : ι (o : L) = ι ca * (ι cb)⁻¹ := by
          show ι (ca * (cbi : L)) = _; rw [map_mul, hcbi', map_inv₀]
        rw [ho]
        have hu : ι cb * (ι cb)⁻¹ = 1 := mul_inv_cancel₀ ((map_ne_zero ι).mpr hcb0)
        linear_combination (-(ι ca)) * hu)
      rw [this]
      exact 𝔐.sub_mem h𝔐a (𝔐.mul_mem_right _ h𝔐b)
    rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    have hbu : IsUnit (algebraMap ↥T'' ↥TLs b) := IsLocalization.map_units ↥TLs (⟨b, hb⟩ : ↥𝔐.primeCompl)
    rw [← Ideal.mul_unit_mem_iff_mem _ hbu]
    have : (g - ⟨ι (o : L), hT''TL hoT⟩) * algebraMap ↥T'' ↥TLs b = algebraMap ↥T'' ↥TLs (a - b * ⟨ι (o : L), hoT⟩) :=
      Subtype.ext (by
        show ((g : F) - ι (o : L)) * (b : F) = (a : F) - (b : F) * ι (o : L)
        rw [← hgb]; ring)
    rw [this]
    exact (hmemmax _).mpr hnum

  have hmaxle : ∀ hϖ'' : algebraMap L F ((ϖ'' : ↥C'') : L) ∈ TLs,
      maximalIdeal ↥TLs ≤ (maximalIdeal ↥N₀).map (Subring.inclusion hle) ⊔ Ideal.span {⟨_, hϖ''⟩} := by
    intro hϖ'' x hx
    obtain ⟨a, b, hb, hxb⟩ := x.2
    have hbu : IsUnit (algebraMap ↥T'' ↥TLs b) := IsLocalization.map_units ↥TLs (⟨b, hb⟩ : ↥𝔐.primeCompl)
    have hxa : x * algebraMap ↥T'' ↥TLs b = algebraMap ↥T'' ↥TLs a := Subtype.ext hxb
    have ha : a ∈ 𝔐 := by
      rw [← hmemmax, ← hxa]; exact Ideal.mul_mem_right _ _ hx
    have hx' : x = algebraMap ↥T'' ↥TLs a * ↑hbu.unit⁻¹ := by
      rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]; exact hxa
    have hmap : 𝔐.map (algebraMap ↥T'' ↥TLs) ≤
        (maximalIdeal ↥N₀).map (Subring.inclusion hle) ⊔ Ideal.span {⟨_, hϖ''⟩} := by
      rw [h𝔐, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨t, ht, rfl⟩
      rcases ht with ⟨f, hf, htf⟩ | htϖ
      · have : algebraMap ↥T'' ↥TLs t = Subring.inclusion hle f := Subtype.ext htf
        rw [this]
        exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal _).mpr hf))
      · have : algebraMap ↥T'' ↥TLs t = ⟨_, hϖ''⟩ := Subtype.ext htϖ
        rw [this]
        exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [hx']
    exact Ideal.mul_mem_right _ _ (hmap (Ideal.mem_map_of_mem _ ha))

  letI algN₀T : Algebra ↥N₀ ↥T'' := (Subring.inclusion hN₀T'').toAlgebra
  haveI : IsScalarTower ↥N₀ ↥R' ↥T'' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat ↥R' ↥T'' := IsLocalization.flat ↥T'' S₀
  haveI : Module.Flat ↥N₀ ↥T'' := Module.Flat.trans ↥N₀ ↥R' ↥T''
  letI algN₀TL : Algebra ↥N₀ ↥TLs := (Subring.inclusion hle).toAlgebra
  haveI : IsScalarTower ↥N₀ ↥T'' ↥TLs := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Flat ↥T'' ↥TLs := IsLocalization.flat ↥TLs 𝔐.primeCompl
  haveI : Module.Flat ↥N₀ ↥TLs := Module.Flat.trans ↥N₀ ↥T'' ↥TLs
  haveI : Algebra.HasGoingDown ↥N₀ ↥TLs := inferInstance
  haveI hover : (maximalIdeal ↥TLs).LiesOver (maximalIdeal ↥N₀) := by
    refine ⟨Ideal.ext (fun f => ?_)⟩
    rw [Ideal.under_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff]
    refine ⟨fun hf => hlocal f hf, fun hf hu => hf (hu.map _)⟩
  have hdim2 : 2 ≤ ringKrullDim ↥TLs := by
    have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum ↥N₀) := by
      unfold ringKrullDim at hdim; exact_mod_cast hdim
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h2
    have h01 := l.step ⟨0, by omega⟩
    have h12 := l.step ⟨1, by omega⟩
    set P0 := l (Fin.castSucc ⟨0, by omega⟩) with hP0
    set P1 := l (Fin.succ ⟨0, by omega⟩) with hP1
    set P2 := l (Fin.succ ⟨1, by omega⟩) with hP2
    have hP1' : l (Fin.castSucc ⟨1, by omega⟩) = P1 := by rw [hP1]; congr 1
    rw [hP1'] at h12
    have h01' : P0.asIdeal < P1.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal P0 P1).mpr h01
    have h12' : P1.asIdeal < P2.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal P1 P2).mpr h12
    have h𝔭0 : P1.asIdeal ≠ ⊥ := ne_bot_of_gt h01'
    have h𝔭m : P1.asIdeal < maximalIdeal ↥N₀ :=
      lt_of_lt_of_le h12' (IsLocalRing.le_maximalIdeal P2.isPrime.ne_top)
    haveI := P1.isPrime
    obtain ⟨P, hPle, hPp, hPo⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal ↥TLs) h𝔭m.le
    have hPunder : P.under ↥N₀ = P1.asIdeal := hPo.over.symm
    have hP0 : P ≠ ⊥ := by
      intro h
      apply h𝔭0
      rw [← hPunder, h, Ideal.under_def, Ideal.comap_bot_of_injective]
      exact fun a b hab => Subtype.ext (congrArg (fun z : ↥TLs => (z : F)) hab)
    have hPm : P ≠ maximalIdeal ↥TLs := by
      intro h
      apply h𝔭m.ne
      rw [← hPunder, h]
      exact hover.over.symm
    have ha := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)
    have hb := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPle hPm)
    have hm2 : (2 : ℕ∞) ≤ (maximalIdeal ↥TLs).height := by
      calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
        _ ≤ (⊥ : Ideal ↥TLs).height + 1 + 1 := by gcongr; exact zero_le
        _ ≤ P.height + 1 := by gcongr
        _ ≤ (maximalIdeal ↥TLs).height := hb
    calc (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := rfl
      _ ≤ ((maximalIdeal ↥TLs).height : WithBot ℕ∞) := WithBot.coe_le_coe.mpr hm2
      _ ≤ ringKrullDim ↥TLs := Ideal.height_le_ringKrullDim_of_isPrime

  exact ⟨h𝔐max, TLs, hTLs, inferInstance, inferInstance, hle, hlocal, hres, hmaxle, hdim2⟩

end S_AlgebraicCurve_NodeRingLayers_isMaximal_and_exists_isNoetherianRing_isLocalRing_localization_closure_union_layer
end P2MW
export P2MW.S_AlgebraicCurve_NodeRingLayers_isMaximal_and_exists_isNoetherianRing_isLocalRing_localization_closure_union_layer (solution)
