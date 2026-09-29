-- Prove2me | Definitions.Def_AlgebraicCurve_SemistableChartsComap
-- name    : AlgebraicCurve_SemistableChartsComap
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/15e35230-c07b-5bd0-9528-6af0cbb92a04
-- title:
--   Transport of component charts and annuli along field automorphisms
-- statement:
--   Throughout, $L$ is a field, $A \subseteq L$ a valuation subring, $F$ an extension field of $L$, $\bar F$ an extension of the residue field of $A$, and $\sigma$ an $L$-algebra automorphism of $F$. The module first records how the (pointwise) action of $\sigma$ on places of $F/L$ interacts with the valuation-theoretic data attached to a place $v$: $f$ lies in the valuation subring of $\sigma \cdot v$ exactly when $\sigma^{-1} f$ lies in that of $v$ (equivalently $\sigma f \in \sigma\cdot v$ iff $f \in v$, and $f \in \sigma^{-1}\cdot v$ iff $\sigma f \in v$); $(\sigma\cdot v).\mathrm{ord}\, f = v.\mathrm{ord}(\sigma^{-1} f)$; $\sigma\cdot v$ is rational over $L$ (i.e. $L \to$ its residue field is surjective) iff $v$ is; the residue of $\sigma f$ at $\sigma\cdot v$ corresponds to the residue of $f$ at $v$ under the induced isomorphism of residue fields; and, for rational $v$, the evaluation maps satisfy $(\sigma\cdot v)(\sigma f) = v(f)$, equivalently $(\sigma\cdot v)(f) = v(\sigma^{-1} f)$.
--
--   On this basis, `ComponentChart.comap` transports a component chart $C$ (a valuation subring $\mathcal O_C$ of $F$ prolonging $A$, a surjective residue map $\mathcal O_C \to \bar F$ with kernel the maximal ideal and compatible with $A \to \bar A$, a set of places of $F/L$, a finite set of nodes among places of $\bar F$, a reduction map on places, together with its pointwise-compatibility and divisor-pushforward axioms) to the chart with integers $\sigma^{-1}(\mathcal O_C)$, residue $f \mapsto \overline{\sigma f}$, domain $\{P : \sigma\cdot P \in C.\mathrm{dom}\}$, reduction $P \mapsto C.\mathrm{placeMap}(\sigma\cdot P)$ and the same nodes; all chart axioms are re-proved for this data, including the surjectivity and kernel statements for the transported residue map, which are also isolated as separate lemmas. Similarly `Annulus.comap` transports an annulus to the one with domain $\{P : \sigma\cdot P \in \mathrm{dom}\}$, parameter $\sigma^{-1}$ of the original parameter and unchanged modulus, its existence-and-uniqueness, $\mathrm{ord}$-of-difference and unit-principle fields being verified through the place lemmas above. Attachment of an annulus to a chart at a node $x$ (namely: $x$ is a node, the parameter lies in the chart's integers with residue of order $1$ at $x$, and a slope condition on all $f$ with nonzero residue and vanishing order on the annulus) is preserved in both directions, giving `isAttached_comap_iff`. Finally, iterated transport is computed: transporting along $\sigma$ and then along $\sigma^{-1}$ returns the original integers, domain, parameter, reduction map and residues.
--
--   **Relation to Mathlib.** `Place`, `ComponentChart` and `Annulus` are the project's own notions; the transport is built from Mathlib's pointwise action of algebra automorphisms on valuation subrings, `ValuationSubring.comap`, and the functoriality of `IsLocalRing.ResidueField` under ring isomorphisms.
--
--   **Where it is used.** These transports are used in the treatment of semistable reduction of curves over valuation rings, where an automorphism of the function field over the constant field permutes the data describing the components and the annuli joining them, so that one component chart with its annuli and attachments yields the charts and annuli of its images.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_SemistableChartsComap.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

open scoped Pointwise

namespace Place.Transport

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : Place K F)

theorem mem_smul_iff (f : F) : f ∈ (σ • v).toValuationSubring ↔ σ.symm f ∈ v.toValuationSubring := by
  rw [smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
    AlgEquiv.aut_inv]

theorem mem_smul_iff' (f : F) : σ f ∈ (σ • v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [mem_smul_iff, AlgEquiv.symm_apply_apply]

theorem mem_inv_smul_iff (f : F) : f ∈ (σ⁻¹ • v).toValuationSubring ↔ σ f ∈ v.toValuationSubring := by
  rw [mem_smul_iff, AlgEquiv.aut_inv, AlgEquiv.symm_symm]

theorem ord_smul' (f : F) : (σ • v).ord f = v.ord (σ.symm f) := by
  conv_lhs => rw [← AlgEquiv.apply_symm_apply σ f]
  exact ord_smul σ v (σ.symm f)

theorem ord_inv_smul (f : F) : (σ⁻¹ • v).ord f = v.ord (σ f) := by
  rw [ord_smul', AlgEquiv.aut_inv, AlgEquiv.symm_symm]

theorem isRational_smul_iff : (σ • v).IsRational ↔ v.IsRational := by
  unfold IsRational
  have h : (algebraMap K (σ • v).ResidueField) = (smulResidueAlgEquiv σ v).toAlgHom.toRingHom.comp
      (algebraMap K v.ResidueField) := by
    ext a; simp
  rw [h, RingHom.coe_comp]
  constructor
  · intro hs
    have : Function.Surjective ((smulResidueAlgEquiv σ v).symm ∘ ((smulResidueAlgEquiv σ v).toAlgHom.toRingHom
        ∘ algebraMap K v.ResidueField)) := (smulResidueAlgEquiv σ v).symm.surjective.comp hs
    convert this using 1
    ext a; simp
  · intro hs
    exact (smulResidueAlgEquiv σ v).surjective.comp hs

theorem residue_smul {f : F} (hf : f ∈ v.toValuationSubring) (hf' : σ f ∈ (σ • v).toValuationSubring) :
    IsLocalRing.residue (σ • v).toValuationSubring ⟨σ f, hf'⟩
      = smulResidueAlgEquiv σ v (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩) := by
  have h1 : (⟨σ f, hf'⟩ : (σ • v).toValuationSubring) = smulRingEquiv σ v.toValuationSubring ⟨f, hf⟩ :=
    Subtype.ext rfl
  rw [h1]
  show _ = IsLocalRing.ResidueField.mapEquiv (smulRingEquiv σ v.toValuationSubring) _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  rfl

theorem evalAt_smul (hv : v.IsRational) (f : F) : (σ • v).evalAt (σ f) = v.evalAt f := by
  by_cases hf : f ∈ v.toValuationSubring
  · have hf' : σ f ∈ (σ • v).toValuationSubring := (mem_smul_iff' σ v f).mpr hf
    rw [(σ • v).evalAt_of_mem hf', residue_smul σ v hf hf', ← v.algebraMap_evalAt hv hf, AlgEquiv.commutes,
      residueInv_algebraMap]
  · have hf' : σ f ∉ (σ • v).toValuationSubring := fun h => hf ((mem_smul_iff' σ v f).mp h)
    rw [Place.evalAt, Place.evalAt, dif_neg hf, dif_neg hf']

theorem evalAt_smul_symm (hv : v.IsRational) (f : F) : (σ • v).evalAt f = v.evalAt (σ.symm f) := by
  conv_lhs => rw [← AlgEquiv.apply_symm_apply σ f]
  exact evalAt_smul σ v hv _

theorem evalAt_symm (hv : v.IsRational) (f : F) : v.evalAt (σ.symm f) = (σ • v).evalAt f :=
  (evalAt_smul_symm σ v hv f).symm

theorem smul_inv_smul' (P : Place K F) : σ • σ⁻¹ • P = P := smul_inv_smul σ P

theorem inv_smul_smul' (P : Place K F) : σ⁻¹ • σ • P = P := inv_smul_smul σ P

end Place.Transport

namespace ComponentChart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  (σ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar)

def comapIntegers : ValuationSubring F := C.integers.comap σ.toAlgHom.toRingHom

@[simp] theorem mem_comapIntegers (f : F) : f ∈ comapIntegers σ C ↔ σ f ∈ C.integers := Iff.rfl

def comapIntegersEquiv : comapIntegers σ C ≃+* C.integers where
  toFun x := ⟨σ x, x.2⟩
  invFun y := ⟨σ.symm y, by simp [mem_comapIntegers]⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv y := Subtype.ext (σ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul σ (x : F) (y : F))
  map_add' x y := Subtype.ext (map_add σ (x : F) (y : F))

@[simp] theorem coe_comapIntegersEquiv (x : comapIntegers σ C) : ((comapIntegersEquiv σ C x : C.integers) : F) = σ x := rfl

def comapResidue : comapIntegers σ C →+* Fbar := C.residue.comp (comapIntegersEquiv σ C).toRingHom

@[simp] theorem comapResidue_apply (x : comapIntegers σ C) : comapResidue σ C x = C.residue ⟨σ x, x.2⟩ := rfl

theorem comapResidue_surjective : Function.Surjective (comapResidue σ C) :=
  C.residue_surjective.comp (comapIntegersEquiv σ C).surjective

theorem ker_comapResidue : RingHom.ker (comapResidue σ C) = maximalIdeal (comapIntegers σ C) := by
  ext x
  rw [RingHom.mem_ker, comapResidue, RingHom.comp_apply, ← RingHom.mem_ker, C.ker_residue,
    IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
  exact (MulEquiv.isUnit_map (comapIntegersEquiv σ C).toMulEquiv).not

theorem comapResidue_algebraMap (a : A) :
    comapResidue σ C ⟨algebraMap L F a, by rw [mem_comapIntegers, AlgEquiv.commutes]; exact (C.algebraMap_mem_iff a).mpr a.2⟩
      = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
  rw [comapResidue_apply, ← C.residue_algebraMap a]
  congr 1
  exact Subtype.ext (AlgEquiv.commutes σ a)

def comap : ComponentChart A F Fbar where
  integers := comapIntegers σ C
  residue := comapResidue σ C
  dom := {P | σ • P ∈ C.dom}
  nodes := C.nodes
  placeMap P := C.placeMap (σ • P)
  algebraMap_mem_iff x := by
    rw [mem_comapIntegers, AlgEquiv.commutes]; exact C.algebraMap_mem_iff x
  residue_surjective := comapResidue_surjective σ C
  ker_residue := ker_comapResidue σ C
  residue_algebraMap a := comapResidue_algebraMap σ C a
  exists_smul_mem f hf := by
    obtain ⟨c, h, hres⟩ := C.exists_smul_mem (σ f) (by simpa using hf)
    refine ⟨c, by rw [mem_comapIntegers, map_smul]; exact h, ?_⟩
    rw [comapResidue_apply]
    convert hres using 2
    exact Subtype.ext (map_smul σ c f)
  placeMap_not_mem_nodes P hP := C.placeMap_not_mem_nodes (σ • P) hP
  pointwise P hP hrat f hf hreg := by
    have hrat' : (σ • P).IsRational := (Place.Transport.isRational_smul_iff σ P).mpr hrat
    have hreg' : ∀ w ∈ C.dom, C.placeMap w = C.placeMap (σ • P) → σ f ∈ w.toValuationSubring := by
      intro w hw hpw
      have hw1 : σ • σ⁻¹ • w ∈ C.dom := by rwa [smul_inv_smul]
      have h := hreg (σ⁻¹ • w) hw1 (by show C.placeMap (σ • σ⁻¹ • w) = C.placeMap (σ • P); rw [smul_inv_smul, hpw])
      rwa [Place.Transport.mem_inv_smul_iff] at h
    obtain ⟨hm, h, heq⟩ := C.pointwise (σ • P) hP hrat' (σ f) hf hreg'
    have e := Place.Transport.evalAt_smul σ P hrat f
    refine ⟨hm, e ▸ h, ?_⟩
    have hsub : (⟨P.evalAt f, e ▸ h⟩ : A) = ⟨(σ • P).evalAt (σ f), h⟩ := Subtype.ext e.symm
    rw [hsub]
    exact heq
  mapDomain_placeMap f hf D hD hD0 Q hQ := by
    have hmap : Finsupp.mapDomain (fun P => C.placeMap (σ • P)) D = Finsupp.mapDomain C.placeMap (σ • D) := by
      rw [Divisor.smul_def, ← Finsupp.mapDomain_comp]; rfl
    rw [hmap]
    have key := C.mapDomain_placeMap ⟨σ (f : F), f.2⟩ (by simpa [comapResidue_apply] using hf) (σ • D)
      (fun P hP => by
        rw [Divisor.smul_apply, hD (σ⁻¹ • P) (show σ • σ⁻¹ • P ∈ C.dom by rwa [smul_inv_smul]), Place.Transport.ord_inv_smul])
      (fun P hP => by
        rw [Divisor.smul_apply]
        exact hD0 _ (fun h => hP (by rwa [Set.mem_setOf_eq, smul_inv_smul] at h)))
      Q hQ
    rw [key, comapResidue_apply]

@[simp] theorem comap_integers : (C.comap σ).integers = comapIntegers σ C := rfl
@[simp] theorem mem_comap_integers (f : F) : f ∈ (C.comap σ).integers ↔ σ f ∈ C.integers := Iff.rfl
@[simp] theorem comap_dom : (C.comap σ).dom = {P | σ • P ∈ C.dom} := rfl
theorem mem_comap_dom (P : Place L F) : P ∈ (C.comap σ).dom ↔ σ • P ∈ C.dom := Iff.rfl
@[simp] theorem comap_nodes : (C.comap σ).nodes = C.nodes := rfl
@[simp] theorem comap_placeMap (P : Place L F) : (C.comap σ).placeMap P = C.placeMap (σ • P) := rfl
@[simp] theorem comap_residue_apply (x : (C.comap σ).integers) :
    (C.comap σ).residue x = C.residue ⟨σ (x : F), x.2⟩ := rfl

end ComponentChart

namespace Annulus

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  (σ : F ≃ₐ[L] F) (An : Annulus A F)

theorem evalAt_symm_param {P : Place L F} (hP : σ • P ∈ An.dom) :
    P.evalAt (σ.symm An.param) = (σ • P).evalAt An.param := by
  have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
  rw [Place.Transport.evalAt_smul_symm σ P hrat]

def comap : Annulus A F where
  dom := {P | σ • P ∈ An.dom}
  param := σ.symm An.param
  modulus := An.modulus
  modulus_mem := An.modulus_mem
  mem_dom P hP := by
    obtain ⟨hrat, hmem, hval, hne, hmod⟩ := An.mem_dom (σ • P) hP
    have hratP : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp hrat
    refine ⟨hratP, (Place.Transport.mem_smul_iff σ P An.param).mp hmem, ?_, ?_, ?_⟩ <;>
      rw [Place.Transport.evalAt_symm σ P hratP]
    exacts [hval, hne, hmod]
  existsUnique_evalAt_eq c hc hc0 hmod := by
    obtain ⟨P₀, ⟨hP₀, hval⟩, huniq⟩ := An.existsUnique_evalAt_eq c hc hc0 hmod
    refine ⟨σ⁻¹ • P₀, ⟨?_, ?_⟩, ?_⟩
    · show σ • σ⁻¹ • P₀ ∈ An.dom; rwa [smul_inv_smul]
    · have hrat : (σ⁻¹ • P₀).IsRational := by
        rw [← Place.Transport.isRational_smul_iff σ, smul_inv_smul]; exact (An.mem_dom _ hP₀).1
      rw [Place.Transport.evalAt_symm σ _ hrat, smul_inv_smul]; exact hval
    · rintro P ⟨hP, hPval⟩
      have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
      rw [Place.Transport.evalAt_symm σ P hrat] at hPval
      have := huniq (σ • P) ⟨hP, hPval⟩
      rw [← this, inv_smul_smul]
  ord_param_sub P hP := by
    have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
    have h := An.ord_param_sub (σ • P) hP
    rw [Place.Transport.ord_smul', map_sub, AlgEquiv.commutes] at h
    rw [Place.Transport.evalAt_symm σ P hrat]
    exact h
  unit_principle f hf0 hord := by
    have hord' : ∀ P₀ ∈ An.dom, P₀.ord (σ f) = 0 := by
      intro P₀ hP₀
      have h := hord (σ⁻¹ • P₀) (show σ • σ⁻¹ • P₀ ∈ An.dom by rwa [smul_inv_smul])
      rwa [Place.Transport.ord_inv_smul] at h
    obtain ⟨m, c, hc, H⟩ := An.unit_principle (σ f) (by simpa using hf0) hord'
    refine ⟨m, c, hc, fun P hP => ?_⟩
    have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
    obtain ⟨h, hu⟩ := H (σ • P) hP
    have key : P.evalAt f * c⁻¹ * P.evalAt (σ.symm An.param) ^ (-m)
        = (σ • P).evalAt (σ f) * c⁻¹ * (σ • P).evalAt An.param ^ (-m) := by
      rw [Place.Transport.evalAt_smul σ P hrat, Place.Transport.evalAt_symm σ P hrat]
    refine ⟨key ▸ h, ?_⟩
    have hsub : (⟨_, key ▸ h⟩ : A) = ⟨_, h⟩ := Subtype.ext key
    rw [hsub]; exact hu

@[simp] theorem comap_dom : (An.comap σ).dom = {P | σ • P ∈ An.dom} := rfl
theorem mem_comap_dom (P : Place L F) : P ∈ (An.comap σ).dom ↔ σ • P ∈ An.dom := Iff.rfl
@[simp] theorem comap_param : (An.comap σ).param = σ.symm An.param := rfl
@[simp] theorem comap_modulus : (An.comap σ).modulus = An.modulus := rfl

variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem IsAttached.comap {C : ComponentChart A F Fbar} {x : Place (ResidueField A) Fbar}
    (h : An.IsAttached C x) : (An.comap σ).IsAttached (C.comap σ) x := by
  obtain ⟨hx, hz, hord, hslope⟩ := h
  have hz' : σ.symm An.param ∈ (C.comap σ).integers := by
    rw [ComponentChart.mem_comap_integers, AlgEquiv.apply_symm_apply]; exact hz
  refine ⟨hx, hz', ?_, ?_⟩
  · rw [ComponentChart.comap_residue_apply]
    convert hord using 3
    exact Subtype.ext (σ.apply_symm_apply An.param)
  · intro f hf hres hordf P hP
    have hres' : C.residue ⟨σ f, hf⟩ ≠ 0 := by rwa [ComponentChart.comap_residue_apply] at hres
    have hordf' : ∀ P₀ ∈ An.dom, P₀.ord (σ f) = 0 := by
      intro P₀ hP₀
      have h := hordf (σ⁻¹ • P₀) (show σ • σ⁻¹ • P₀ ∈ An.dom by rwa [smul_inv_smul])
      rwa [Place.Transport.ord_inv_smul] at h
    have hrat : P.IsRational := (Place.Transport.isRational_smul_iff σ P).mp (An.mem_dom _ hP).1
    obtain ⟨h, hu⟩ := hslope (σ f) hf hres' hordf' (σ • P) hP
    have key : P.evalAt f * P.evalAt (σ.symm An.param) ^ (-(x.ord ((C.comap σ).residue ⟨f, hf⟩)))
        = (σ • P).evalAt (σ f) * (σ • P).evalAt An.param ^ (-(x.ord (C.residue ⟨σ f, hf⟩))) := by
      rw [Place.Transport.evalAt_smul σ P hrat, Place.Transport.evalAt_symm σ P hrat, ComponentChart.comap_residue_apply]
    refine ⟨key ▸ h, ?_⟩
    convert hu using 1
    exact Subtype.ext key

theorem IsAttached.of_comap {C : ComponentChart A F Fbar} {x : Place (ResidueField A) Fbar}
    (h : (An.comap σ).IsAttached (C.comap σ) x) : An.IsAttached C x := by
  obtain ⟨hx, hz', hord', hslope'⟩ := h
  have hz : An.param ∈ C.integers := by
    have := hz'; rw [ComponentChart.mem_comap_integers, comap_param, AlgEquiv.apply_symm_apply] at this; exact this
  refine ⟨hx, hz, ?_, ?_⟩
  · rw [ComponentChart.comap_residue_apply] at hord'
    convert hord' using 3
    exact Subtype.ext (σ.apply_symm_apply An.param).symm
  · intro f hf hres hordf P hP
    have hf' : σ.symm f ∈ (C.comap σ).integers := by
      rw [ComponentChart.mem_comap_integers, AlgEquiv.apply_symm_apply]; exact hf
    have hres' : (C.comap σ).residue ⟨σ.symm f, hf'⟩ ≠ 0 := by
      rw [ComponentChart.comap_residue_apply]
      convert hres using 2
      exact Subtype.ext (σ.apply_symm_apply f)
    have hordf' : ∀ Q ∈ (An.comap σ).dom, Q.ord (σ.symm f) = 0 := by
      intro Q hQ
      rw [← Place.Transport.ord_smul' σ Q f]
      exact hordf (σ • Q) hQ
    have hPQ : σ⁻¹ • P ∈ (An.comap σ).dom := by
      show σ • σ⁻¹ • P ∈ An.dom; rwa [smul_inv_smul]
    have hrat : (σ⁻¹ • P).IsRational := by
      rw [← Place.Transport.isRational_smul_iff σ, smul_inv_smul]; exact (An.mem_dom _ hP).1
    obtain ⟨h, hu⟩ := hslope' (σ.symm f) hf' hres' hordf' (σ⁻¹ • P) hPQ
    have e1 : (σ⁻¹ • P).evalAt (σ.symm f) = P.evalAt f := by
      rw [Place.Transport.evalAt_symm σ _ hrat, smul_inv_smul]
    have e2 : (σ⁻¹ • P).evalAt (An.comap σ).param = P.evalAt An.param := by
      rw [comap_param, Place.Transport.evalAt_symm σ _ hrat, smul_inv_smul]
    have e3 : x.ord ((C.comap σ).residue ⟨σ.symm f, hf'⟩) = x.ord (C.residue ⟨f, hf⟩) := by
      rw [ComponentChart.comap_residue_apply]
      congr 2
      exact Subtype.ext (σ.apply_symm_apply f)
    have key : P.evalAt f * P.evalAt An.param ^ (-(x.ord (C.residue ⟨f, hf⟩)))
        = (σ⁻¹ • P).evalAt (σ.symm f) * (σ⁻¹ • P).evalAt (An.comap σ).param
            ^ (-(x.ord ((C.comap σ).residue ⟨σ.symm f, hf'⟩))) := by
      rw [e1, e2, e3]
    refine ⟨key ▸ h, ?_⟩
    convert hu using 1
    exact Subtype.ext key

theorem isAttached_comap_iff {C : ComponentChart A F Fbar} {x : Place (ResidueField A) Fbar} :
    (An.comap σ).IsAttached (C.comap σ) x ↔ An.IsAttached C x :=
  ⟨IsAttached.of_comap σ An, IsAttached.comap σ An⟩

theorem mem_comap_comap_dom (τ : F ≃ₐ[L] F) (P : Place L F) :
    P ∈ ((An.comap σ).comap τ).dom ↔ σ • τ • P ∈ An.dom := Iff.rfl

theorem comap_comap_param (τ : F ≃ₐ[L] F) : ((An.comap σ).comap τ).param = τ.symm (σ.symm An.param) := rfl

theorem mem_comap_symm_dom (P : Place L F) : P ∈ ((An.comap σ).comap σ.symm).dom ↔ P ∈ An.dom := by
  rw [mem_comap_comap_dom]
  show σ • σ⁻¹ • P ∈ An.dom ↔ P ∈ An.dom
  rw [smul_inv_smul]

theorem comap_symm_param : ((An.comap σ).comap σ.symm).param = An.param := by
  rw [comap_comap_param, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]

end Annulus

namespace ComponentChart

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
  (σ τ : F ≃ₐ[L] F) (C : ComponentChart A F Fbar)

theorem mem_comap_comap_integers (f : F) : f ∈ ((C.comap σ).comap τ).integers ↔ σ (τ f) ∈ C.integers := Iff.rfl

theorem mem_comap_comap_dom (P : Place L F) : P ∈ ((C.comap σ).comap τ).dom ↔ σ • τ • P ∈ C.dom := Iff.rfl

theorem comap_comap_placeMap (P : Place L F) : ((C.comap σ).comap τ).placeMap P = C.placeMap (σ • τ • P) := rfl

theorem mem_comap_symm_integers (f : F) : f ∈ ((C.comap σ).comap σ.symm).integers ↔ f ∈ C.integers := by
  rw [mem_comap_comap_integers, AlgEquiv.apply_symm_apply]

theorem mem_comap_symm_dom (P : Place L F) : P ∈ ((C.comap σ).comap σ.symm).dom ↔ P ∈ C.dom := by
  rw [mem_comap_comap_dom]
  show σ • σ⁻¹ • P ∈ C.dom ↔ P ∈ C.dom
  rw [smul_inv_smul]

theorem comap_symm_placeMap (P : Place L F) : ((C.comap σ).comap σ.symm).placeMap P = C.placeMap P := by
  rw [comap_comap_placeMap]
  show C.placeMap (σ • σ⁻¹ • P) = C.placeMap P
  rw [smul_inv_smul]

theorem comap_symm_residue_apply (f : F) (hf : f ∈ ((C.comap σ).comap σ.symm).integers) (hf' : f ∈ C.integers) :
    ((C.comap σ).comap σ.symm).residue ⟨f, hf⟩ = C.residue ⟨f, hf'⟩ := by
  rw [comap_residue_apply, comap_residue_apply]
  congr 1
  exact Subtype.ext (σ.apply_symm_apply f)

end ComponentChart

end AlgebraicCurve

end


