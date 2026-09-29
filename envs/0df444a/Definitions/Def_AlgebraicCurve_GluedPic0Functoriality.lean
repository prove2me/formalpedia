-- Prove2me | Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
-- name    : AlgebraicCurve_GluedPic0Functoriality
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/caa0faf8-722f-54c4-823e-2425076714fc
-- title:
--   Semilinear functoriality of the glued degree-zero Picard group
-- statement:
--   Throughout, $F$ is a field extension of a field $K$, $S$ is a finite set of ordered pairs of places of $F/K$ (a place being a valuation subring of $F$ containing $K$, proper and a principal ideal ring), and $g$ is an element of `SemilinearAut K F`, i.e. a pair consisting of a ring automorphism of $F$ and a ring automorphism `baseAut g` of $K$ which are compatible with the structure map $K \to F$. First, transport of values: if $f$ lies in the valuation subring of $v$ and its residue is the image of $a \in K$, then $g \cdot f$ lies in the valuation subring of $g \cdot v$ with residue the image of `baseAut g` $a$. Next, `IsNodeStable S g` asserts that $(g \cdot s_1, g \cdot s_2) \in S$ for every $s \in S$; under this hypothesis $g$ induces a permutation `nodePerm` of $S$ (injectivity of the action on places plus finiteness of $S$), whose inverse is described explicitly by $g^{-1}$, and $g^{-1}$ is again node stable. The additive endomorphism `baseAutUnitsHom` of `Additive Kˣ` is `baseAut g` applied to units. On gluing data, triples $(D_1, D_2, w)$ with $D_i$ divisors and $w : S \to$ `Additive Kˣ`, `gluingMap` sends such a triple to $(g \cdot D_1, g \cdot D_2, t \mapsto \mathrm{baseAut}(g)(w(\mathrm{nodePerm}^{-1} t)))$; it preserves admissibility (both divisors of degree zero, $D_1$ vanishing at each $s_1$ and $D_2$ at each $s_2$) and the glued-principal condition, whence `admissibleMap` on admissible data and, by descent to the quotient, the additive endomorphism `glueMap` of `GluedPic0 K F S`. Two identities are recorded: the projection to $\mathrm{Pic}^0 \times \mathrm{Pic}^0$ carries `glueMap` to the action of $g$ on each factor, and on the node-unit subgroup `glueMap` acts by `baseAut g` on values composed with the inverse node permutation.
--
--   **Relation to Mathlib.** Places, divisors, $\mathrm{Pic}^0$, the glued Picard group and the group `SemilinearAut K F` of ring automorphisms of $F$ covering an automorphism of $K$ are all notions of this project; Mathlib supplies the underlying valuation subrings, pointwise group actions on subrings, residue fields and quotient-group machinery.
--
--   **Where it is used.** The glued degree-zero Picard group models the Picard group of a curve obtained by identifying finitely many pairs of places, and its $p$-power torsion is the source of the Galois representations attached to such curves. The constructions here provide the semilinear (in particular Galois) functoriality of that group, so that the torsion subgroups become modules over the relevant automorphism groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_GluedPic0Functoriality.lean

import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

open scoped Pointwise

section Functoriality

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Place.HasValue.smul {v : Place K F} {f : F} {a : K} (g : SemilinearAut K F)
    (h : v.HasValue f a) : (g • v).HasValue (g • f) (SemilinearAut.baseAut g a) := by
  obtain ⟨hm, hr⟩ := h
  have hmem : g • f ∈ (g • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g f v.toValuationSubring hm
  refine ⟨hmem, ?_⟩
  have hx : (⟨g • f, hmem⟩ : (g • v).toValuationSubring)
      = SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨f, hm⟩ := by
    ext
    rw [SemilinearAut.coe_smulValuationSubringEquiv_apply]
  rw [hx]
  have hres : residue ((g • v).toValuationSubring)
        (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨f, hm⟩)
      = SemilinearAut.smulResidueRingEquiv g v (residue v.toValuationSubring ⟨f, hm⟩) := by
    rw [SemilinearAut.smulResidueRingEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  rw [hres, hr, SemilinearAut.smulResidueRingEquiv_algebraMap]

namespace SemilinearAut

variable (S : Finset (Place K F × Place K F))

def IsNodeStable (g : SemilinearAut K F) : Prop :=
  ∀ s ∈ S, (g • s.1, g • s.2) ∈ S

variable (g : SemilinearAut K F)

def nodePerm (hstab : IsNodeStable S g) : ↥S ≃ ↥S :=
  Equiv.ofBijective
    (fun s => ⟨(g • (s : Place K F × Place K F).1, g • (s : Place K F × Place K F).2),
      hstab _ s.2⟩)
    (Finite.injective_iff_bijective.mp (by
      intro s t hst
      have h1 := congrArg (fun z : ↥S => (z : Place K F × Place K F).1) hst
      have h2 := congrArg (fun z : ↥S => (z : Place K F × Place K F).2) hst
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact MulAction.injective g (by simpa using h1)
      · exact MulAction.injective g (by simpa using h2)))

@[simp]
theorem nodePerm_apply (hstab : IsNodeStable S g) (s : ↥S) :
    (nodePerm S g hstab s : Place K F × Place K F)
      = (g • (s : Place K F × Place K F).1, g • (s : Place K F × Place K F).2) :=
  rfl

theorem nodePerm_symm_apply (hstab : IsNodeStable S g) (t : ↥S) :
    ((nodePerm S g hstab).symm t : Place K F × Place K F)
      = (g⁻¹ • (t : Place K F × Place K F).1, g⁻¹ • (t : Place K F × Place K F).2) := by
  have h := nodePerm_apply S g hstab ((nodePerm S g hstab).symm t)
  rw [Equiv.apply_symm_apply] at h
  refine Prod.ext ?_ ?_
  · rw [eq_inv_smul_iff]
    exact (congrArg Prod.fst h).symm
  · rw [eq_inv_smul_iff]
    exact (congrArg Prod.snd h).symm

theorem IsNodeStable.inv (hstab : IsNodeStable S g) : IsNodeStable S g⁻¹ := by
  intro s hs
  have hsym := nodePerm_symm_apply S g hstab ⟨s, hs⟩
  exact hsym ▸ ((nodePerm S g hstab).symm ⟨s, hs⟩).2

def baseAutUnitsHom : Additive Kˣ →+ Additive Kˣ :=
  AddMonoidHom.mk'
    (fun x => Additive.ofMul (Units.map ((baseAut g : K →+* K) : K →* K) x.toMul))
    (fun x y => by simp)

@[simp]
theorem baseAutUnitsHom_apply (x : Additive Kˣ) :
    baseAutUnitsHom g x
      = Additive.ofMul (Units.map ((baseAut g : K →+* K) : K →* K) x.toMul) :=
  rfl

def gluingMap (hstab : IsNodeStable S g) :
    GluingData K F S →+ GluingData K F S :=
  AddMonoidHom.mk'
    (fun x => (g • x.1, g • x.2.1,
      fun t => baseAutUnitsHom g (x.2.2 ((nodePerm S g hstab).symm t))))
    (fun x y => by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [smul_add]
      · simp [smul_add]
      · funext t
        simp)

@[simp]
theorem gluingMap_apply (hstab : IsNodeStable S g) (x : GluingData K F S) :
    gluingMap S g hstab x = (g • x.1, g • x.2.1,
      fun t => baseAutUnitsHom g (x.2.2 ((nodePerm S g hstab).symm t))) :=
  rfl

theorem gluingMap_mem_admissible (hstab : IsNodeStable S g) {x : GluingData K F S}
    (hx : x ∈ GluingData.admissible S) :
    gluingMap S g hstab x ∈ GluingData.admissible S := by
  obtain ⟨h₁, h₂, hav⟩ := hx
  refine ⟨smul_mem_degZero g h₁, smul_mem_degZero g h₂, fun s hs => ?_⟩
  obtain ⟨hz₁, hz₂⟩ := hav _ (IsNodeStable.inv S g hstab s hs)
  constructor
  · rw [show (gluingMap S g hstab x).1 = g • x.1 from rfl, divisor_smul_apply]
    exact hz₁
  · rw [show (gluingMap S g hstab x).2.1 = g • x.2.1 from rfl, divisor_smul_apply]
    exact hz₂

theorem gluingMap_mem_gluedPrincipal (hstab : IsNodeStable S g) {x : GluingData K F S}
    (hx : GluingData.IsGluedPrincipal S x) :
    GluingData.IsGluedPrincipal S (gluingMap S g hstab x) := by
  obtain ⟨g₁, g₂, a, b, hg₁, hg₂, h₁, h₂, hv, hw⟩ := hx
  refine ⟨g • g₁, g • g₂,
    fun t => Units.map ((baseAut g : K →+* K) : K →* K) (a ((nodePerm S g hstab).symm t)),
    fun t => Units.map ((baseAut g : K →+* K) : K →* K) (b ((nodePerm S g hstab).symm t)),
    by simpa using hg₁, by simpa using hg₂, fun v => ?_, fun v => ?_, fun t => ⟨?_, ?_⟩, ?_⟩
  · rw [show (gluingMap S g hstab x).1 = g • x.1 from rfl, divisor_smul_apply, h₁ (g⁻¹ • v)]
    have h := ord_smul g (g⁻¹ • v) g₁
    rw [smul_inv_smul] at h
    exact h.symm
  · rw [show (gluingMap S g hstab x).2.1 = g • x.2.1 from rfl, divisor_smul_apply,
      h₂ (g⁻¹ • v)]
    have h := ord_smul g (g⁻¹ • v) g₂
    rw [smul_inv_smul] at h
    exact h.symm
  · have hs := (hv ((nodePerm S g hstab).symm t)).1
    have hres := Place.HasValue.smul g hs
    have hc : (((nodePerm S g hstab).symm t : Place K F × Place K F)).1
        = g⁻¹ • (t : Place K F × Place K F).1 :=
      congrArg Prod.fst (nodePerm_symm_apply S g hstab t)
    rw [hc, smul_inv_smul] at hres
    exact hres
  · have hs := (hv ((nodePerm S g hstab).symm t)).2
    have hres := Place.HasValue.smul g hs
    have hc : (((nodePerm S g hstab).symm t : Place K F × Place K F)).2
        = g⁻¹ • (t : Place K F × Place K F).2 :=
      congrArg Prod.snd (nodePerm_symm_apply S g hstab t)
    rw [hc, smul_inv_smul] at hres
    exact hres
  · rw [show (gluingMap S g hstab x).2.2
        = fun t => baseAutUnitsHom g (x.2.2 ((nodePerm S g hstab).symm t)) from rfl, hw]
    funext t
    simp [div_eq_mul_inv]

def admissibleMap (hstab : IsNodeStable S g) :
    ↥(GluingData.admissible S) →+ ↥(GluingData.admissible S) :=
  ((gluingMap S g hstab).domRestrict (GluingData.admissible S)).codRestrict _
    (fun x => gluingMap_mem_admissible S g hstab x.2)

@[simp]
theorem coe_admissibleMap (hstab : IsNodeStable S g) (x : ↥(GluingData.admissible S)) :
    (admissibleMap S g hstab x : GluingData K F S) = gluingMap S g hstab (x : GluingData K F S) :=
  rfl

end SemilinearAut

namespace GluedPic0

open SemilinearAut

variable (S : Finset (Place K F × Place K F)) (g : SemilinearAut K F)

def glueMap (hstab : IsNodeStable S g) : GluedPic0 K F S →+ GluedPic0 K F S :=
  QuotientAddGroup.map _ _ (admissibleMap S g hstab) (by
    rintro x hx
    simp only [AddSubgroup.mem_addSubgroupOf] at hx ⊢
    exact gluingMap_mem_gluedPrincipal S g hstab hx)

@[simp]
theorem glueMap_mk (hstab : IsNodeStable S g) (x : ↥(GluingData.admissible S)) :
    glueMap S g hstab (mk S x) = mk S (admissibleMap S g hstab x) :=
  rfl

theorem toPic0Pair_glueMap (hstab : IsNodeStable S g) (ξ : GluedPic0 K F S) :
    toPic0Pair S (glueMap S g hstab ξ)
      = (g • (toPic0Pair S ξ).1, g • (toPic0Pair S ξ).2) := by
  obtain ⟨x, rfl⟩ := mk_surjective S ξ
  rw [glueMap_mk, toPic0Pair_mk, toPic0Pair_mk]
  refine Prod.ext ?_ ?_
  · rw [pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [coe_degZeroSMulHom]; rfl))
  · rw [pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [coe_degZeroSMulHom]; rfl))

theorem glueMap_nodeUnit (hstab : IsNodeStable S g) (w : ↥S → Additive Kˣ) :
    glueMap S g hstab (nodeUnit S w)
      = nodeUnit S (fun t => baseAutUnitsHom g (w ((nodePerm S g hstab).symm t))) := by
  rw [nodeUnit_apply, nodeUnit_apply, glueMap_mk]
  refine congrArg (mk S) (Subtype.ext ?_)
  rw [coe_admissibleMap]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show g • (0 : Divisor K F) = 0
    exact smul_zero g
  · show g • (0 : Divisor K F) = 0
    exact smul_zero g
  · rfl

end GluedPic0

end Functoriality

end AlgebraicCurve

end


