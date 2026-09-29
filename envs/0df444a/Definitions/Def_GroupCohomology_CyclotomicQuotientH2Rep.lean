-- Prove2me | Definitions.Def_GroupCohomology_CyclotomicQuotientH2Rep
-- name    : GroupCohomology_CyclotomicQuotientH2Rep
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/d7fbe832-926f-5b74-9b13-6db453b3d54f
-- title:
--   Twisted permutation module, right translations, and its level-S H2
-- statement:
--   Throughout, $K$ and $L$ are intermediate fields of $\mathbb{Q}$ in $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, $p$ is a prime, $S$ is a finite set of primes, and $\Lambda :=$ `L.fixingSubgroup.subgroupOf K.fixingSubgroup`, the intersection of the two fixing subgroups viewed inside $\Gamma_K :=$ `K.fixingSubgroup`, is assumed normal in $\Gamma_K$. The module `cyclotomicQuotientRep K L p` is the $\mathbb{F}_p$-representation of $\Gamma_K$ on finitely supported functions $\Gamma_K/\Lambda \to \mathbb{Z}/p$ with the left translation action, twisted by the mod-$p$ cyclotomic character `cycloChar p` restricted along the inclusion $\Gamma_K \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; that is, $\mathbb{F}_p[\Gamma_K/\Lambda](1)$. For $c \in \Gamma_K$, `cyclotomicQuotientRT K L p c` is the endomorphism of this twisted module given by right translation $q \mapsto q\bar{c}^{-1}$ of the index set, $\bar c$ being the image of $c$ in $\Gamma_K/\Lambda$. Three lemmas record that this operator is the identity for $c = 1$, that it is the identity whenever $c$, regarded as an element of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, lies in `L.fixingSubgroup`, and that $R_{cc'} = R_{c'}$ followed by $R_c$.
--
--   Applying the functoriality map `continuousH2SrMapHom` for the level-$S$ continuous second cohomology `continuousH2Sr` attached to the inclusion $\Gamma_K \hookrightarrow \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, the assignment $c \mapsto H^2_S(R_c)$ is shown to be a representation `cyclotomicQuotientH2ρ` of $\Gamma_K$ on $H^2_S(\Gamma_K, \mathbb{F}_p[\Gamma_K/\Lambda](1))$, the unit and multiplicativity axioms coming from the three lemmas together with the identity and composition laws for `continuousH2SrMapHom`. `cyclotomicQuotientH2Rep S K L p` is the corresponding object of `Rep (ZMod p) ↥K.fixingSubgroup`; its action is computed by `cyclotomicQuotientH2Rep_ρ_apply`, and `cyclotomicQuotientH2Rep_ρ_eq_one_of_mem` states that elements of $\Gamma_K$ lying in `L.fixingSubgroup` act trivially, so the action factors through $\Gamma_K/\Lambda$.
--
--   **Relation to Mathlib.** The underlying permutation module is [`Rep.ofMulActionFinsupp`](../def/Compat_Mathlib430.html#L100), a verbatim copy of a Mathlib definition kept under a new name for version compatibility. The level-$S$ continuous cohomology `continuousH2Sr` and its functoriality `continuousH2SrMapHom` are project notions; Mathlib's group cohomology carries no such level condition.
--
--   **Where it is used.** This supplies the coefficient module on which the global class field theory input of the Selmer-group argument is docked: a $\Gamma_K$-module structure, trivial on the subgroup fixing $L$, on the level-$S$ second cohomology of the cyclotomically twisted permutation module $\mathbb{F}_p[\Gamma_K/\Lambda](1)$, so that the action is one of $\Gamma_K/\Lambda$ and can be compared with $H^2(G_{L,S}, \mu_p)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_CyclotomicQuotientH2Rep.lean

import Mathlib
import Definitions.Def_Rep_QuotientRightTranslation
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace groupCohomology

open CategoryTheory ExtCitation

abbrev cyclotomicQuotientRep (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime] : Rep (ZMod p) ↥K.fixingSubgroup :=
  (Rep.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)).twist
    ((cycloChar p).comp K.fixingSubgroup.subtype)

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime]
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]

abbrev cyclotomicQuotientRT (c : ↥K.fixingSubgroup) : cyclotomicQuotientRep K L p ⟶ cyclotomicQuotientRep K L p :=
  Rep.quotientRightTranslationTwist (L.fixingSubgroup.subgroupOf K.fixingSubgroup) ((cycloChar p).comp K.fixingSubgroup.subtype)
    (c : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)

theorem cyclotomicQuotientRT_one : cyclotomicQuotientRT K L p 1 = 𝟙 _ := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  change Finsupp.mapDomain (fun q => q * ((QuotientGroup.mk 1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup))⁻¹) x = x
  rw [QuotientGroup.mk_one, inv_one]
  simp only [mul_one]
  exact Finsupp.mapDomain_id

theorem cyclotomicQuotientRT_of_mem (c : ↥K.fixingSubgroup) (hc : (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup) :
    cyclotomicQuotientRT K L p c = 𝟙 _ := by
  have h1 : (c : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) = 1 :=
    (QuotientGroup.eq_one_iff c).2 (Subgroup.mem_subgroupOf.2 hc)
  have h2 : (c : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) = ((1 : ↥K.fixingSubgroup) : _ ⧸ _) := by
    rw [h1, QuotientGroup.mk_one]
  change Rep.quotientRightTranslationTwist _ _ (c : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) = _
  rw [h2]
  exact cyclotomicQuotientRT_one K L p

theorem cyclotomicQuotientRT_mul (c c' : ↥K.fixingSubgroup) :
    cyclotomicQuotientRT K L p (c * c') = cyclotomicQuotientRT K L p c' ≫ cyclotomicQuotientRT K L p c := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  change Finsupp.mapDomain (fun q => q * ((QuotientGroup.mk (c * c') : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup))⁻¹) x =
    Finsupp.mapDomain (fun q => q * ((QuotientGroup.mk c : _ ⧸ _))⁻¹) (Finsupp.mapDomain (fun q => q * ((QuotientGroup.mk c' : _ ⧸ _))⁻¹) x)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  ext q
  simp only [Function.comp_apply, QuotientGroup.mk_mul, mul_inv_rev, mul_assoc]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

def cyclotomicQuotientH2ρ : Representation (ZMod p) ↥K.fixingSubgroup (continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p)) where
  toFun c := continuousH2SrMapHom S K.fixingSubgroup.subtype (cyclotomicQuotientRT K L p c)
  map_one' := (congrArg (continuousH2SrMapHom S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p) (B := cyclotomicQuotientRep K L p))
      (cyclotomicQuotientRT_one K L p)).trans (continuousH2SrMapHom_id S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p))
  map_mul' c c' := (congrArg (continuousH2SrMapHom S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p) (B := cyclotomicQuotientRep K L p))
      (cyclotomicQuotientRT_mul K L p c c')).trans (continuousH2SrMapHom_comp S K.fixingSubgroup.subtype _ _)

set_option synthInstance.maxHeartbeats 400000 in

def cyclotomicQuotientH2Rep : Rep (ZMod p) ↥K.fixingSubgroup := Rep.of (cyclotomicQuotientH2ρ S K L p)

set_option synthInstance.maxHeartbeats 400000 in
theorem cyclotomicQuotientH2Rep_ρ_apply (c : ↥K.fixingSubgroup) (x : cyclotomicQuotientH2Rep S K L p) :
    (cyclotomicQuotientH2Rep S K L p).ρ c x = continuousH2SrMapHom S K.fixingSubgroup.subtype (cyclotomicQuotientRT K L p c) x := rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem cyclotomicQuotientH2Rep_ρ_eq_one_of_mem (c : ↥K.fixingSubgroup) (hc : (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup) :
    (cyclotomicQuotientH2Rep S K L p).ρ c = 1 :=
  (congrArg (continuousH2SrMapHom S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p) (B := cyclotomicQuotientRep K L p))
      (cyclotomicQuotientRT_of_mem K L p c hc)).trans (continuousH2SrMapHom_id S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p))

end groupCohomology

end


