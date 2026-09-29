-- Prove2me | Definitions.Def_GroupCohomology_LocallyConstantClasses
-- name    : GroupCohomology_LocallyConstantClasses
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/c27b4974-515a-5572-8b62-1437131f85e0
-- title:
--   Inflation in degree one and locally constant classes
-- statement:
--   Throughout, $k$ is a commutative ring, $G$ a group and $M$ an object of `Rep k G`, i.e. a $k$-linear representation of $G$. For a normal subgroup $S \trianglelefteq G$, [`groupCohomology.inflation M S`](../def/GroupCohomology_LocallyConstantClasses.html#L13) is the morphism $H^1(G/S, M^S) \to H^1(G,M)$ obtained by applying the degree-one functoriality `groupCohomology.map` of group cohomology to the quotient homomorphism $G \to G/S$ together with the representation morphism that realises $M^S$, viewed as a $G/S$-representation via `Rep.quotientToInvariants`, inside $M$; it is recorded to be exactly the first map of Mathlib's inflation–restriction sequence object `H1InfRes M S` (`inflation_eq_H1InfRes_f`). The submodule [`groupCohomology.inflationImage M S`](../def/GroupCohomology_LocallyConstantClasses.html#L21) of $H^1(G,M)$ is the range of the underlying $k$-linear map of this morphism, i.e. the submodule of classes inflated from level $S$; two helper lemmas unfold membership in it as the existence of a preimage and state that inflated classes lie in it.
--
--   The main definition, [`groupCohomology.locallyConstantClasses M`](../def/GroupCohomology_LocallyConstantClasses.html#L34), is the supremum in the lattice of $k$-submodules of $H^1(G,M)$ — that is, the sum — of the submodules `inflationImage M S` as $S$ ranges over the subtype of subgroups of $G$ that are simultaneously normal and of finite index, the normality instance needed to form the inflation map being supplied by the first component of that conjunction. Thus a class is locally constant precisely when it is a finite sum of classes each inflated from a finite quotient of $G$. Two order lemmas accompany the definition: for every normal subgroup of finite index the corresponding inflation image is contained in `locallyConstantClasses M`, and consequently any submodule contained in a single inflation image is contained in `locallyConstantClasses M`.
--
--   **Relation to Mathlib.** The inflation morphism is defined from Mathlib's degree-one functoriality `groupCohomology.map` and is identified with the first component of Mathlib's inflation–restriction datum `H1InfRes`; the submodule of locally constant classes, i.e. the sum of the images of inflation from all finite quotients, is the project's own notion.
--
--   **Where it is used.** For a Galois group treated as a bare group, a continuous cocycle with values in a finite discrete module factors through a finite quotient, so the submodule of locally constant classes contains all continuous classes while remaining a submodule of the abstract $H^1$; it serves as the ambient module in which Selmer groups and their local conditions are formulated for the Greenberg–Wiles-style numerology used in the $R = T$ argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_LocallyConstantClasses.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

namespace groupCohomology

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

noncomputable abbrev inflation (M : Rep k G) (S : Subgroup G) [S.Normal] :
    H1 (M.quotientToInvariants S) ⟶ H1 M :=
  groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (M.ρ.quotientToInvariants_lift S)) 1

lemma inflation_eq_H1InfRes_f (M : Rep k G) (S : Subgroup G) [S.Normal] :
    inflation M S = (H1InfRes M S).f :=
  rfl

noncomputable def inflationImage (M : Rep k G) (S : Subgroup G) [S.Normal] :
    Submodule k (H1 M) :=
  LinearMap.range (inflation M S).hom

lemma mem_inflationImage_iff (M : Rep k G) (S : Subgroup G) [S.Normal] (x : H1 M) :
    x ∈ inflationImage M S ↔ ∃ y, (inflation M S).hom y = x :=
  Iff.rfl

lemma inflation_mem_inflationImage (M : Rep k G) (S : Subgroup G) [S.Normal]
    (y : H1 (M.quotientToInvariants S)) :
    (inflation M S).hom y ∈ inflationImage M S :=
  LinearMap.mem_range_self _ y

noncomputable def locallyConstantClasses (M : Rep k G) : Submodule k (H1 M) :=
  ⨆ S : {S : Subgroup G // S.Normal ∧ S.FiniteIndex},
    haveI : S.1.Normal := S.2.1
    inflationImage M S.1

lemma inflationImage_le_locallyConstantClasses (M : Rep k G) (S : Subgroup G) [hN : S.Normal]
    [hF : S.FiniteIndex] : inflationImage M S ≤ locallyConstantClasses M :=
  le_iSup (fun S : {S : Subgroup G // S.Normal ∧ S.FiniteIndex} =>
    haveI : S.1.Normal := S.2.1
    inflationImage M S.1) ⟨S, hN, hF⟩

lemma le_locallyConstantClasses_of_le_inflationImage (M : Rep k G) {L : Submodule k (H1 M)}
    {S : Subgroup G} [S.Normal] [S.FiniteIndex] (hL : L ≤ inflationImage M S) :
    L ≤ locallyConstantClasses M :=
  hL.trans (inflationImage_le_locallyConstantClasses M S)

end groupCohomology


