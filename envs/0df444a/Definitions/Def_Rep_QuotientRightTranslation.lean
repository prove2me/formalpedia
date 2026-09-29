-- Prove2me | Definitions.Def_Rep_QuotientRightTranslation
-- name    : Rep_QuotientRightTranslation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/c9f9ded5-83c0-5850-9848-aec2945363e5
-- title:
--   Right-translation endomorphisms of the permutation module of a quotient group
-- statement:
--   Fix a commutative ring $k$, a group $G$ and a normal subgroup $\Lambda \le G$, and consider the $k$-linear permutation representation of $G$ on the finitely supported functions $(G/\Lambda) \to k$, with $G$ acting through left translation on the index set: this is [`Rep.ofMulActionFinsupp k G (G ⧸ Λ)`](../def/Compat_Mathlib430.html#L100), an object of `Rep k G`. A preliminary lemma records that the `MulAction` of $G$ on $G/\Lambda$ is given by multiplication by the image class, $g \bullet q = \bar g\, q$.
--
--   For each class $c \in G/\Lambda$, [`Rep.quotientRightTranslation Λ c`](../def/Rep_QuotientRightTranslation.html#L19) is the endomorphism of this representation whose underlying linear map is the pushforward of finitely supported functions along right translation $q \mapsto q c^{-1}$ of $G/\Lambda$; the $G$-equivariance is exactly the commutation of left and right multiplication in the quotient group. The structural lemmas give the value on a basis vector, $\mathrm{single}(q,a) \mapsto \mathrm{single}(qc^{-1},a)$, the formula on a general element as `Finsupp.mapDomain`, the fact that $c = 1$ gives the identity morphism, and multiplicativity in the form $R_{cc'} = R_{c'}$ followed by $R_{c}$, so that $c \mapsto R_c$ is a left action of $G/\Lambda$ on the module by endomorphisms of the ambient $G$-representation.
--
--   The second definition, [`Rep.quotientRightTranslationTwist Λ χ c`](../def/Rep_QuotientRightTranslation.html#L55), carries the same linear map to an endomorphism of the twist of that representation by a character $\chi : G \to k^{\times}$, where the twist is the representation $g \mapsto \chi(g)\,\rho(g)$; twisting only rescales the $G$-action by scalars, so the same map remains equivariant. Its value on a general element and on a basis vector are again recorded.
--
--   **Relation to Mathlib.** Mathlib supplies the left permutation representation (here in the vendored `Finsupp`-model form [`Rep.ofMulActionFinsupp`](../def/Compat_Mathlib430.html#L100)) and `Finsupp.lmapDomain`/`Finsupp.mapDomain`; the commuting right-translation endomorphisms, and their transport to the twist [`Rep.twist`](../def/GroupCohomology_Selmer.html#L38) by a character, are the project's own definitions.
--
--   **Where it is used.** These endomorphisms provide the action of a quotient group $G/\Lambda$ — in applications a Galois group $\mathrm{Gal}(L/K)$ — on the coefficient module of a permutation (co)induced representation, so that the resulting action on its group cohomology can be used in the local–global cohomological bookkeeping behind the Selmer-group and $H^2$ computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Rep_QuotientRightTranslation.lean

import Mathlib
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

namespace Rep

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G] (Λ : Subgroup G) [Λ.Normal]

theorem smul_quotient_eq_mul (g : G) (q : G ⧸ Λ) : g • q = (g : G ⧸ Λ) * q := by
  induction q using QuotientGroup.induction_on with
  | H a => rfl

noncomputable def quotientRightTranslation (c : G ⧸ Λ) : Rep.ofMulActionFinsupp k G (G ⧸ Λ) ⟶ Rep.ofMulActionFinsupp k G (G ⧸ Λ) :=
  Rep.ofHom ⟨Finsupp.lmapDomain k k (· * c⁻¹), fun g => by
    apply LinearMap.ext; intro x
    show Finsupp.lmapDomain k k (· * c⁻¹) (Representation.ofMulActionFinsupp k G (G ⧸ Λ) g x) =
      Representation.ofMulActionFinsupp k G (G ⧸ Λ) g (Finsupp.lmapDomain k k (· * c⁻¹) x)
    rw [Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply,
      Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    congr 1
    funext q
    show g • q * c⁻¹ = g • (q * c⁻¹)
    rw [smul_quotient_eq_mul, smul_quotient_eq_mul, mul_assoc]⟩

@[simp] theorem quotientRightTranslation_hom_single (c q : G ⧸ Λ) (a : k) :
    (quotientRightTranslation (k := k) Λ c).hom (Finsupp.single q a) = Finsupp.single (q * c⁻¹) a := by
  show Finsupp.lmapDomain k k (· * c⁻¹) (Finsupp.single q a) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem quotientRightTranslation_hom_apply (c : G ⧸ Λ) (x : G ⧸ Λ →₀ k) :
    (quotientRightTranslation (k := k) Λ c).hom x = Finsupp.mapDomain (· * c⁻¹) x := rfl

theorem quotientRightTranslation_one : quotientRightTranslation (k := k) Λ 1 = 𝟙 _ := by
  apply Rep.hom_ext; refine DFunLike.ext _ _ fun x => ?_
  show Finsupp.mapDomain (· * (1 : G ⧸ Λ)⁻¹) x = x
  simp only [inv_one, mul_one]
  exact Finsupp.mapDomain_id

theorem quotientRightTranslation_mul (c c' : G ⧸ Λ) :
    quotientRightTranslation (k := k) Λ (c * c') = quotientRightTranslation Λ c' ≫ quotientRightTranslation Λ c := by
  apply Rep.hom_ext; refine DFunLike.ext _ _ fun x => ?_
  show Finsupp.mapDomain (· * (c * c')⁻¹) x = Finsupp.mapDomain (· * c⁻¹) (Finsupp.mapDomain (· * c'⁻¹) x)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext q
  show q * (c * c')⁻¹ = q * c'⁻¹ * c⁻¹
  rw [mul_inv_rev, mul_assoc]

noncomputable def quotientRightTranslationTwist (χ : G →* kˣ) (c : G ⧸ Λ) :
    (Rep.ofMulActionFinsupp k G (G ⧸ Λ)).twist χ ⟶ (Rep.ofMulActionFinsupp k G (G ⧸ Λ)).twist χ :=
  Rep.ofHom ⟨Finsupp.lmapDomain k k (· * c⁻¹), fun g => by
    apply LinearMap.ext; intro x
    show Finsupp.lmapDomain k k (· * c⁻¹) (((Rep.ofMulActionFinsupp k G (G ⧸ Λ)).ρ.twist χ) g x) =
      ((Rep.ofMulActionFinsupp k G (G ⧸ Λ)).ρ.twist χ) g (Finsupp.lmapDomain k k (· * c⁻¹) x)
    rw [Representation.twist_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    congr 1
    exact Rep.hom_comm_apply (quotientRightTranslation (k := k) Λ c) g x⟩

@[simp] theorem quotientRightTranslationTwist_hom_apply (χ : G →* kˣ) (c : G ⧸ Λ) (x : G ⧸ Λ →₀ k) :
    (quotientRightTranslationTwist (k := k) Λ χ c).hom x = Finsupp.mapDomain (· * c⁻¹) x := rfl

theorem quotientRightTranslationTwist_hom_single (χ : G →* kˣ) (c q : G ⧸ Λ) (a : k) :
    (quotientRightTranslationTwist (k := k) Λ χ c).hom (Finsupp.single q a) = Finsupp.single (q * c⁻¹) a := by
  rw [quotientRightTranslationTwist_hom_apply, Finsupp.mapDomain_single]

end Rep


