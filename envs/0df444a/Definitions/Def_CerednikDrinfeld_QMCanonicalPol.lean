-- Prove2me | Definitions.Def_CerednikDrinfeld_QMCanonicalPol
-- name    : CerednikDrinfeld_QMCanonicalPol
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/1021d184-c7cb-5d74-afd2-28c743fc9f7e
-- title:
--   Canonical polarisation data for fake elliptic curves
-- statement:
--   The module defines the predicate [`CerednikDrinfeld.QM.IsCanonicalPolData`](../def/CerednikDrinfeld_QMCanonicalPol.html#L15) on a module $\mathcal L$ over a scheme $A$ equipped with a structure morphism $f : A \to \operatorname{Spec} S$ ($S$ a commutative ring), a relative group law $L$ for $f$, a family of endomorphisms $\mathrm{act} : I \to (A \to A)$ all lying over the base ($\mathrm{act}\,x$ followed by $f$ equals $f$), and a map $\mathrm{star} : I \to I$. It is the conjunction of six clauses. First, $\mathcal L$ is invertible. Second, `IsSymmetric`: the pullback of $\mathcal L$ along the inversion morphism $\mathrm{negMor}$ (the underlying morphism of the $L$-inverse of the identity point) and $\mathcal L$ itself become isomorphic after restriction to $f^{-1}(U)$ for suitable opens $U$ covering $\operatorname{Spec} S$ — isomorphy locally on the base, not a chosen isomorphism. Third, `KernelIsTwoTorsion`: for every affine base change $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and every $t$-point $x$ of $A$, the pullback of the Mumford bundle $m^*\mathcal L \otimes (p_1^*\mathcal L^\vee \otimes p_2^*\mathcal L^\vee)$ along the slice $(\mathrm{id}, x)$ is locally on $\operatorname{Spec} R$ isomorphic to the unit module if and only if $x + x = 0$; thus $K(\mathcal L) = A[2]$ on affine test objects. Fourth, there is a faithfully flat $S$-algebra $S'$ such that for every relative group law $L'$ on $A_{S'} \to \operatorname{Spec} S'$ compatible with $L$ under the first projection (the compatibility is spelled out on points) one can find an invertible $\mathcal L_0$ on $A_{S'}$ whose Mumford kernel is trivial — `KernelTrivial`, i.e. the slice of the Mumford bundle is locally trivial only at the identity point — with the pullback of $\mathcal L$ to $A_{S'}$ isomorphic, locally on $\operatorname{Spec} S'$, to $\mathcal L_0 \otimes [-1]^*\mathcal L_0$. Fifth, positivity: for every algebraically closed field $k$ and every ring map $S \to k$ the `geomFibreH0Finrank` of $\mathcal L$, the $k$-dimension of the global sections of the pullback of $\mathcal L$ to the geometric fibre, is strictly positive. Sixth, `RosatiCompatible` for the family $\mathrm{act}$ and the map $\mathrm{star}$: for each $b \in I$ the pullbacks of the Mumford bundle along $(\mathrm{id}, \mathrm{act}\, b)$ and along $(\mathrm{act}\,(\mathrm{star}\, b), \mathrm{id})$ on $A \times_S A$ are isomorphic locally on $\operatorname{Spec} S$.
--
--   The abbreviation [`CerednikDrinfeld.QM.FakeEllipticCurve.IsCanonicalPol`](../def/CerednikDrinfeld_QMCanonicalPol.html#L37) specialises this: for rationals $a, b$, a $\mathbb Z$-submodule $\Lambda$ of $\mathbb H[\mathbb Q, a, b]$, a natural number $N$, a fake elliptic curve $E$ over $S$ of level data $(\Lambda, N)$, a map $\mathrm{star} : \Lambda \to \Lambda$ and a module $\mathcal L$ on $E.A$, it is `IsCanonicalPolData` applied to the structure morphism, group law, $\Lambda$-action and its compatibility over the base carried by $E$.
--
--   **Relation to Mathlib.** Mathlib has no notion of polarisation, Mumford bundle or abelian scheme; these are the project's own, formulated with Mathlib's sheaves of modules on a scheme (`Scheme.Modules`, with its monoidal structure and duals) and pullbacks of schemes.
--
--   **Where it is used.** The predicate pins down the polarisation in the moduli problem for fake elliptic curves over a quaternion order, used in the Čerednik–Drinfeld description of the Shimura curves attached to $\Lambda$ with level structure; the same predicate serves the existence and uniqueness statements for the canonical polarisation and the cutting out of the quaternionic-multiplication locus.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMCanonicalPol.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

universe u v

def CerednikDrinfeld.QM.IsCanonicalPolData
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    {I : Type v} (act : I → (A ⟶ A)) (act_over : ∀ x : I, act x ≫ f = f) (star : I → I) (𝓛 : A.Modules) : Prop :=
  Scheme.Modules.IsInvertible 𝓛 ∧ IsSymmetric f L 𝓛 ∧ KernelIsTwoTorsion f L 𝓛 ∧

  (∃ (S' : Type u) (_ : CommRing S') (_ : Algebra S S'),
      Module.FaithfullyFlat S S' ∧
      ∀ (L' : RelativeGroupLaw S' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
        (∀ (T : Scheme.{u}) (t' : T ⟶ Spec (CommRingCat.of S')) (P Q : SchemeHomOver t' (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))),
            (L'.mul t' P Q).1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) =
              (L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
                ⟨P.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
                ⟨Q.1 ≫ pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1) →
        ∃ 𝓛₀ : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap S S')))).Modules,
          Scheme.Modules.IsInvertible 𝓛₀ ∧ KernelTrivial (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L' 𝓛₀ ∧
          LocIsoOnBase (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
            ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))).obj 𝓛)
            (𝓛₀ ⊗ (Scheme.Modules.pullback (negMor (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) L')).obj 𝓛₀)) ∧

  (∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : S →+* k), 0 < Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk) ∧
  RosatiCompatible f L 𝓛 act act_over star

abbrev CerednikDrinfeld.QM.FakeEllipticCurve.IsCanonicalPol
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (star : ↥Λ → ↥Λ) (𝓛 : E.A.Modules) : Prop :=
  CerednikDrinfeld.QM.IsCanonicalPolData E.f E.L E.act E.act_over star 𝓛

end


