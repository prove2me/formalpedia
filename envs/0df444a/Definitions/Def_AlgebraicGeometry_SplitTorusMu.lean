-- Prove2me | Definitions.Def_AlgebraicGeometry_SplitTorusMu
-- name    : AlgebraicGeometry_SplitTorusMu
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/a45f8389-bb08-5d4f-a95d-1deff3206fa4
-- title:
--   Split tori and diagonalisable groups as spectra of group algebras
-- statement:
--   For a commutative ring $S$ and natural numbers $t, m$, `muCoord S t m` is the group algebra $S[(\mathbb{Z}/m)^{t}]$, realised as the additive monoid algebra of the additive group $\mathrm{Fin}\,t \to \mathbb{Z}/m$ with coefficients in $S$, and `torusCoord S t` is $S[\mathbb{Z}^{t}]$, the Laurent polynomial ring in $t$ variables. Their spectra `muScheme S t m` and `torusScheme S t` are the split diagonalisable group $\mu_{m}^{t}$ and the split torus $\mathbb{G}_{m}^{t}$ over $S$ (for $m = 0$ the two coincide, since $\mathbb{Z}/0 = \mathbb{Z}$), and `muStr`, `torusStr` are the morphisms to $\operatorname{Spec} S$ obtained by applying $\operatorname{Spec}$ to the structural algebra maps. Four morphisms are then named, each as $\operatorname{Spec}$ of an explicit ring map: `muToTorus`, from the surjection $S[\mathbb{Z}^{t}] \to S[(\mathbb{Z}/m)^{t}]$ reducing exponents coordinatewise modulo $m$; `muIncl`, for $m \mid m'$, from the map $S[(\mathbb{Z}/m')^{t}] \to S[(\mathbb{Z}/m)^{t}]$ induced by the coordinatewise reduction $\mathbb{Z}/m' \to \mathbb{Z}/m$; and `muBaseChange`, `torusBaseChange`, for a ring homomorphism $\varphi : S \to S'$, from the coefficientwise extension of $\varphi$, so that they go from the $S'$-scheme to the $S$-scheme.
--
--   The remaining definitions package points. With $S'$ an $S$-algebra, `muPt` (resp. `torusPt`) sends an $S$-algebra homomorphism $\chi : S[(\mathbb{Z}/m)^{t}] \to S'$ (resp. $S[\mathbb{Z}^{t}] \to S'$) to the pair consisting of $\operatorname{Spec} \chi$ together with the proof that composing it with the structure morphism gives $\operatorname{Spec}$ of $S \to S'$; this is an element of `SchemeHomOver`, the subtype of morphisms over a fixed base morphism. `muPtId` and `torusPtId` are the case $S' = S$ with $\chi$ unital over $S$, giving sections of the structure morphism, i.e. elements over the identity of $\operatorname{Spec} S$.
--
--   **Relation to Mathlib.** Mathlib has no named scheme-theoretic split torus or $\mu_m$; these abbreviations build them from Mathlib's `AddMonoidAlgebra` and `Spec`. `SchemeHomOver`, the subtype of morphisms commuting with fixed morphisms to a base, is the project's own notion.
--
--   **Where it is used.** These abbreviations provide base-ring- and universe-polymorphic vocabulary for split tori and split groups of multiplicative type, used in the many statements about Néron models and about the multiplicative-type part of the reduction of Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SplitTorusMu.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.SplitTorus

abbrev muCoord (S : Type u) [CommRing S] (t m : ℕ) : Type u := AddMonoidAlgebra S (Fin t → ZMod m)

abbrev muScheme (S : Type u) [CommRing S] (t m : ℕ) : Scheme.{u} := Spec (CommRingCat.of (muCoord S t m))

abbrev muStr (S : Type u) [CommRing S] (t m : ℕ) : muScheme S t m ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (muCoord S t m)))

abbrev torusCoord (S : Type u) [CommRing S] (t : ℕ) : Type u := AddMonoidAlgebra S (Fin t → ℤ)

abbrev torusScheme (S : Type u) [CommRing S] (t : ℕ) : Scheme.{u} := Spec (CommRingCat.of (torusCoord S t))

abbrev torusStr (S : Type u) [CommRing S] (t : ℕ) : torusScheme S t ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (torusCoord S t)))

abbrev muToTorus (S : Type u) [CommRing S] (t m : ℕ) : muScheme S t m ⟶ torusScheme S t :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S
    (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i))))

abbrev muIncl (S : Type u) [CommRing S] (t : ℕ) {m m' : ℕ} (h : m ∣ m') : muScheme S t m ⟶ muScheme S t m' :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom S
    (AddMonoidHom.pi fun i => ((ZMod.castHom h (ZMod m)).toAddMonoidHom).comp
      (Pi.evalAddMonoidHom (fun _ : Fin t => ZMod m') i))))

abbrev muBaseChange {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (t m : ℕ) :
    muScheme S' t m ⟶ muScheme S t m :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) φ))

abbrev torusBaseChange {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S') (t : ℕ) :
    torusScheme S' t ⟶ torusScheme S t :=
  Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) φ))

def muPt (S S' : Type u) [CommRing S] [CommRing S'] [Algebra S S'] (t m : ℕ) (χ : muCoord S t m →ₐ[S] S') :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) (muStr S t m) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact χ.comp_algebraMap⟩

def torusPt (S S' : Type u) [CommRing S] [CommRing S'] [Algebra S S'] (t : ℕ) (χ : torusCoord S t →ₐ[S] S') :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap S S'))) (torusStr S t) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact χ.comp_algebraMap⟩

def torusPtId (S : Type u) [CommRing S] (t : ℕ) (χ : torusCoord S t →ₐ[S] S) : SchemeHomOver (𝟙 _) (torusStr S t) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χ.toRingHom.comp (algebraMap S (torusCoord S t)) = RingHom.id S := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]⟩

def muPtId (S : Type u) [CommRing S] (t m : ℕ) (χ : muCoord S t m →ₐ[S] S) : SchemeHomOver (𝟙 _) (muStr S t m) :=
  ⟨Spec.map (CommRingCat.ofHom χ.toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χ.toRingHom.comp (algebraMap S (muCoord S t m)) = RingHom.id S := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]⟩

end AlgebraicGeometry.SplitTorus

end


