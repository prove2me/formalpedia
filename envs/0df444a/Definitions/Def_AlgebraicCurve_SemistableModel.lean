-- Prove2me | Definitions.Def_AlgebraicCurve_SemistableModel
-- name    : AlgebraicCurve_SemistableModel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/a33fbb5e-2824-5f1d-acc4-d2ffb4e7c16e
-- title:
--   Semistable models over a valuation ring, with descent data
-- statement:
--   Throughout, $L$ is a field with a valuation subring $A$, $F$ is an $L$-algebra field, and the reduction data consist of residue-field extensions $\bar F_i$ of $\mathrm{ResidueField}(A)$ indexed by $\iota_V$, component charts $C_i : \mathtt{ComponentChart}\ A\ F\ (\bar F_i)$ (a valuation subring $(C_i).\mathrm{integers}$ of $F$ with a surjective reduction onto $\bar F_i$ whose kernel is the maximal ideal, a set $(C_i).\mathrm{dom}$ of places of $F/L$, a finite set $(C_i).\mathrm{nodes}$ of places of $\bar F_i$, and a map $\mathrm{placeMap}$ on places), annuli $\mathrm{An}_e$ indexed by $\iota_E$ with source and target components $\mathrm{src}, \mathrm{tgt}$ and attaching places $x_s(e)$ on $\bar F_{\mathrm{src}\,e}$, $x_t(e)$ on $\bar F_{\mathrm{tgt}\,e}$.
--
--   Two helpers come first: `baseToFunctionField` sends $R$ into the function field of an integral scheme $X$ equipped with $f : X \to \operatorname{Spec} R$, by global sections followed by the germ at the generic point; `localRing X φ x` is the subring of $F$ obtained as the image of the stalk $\mathcal O_{X,x}$ in the function field, transported by $\varphi^{-1} : K(X) \cong F$.
--
--   `SemistableModel` is a structure whose fields are an integral scheme $X$ with a proper, flat, locally of finite presentation morphism $X \to \operatorname{Spec} A$, an isomorphism $\varphi : F \cong K(X)$ compatible with $A \to F$, and a complete dictionary between points of $X$ and the data: points $\mathrm{pt}\,P$ for places $P$ of $F/L$ (lying over the generic point of $\operatorname{Spec} A$, with local ring $P$'s valuation subring), points $\mathrm{gen}\,i$ over the closed point with local ring $(C_i).\mathrm{integers}$, points $\mathrm{sm}\,i\,Q$ for non-node places $Q$ of $\bar F_i$, and points $\mathrm{nd}\,e$; `classify_bijective` asserts that these together with the generic point enumerate $X$ bijectively. Further fields prescribe all specialisations ($\mathrm{pt}\,P \rightsquigarrow \mathrm{sm}\,i\,(\mathrm{placeMap}_i P)$ on $(C_i).\mathrm{dom}$, $\mathrm{pt}\,P \rightsquigarrow \mathrm{nd}\,e$ on $(\mathrm{An}_e).\mathrm{dom}$, $\mathrm{gen}\,i \rightsquigarrow \mathrm{sm}\,i\,Q$, $\mathrm{gen}\,(\mathrm{src}\,e),\mathrm{gen}\,(\mathrm{tgt}\,e) \rightsquigarrow \mathrm{nd}\,e$, and nothing else, the $\mathrm{sm}$ and $\mathrm{nd}$ points being closed), describe the local rings at $\mathrm{sm}\,i\,Q$ (functions integral along $C_i$ with no pole at places of $(C_i).\mathrm{dom}$ above $Q$) and at $\mathrm{nd}\,e$ (integral along both branches, no pole on the annulus), and pin down the reduction: the reduction map at $\mathrm{sm}\,i\,Q$ lands in and surjects onto the valuation subring of $Q$ and its kernel is $\mathfrak m_A \cdot \mathcal O$; at $\mathrm{nd}\,e$ the two branch reductions lie in the valuation subrings of $x_s(e)$, $x_t(e)$ and have a common value in $\mathrm{ResidueField}(A)$ there, every such matching pair is realised, and again the joint vanishing locus is $\mathfrak m_A \cdot \mathcal O$. Final fields place $\mathrm{pt}$, $\mathrm{gen}$, $\mathrm{sm}$ in the smooth locus of $X \to \operatorname{Spec} A$ and $\mathrm{nd}\,e$ outside it. Nothing is constructed: this is a property bundle on a presentation, satisfied or not by given data.
--
--   The abbreviations `closedPointι`, `closedFibre`, `closedFibreι` form the closed fibre as the pullback along $\operatorname{Spec}$ of the residue map of $A$ (a closed immersion, by the accompanying instance). `Descent` is a structure on a `SemistableModel` recording a noetherian henselian local ring $A_0$ with an injective local homomorphism $\iota : A_0 \to A$ whose image in $L$ is $A \cap K_0$ for a subfield $K_0$ with $L/K_0$ algebraic and whose composite with the residue map of $A$ is surjective, a model $X_0 \to \operatorname{Spec} A_0$ (integral, proper, flat, locally of finite presentation), an isomorphism of $X$ with the base change $X_0 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ over $\operatorname{Spec} A$ carrying generic point to generic point, and a subfield $F_0 \subseteq F$ with $F/F_0$ algebraic together with $F_0 \cong K(X_0)$ compatible with $\varphi$ through the stalk map at the generic point. `Descent.closedFibre₀` is the closed fibre of $X_0$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — schemes, `IsIntegral`, `IsProper`, `Flat`, `LocallyOfFinitePresentation`, `Scheme.functionField`, `genericPoint`, `Hom.smoothLocus`, specialisation `⤳`, and `HenselianLocalRing` — but has no notion of a semistable model described through charts, annuli and places; `SemistableModel` and `Descent`, like `ComponentChart` and `Annulus`, are the project's own.
--
--   **Where it is used.** These structures give the geometric language in which reduction of a curve over a valuation ring of $\bar{\mathbb Q}$ is recorded: the semistable models of modular curves at a place, with their components, nodes and annuli, and their descent to a noetherian henselian base. They are the input for the arguments about torsion and reduction on Jacobians that underlie the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_SemistableModel.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v w u₁ u₂

namespace AlgebraicCurve

namespace SemistableModel

def baseToFunctionField {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) : R →+* X.functionField :=
  (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def localRing {F : Type v} [Field F] (X : Scheme.{u}) [IsIntegral X] (φ : F ≃+* X.functionField)
    (x : X) : Subring F :=
  ((φ.symm : X.functionField ≃+* F).toRingHom.comp
    (algebraMap (X.presheaf.stalk x) X.functionField)).range

end SemistableModel

variable {L : Type u} [Field L] (A : ValuationSubring L)
variable (F : Type v) [Field F] [Algebra L F]
variable {ιV : Type u₁} {ιE : Type u₂} (Fbar : ιV → Type w) [∀ i, Field (Fbar i)] [∀ i, Algebra (ResidueField A) (Fbar i)]
variable (C : ∀ i, ComponentChart A F (Fbar i)) (An : ιE → Annulus A F) (src tgt : ιE → ιV)
variable (xs : ∀ e, Place (ResidueField A) (Fbar (src e))) (xt : ∀ e, Place (ResidueField A) (Fbar (tgt e)))

structure SemistableModel where

  X : Scheme.{u}

  toBase : X ⟶ Spec (CommRingCat.of A)
  [isIntegral : IsIntegral X]
  [isProper : IsProper toBase]
  [flat : Flat toBase]
  [locallyOfFinitePresentation : LocallyOfFinitePresentation toBase]

  ffEquiv : F ≃+* X.functionField

  ffEquiv_algebraMap : ∀ a : A,
    ffEquiv (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a

  pt : Place L F → X

  localRing_pt : ∀ P, SemistableModel.localRing X ffEquiv (pt P) = P.toValuationSubring.toSubring

  toBase_pt : ∀ P, (toBase.base (pt P)).asIdeal = ⊥

  gen : ιV → X

  localRing_gen : ∀ i, SemistableModel.localRing X ffEquiv (gen i) = (C i).integers.toSubring

  toBase_gen : ∀ i, toBase.base (gen i) = IsLocalRing.closedPoint A

  sm : ∀ i, {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes} → X

  nd : ιE → X

  classify_bijective : Function.Bijective
    (Sum.elim (fun _ : Unit => genericPoint X)
      (Sum.elim pt (Sum.elim gen (Sum.elim
        (fun iQ : (Σ i, {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) => sm iQ.1 iQ.2) nd))) :
      Unit ⊕ (Place L F ⊕ (ιV ⊕ ((Σ i, {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) ⊕ ιE))) → X)

  pt_specializes_sm : ∀ i (P : Place L F) (hP : P ∈ (C i).dom),
    pt P ⤳ sm i ⟨(C i).placeMap P, (C i).placeMap_not_mem_nodes P hP⟩

  pt_specializes_nd : ∀ e, ∀ P ∈ (An e).dom, pt P ⤳ nd e

  eq_of_pt_specializes : ∀ (P : Place L F) (x : X), pt P ⤳ x → x = pt P ∨
    (∃ i, ∃ hP : P ∈ (C i).dom, x = sm i ⟨(C i).placeMap P, (C i).placeMap_not_mem_nodes P hP⟩) ∨
    (∃ e, P ∈ (An e).dom ∧ x = nd e)

  gen_specializes_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}), gen i ⤳ sm i Q
  gen_specializes_nd : ∀ e, gen (src e) ⤳ nd e ∧ gen (tgt e) ⤳ nd e
  eq_of_gen_specializes : ∀ (j : ιV) (x : X), gen j ⤳ x → x = gen j ∨ (∃ Q, x = sm j Q) ∨
    (∃ e, (src e = j ∨ tgt e = j) ∧ x = nd e)

  eq_of_sm_specializes : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (x : X), sm i Q ⤳ x → x = sm i Q
  eq_of_nd_specializes : ∀ e (x : X), nd e ⤳ x → x = nd e

  localRing_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (f : F),
    f ∈ SemistableModel.localRing X ffEquiv (sm i Q) ↔
      (f ∈ (C i).integers ∧ ∀ P ∈ (C i).dom, (C i).placeMap P = Q.1 → f ∈ P.toValuationSubring)

  localRing_nd : ∀ e (f : F), f ∈ SemistableModel.localRing X ffEquiv (nd e) ↔
      (f ∈ (C (src e)).integers ∧ f ∈ (C (tgt e)).integers ∧ ∀ P ∈ (An e).dom, f ∈ P.toValuationSubring)

  residue_mem_of_mem_localRing_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (f : F) (hf : f ∈ (C i).integers),
    f ∈ SemistableModel.localRing X ffEquiv (sm i Q) →
      (C i).residue ⟨f, hf⟩ ∈ Q.1.toValuationSubring

  exists_residue_eq_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (g : Fbar i), g ∈ Q.1.toValuationSubring →
    ∃ (f : F) (hf : f ∈ (C i).integers), f ∈ SemistableModel.localRing X ffEquiv (sm i Q) ∧ (C i).residue ⟨f, hf⟩ = g

  exists_eq_mul_sm : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}) (f : F) (hf : f ∈ (C i).integers), f ∈ SemistableModel.localRing X ffEquiv (sm i Q) →
    (C i).residue ⟨f, hf⟩ = 0 → ∃ a ∈ maximalIdeal A, ∃ g ∈ SemistableModel.localRing X ffEquiv (sm i Q),
      f = algebraMap L F (a : L) * g

  residue_nd : ∀ e (f : F) (hs : f ∈ (C (src e)).integers) (ht : f ∈ (C (tgt e)).integers),
    f ∈ SemistableModel.localRing X ffEquiv (nd e) →
      ∃ (h1 : (C (src e)).residue ⟨f, hs⟩ ∈ (xs e).toValuationSubring)
        (h2 : (C (tgt e)).residue ⟨f, ht⟩ ∈ (xt e).toValuationSubring) (c : ResidueField A),
        IsLocalRing.residue (xs e).toValuationSubring ⟨_, h1⟩ = algebraMap (ResidueField A) (xs e).ResidueField c ∧
        IsLocalRing.residue (xt e).toValuationSubring ⟨_, h2⟩ = algebraMap (ResidueField A) (xt e).ResidueField c

  exists_residue_eq_nd : ∀ e (g : ∀ j, Fbar j) (h1 : g (src e) ∈ (xs e).toValuationSubring)
    (h2 : g (tgt e) ∈ (xt e).toValuationSubring) (c : ResidueField A),
    IsLocalRing.residue (xs e).toValuationSubring ⟨_, h1⟩ = algebraMap (ResidueField A) (xs e).ResidueField c →
    IsLocalRing.residue (xt e).toValuationSubring ⟨_, h2⟩ = algebraMap (ResidueField A) (xt e).ResidueField c →
      ∃ (f : F) (hs : f ∈ (C (src e)).integers) (ht : f ∈ (C (tgt e)).integers),
        f ∈ SemistableModel.localRing X ffEquiv (nd e) ∧
        (C (src e)).residue ⟨f, hs⟩ = g (src e) ∧ (C (tgt e)).residue ⟨f, ht⟩ = g (tgt e)

  exists_eq_mul_nd : ∀ e (f : F) (hs : f ∈ (C (src e)).integers) (ht : f ∈ (C (tgt e)).integers),
    f ∈ SemistableModel.localRing X ffEquiv (nd e) →
    (C (src e)).residue ⟨f, hs⟩ = 0 → (C (tgt e)).residue ⟨f, ht⟩ = 0 →
      ∃ a ∈ maximalIdeal A, ∃ g ∈ SemistableModel.localRing X ffEquiv (nd e), f = algebraMap L F (a : L) * g

  pt_mem_smoothLocus : ∀ P, pt P ∈ toBase.smoothLocus
  gen_mem_smoothLocus : ∀ i, gen i ∈ toBase.smoothLocus
  sm_mem_smoothLocus : ∀ i (Q : {Q : Place (ResidueField A) (Fbar i) // Q ∉ (C i).nodes}), sm i Q ∈ toBase.smoothLocus
  nd_not_mem_smoothLocus : ∀ e, nd e ∉ toBase.smoothLocus

attribute [instance] SemistableModel.isIntegral SemistableModel.isProper SemistableModel.flat
  SemistableModel.locallyOfFinitePresentation

example (M : SemistableModel A F Fbar C An src tgt xs xt) (i : ιV) : M.gen i ∈ M.toBase.smoothLocus :=
  M.gen_mem_smoothLocus i

example (M : SemistableModel A F Fbar C An src tgt xs xt) (e : ιE) (P : Place L F)
    (hP : P ∈ (An e).dom) : M.pt P ⤳ M.nd e :=
  M.pt_specializes_nd e P hP

example (M : SemistableModel A F Fbar C An src tgt xs xt) (P : Place L F) :
    SemistableModel.localRing M.X M.ffEquiv (M.pt P) = P.toValuationSubring.toSubring :=
  M.localRing_pt P

namespace SemistableModel

variable {A F Fbar C An src tgt xs xt}

abbrev closedPointι (A : ValuationSubring L) :
    Spec (CommRingCat.of (ResidueField A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

abbrev closedFibre (M : SemistableModel A F Fbar C An src tgt xs xt) : Scheme.{u} :=
  Limits.pullback M.toBase (closedPointι A)

abbrev closedFibreι (M : SemistableModel A F Fbar C An src tgt xs xt) : M.closedFibre ⟶ M.X :=
  Limits.pullback.fst M.toBase (closedPointι A)

instance isClosedImmersion_specMap_residue (R : Type u) [CommRing R] [IsLocalRing R] :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

example (A : ValuationSubring L) : IsClosedImmersion (closedPointι A) := inferInstance

structure Descent (M : SemistableModel A F Fbar C An src tgt xs xt) where

  A₀ : Type u
  [commRing : CommRing A₀]
  [isNoetherianRing : IsNoetherianRing A₀]
  [henselianLocalRing : HenselianLocalRing A₀]

  ι : A₀ →+* A
  [isLocalHom : IsLocalHom ι]
  ι_injective : Function.Injective ι

  K₀ : Subfield L
  range_ι : Set.range (fun a : A₀ => ((ι a : A) : L)) = (A : Set L) ∩ (K₀ : Set L)
  [isAlgebraic : Algebra.IsAlgebraic K₀ L]

  residue_comp_surjective : Function.Surjective ((IsLocalRing.residue A).comp ι)

  X₀ : Scheme.{u}
  toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀)
  [isIntegral₀ : IsIntegral X₀]
  [isProper₀ : IsProper toBase₀]
  [flat₀ : Flat toBase₀]
  [locallyOfFinitePresentation₀ : LocallyOfFinitePresentation toBase₀]

  iso : M.X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι))
  iso_snd : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι)) = M.toBase

  base_genericPoint :
    (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).base (genericPoint M.X) =
      genericPoint X₀

  F₀ : Subfield F
  [isAlgebraic_F₀ : Algebra.IsAlgebraic F₀ F]

  ffEquiv₀ : F₀ ≃+* X₀.functionField

  ffEquiv₀_ffEquiv : ∀ s : F₀, M.ffEquiv (s : F) =
    ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι))).stalkMap (genericPoint M.X)).hom
      ((X₀.presheaf.stalkSpecializes (specializes_of_eq base_genericPoint)).hom (ffEquiv₀ s))

attribute [instance] Descent.commRing Descent.isNoetherianRing Descent.henselianLocalRing Descent.isLocalHom
  Descent.isAlgebraic Descent.isIntegral₀ Descent.isProper₀ Descent.flat₀ Descent.locallyOfFinitePresentation₀
  Descent.isAlgebraic_F₀

abbrev Descent.closedFibre₀ {M : SemistableModel A F Fbar C An src tgt xs xt} (D : M.Descent) : Scheme.{u} :=
  Limits.pullback D.toBase₀ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue D.A₀)))

end SemistableModel

end AlgebraicCurve

end


