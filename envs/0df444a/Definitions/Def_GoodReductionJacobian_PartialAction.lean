-- Prove2me | Definitions.Def_GoodReductionJacobian_PartialAction
-- name    : GoodReductionJacobian_PartialAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/460acb11-3309-552c-82bc-eb8e7ae1522a
-- title:
--   Partial (rational) actions of a group scheme on a scheme
-- statement:
--   Fix a field $k$, a $k$-scheme $G$ with structure morphism $f\colon G\to\operatorname{Spec} k$ and a $k$-scheme $P$ with structure morphism $p$. A `PartialAction` is a structure with four fields: an open subscheme `dom` of the fibre product $G\times_{\operatorname{Spec} k}P$; a proof that the underlying set of `dom` is dense in the space of that fibre product; a morphism of schemes `hom` from `dom` to $P$; and the identity `hom ≫ p = dom.ι ≫ pullback.snd f p ≫ p`, i.e. `hom` is a morphism over $\operatorname{Spec} k$ when the domain is given the structure map obtained by restricting the second projection. Thus the datum is a $k$-morphism $\alpha$ defined on a dense open part of $G\times_k P$, with no axioms built in.
--
--   For a $k$-scheme $T$ with structure map $t$ and points $\gamma\in G(T)$, $x\in P(T)$ over $t$ (elements of `SchemeHomOver`, i.e. morphisms whose composite with the structure map is $t$), `pair` is the induced morphism $T\to G\times_kP$; `Defined` says its set-theoretic image lies in `dom`; `liftDom` then factors it through the open immersion, and `act` is the resulting $T$-point $\gamma\cdot x=\alpha\circ(\gamma,x)$ of $P$, shown to lie over $t$.
--
--   Four predicates on such a datum are then defined relative to a `RelativeGroupLaw` $L$ on $f$ (a functorial group structure on the points $G(T)$): `UnitActs`, that $e\cdot x=x$ whenever defined; `Assoc`, that if $\delta\cdot x$ and $\gamma\cdot(\delta\cdot x)$ are defined then $(\gamma\delta)\cdot x$ is defined and equal to $\gamma\cdot(\delta\cdot x)$; `Compatible`, for an open $V\subseteq G$ and a $k$-morphism $\iota\colon V\to P$, that whenever $T$-points $v,w$ of $V$ satisfy $w=\gamma\cdot v$ in $G(T)$ the product $\gamma\cdot\iota(v)$ is defined and equals $\iota(w)$ (here `modelPoint` denotes $v$ followed by $\iota$); `Maximal`, that any open $U'\supseteq$ `dom` carrying a morphism to $P$ restricting to `hom` equals `dom`; and `Stable W` for $W\subseteq P$, that for every point $z$ of `dom` whose second coordinate lies in $W$, the image $\alpha(z)$ lies in $W$.
--
--   **Relation to Mathlib.** Mathlib has no notion of a rational or partially defined action of a group scheme; this is the project's own structure, formulated through the project's `RelativeGroupLaw` (a group law on the functor of points) rather than through monoid-object actions in the category of schemes.
--
--   **Where it is used.** These definitions belong to the scheme-theoretic infrastructure for group laws and Néron models, where a group structure on a dense open part of a product is used to transport translation on a group scheme to a model containing it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_PartialAction.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian

structure PartialAction (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) where

  dom : (pullback f p).Opens

  dense_dom : Dense (dom : Set ↥(pullback f p))

  hom : (dom : Scheme.{u}) ⟶ P

  hom_comp : hom ≫ p = dom.ι ≫ pullback.snd f p ≫ p

namespace PartialAction

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

abbrev pair {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f)
    (x : SchemeHomOver t p) : T ⟶ pullback f p :=
  pullback.lift γ.1 x.1 (γ.2.trans x.2.symm)

def Defined (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) : Prop :=
  Set.range (pair γ x) ⊆ (a.dom : Set ↥(pullback f p))

def liftDom (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    T ⟶ (a.dom : Scheme.{u}) :=
  IsOpenImmersion.lift a.dom.ι (pair γ x) (by rw [Scheme.Opens.range_ι]; exact hd)

@[simp]
theorem liftDom_ι (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    a.liftDom γ x hd ≫ a.dom.ι = pair γ x :=
  IsOpenImmersion.lift_fac _ _ _

theorem liftDom_hom_comp (a : PartialAction k f p) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (γ : SchemeHomOver t f) (x : SchemeHomOver t p)
    (hd : a.Defined γ x) : (a.liftDom γ x hd ≫ a.hom) ≫ p = t := by
  rw [Category.assoc, a.hom_comp, ← Category.assoc (a.liftDom γ x hd), liftDom_ι,
    ← Category.assoc, pullback.lift_snd]
  exact x.2

def act (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) : SchemeHomOver t p :=
  ⟨a.liftDom γ x hd ≫ a.hom, a.liftDom_hom_comp γ x hd⟩

@[simp]
theorem act_coe (a : PartialAction k f p) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    (a.act γ x hd).1 = a.liftDom γ x hd ≫ a.hom :=
  rfl

def UnitActs (a : PartialAction k f p) (L : RelativeGroupLaw k f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t p)
    (hd : a.Defined (L.one t) x), a.act (L.one t) x hd = x

def Assoc (a : PartialAction k f p) (L : RelativeGroupLaw k f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ δ : SchemeHomOver t f)
    (x : SchemeHomOver t p) (hd₁ : a.Defined δ x) (hd₂ : a.Defined γ (a.act δ x hd₁)),
    ∃ hd₃ : a.Defined (L.mul t γ δ) x, a.act γ (a.act δ x hd₁) hd₂ = a.act (L.mul t γ δ) x hd₃

def modelPoint {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (v : SchemeHomOver t (V.ι ≫ f)) : SchemeHomOver t p :=
  ⟨v.1 ≫ ι, by rw [Category.assoc, hι]; exact v.2⟩

@[simp]
theorem modelPoint_coe {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} (v : SchemeHomOver t (V.ι ≫ f)) :
    (modelPoint ι hι v).1 = v.1 ≫ ι :=
  rfl

def Compatible (a : PartialAction k f p) (L : RelativeGroupLaw k f) (V : G.Opens)
    (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f)
    (v w : SchemeHomOver t (V.ι ≫ f)),
    NeronModelInfra.schemeHomOverComp w (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul t γ (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) →
    ∃ hd : a.Defined γ (modelPoint ι hι v), a.act γ (modelPoint ι hι v) hd = modelPoint ι hι w

def Maximal (a : PartialAction k f p) : Prop :=
  ∀ (U' : (pullback f p).Opens) (h' : (U' : Scheme.{u}) ⟶ P) (hle : a.dom ≤ U'),
    (pullback f p).homOfLE hle ≫ h' = a.hom → U' = a.dom

def Stable (a : PartialAction k f p) (W : Set ↥P) : Prop :=
  ∀ z : ↥(a.dom : Scheme.{u}), pullback.snd f p (a.dom.ι z) ∈ W → a.hom z ∈ W

end PartialAction

end GoodReductionJacobian

end


