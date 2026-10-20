-- Prove2me | Definitions.Def_Milne_motives
-- name    : Milne_motives
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-20T02:09:09.9121+00:00
-- url     : https://prove2.me/theorems/d603c34d-5993-4ceb-beec-66466c085dec
-- title:
--   Effective pure motives: objects, morphisms, tensor products, and fiber functors
-- statement:
--   The category of effective pure motives of the source, in the paper's second attempt of Section 5. An object is a pair h(X, e) of a variety X and an idempotent degree-zero correspondence e on X; a morphism from h(X, e) to h(Y, f) is a degree-zero correspondence γ from X to Y with f ∘ γ ∘ e = γ — the paper's f ∘ Corr⁰(X, Y)_Q ∘ e. The file defines the identity morphism of a motive (its idempotent), composition of morphisms, their pointwise addition and zero, the tensor product of motives and of morphisms through the exterior product, the motive hX of a variety, the two summands of the motive of the projective line, the image and complement summands of an idempotent endomorphism sandwiched by a projector, and the fiber functor structure: an assignment of finite-dimensional Q-vector spaces to motives that acts on morphisms, preserves identities and composition, multiplies dimensions over tensor products, and identifies the trace of the identity endomorphism of each motive with the dimension of its fiber — the data whose nonexistence is the paper's tannakian obstruction.
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Sections 5-6 (pp. 6-7, 10).

import Mathlib
import Definitions.Def_Milne_world

universe u v

/-!
# Motives — Grothendieck's dream: effective motives and fiber functors

The category of effective motives of the source (the paper's second
attempt of section 5): objects are pairs h(X, e) of a variety X and an
idempotent degree-zero correspondence e on X; a morphism from h(X, e)
to h(Y, f) is a degree-zero correspondence γ with f ∘ γ ∘ e = γ.
The file carries the identity, composition, addition, and zero of
morphisms, the tensor product of motives and morphisms, the designated
motives of the point's summands of the projective line, the splitting data
of idempotent endomorphisms, and the fiber functor data whose
nonexistence is the paper's tannakian obstruction.
-/

namespace Milne

/-- A motive is a pair h(X, e): a variety X together with an idempotent
degree-zero correspondence e on X (the paper's h(X, e), second
attempt of section 5). -/
structure MotElem (W : CorrWorld.{u, v}) where
  /-- the underlying variety -/
  X : W.Var
  /-- the idempotent degree-zero correspondence cutting out the motive -/
  e : W.Corr X X
  idem : W.cc e e = e
  dege : W.deg e = 0

/-- A morphism from h(X, e) to h(Y, f) is a degree-zero correspondence
γ from X to Y with f ∘ γ ∘ e = γ — the paper's
f ∘ Corr⁰(X, Y)_ℚ ∘ e. -/
def Hom (W : CorrWorld.{u, v}) (M N : MotElem W) : Type v :=
  {γ : W.Corr M.X N.X // W.cc (W.cc M.e γ) N.e = γ ∧ W.deg γ = 0}

/-- The identity morphism of a motive: the idempotent itself. -/
def idM (W : CorrWorld.{u, v}) (M : MotElem W) : Hom W M M :=
  ⟨M.e, by rw [M.idem, M.idem], M.dege⟩

/-- Composition of morphisms: composition of the underlying
correspondences, which the interface axioms keep inside the sandwiched
subspace. -/
def homComp (W : CorrWorld.{u, v}) {M N P : MotElem W}
    (f : Hom W M N) (g : Hom W N P) : Hom W M P :=
  ⟨W.cc f.val g.val,
    W.comp_sandwich M.e N.e P.e f.val g.val M.idem N.idem P.idem
      f.property.1 g.property.1,
    W.deg_cc_zero f.val g.val f.property.2 g.property.2⟩

/-- Pointwise addition of parallel morphisms. -/
def homAdd (W : CorrWorld.{u, v}) {M N : MotElem W}
    (f g : Hom W M N) : Hom W M N :=
  ⟨W.add f.val g.val,
    by rw [W.add_sandwich M.e N.e f.val g.val, f.property.1, g.property.1],
    (W.deg_add_eq f.val g.val (f.property.2.trans g.property.2.symm)).trans
      f.property.2⟩

/-- The zero morphism between two motives. -/
def homZero (W : CorrWorld.{u, v}) (M N : MotElem W) : Hom W M N :=
  ⟨W.zero M.X N.X, W.zero_sandwich M.X N.X M.e N.e, W.deg_zero M.X N.X⟩

/-- The tensor product of motives: h(X, e) ⊗ h(Y, f) = h(X × Y, e × f)
(the paper's tensor structure of section 6). -/
def tensorObj (W : CorrWorld.{u, v}) (M N : MotElem W) : MotElem W :=
  ⟨W.prod M.X N.X, W.cross M.e N.e,
    W.cross_idem M.e N.e M.idem N.idem,
    W.deg_cross_zero M.e N.e M.dege N.dege⟩

/-- The tensor product of morphisms: the exterior product of the
underlying correspondences. -/
def crossHom (W : CorrWorld.{u, v}) {M M' N N' : MotElem W}
    (f : Hom W M N) (g : Hom W M' N') :
    Hom W (tensorObj W M M') (tensorObj W N N') :=
  show
      {γ : W.Corr (W.prod M.X M'.X) (W.prod N.X N'.X) //
        W.cc (W.cc (W.cross M.e M'.e) γ) (W.cross N.e N'.e) = γ ∧
        W.deg γ = 0} from
    ⟨W.cross f.val g.val,
      by
        rw [W.cross_sandwich M.e N.e M'.e N'.e f.val g.val, f.property.1,
          g.property.1],
      W.deg_cross_zero f.val g.val f.property.2 g.property.2⟩

/-- The motive of a variety: hX = h(X, Δ_X). -/
def hOf (W : CorrWorld.{u, v}) (X : W.Var) : MotElem W :=
  ⟨X, W.delta X, W.cc_id_left (W.delta X), W.deg_delta X⟩

/-- The motive of the projective line. -/
def P1M (W : CorrWorld.{u, v}) : MotElem W := hOf W W.P1

/-- The unit summand of the projective line: h⁰ℙ¹ = h(ℙ¹, e₀). -/
def H0 (W : CorrWorld.{u, v}) : MotElem W := ⟨W.P1, W.e0, W.e0_idem, W.e0_deg⟩

/-- The Lefschetz summand of the projective line: h²ℙ¹ = h(ℙ¹, e₂). -/
def L1 (W : CorrWorld.{u, v}) : MotElem W := ⟨W.P1, W.e2, W.e2_idem, W.e2_deg⟩

/-- The image summand of an idempotent endomorphism f of the motive
h(X, e): the motive h(X, f). -/
def idemImg (W : CorrWorld.{u, v}) (M : MotElem W) (f : W.Corr M.X M.X)
    (hf : W.cc f f = f) (hdf : W.deg f = 0) : MotElem W :=
  ⟨M.X, f, hf, hdf⟩

/-- The complement summand of an idempotent endomorphism f of the motive
h(X, e): the motive h(X, e − f) — the paper's h(X, e − efe), with f
sandwiched by e, so that efe = f. -/
def idemCompl (W : CorrWorld.{u, v}) (M : MotElem W) (f : W.Corr M.X M.X)
    (hf : W.cc f f = f) (hdf : W.deg f = 0)
    (hfe : W.cc (W.cc M.e f) M.e = f) : MotElem W :=
  ⟨M.X, W.add M.e (W.neg f),
    W.compl_idem M.e f M.idem hf hfe,
    (W.deg_add_eq M.e (W.neg f)
      (M.dege.trans ((W.deg_neg f).trans hdf).symm)).trans M.dege⟩

/-- Fiber functor data on the category of effective motives: an assignment
of a finite-dimensional ℚ-vector space to each motive, acting on
morphisms, preserving identities and composition, multiplying dimensions
over tensor products, and identifying the trace of the identity
endomorphism of each motive with the dimension of its fiber. This packages
the consequence of exactness and faithfulness that the paper's tannakian
obstruction needs: Tr(id | M) = dim ω(M). -/
structure FibFun (W : CorrWorld.{u, v}) where
  /-- the dimension of the fiber of each motive -/
  dimv : MotElem W → ℕ
  /-- the action on morphisms -/
  fmap : ∀ {M N : MotElem W}, Hom W M N → ((Fin (dimv M) → ℚ) → (Fin (dimv N) → ℚ))
  /-- identities are preserved -/
  mapId : ∀ (M : MotElem W), fmap (idM W M) = id
  /-- composition is preserved -/
  mapComp : ∀ {M N P : MotElem W} (f : Hom W M N) (g : Hom W N P),
    fmap (homComp W f g) = (fmap g) ∘ (fmap f)
  /-- dimensions multiply over tensor products -/
  dimTensor : ∀ (M N : MotElem W), dimv (tensorObj W M N) = dimv M * dimv N
  /-- the trace of the identity is the dimension of the fiber -/
  trDim : ∀ (M : MotElem W), W.trId M.X M.e = (dimv M : ℚ)

end Milne


