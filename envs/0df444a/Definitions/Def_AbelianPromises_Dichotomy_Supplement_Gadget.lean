-- Prove2me | Definitions.Def_AbelianPromises_Dichotomy_Supplement_Gadget
-- name    : AbelianPromises_Dichotomy_Supplement_Gadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:54:58.40728+00:00
-- url     : https://prove2.me/theorems/13f6d3ec-11c4-4dcc-a59a-26a5764403e5
-- title:
--   The universal S-gadget and the specified Phi transformation
-- statement:
--   For each vertex $v$ of a finite Label Cover instance $L$, take a copy of the direct power $S^{X_v}$, whose variables are functions $X_v\to\operatorname{dom}(S)$. For each edge $e:v\to w$, identify $b$ in the $w$-copy with $b\circ\pi_e$ in the $v$-copy. Retain every induced ternary $S$-constraint in the quotient. This defines the concrete universal gadget $\pi_S(L)$.
--
--   Let $J_\circ$ have one variable and the single repeated-variable constraint $(x,x,x)$. On a base input $I$ with fixed source template $R$, define
--
--   $$
--   \Phi_S(I)=\begin{cases}
--   J_\circ,&\text{if CSinglAIP rejects on }\operatorname{LC}(I),\
--   \pi_S(\kappa_{\mathrm{CSinglAIP}}(\operatorname{LC}(I))),&\text{otherwise}.
--   \end{cases}
--   $$
--
--   The source template supplies the current domains implicit in the paper's notation. The definition includes the actual quotient construction and all positional constraints, including repeated variables, empty templates, and isolated variables. It does not postulate the universal-gadget polymorphism correspondence. This is the specific transformation characterized by Theorem C.15.
-- source:
--   Tamio-Vesa Nakajima, Zephyr Verwimp, Stanislav Živný, STOC 2027 submission #967 (October 2026). Canonical submission artifact; no arXiv pin or acceptance claim. printed p. 21 (PDF p. 22), universal S-gadget paragraph and Definition C.13; Section 2 for template instances.

import Mathlib
import Definitions.Def_AbelianPromises_Dichotomy_Supplement_LabelCover

set_option autoImplicit false

namespace AbelianPromises.Dichotomy.Supplement

/-- Vertices of the disjoint union of the direct powers S^(X_v). -/
abbrev PowerVertex {A : Type} (S : Relation A) (L : LCData) :=
  (v : Fin L.n) × ({a // a ∈ L.domain v} → Carrier S)

/-- The universal gadget's identifications b at w ~ b∘π_e at v.
Quot takes the equivalence closure, so chains, either orientation, and parallel edges
all impose their identifications. This is not a homomorphism-existence predicate. -/
def GadgetIdentification {A : Type} (S : Relation A) (L : LCData)
    (u v : PowerVertex S L) : Prop :=
  ∃ (e : Fin L.m)
    (π : {a // a ∈ L.domain (L.source e)} → {a // a ∈ L.domain (L.target e)})
    (b : {a // a ∈ L.domain (L.target e)} → Carrier S),
    (∀ a, (π a).val = L.projection e a.val) ∧
      u = ⟨L.target e, b⟩ ∧ v = ⟨L.source e, b ∘ π⟩

abbrev GadgetVertex {A : Type} (S : Relation A) (L : LCData) :=
  Quot (GadgetIdentification S L)

/-- All constraints from each direct power, mapped to the quotient. -/
def GadgetConstraint {A : Type} (S : Relation A) (L : LCData)
    (t : Fin 3 → GadgetVertex S L) : Prop :=
  ∃ (v : Fin L.n) (u : Fin 3 → ({a // a ∈ L.domain v} → Carrier S)),
    (∀ a, (fun i => u i a) ∈ (actual S).rel ()) ∧
      ∀ i, t i = Quot.mk (GadgetIdentification S L) ⟨v, u i⟩

/-- Turn a concrete finite set of ordered ternary constraints into the base Instance.
The use of sets discards duplicate constraints but preserves repeated positions. -/
noncomputable def instanceOf {V : Type} [Fintype V]
    (constraints : Finset (Fin 3 → V)) : Instance := by
  classical
  exact {
    n := Fintype.card V
    m := constraints.card
    sym := fun _ => ()
    scope := fun c i => Fintype.equivFin V
      (((Fintype.equivFin {t // t ∈ constraints}).symm (Fin.cast (by simp) c)).val i) }

/-- The universal S-gadget π_S(L), including every power constraint and exactly the
edge-generated quotient identifications. Empty S and empty L are retained. -/
noncomputable def universalGadget {A : Type} [Fintype A] (S : Relation A)
    (L : LCData) : Instance := by
  classical
  letI : Fintype (PowerVertex S L) := inferInstance
  letI : Fintype (GadgetVertex S L) := Fintype.ofFinite _
  exact instanceOf (Finset.univ.filter (GadgetConstraint S L))

/-- The current-domain CSP associated with a base input over template R. -/
noncomputable def templateCSP {A : Type} [Fintype A] (R : Relation A)
    (I : Instance) : CurrentCSP := by
  classical
  let e := Fintype.equivFin (Carrier R)
  let tuples : Finset (Fin 3 → ℕ) :=
    (Finset.univ.filter fun t : Fin 3 → Carrier R => t ∈ (actual R).rel ()).image
      (fun t i => (e (t i)).val)
  exact {
    n := I.n
    m := I.m
    arity := fun _ => 3
    scope := I.scope
    domain := fun _ => Finset.range (Fintype.card (Carrier R))
    tuples := fun _ => tuples }

/-- The explicit rejection instance J_circle of Definition C.13. -/
def rejectionInstance : Instance where
  n := 1
  m := 1
  sym _ := ()
  scope _ _ := 0

/-- Definition C.13: reject to J_circle, otherwise output the universal gadget of
kappa(LC(I)). The fixed source R supplies the domains that are implicit in the paper. -/
noncomputable def phi {A C : Type} [Fintype A] [Fintype C] (R : Relation A)
    (S : Relation C) (I : Instance) : Instance :=
  let L := incidence (templateCSP R I)
  match kappa (labelCSP L) with
  | none => rejectionInstance
  | some J => universalGadget S (residualLC L J)

end AbelianPromises.Dichotomy.Supplement


