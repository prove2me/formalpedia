-- Prove2me | Definitions.Def_IntertempDUI_Finite_Axioms
-- name    : IntertempDUI_Finite_Axioms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:15.44104+00:00
-- url     : https://prove2.me/theorems/79682b98-6f54-479a-b2d3-c965e72cf201
-- title:
--   §3 and Appendix A — richness and preference axioms
-- statement:
--   The paper's structural conditions are predicates of the feasible trajectory set $\mathcal A$ and primitive interval preferences $\succeq_{\mathcal I}$. They include the insertion condition (R), its span version (R*), the contour-set condition (MinEqn), continuity (C), separability (ISep), (ISep*), (LSep), (LSep*), and (Sep), static equivalents (StEq), dominance (Dom), preference continuity (CIP), tradeoff consistency (TC), ephemerality (Eph), and richness for restricted trajectories (Rch).
--
--   $$\text{These conditions depend on }(\mathcal A,\{\succeq_{\mathcal I}\}_{\mathcal I\in\mathfrak I})\text{ alone.}$$
--
--   The comparison relations of (TC) use the paper's existential alternations satisfying (B1)–(B2). This definition layer permits the representation results to state the axioms without referring to a prospective utility or discount function.
--
--   **Formalization Note** The strict clauses of (Dom), (TC), and (CIP) are restricted to nonempty spans; (R) is quantified over $q\le r<s\le t$: the page prints $r\le s$, but at $r=s$ a continuous $\phi$ equal to $\alpha$ on $\lfloor q,r\rceil$ and to $\gamma$ on $\lfloor r,t\rceil$ forces $\alpha(r)=\gamma(r)$, so the printed condition fails for two distinct constant trajectories in any Hausdorff $\mathcal X$; the proof of Lemma A1 (p. 20) treats (R) as the case $\mathcal R=\lfloor r,s\rceil$ of (R*), i.e. $r<s$.
-- source:
--   Pivato, Intertemporal choice with continuity constraints, SSRN 3232014 (August 10, 2018), pp. 6–11, 14, 25, (R), (MinEqn), (C), (ISep), (LSep), (StEq), (Dom), (CIP), (TC), (Eph), (R*), (ISep*), (Rch); https://ssrn.com/abstract=3232014

import Mathlib
import Definitions.Def_IntertempDUI_Finite_Framework

namespace IntertempDUI.Finite

/-- (R), p. 7, read with a nonempty middle interval ⌊r,s⌉ (r < s). The page prints q ≤ r ≤ s ≤ t;
at r = s a continuous φ equal to α on ⌊q,r⌉ and to γ on ⌊r,t⌉ forces α(r) = γ(r), so the printed
condition fails for two distinct constant trajectories in any Hausdorff 𝒳. The proof of Lemma A1
(p. 20) treats (R) as the case ℛ = ⌊r,s⌉ of (R*), i.e. r < s. Empty outer brackets (q = r, s = t)
remain allowed. -/
def Richness {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ q r s t : ℝ, 0 ≤ q → q ≤ r → r < s → s ≤ t → t ≤ T →
    ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
      ∃ f ∈ A, Set.EqOn f a (bracket T q r) ∧
        indiff pref (bracket T r s) f b ∧
        Set.EqOn f c (bracket T s t)

/-- (R*), p. 14. -/
def RichnessStar {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ Q R, IsTimeSpan Q → IsTimeSpan R → Disjoint Q R →
    ∀ a ∈ A, ∀ b ∈ A, ∃ f ∈ A,
      Set.EqOn f a Q ∧
      (∀ I, IsComponent R I → indiff pref I f b)

/-- (MinEqn), p. 8: both synchronic contour preimages have time-span interiors. -/
def MinEqn {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ x : X, ∀ a ∈ A,
    IsTimeSpan (interior {t | sy pref (a t) x}) ∧
    IsTimeSpan (interior {t | sy pref x (a t)})

/-- (C), p. 9. -/
def CondC {T : ℝ} {X : Type*} [TopologicalSpace X] (pref : Pref T X) : Prop :=
  ∀ x : X, IsClosed {y : X | sy pref y x} ∧ IsClosed {y : X | sy pref x y}

/-- (ISep), p. 9. -/
def ISep {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ I J H, AreAdjacent I J H → ∀ a ∈ A, ∀ b ∈ A,
    indiff pref I a b → (pref H a b ↔ pref J a b)

/-- (ISep*), p. 14. -/
def ISepStar {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ H Q R, IsTimeInterval H → IsTimeSpan Q → IsTimeSpan R →
    Disjoint Q R → H = join Q R → ∀ a ∈ A, ∀ b ∈ A,
      (∀ I, (IsComponent Q I ∨ IsComponent R I) → pref I a b) →
      pref H a b ∧
      ((∃ I, (IsComponent Q I ∨ IsComponent R I) ∧ strict pref I a b) →
        strict pref H a b)

/-- (LSep), pp. 6–7. -/
def LSep {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ S, IsTimeSpan S → ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ A, ∀ b' ∈ A,
    Set.EqOn a a' S → Set.EqOn b b' S →
    (∀ I, IsComponent (neg S) I → indiff pref I a b) →
    (∀ I, IsComponent (neg S) I → indiff pref I a' b') →
    (pref Set.univ a b ↔ pref Set.univ a' b')

/-- The family of preference orders on restricted trajectories required in (LSep*). -/
def IsSpanOrder {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X))
    (order : Set (Time T) → Traj T X → Traj T X → Prop) : Prop :=
  ∀ S, IsTimeSpan S →
    (∀ a ∈ A, ∀ b ∈ A, order S a b ∨ order S b a) ∧
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, order S a b → order S b c → order S a c) ∧
    (∀ a ∈ A, ∀ b ∈ A, ∀ a' ∈ A, ∀ b' ∈ A,
      Set.EqOn a a' S → Set.EqOn b b' S →
      (order S a b ↔ order S a' b'))

/-- (LSep*), p. 7: existence of an intermittent order family. -/
def LSepStar {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∃ order : Set (Time T) → Traj T X → Traj T X → Prop,
    IsSpanOrder A order ∧
    ∀ S, IsTimeSpan S → ∀ a ∈ A, ∀ b ∈ A,
      (∀ I, IsComponent (neg S) I → indiff pref I a b) →
      (pref Set.univ a b ↔ order S a b)

/-- (Sep), p. 9, for the induced intermittent orders. -/
def Sep {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ S Q R, IsTimeSpan S → IsTimeSpan Q → IsTimeSpan R →
    Disjoint Q R → S = join Q R → ∀ a ∈ A, ∀ b ∈ A,
      inducedIndiff A pref Q a b →
      (induced A pref S a b ↔ induced A pref R a b)

/-- (Rch), p. 25. -/
def Rch {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ Q R, IsTimeSpan Q → IsTimeSpan R → Disjoint Q R →
    ∀ a ∈ A, ∀ b ∈ A, ∃ c ∈ A,
      Set.EqOn c a Q ∧ inducedIndiff A pref R c b

/-- (StEq), p. 10. -/
def StEq {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ S, IsTimeSpan S → ∀ a ∈ A,
    ∃ x : X, inducedIndiff A pref S (ContinuousMap.const (Time T) x) a

/-- (Dom), p. 10, with the nonempty-span domain needed for its strict clause. -/
def Dom {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ S, IsTimeSpan S → S.Nonempty → ∀ a ∈ A, ∀ b ∈ A,
    ((∀ t ∈ S, sy pref (a t) (b t)) → induced A pref S a b) ∧
    ((∀ t ∈ S,
       sy pref (a t) (b t) ∧ ¬ sy pref (b t) (a t)) → inducedStrict A pref S a b)

/-- (CIP), p. 10, on nonempty disjoint constituent spans. -/
def CIP {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ S Q R, IsTimeSpan S → IsTimeSpan Q → IsTimeSpan R →
    Q.Nonempty → R.Nonempty → Disjoint Q R → S = join Q R →
    ∀ blo ∈ A, ∀ a ∈ A, ∀ bhi ∈ A,
      inducedStrict A pref S a blo → inducedStrict A pref S bhi a →
      ∃ qlo ∈ A, ∃ qhi ∈ A, ∃ rlo ∈ A, ∃ rhi ∈ A,
        inducedStrict A pref Q a qlo ∧ inducedStrict A pref Q qhi a ∧
        inducedStrict A pref R a rlo ∧ inducedStrict A pref R rhi a ∧
        ∀ a' ∈ A,
          inducedStrict A pref Q a' qlo → inducedStrict A pref Q qhi a' →
          inducedStrict A pref R a' rlo → inducedStrict A pref R rhi a' →
          inducedStrict A pref S a' blo ∧ inducedStrict A pref S bhi a'

/-- (B1)–(B2), p. 10. -/
def IsAlternation {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X)
    (S : Set (Time T)) (x : X) (a f : Traj T X) : Prop :=
  f ∈ A ∧ inducedIndiff A pref S f (ContinuousMap.const (Time T) x) ∧
    inducedIndiff A pref (neg S) f a

/-- The weak tradeoff comparison on p. 10. -/
def TradeoffGe {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X)
    (S : Set (Time T)) (x y v w : X) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ xa ∈ A, ∃ yb ∈ A, ∃ va ∈ A, ∃ wb ∈ A,
    IsAlternation A pref S x a xa ∧ IsAlternation A pref S y b yb ∧
    IsAlternation A pref S v a va ∧ IsAlternation A pref S w b wb ∧
    pref Set.univ yb xa ∧ pref Set.univ va wb

/-- The strict reverse tradeoff comparison on p. 11. -/
def TradeoffLt {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X)
    (S : Set (Time T)) (x y v w : X) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A, ∃ xa ∈ A, ∃ yb ∈ A, ∃ va ∈ A, ∃ wb ∈ A,
    IsAlternation A pref S x a xa ∧ IsAlternation A pref S y b yb ∧
    IsAlternation A pref S v a va ∧ IsAlternation A pref S w b wb ∧
    pref Set.univ xa yb ∧ strict pref Set.univ wb va

/-- (TC), p. 11. -/
def TC {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ S₁ S₂, IsTimeSpan S₁ → IsTimeSpan S₂ → S₁.Nonempty → S₂.Nonempty →
    ∀ x y v w : X, ¬ (TradeoffGe A pref S₁ x y v w ∧ TradeoffLt A pref S₂ x y v w)

/-- (Eph), p. 11, with the existential alternation reading. -/
def Eph {T : ℝ} {X : Type*} [TopologicalSpace X]
    (A : Set (Traj T X)) (pref : Pref T X) : Prop :=
  ∀ t : Time T, ∀ w x y z : X,
    (sy pref y z ∧ ¬ sy pref z y) →
    ∃ S, IsTimeSpan S ∧ t ∈ S ∧
      ∃ a ∈ A, ∃ b ∈ A,
        IsAlternation A pref S w (ContinuousMap.const (Time T) y) a ∧
        IsAlternation A pref S x (ContinuousMap.const (Time T) z) b ∧
        strict pref Set.univ a b

end IntertempDUI.Finite


