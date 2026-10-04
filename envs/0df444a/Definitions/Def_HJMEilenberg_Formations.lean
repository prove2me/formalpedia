-- Prove2me | Definitions.Def_HJMEilenberg_Formations
-- name    : HJMEilenberg_Formations
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-09T10:35:56.922133+00:00
-- url     : https://prove2.me/theorems/37fd9f6c-98c5-445f-a3d0-59dec1242166
-- title:
--   Many-sorted congruence and regular-language formations
-- statement:
--   This definition bundle fixes the many-sorted objects used in the final section of the paper. For a sorted signature it defines compatible sortwise algebra congruences, their inclusion order, intersection, universal element, and pullback; finite index means finiteness of the complete sorted quotient family. It also defines sorted languages, congruence saturation, the syntactic congruence as the supremum of all congruences saturating a language, and regularity by finite syntactic index. Finally it defines finite-index congruence formations, regular-language formations, quotient-surjective homomorphisms, and the two correspondence maps $\mathfrak F\mapsto\mathcal L_{\mathfrak F}$ and $\mathcal L\mapsto\mathfrak F_{\mathcal L}$.
--
--   The bundle is the formal interface needed by all theorem items in the mission. Its formation structures contain the closure axioms from the source but do not assume either correspondence theorem or either recovery identity.
-- source:
--   Juan Climent Vidal and Enric Cosme Llópez, Eilenberg theorems for many-sorted formations, Houston Journal of Mathematics 45(2) (2019), Section 6, pp. 351–416; arXiv:1604.04792. The free-term substrate is cross-checked against the companion TeX source A Kleene theorem for free many-sorted algebras. Definitions DefFormCgr and Def1FRL, the finite-index definition, the syntactic-congruence characterization in Section 5, and the two maps preceding the final formation theorem.

/-
Core definitions for the formation theorem in
"An Eilenberg theorem" (HJM), final section.
-/
import Definitions.Def_MSKleene_Term
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Hom.Basic

namespace HJMEilenberg

open MSKleene

universe u

variable {S : Type u} {sig : Signature S}

/-- Componentwise lifting of a sorted binary relation to an argument tuple. -/
def Args.Rel {A : SSet S} (R : (s : S) → A s → A s → Prop) :
    {w : List S} → Args A w → Args A w → Prop
  | [], _, _ => True
  | s :: w, (a, as), (b, bs) => R s a b ∧ Args.Rel R as bs

theorem Args.rel_map {A B : SSet S} (R : (s : S) → B s → B s → Prop)
    (f : SMap A B) :
    ∀ {w : List S} {xs ys : Args A w},
      Args.Rel (fun s x y => R s (f s x) (f s y)) xs ys →
        Args.Rel R (Args.map f xs) (Args.map f ys)
  | [], _, _, _ => trivial
  | _ :: _, (_, _), (_, _), h => ⟨h.1, Args.rel_map R f h.2⟩

theorem Args.rel_mono {A : SSet S}
    {R Q : (s : S) → A s → A s → Prop}
    (hRQ : ∀ s x y, R s x y → Q s x y) :
    ∀ {w : List S} {xs ys : Args A w}, Args.Rel R xs ys → Args.Rel Q xs ys
  | [], _, _, _ => trivial
  | _ :: _, (_, _), (_, _), h =>
      ⟨hRQ _ _ _ h.1, Args.rel_mono hRQ h.2⟩

/-- A many-sorted algebra congruence: a setoid at each sort, compatible with
every basic operation. -/
structure Congruence (A : Algebra sig) where
  setoid : (s : S) → Setoid (A.carrier s)
  compatible : ∀ {w : List S} {s : S} (σ : sig w s)
    (xs ys : Args A.carrier w),
    Args.Rel (fun r => setoid r) xs ys → setoid s (A.op σ xs) (A.op σ ys)

namespace Congruence

variable {A B : Algebra sig}

def Rel (Phi : Congruence A) (s : S) : A.carrier s → A.carrier s → Prop :=
  Phi.setoid s

instance : LE (Congruence A) where
  le Phi Psi := ∀ s x y, Phi.Rel s x y → Psi.Rel s x y

@[ext] theorem ext {Phi Psi : Congruence A}
    (h : ∀ s x y, Phi.Rel s x y ↔ Psi.Rel s x y) : Phi = Psi := by
  cases Phi with
  | mk Phi hPhi =>
      cases Psi with
      | mk Psi hPsi =>
          have hs : Phi = Psi := by
            funext s
            exact Setoid.ext (h s)
          subst Psi
          rfl

instance : PartialOrder (Congruence A) where
  le_refl _ _ _ _ h := h
  le_trans _ _ _ hFG hGH s x y h := hGH s x y (hFG s x y h)
  le_antisymm Phi Psi hFP hPF := by
    ext s x y
    exact ⟨hFP s x y, hPF s x y⟩

/-- Intersection of two congruences. -/
def inter (Phi Psi : Congruence A) : Congruence A where
  setoid s :=
    { r := fun x y => Phi.Rel s x y ∧ Psi.Rel s x y
      iseqv :=
        { refl := fun x => ⟨(Phi.setoid s).refl x, (Psi.setoid s).refl x⟩
          symm := fun h => ⟨(Phi.setoid s).symm h.1, (Psi.setoid s).symm h.2⟩
          trans := fun hxy hyz =>
            ⟨(Phi.setoid s).trans hxy.1 hyz.1,
              (Psi.setoid s).trans hxy.2 hyz.2⟩ } }
  compatible σ xs ys h :=
    ⟨Phi.compatible σ xs ys
        (Args.rel_mono (fun _ _ _ h => h.1) h),
      Psi.compatible σ xs ys
        (Args.rel_mono (fun _ _ _ h => h.2) h)⟩

/-- The universal congruence. -/
def top (A : Algebra sig) : Congruence A where
  setoid _ :=
    { r := fun _ _ => True
      iseqv :=
        { refl := fun _ => trivial
          symm := fun _ => trivial
          trans := fun _ _ => trivial } }
  compatible _ _ _ _ := trivial

/-- Pull a congruence back along a homomorphism. -/
def pullback (f : Hom A B) (Psi : Congruence B) : Congruence A where
  setoid s :=
    { r := fun x y => Psi.Rel s (f.toFun s x) (f.toFun s y)
      iseqv :=
        { refl := fun x => (Psi.setoid s).refl _
          symm := fun h => (Psi.setoid s).symm h
          trans := fun hxy hyz => (Psi.setoid s).trans hxy hyz } }
  compatible σ xs ys h := by
    change Psi.Rel _ (f.toFun _ (A.op σ xs)) (f.toFun _ (A.op σ ys))
    rw [f.map_op, f.map_op]
    exact Psi.compatible σ _ _ (Args.rel_map (fun r => Psi.Rel r) f.toFun h)

/-- A congruence has finite index when the sorted family of its quotient
carriers is finite. -/
def FiniteIndex (Phi : Congruence A) : Prop :=
  SFinite (fun s => Quotient (Phi.setoid s))

end Congruence

/-- A sorted language in an algebra. -/
abbrev Language (A : Algebra sig) := SSub A.carrier

/-- A language is saturated by a congruence when membership is constant on
every congruence class, sort by sort. -/
def Saturated {A : Algebra sig} (Phi : Congruence A) (L : Language A) : Prop :=
  ∀ s x y, Phi.Rel s x y → (x ∈ L s ↔ y ∈ L s)

/-- Supremum-style definition of the syntactic congruence: the intersection of
all congruences that upper-bound every congruence saturating `L`. -/
def syntacticCongruence (A : Algebra sig) (L : Language A) : Congruence A where
  setoid s :=
    { r := fun x y => ∀ Psi : Congruence A,
        (∀ Phi : Congruence A, Saturated Phi L → Phi ≤ Psi) →
          Psi.Rel s x y
      iseqv :=
        { refl := fun x Psi _ => (Psi.setoid s).refl x
          symm := fun h Psi hPsi => (Psi.setoid s).symm (h Psi hPsi)
          trans := fun hxy hyz Psi hPsi =>
            (Psi.setoid s).trans (hxy Psi hPsi) (hyz Psi hPsi) } }
  compatible σ xs ys h := by
    intro Psi hPsi
    apply Psi.compatible σ xs ys
    exact Args.rel_mono (fun _ _ _ h => h Psi hPsi) h

/-- A language is regular when its syntactic congruence has finite index. -/
def Regular (A : Algebra sig) (L : Language A) : Prop :=
  Congruence.FiniteIndex (syntacticCongruence A L)

/-- Sortwise inverse image of a language along a homomorphism. -/
def languagePreimage {A B : Algebra sig} (f : Hom A B) (L : Language B) :
    Language A := fun s => f.toFun s ⁻¹' L s

/-- `f` is a `Theta`-epimorphism: its composite with the quotient projection
is surjective at every sort. -/
def IsQuotientEpi {A B : Algebra sig} (f : Hom A B)
    (Theta : Congruence B) : Prop :=
  ∀ s, Function.Surjective
    (fun x : A.carrier s =>
      Quotient.mk'' (s₁ := Theta.setoid s) (f.toFun s x))

/-- Definition `DefFormCgr`, with the additional final-section requirement
that every selected congruence have finite index. -/
structure FiniteIndexCongruenceFormation (sig : Signature S) where
  congruences : (X : SSet S) → Set (Congruence (freeAlgebra sig X))
  nonempty : ∀ X, (congruences X).Nonempty
  inter_closed : ∀ X {Phi Psi}, Phi ∈ congruences X →
    Psi ∈ congruences X → Congruence.inter Phi Psi ∈ congruences X
  upward_closed : ∀ X {Phi Psi}, Phi ∈ congruences X →
    Phi ≤ Psi → Psi ∈ congruences X
  pullback_closed : ∀ X Y (Theta : Congruence (freeAlgebra sig Y)),
    Theta ∈ congruences Y → ∀ f : Hom (freeAlgebra sig X) (freeAlgebra sig Y),
      IsQuotientEpi f Theta → Congruence.pullback f Theta ∈ congruences X
  finite_index : ∀ X {Phi}, Phi ∈ congruences X → Phi.FiniteIndex

namespace FiniteIndexCongruenceFormation

instance : LE (FiniteIndexCongruenceFormation sig) where
  le F G := ∀ X, F.congruences X ⊆ G.congruences X

@[ext] theorem ext {F G : FiniteIndexCongruenceFormation sig}
    (h : ∀ X Phi, Phi ∈ F.congruences X ↔ Phi ∈ G.congruences X) :
    F = G := by
  cases F with
  | mk f a b c d e =>
      cases G with
      | mk g a' b' c' d' e' =>
          have hfg : f = g := by
            funext X
            ext Phi
            exact h X Phi
          subst g
          rfl

instance : PartialOrder (FiniteIndexCongruenceFormation sig) where
  le_refl _ _ _ h := h
  le_trans _ _ _ hFG hGH X Phi h := hGH X (hFG X h)
  le_antisymm F G hFG hGF := by
    ext X Phi
    exact ⟨fun h => hFG X h, fun h => hGF X h⟩

end FiniteIndexCongruenceFormation

/-- Definition `Def1FRL`: a formation of regular languages on free algebras. -/
structure RegularLanguageFormation (sig : Signature S) where
  languages : (X : SSet S) → Set (Language (freeAlgebra sig X))
  regular : ∀ X {L}, L ∈ languages X → Regular (freeAlgebra sig X) L
  top_saturated : ∀ X {L}, Saturated (Congruence.top (freeAlgebra sig X)) L →
    L ∈ languages X
  inter_saturated : ∀ X {L K}, L ∈ languages X → K ∈ languages X →
    ∀ {M}, Saturated
      (Congruence.inter (syntacticCongruence (freeAlgebra sig X) L)
        (syntacticCongruence (freeAlgebra sig X) K)) M →
      M ∈ languages X
  pullback_saturated : ∀ X Y {M}, M ∈ languages Y →
    ∀ f : Hom (freeAlgebra sig X) (freeAlgebra sig Y),
      IsQuotientEpi f (syntacticCongruence (freeAlgebra sig Y) M) →
      ∀ {L}, Saturated
        (Congruence.pullback f (syntacticCongruence (freeAlgebra sig Y) M)) L →
        L ∈ languages X

namespace RegularLanguageFormation

instance : LE (RegularLanguageFormation sig) where
  le L K := ∀ X, L.languages X ⊆ K.languages X

@[ext] theorem ext {L K : RegularLanguageFormation sig}
    (h : ∀ X M, M ∈ L.languages X ↔ M ∈ K.languages X) : L = K := by
  cases L with
  | mk l a b c d =>
      cases K with
      | mk k a' b' c' d' =>
          have hlk : l = k := by
            funext X
            ext M
            exact h X M
          subst k
          rfl

instance : PartialOrder (RegularLanguageFormation sig) where
  le_refl _ _ _ h := h
  le_trans _ _ _ hLK hKM X L h := hKM X (hLK X h)
  le_antisymm L K hLK hKL := by
    ext X M
    exact ⟨fun h => hLK X h, fun h => hKL X h⟩

end RegularLanguageFormation

/-- Languages saturated by some congruence selected by a congruence
formation. This is the paper's map `F ↦ L_F`. -/
def languagesOf (F : FiniteIndexCongruenceFormation sig) (X : SSet S) :
    Set (Language (freeAlgebra sig X)) :=
  {L | ∃ Phi, Phi ∈ F.congruences X ∧ Saturated Phi L}

/-- Finite-index congruences all of whose saturated languages lie in a
language formation. This is the paper's map `L ↦ F_L`. -/
def congruencesOf (L : RegularLanguageFormation sig) (X : SSet S) :
    Set (Congruence (freeAlgebra sig X)) :=
  {Phi | Phi.FiniteIndex ∧
    ∀ K, Saturated Phi K → K ∈ L.languages X}

end HJMEilenberg


