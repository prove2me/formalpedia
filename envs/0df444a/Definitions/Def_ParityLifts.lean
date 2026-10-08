-- Prove2me | Definitions.Def_ParityLifts
-- name    : ParityLifts
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:00.509379+00:00
-- url     : https://prove2.me/theorems/3385df69-08db-44f8-b26b-3411f8981068
-- statement:
--   For t, a choice system consists of finite domain sets D_i for each i<t and, for each pair p=(i,j) with i<j<t, a finite label set L_p with a left map D_i→L_p and a right map D_j→L_p. It is successful if one can pick d_i in D_i for all i so that for every pair i<j the left label of d_i equals the right label of d_j; it has size at most A if every domain and label set has at most A elements. The template graph on t main vertices plus helper vertices (one helper for each pair i<j and each third index m different from i and j) joins distinct main vertices to each other and joins a helper to its three incident main indices i, j, m, with no helper-helper edges. The base graph of a choice system has vertices (i,d) with d in D_i and helper vertices (h,q) with q a label of the helper's pair; its edges join (i,d) to (j,e) when the labels of d and e agree for the pair, join a helper carrying the label of d to (i,d) and likewise on the right side, and join a helper carrying any label to every vertex of its third index. Projecting to types is a graph homomorphism onto the template. Given a homomorphism τ from G to a template T on a finite vertex type and a bit assignment b on template vertices, the lift has vertices (u,z) where z assigns a bit to each template neighbor of τ(u) with total parity b(τ(u)); two lift vertices are adjacent when u,v are adjacent in G and their tags agree on the edge coordinates, z_u(τ v)=z_v(τ u). The zero lift uses b≡0, and the star lift uses b=1 exactly at main vertex 0. Two conventions, joint and separate, set the bag parameter to k+1 or k and the detection round to 2 or 1; orderFactor(t)=t·2^(t-2+3·C(t-1,2))+12·C(t,3). Joint and separate k-dimensional Weisfeiler-Leman colors of k-tuples are defined recursively from atomic types (pairwise equality and adjacency), refining by the multiset of colors obtained by replacing one coordinate by every vertex, jointly or per coordinate. Graphs are WL-equivalent if the color histograms of all k-tuples agree at every round, and pure WL-equivalent if the histograms of tuples taken wholly from each side of the disjoint union agree. ParityReductionStatement is a defined proposition, not an established theorem: for every k≥4, convention c, and choice system with t equal to the bag parameter, the two lifts have equal vertex counts, the count is at most A·orderFactor(t) whenever the system has size at most A≥1, WL-equivalence and pure WL-equivalence of the zero and star lifts each hold exactly when the system is not successful, and if it is successful the lifts have different histograms at the detection round in both senses.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ParityLifts.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ParityLifts.lean; bytes 16..8004
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI



namespace ParityWL

open scoped BigOperators

abbrev Bit := ZMod 2
abbrev MainPair (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}
abbrev Helper (t : ℕ) :=
  {q : MainPair t × Fin t // q.2 ≠ q.1.1.1 ∧ q.2 ≠ q.1.1.2}
abbrev TemplateVertex (t : ℕ) := Fin t ⊕ Helper t

structure ChoiceSystem (t : ℕ) where
  Domain : Fin t → Type
  domainFintype : ∀ i, Fintype (Domain i)
  Label : MainPair t → Type
  labelFintype : ∀ p, Fintype (Label p)
  leftLabel : (p : MainPair t) → Domain p.1.1 → Label p
  rightLabel : (p : MainPair t) → Domain p.1.2 → Label p

attribute [instance] ChoiceSystem.domainFintype ChoiceSystem.labelFintype

def ChoiceSystem.Successful {t : ℕ} (C : ChoiceSystem t) : Prop :=
  ∃ d : (i : Fin t) → C.Domain i,
    ∀ p : MainPair t, C.leftLabel p (d p.1.1) = C.rightLabel p (d p.1.2)

def ChoiceSystem.SizeAtMost {t : ℕ} (C : ChoiceSystem t) (A : ℕ) : Prop :=
  (∀ i, Fintype.card (C.Domain i) ≤ A) ∧ (∀ p, Fintype.card (C.Label p) ≤ A)

def helperIncident {t : ℕ} (h : Helper t) (i : Fin t) : Prop :=
  i = h.1.1.1.1 ∨ i = h.1.1.1.2 ∨ i = h.1.2

def templateAdj {t : ℕ} : TemplateVertex t → TemplateVertex t → Prop
  | .inl i, .inl j => i ≠ j
  | .inl i, .inr h => helperIncident h i
  | .inr h, .inl i => helperIncident h i
  | .inr _, .inr _ => False

def template (t : ℕ) : SimpleGraph (TemplateVertex t) where
  Adj := templateAdj
  symm := ⟨by
    intro x y h
    cases x <;> cases y <;> simp_all [templateAdj, ne_comm]⟩
  loopless := ⟨by
    intro x
    cases x <;> simp [templateAdj]⟩

abbrev BaseVertex {t : ℕ} (C : ChoiceSystem t) :=
  ((i : Fin t) × C.Domain i) ⊕ ((h : Helper t) × C.Label h.1.1)

def baseType {t : ℕ} {C : ChoiceSystem t} : BaseVertex C → TemplateVertex t
  | .inl x => .inl x.1
  | .inr x => .inr x.1

inductive BaseArc {t : ℕ} (C : ChoiceSystem t) : BaseVertex C → BaseVertex C → Prop
  | main (p : MainPair t) (d : C.Domain p.1.1) (e : C.Domain p.1.2)
      (h : C.leftLabel p d = C.rightLabel p e) :
      BaseArc C (.inl ⟨p.1.1, d⟩) (.inl ⟨p.1.2, e⟩)
  | left (h : Helper t) (d : C.Domain h.1.1.1.1) :
      BaseArc C (.inr ⟨h, C.leftLabel h.1.1 d⟩) (.inl ⟨h.1.1.1.1, d⟩)
  | right (h : Helper t) (e : C.Domain h.1.1.1.2) :
      BaseArc C (.inr ⟨h, C.rightLabel h.1.1 e⟩) (.inl ⟨h.1.1.1.2, e⟩)
  | third (h : Helper t) (q : C.Label h.1.1) (f : C.Domain h.1.2) :
      BaseArc C (.inr ⟨h, q⟩) (.inl ⟨h.1.2, f⟩)

def baseGraph {t : ℕ} (C : ChoiceSystem t) : SimpleGraph (BaseVertex C) :=
  SimpleGraph.fromRel (BaseArc C)

def baseProjection {t : ℕ} (C : ChoiceSystem t) : baseGraph C →g template t where
  toFun := baseType
  map_rel' := by
    intro x y h
    have arc : ∀ u v, BaseArc C u v → (template t).Adj (baseType u) (baseType v) := by
      intro u v huv
      cases huv with
      | main p d e he => exact ne_of_lt p.property
      | left h d => exact Or.inl rfl
      | right h e => exact Or.inr (Or.inl rfl)
      | third h q f => exact Or.inr (Or.inr rfl)
    rcases h.2 with hxy | hyx
    · exact arc x y hxy
    · exact (arc y x hyx).symm

section Lifts

variable {A V : Type} [Fintype A] (T : SimpleGraph A) (G : SimpleGraph V)

noncomputable def Tag (b : A → Bit) (a : A) := by
  classical
  exact {z : T.neighborSet a → Bit // ∑ v, z v = b a}

noncomputable instance tagFintype (b : A → Bit) (a : A) : Fintype (Tag T b a) := by
  classical
  unfold Tag
  infer_instance

abbrev LiftVertex (τ : G →g T) (b : A → Bit) := (u : V) × Tag T b (τ u)

noncomputable def liftGraph (τ : G →g T) (b : A → Bit) :
    SimpleGraph (LiftVertex T G τ b) where
  Adj u v := ∃ h : G.Adj u.1 v.1,
    u.2.1 ⟨τ v.1, τ.map_adj h⟩ = v.2.1 ⟨τ u.1, τ.map_adj h.symm⟩
  symm := ⟨by
    intro u v h
    rcases h with ⟨h, e⟩
    exact ⟨h.symm, e.symm⟩⟩
  loopless := ⟨by
    intro u h
    exact G.irrefl h.1⟩

end Lifts

noncomputable def starParity (t : ℕ) : TemplateVertex t → Bit :=
  fun a => if ∃ i : Fin t, i.val = 0 ∧ a = .inl i then 1 else 0

noncomputable def zeroLift {t : ℕ} (C : ChoiceSystem t) :=
  liftGraph (template t) (baseGraph C) (baseProjection C) (fun _ => 0)

noncomputable def starLift {t : ℕ} (C : ChoiceSystem t) :=
  liftGraph (template t) (baseGraph C) (baseProjection C) (starParity t)

inductive Convention | joint | separate
  deriving DecidableEq

def bagParameter (c : Convention) (k : ℕ) : ℕ :=
  match c with | .joint => k + 1 | .separate => k

def detectionRound : Convention → ℕ | .joint => 2 | .separate => 1

def orderFactor (t : ℕ) : ℕ :=
  t * 2 ^ (t - 2 + 3 * (t - 1).choose 2) + 12 * t.choose 3

abbrev AtomicType (k : ℕ) := Fin k → Fin k → Bool × Bool

def JointColor (k : ℕ) : ℕ → Type
  | 0 => AtomicType k
  | r + 1 => JointColor k r × Multiset (Fin k → JointColor k r)

def SeparateColor (k : ℕ) : ℕ → Type
  | 0 => AtomicType k
  | r + 1 => SeparateColor k r × (Fin k → Multiset (SeparateColor k r))

noncomputable def atomicType {V : Type} (G : SimpleGraph V) {k : ℕ}
    (x : Fin k → V) : AtomicType k := by
  classical
  exact fun i j => (decide (x i = x j), decide (G.Adj (x i) (x j)))

noncomputable def jointColor {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (r : ℕ) → (Fin k → V) → JointColor k r
  | 0, x => atomicType G x
  | r + 1, x => (jointColor G k r x,
      Finset.univ.val.map (fun y => fun i => jointColor G k r (Function.update x i y)))

noncomputable def separateColor {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (r : ℕ) → (Fin k → V) → SeparateColor k r
  | 0, x => atomicType G x
  | r + 1, x => (separateColor G k r x,
      fun i => Finset.univ.val.map (fun y => separateColor G k r (Function.update x i y)))

noncomputable def sameHistogram {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : Convention) (k r : ℕ) : Prop :=
  match c with
  | .joint => Finset.univ.val.map (jointColor G k r) =
      Finset.univ.val.map (jointColor H k r)
  | .separate => Finset.univ.val.map (separateColor G k r) =
      Finset.univ.val.map (separateColor H k r)

noncomputable def samePureHistogram {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : Convention) (k r : ℕ) : Prop :=
  match c with
  | .joint =>
      Finset.univ.val.map (fun x : Fin k → V => jointColor (G.sum H) k r (Sum.inl ∘ x)) =
      Finset.univ.val.map (fun x : Fin k → W => jointColor (G.sum H) k r (Sum.inr ∘ x))
  | .separate =>
      Finset.univ.val.map (fun x : Fin k → V => separateColor (G.sum H) k r (Sum.inl ∘ x)) =
      Finset.univ.val.map (fun x : Fin k → W => separateColor (G.sum H) k r (Sum.inr ∘ x))

noncomputable def WLEquivalent {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : Convention) (k : ℕ) : Prop :=
  ∀ r, sameHistogram G H c k r

noncomputable def PureWLEquivalent {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (c : Convention) (k : ℕ) : Prop :=
  ∀ r, samePureHistogram G H c k r

noncomputable def ParityReductionStatement : Prop :=
  ∀ (k : ℕ), 4 ≤ k → ∀ c : Convention, ∀ C : ChoiceSystem (bagParameter c k),
    let T := template (bagParameter c k)
    let G := baseGraph C
    let τ := baseProjection C
    let V₀ := LiftVertex T G τ (fun _ => 0)
    let V₁ := LiftVertex T G τ (starParity (bagParameter c k))
    Fintype.card V₀ = Fintype.card V₁ ∧
    (∀ A : ℕ, 1 ≤ A → C.SizeAtMost A → Fintype.card V₀ ≤ A * orderFactor (bagParameter c k)) ∧
    (WLEquivalent (zeroLift C) (starLift C) c k ↔ ¬ C.Successful) ∧
    (PureWLEquivalent (zeroLift C) (starLift C) c k ↔ ¬ C.Successful) ∧
    (C.Successful → ¬ sameHistogram (zeroLift C) (starLift C) c k (detectionRound c) ∧
      ¬ samePureHistogram (zeroLift C) (starLift C) c k (detectionRound c))



end ParityWL
end OAI


