-- Prove2me | Definitions.Def_OAI_Combinatorics_Automata_Rank
-- name    : OAI_Combinatorics_Automata_Rank
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:56:27.194281+00:00
-- url     : https://prove2.me/theorems/b4be248c-9175-4721-b495-48454c72a78c
-- title:
--   Rank, support, mirror images and the split factorization of matching diagrams
-- statement:
--   Let $A,B,C$ be sets, assumed finite whenever composites, ranks or supports are involved. As before, a matching diagram from $A$ to $B$ is a pairing of $A\sqcup B$, with left ports $A$ and right ports $B$, and $ab$ denotes the gluing composite in path order. A pair joining a left port to a right port is a *transversal*; a pair of two ports on the same side is a *cap*.
--
--   1. **Identity and composition facts.** The identity diagram pairs every port with the equally indexed port on the other side, and a diagram on $A\sqcup A$ that pairs each left port $i$ with the right port $i$ is the identity. In a composite $ab$, every left cap of $a$ and every right cap of $b$ survives, and transversals $i$–$j$ of $a$ and $j$–$k$ of $b$ produce the transversal $i$–$k$ of $ab$. A pairing all of whose pairs are pairs of another pairing coincides with it.
--
--   2. **Transversal endpoints and rank.** For a diagram $a$ from $A$ to $B$,
--   $$L(a)=\{i\in A:\ \text{the left port } i \text{ is paired with a right port}\},\qquad R(a)=\{j\in B:\ \text{the right port } j \text{ is paired with a left port}\},$$
--   and the rank $\operatorname{rk}(a)=|L(a)|$ is the number of transversals. The transversals give a bijection $L(a)\to R(a)$, and an endpoint of a left cap never lies in $L(a)$.
--
--   3. **Support.** For a diagram $a$ on $A\sqcup A$,
--   $$\operatorname{supp}(a)=\{i\in A:\ a \text{ does not pair the left port } i \text{ with the right port } i\}.$$
--
--   4. **Mirror images and cancellation.** The mirror image $a^{\dagger}$ of a diagram $a$ from $A$ to $B$ is the diagram from $B$ to $A$ obtained by exchanging the two sides. If $L(a)=A$, then $a\,a^{\dagger}=\mathrm{id}_A$. One-sided inverses cancel: for $u$ from $A$ to $B$ and $v$ from $B$ to $A$, if $vu=\mathrm{id}_B$ then $ux=uy$ implies $x=y$ for diagrams $x,y$ from $B$ to $C$, and if $uv=\mathrm{id}_A$ then $xu=yu$ implies $x=y$ for diagrams $x,y$ from $C$ to $A$.
--
--   5. **Split factorization.** For a diagram $e$ on $A\sqcup A$ put $X=L(e)$. The diagram $\lambda_e$ from $A$ to $X$ keeps the left caps of $e$ and pairs each left port $i\in X$ with the right port $i$; the diagram $\rho_e$ from $X$ to $A$ pairs the left port $i\in X$ with the right port $j$ whenever $e$ has the transversal $i$–$j$, keeps the right caps of $e$ and has no left caps. Then
--   $$\lambda_e\,\rho_e=e,\qquad \lambda_e^{\dagger}\,\lambda_e=\mathrm{id}_X,\qquad \rho_e\,\rho_e^{\dagger}=\mathrm{id}_X,$$
--   and if $e$ is idempotent, $ee=e$, then moreover $\rho_e\,\lambda_e=\mathrm{id}_X$.
--
--   Rank and support are the two size measures of matching diagrams used in the lower-bound argument. The split factorization shows that an idempotent diagram $e$ of rank $r$ factors through a set of $r$ ports, with $\rho_e\lambda_e$ the identity there; this is the basis for realizing the corner $e\,\mathcal{D}\,e$ of the diagram monoid on only $r$ ports.
--
--   **Formalization Note** `lefts a` and `rights a` are `Finset`s obtained by filtering `Finset.univ` (under `open scoped Classical`), and `rank a` is the cardinality of `lefts a`; `transversalEquiv`, `support`, `flip` (transport along `Equiv.sumComm`), `splitLeft` and `splitRight` are as above, the index set $X$ being the subtype `{i // i ∈ lefts e}`. The listed facts are `identity_link`, `eq_identity`, `compose_left_cap`, `compose_right_cap`, `compose_transversal`, `eq_of_link_imp`, `left_cap_not_lefts`, `compose_flip_eq_identity`, `compose_cancel_left`, `compose_cancel_right`, `splitLeft_splitRight`, `splitLeft_inverse`, `splitRight_inverse` and `splitRight_splitLeft`; `compose a b` is $ab$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Rank.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Rank.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the OneWayLiveness mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network

namespace OAI

namespace OneWayLiveness

namespace Pairing
open scoped Classical
variable {A B C : Type*}

@[simp] lemma identity_link (x y : A ⊕ A) :
    (identity A).link x y ↔ Sum.swap x = y := by
  cases x <;> rfl

lemma eq_identity (a : Pairing (A ⊕ A))
    (h : ∀ i, a.link (.inl i) (.inr i)) : a = identity A := by
  apply Pairing.ext
  funext x y
  apply propext
  rw [a.link_iff, identity_link]
  have hm : a.mate x = Sum.swap x := by
    cases x with
    | inl i => exact (a.eq_mate (h i)).symm
    | inr i => exact (a.eq_mate (a.symm (h i))).symm
  rw [hm]

variable [Fintype A] [Fintype B] [Fintype C]

lemma compose_left_cap (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C))
    {i j : A} (h : a.link (.inl i) (.inl j)) :
    (compose a b).link (.inl i) (.inl j) := by
  refine ⟨?_, ?_⟩
  · intro he
    have hij : i = j := Sum.inl.inj he
    subst j
    exact a.irrefl _ h
  · exact (show (glueGraph a b).Adj (.inl (.inl i)) (.inl (.inl j)) from h).reachable

lemma compose_right_cap (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C))
    {i j : C} (h : b.link (.inr i) (.inr j)) :
    (compose a b).link (.inr i) (.inr j) := by
  refine ⟨?_, ?_⟩
  · intro he
    have hij : i = j := Sum.inr.inj he
    subst j
    exact b.irrefl _ h
  · exact (show (glueGraph a b).Adj (.inr (.inr i)) (.inr (.inr j)) from h).reachable

lemma compose_transversal (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C))
    {i : A} {j : B} {k : C} (ha : a.link (.inl i) (.inr j))
    (hb : b.link (.inl j) (.inr k)) : (compose a b).link (.inl i) (.inr k) := by
  refine ⟨Sum.inl_ne_inr, ?_⟩
  exact (show (glueGraph a b).Adj (.inl (.inl i)) (.inl (.inr j)) from ha).reachable.trans
    ((show (glueGraph a b).Adj (.inl (.inr j)) (.inr (.inl j)) from rfl).reachable.trans
      (show (glueGraph a b).Adj (.inr (.inl j)) (.inr (.inr k)) from hb).reachable)

noncomputable def lefts (a : Pairing (A ⊕ B)) : Finset A :=
  Finset.univ.filter fun i => ∃ j, a.link (.inl i) (.inr j)
noncomputable def rights (a : Pairing (A ⊕ B)) : Finset B :=
  Finset.univ.filter fun j => ∃ i, a.link (.inl i) (.inr j)
noncomputable def rank (a : Pairing (A ⊕ B)) : ℕ := (lefts a).card

@[simp] lemma mem_lefts (a : Pairing (A ⊕ B)) (i : A) :
    i ∈ lefts a ↔ ∃ j, a.link (.inl i) (.inr j) := by simp [lefts]
@[simp] lemma mem_rights (a : Pairing (A ⊕ B)) (j : B) :
    j ∈ rights a ↔ ∃ i, a.link (.inl i) (.inr j) := by simp [rights]

/-- The matching bijects its left and right transversal endpoints. -/
noncomputable def transversalEquiv (a : Pairing (A ⊕ B)) :
    {i // i ∈ lefts a} ≃ {j // j ∈ rights a} := by
  let f : {i // i ∈ lefts a} → {j // j ∈ rights a} := fun i =>
    ⟨(mem_lefts a i).mp i.property |>.choose,
      (mem_rights a _).mpr ⟨i, ((mem_lefts a i).mp i.property).choose_spec⟩⟩
  have hf (i : {i // i ∈ lefts a}) : a.link (.inl i.val) (.inr (f i).val) :=
    ((mem_lefts a i).mp i.property).choose_spec
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j hij
    apply Subtype.ext
    have hh := a.eq_mate (a.symm (hf i))
    have hj := a.eq_mate (a.symm (hf j))
    rw [hij] at hh
    exact Sum.inl.inj (hh.trans hj.symm)
  · intro j
    obtain ⟨i, hij⟩ := (mem_rights a j).mp j.property
    let i' : {i // i ∈ lefts a} := ⟨i, (mem_lefts a i).mpr ⟨j, hij⟩⟩
    refine ⟨i', Subtype.ext ?_⟩
    exact Sum.inr.inj ((a.eq_mate (hf i')).trans (a.eq_mate hij).symm)

noncomputable def support (a : Pairing (A ⊕ A)) : Finset A :=
  Finset.univ.filter fun i => ¬ a.link (.inl i) (.inr i)
@[simp] lemma mem_support (a : Pairing (A ⊕ A)) (i : A) :
    i ∈ support a ↔ ¬ a.link (.inl i) (.inr i) := by simp [support]

end Pairing

namespace Pairing
open scoped Classical
variable {P : Type*} {A B C D : Type*}

lemma eq_of_link_imp (a b : Pairing P)
    (h : ∀ x y, a.link x y → b.link x y) : a = b := by
  apply Pairing.ext
  funext x y
  apply propext
  refine ⟨h x y, fun hb => ?_⟩
  have he : y = a.mate x := (b.eq_mate hb).trans (b.eq_mate (h x _ (a.mate_link x))).symm
  rw [he]
  exact a.mate_link x

def flip (a : Pairing (A ⊕ B)) : Pairing (B ⊕ A) := a.transport (Equiv.sumComm A B)

@[simp] lemma flip_link (a : Pairing (A ⊕ B)) (x y : B ⊕ A) :
    (flip a).link x y ↔ a.link (Sum.swap x) (Sum.swap y) := Iff.rfl

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

lemma left_cap_not_lefts (a : Pairing (A ⊕ B)) {i j : A}
    (h : a.link (.inl i) (.inl j)) : i ∉ lefts a := by
  intro hi
  obtain ⟨k, hik⟩ := (mem_lefts a i).mp hi
  have he := (a.eq_mate h).trans (a.eq_mate hik).symm
  cases he

lemma compose_flip_eq_identity (a : Pairing (A ⊕ B))
    (ha : ∀ i, i ∈ lefts a) : compose a (flip a) = identity A := by
  apply eq_identity
  intro i
  obtain ⟨j, hij⟩ := (mem_lefts a i).mp (ha i)
  exact compose_transversal a (flip a) hij (a.symm hij)

lemma compose_cancel_left (u : Pairing (A ⊕ B)) (v : Pairing (B ⊕ A))
    (hu : compose v u = identity B) {x y : Pairing (B ⊕ C)}
    (h : compose u x = compose u y) : x = y := by
  have hh := congrArg (compose v) h
  simpa only [← compose_assoc, hu, identity_compose] using hh

lemma compose_cancel_right (u : Pairing (A ⊕ B)) (v : Pairing (B ⊕ A))
    (hu : compose u v = identity A) {x y : Pairing (C ⊕ A)}
    (h : compose x u = compose y u) : x = y := by
  have hh := congrArg (fun z => compose z v) h
  simpa only [compose_assoc, hu, compose_identity] using hh

/-- Retain the left caps and straighten the left transversal endpoints. -/
noncomputable def splitLeft (e : Pairing (A ⊕ A)) : Pairing (A ⊕ {i // i ∈ lefts e}) where
  link
    | .inl i, .inl j => e.link (.inl i) (.inl j)
    | .inl i, .inr j => i = j.val
    | .inr i, .inl j => i.val = j
    | .inr _, .inr _ => False
  symm := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact e.symm h
    · exact h.symm
    · exact h.symm
    · exact h
  irrefl := by
    intro x
    cases x with
    | inl i => exact e.irrefl _
    | inr i => exact id
  unique := by
    intro x
    cases x with
    | inl i =>
      by_cases hi : i ∈ lefts e
      · refine ⟨.inr ⟨i, hi⟩, rfl, ?_⟩
        intro y hy
        cases y with
        | inl j => exact ((left_cap_not_lefts e hy) hi).elim
        | inr j => exact congrArg Sum.inr (Subtype.ext hy.symm)
      · obtain ⟨y, hy, hu⟩ := e.unique (.inl i)
        rcases y with j | j
        · refine ⟨.inl j, hy, ?_⟩
          intro y hy'
          cases y with
          | inl k => exact congrArg Sum.inl (Sum.inl.inj (hu (.inl k) hy'))
          | inr k => exact (hi (hy' ▸ k.property)).elim
        · exact (hi ((mem_lefts e i).mpr ⟨j, hy⟩)).elim
    | inr i =>
      refine ⟨.inl i.val, rfl, ?_⟩
      intro y hy
      cases y with
      | inl j => exact congrArg Sum.inl hy.symm
      | inr j => exact hy.elim

/-- Retain the right caps and all the original transversals. -/
noncomputable def splitRight (e : Pairing (A ⊕ A)) : Pairing ({i // i ∈ lefts e} ⊕ A) where
  link
    | .inl _, .inl _ => False
    | .inl i, .inr j => e.link (.inl i.val) (.inr j)
    | .inr i, .inl j => e.link (.inr i) (.inl j.val)
    | .inr i, .inr j => e.link (.inr i) (.inr j)
  symm := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact h
    all_goals exact e.symm h
  irrefl := by
    intro x
    cases x with
    | inl i => exact id
    | inr i => exact e.irrefl _
  unique := by
    intro x
    cases x with
    | inl i =>
      obtain ⟨j, hij⟩ := (mem_lefts e i).mp i.property
      refine ⟨.inr j, hij, ?_⟩
      intro y hy
      cases y with
      | inl k => exact hy.elim
      | inr k =>
        exact congrArg Sum.inr (Sum.inr.inj ((e.eq_mate hy).trans (e.eq_mate hij).symm))
    | inr i =>
      obtain ⟨y, hy, hu⟩ := e.unique (.inr i)
      rcases y with j | j
      · have hj : j ∈ lefts e := (mem_lefts e j).mpr ⟨i, e.symm hy⟩
        refine ⟨.inl ⟨j, hj⟩, hy, ?_⟩
        intro y hy'
        cases y with
        | inl k => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (hu _ hy')))
        | inr k => have hh := hu _ hy'; cases hh
      · refine ⟨.inr j, hy, ?_⟩
        intro y hy'
        cases y with
        | inl k => have hh := hu _ hy'; cases hh
        | inr k => exact congrArg Sum.inr (Sum.inr.inj (hu _ hy'))

lemma splitLeft_splitRight (e : Pairing (A ⊕ A)) :
    compose (splitLeft e) (splitRight e) = e := by
  symm
  apply eq_of_link_imp
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y
  · exact compose_left_cap _ _ hxy
  · let x' : {i // i ∈ lefts e} := ⟨x, (mem_lefts e x).mpr ⟨y, hxy⟩⟩
    exact compose_transversal _ _ (show (splitLeft e).link (.inl x) (.inr x') from rfl) hxy
  · let y' : {i // i ∈ lefts e} := ⟨y, (mem_lefts e y).mpr ⟨x, e.symm hxy⟩⟩
    exact (compose (splitLeft e) (splitRight e)).symm
      (compose_transversal _ _ (show (splitLeft e).link (.inl y) (.inr y') from rfl) (e.symm hxy))
  · exact compose_right_cap _ _ hxy

lemma splitLeft_inverse (e : Pairing (A ⊕ A)) :
    compose (flip (splitLeft e)) (splitLeft e) = identity {i // i ∈ lefts e} := by
  apply eq_identity
  intro i
  exact compose_transversal _ _
    (show (flip (splitLeft e)).link (.inl i) (.inr i.val) from rfl)
    (show (splitLeft e).link (.inl i.val) (.inr i) from rfl)

lemma splitRight_inverse (e : Pairing (A ⊕ A)) :
    compose (splitRight e) (flip (splitRight e)) = identity {i // i ∈ lefts e} := by
  apply compose_flip_eq_identity
  intro i
  obtain ⟨j, hij⟩ := (mem_lefts e i).mp i.property
  exact (mem_lefts _ _).mpr ⟨j, hij⟩

lemma splitRight_splitLeft (e : Pairing (A ⊕ A)) (he : compose e e = e) :
    compose (splitRight e) (splitLeft e) = identity {i // i ∈ lefts e} := by
  apply compose_cancel_left (splitLeft e) (flip (splitLeft e)) (splitLeft_inverse e)
  apply compose_cancel_right (splitRight e) (flip (splitRight e)) (splitRight_inverse e)
  have hh := he
  rw [← splitLeft_splitRight e] at hh
  simpa only [compose_assoc, identity_compose] using hh

end Pairing

end OneWayLiveness

end OAI


