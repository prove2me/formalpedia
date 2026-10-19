-- Prove2me | Definitions.Def_OAI_ModelTheory_Categoricity_AEC
-- name    : OAI_ModelTheory_Categoricity_AEC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:52:46.418793+00:00
-- url     : https://prove2.me/theorems/90bf14e2-a97c-4421-9350-b25e10eb981b
-- title:
--   Presentations of set-based relational models by arrays and the class of array models with strong inclusions
-- statement:
--   This file connects arrays with relational models whose carriers are sets, and defines the class $\mathbb{K}$ of array models together with its strong-substructure relation.
--
--   **Setting.** A relational model $R$ in a signature $L = (L(n))_{n \in \mathbb{N}}$, where $L(n)$ is the set of $n$-ary symbols, has a set $|R|$ (a ZF set) as carrier and an $n$-ary relation $r^R \subseteq |R|^n$ for each $r \in L(n)$. $R$ is a substructure of $T$ if $|R| \subseteq |T|$ and every $r^R$ is the restriction of $r^T$; an isomorphism $R \cong T$ is a bijection of carriers that preserves and reflects all relations. An array $M$ consists of a nonempty index set $I_M$, a nonempty dense linear order without endpoints $B_M$ whose closed intervals are countable, and binary matrices $\chi^M_t : \mathbb{N} \times B_M \to \{0,1\}$, one for each injective finite tuple $t = (x_0, \dots, x_k)$ from $I_M$. Its point set $\mathrm{Pt}(M)$ has six sorts: index points, base points, group points (finite $s \subseteq B_M$), star points (finite $v \subseteq \mathbb{N}$), row points $(t,n,s)$ and column points $(t,b,v)$. The array signature $L_{\mathrm{arr}}$ is countable; $L_{\mathrm{arr}}(n)$ consists of the array symbols of arity $n$: the four sort predicates; predicates fixing the tuple length of a row or column point and the row number of a row point; a label for each star point; projections relating a row point, or a column point together with its base point, to the entries of its tuple; the strict order of base points; incidence $b \in s$ of base points in group points; the bit relation $\chi_t(n,b) \oplus [b \in s] \oplus [n \in v] = 1$ between row points $(t,n,s)$ and column points $(t,b,v)$ ($\oplus$ is addition mod $2$ and $[P]$ the truth value of $P$); and the graphs of the symmetric-difference actions on group, star, row and column points. An array map $f : M \to N$ (an index injection $f_I$, a base order embedding $f_B$, and finite row shifts $\rho_f(t,n) \subseteq B_N$ and column shifts compatible with the matrices) acts injectively on points and preserves all these relations.
--
--   1. **Typed isomorphisms.** A bijection $\mathrm{Pt}(M) \to \mathrm{Pt}(N)$ that preserves and reflects every relation of $L_{\mathrm{arr}}$ on argument tuples of the correct arity is a raw isomorphism of arrays, i.e. it preserves and reflects the relations on argument lists of every length (lists of the wrong length never satisfy a relation).
--
--   2. **Presentations.** A presentation of a model $R$ in the signature $L_{\mathrm{arr}}$ is an array $M$ with a bijection $e : \mathrm{Pt}(M) \to |R|$ such that for every $n$, every $r \in L_{\mathrm{arr}}(n)$ and every $a : \{0, \dots, n-1\} \to \mathrm{Pt}(M)$,
--   $$
--   r^R(e \circ a) \iff r^M(a).
--   $$
--   A presentation can be transported along an isomorphism $R \cong T$. Two presentations $(M,e)$ and $(M',e')$ of the same $R$ give the raw isomorphism $e'^{-1} \circ e$ from $M$ to $M'$. If $(M,e)$ presents $R$, $(N,e')$ presents $T$, and $f : M \to N$ is an array map that is surjective on points, then $e' \circ f \circ e^{-1}$ is an isomorphism $R \cong T$.
--
--   3. **Inclusions.** For presentations $(M,e)$ of $R$ and $(N,e')$ of $T$, an array map $f : M \to N$ is an inclusion if $e'(f(x)) = e(x)$ as sets for every $x \in \mathrm{Pt}(M)$. In that case $R$ is a substructure of $T$.
--
--   4. **The class $\mathbb{K}$.** Assume CH, i.e. $2^{\aleph_0} = \aleph_1$. The colour of the column $b$ at a tuple $t$ is the class of the sequence $n \mapsto \chi^M_t(n,b)$ modulo finite modifications. A diagram on $\{0, \dots, k\}$ assigns to pairs $(J, m)$, with $J \subseteq \{0, \dots, k\}$ nonempty and $m \in \mathbb{N}$, an equality pattern, a binary relation and tags in $\omega_1$; validity requires, among other things, that tags strictly decrease along the relation and that the relation is extensional. Under CH a fixed injective coding of finite diagrams into colours is available. The column $b$ passes the test at $t$ if there is a single diagram $d$ on $\{0, \dots, k\}$ such that for every increasing subtuple $t \circ \varepsilon$ the restriction $d|_\varepsilon$ is valid and its code is the colour of $b$ at $t \circ \varepsilon$. An array $M$ is an object if for every tuple $t$ all but countably many base points pass the test at $t$. An array map $f : M \to N$ is strong if $f_B[B_M]$ is order-convex in $B_N$ and every base point $b \in B_N \setminus f_B[B_M]$ passes the test at every tuple $t$ from $I_M$, where now the colour at a subtuple $s$ is that of the shifted column $n \mapsto \chi^N_{f_I \circ s}(n,b) \oplus [b \in \rho_f(s,n)]$. Then $R \in \mathbb{K}$ if and only if $R$ has a presentation whose array is an object, and
--   $$
--   R \le_{\mathbb{K}} T \iff \text{there are presentations } (M,e) \text{ of } R,\ (N,e') \text{ of } T \text{ with } M, N \text{ objects, and a strong inclusion } f : M \to N .
--   $$
--   In particular, $R \le_{\mathbb{K}} T$ implies that $R$ is a substructure of $T$.
--
--   5. **Coding arrays as sets.** Every set $X$ is in bijection with the von Neumann ordinal of its cardinality (the initial ordinal of $|X|$, regarded as a ZF set), and an injective map into ZF sets is a bijection onto its range. For an array $M$, a ZF set $A$ and a bijection $e : \mathrm{Pt}(M) \to A$, the model on $A$ whose relations are transported along $e$ is presented by $(M,e)$. Taking for $A$ the initial ordinal of $|\mathrm{Pt}(M)|$ gives the canonical coded model of $M$ with its presentation.
--
--   These definitions put the array constructions into the format of the main theorem: models whose carriers are sets, a signature with countably many symbols, and a class $\mathbb{K}$ with a designated strong-substructure relation. The abstract elementary class axioms, the Löwenheim–Skolem number, the two non-isomorphic models of size $\beth_{\omega_2}$ and the categoricity statements are then proved by working with arrays and array maps.
--
--   **Formalization Note** `Data.rawRel_length` is the arity lemma behind `rawIsoOfTyped` (item 1). `Presentation R` has fields `data`, `equiv`, `relates`; item 2 consists of `transport`, `relates_symm`, `comparison` (with `comparison_onPoint`) and `isoOfMap`, and item 3 of `Inclusion` and `Inclusion.substructure`. `classData hCH : ClassData Language` has fields `objects` and `strong`, built from `Data.IsObject hCH` and `Map.Strong hCH`; `AEC.Object` and `AEC.Strong` abbreviate them and `AEC.substructure` is the last claim of item 4. Item 5 is the namespace `Coding` (`universeEquiv`, `rangeEquiv`, `model`, `presentation`, `coded`, `codedPresentation`); the carrier of `coded M` is `Ordinal.toZFSet (#M.Carrier).ord`. `Language n` is the subtype of array symbols of arity `n`, and a relation of a model is applied to maps `Fin n → carrier`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/AEC.lean

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/AEC.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CHObstruction mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound
import Definitions.Def_OAI_ModelTheory_Categoricity_Arrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayMaps
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayEmbeddings
import Definitions.Def_OAI_ModelTheory_Categoricity_Subarrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayIsomorphisms
import Definitions.Def_OAI_ModelTheory_Categoricity_DirectedLimits

namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace RelModel

variable {L : ℕ → Type} {M N P : RelModel.{u} L}

end RelModel

namespace Arrays

open Tuples

variable {M N : Data.{u}}

theorem Data.rawRel_length (s : Symbol) (xs : List M.Carrier) (h : M.rawRel s xs) :
    xs.length = s.arity := by
  unfold Data.rawRel at h
  split at h <;> simp_all [Symbol.arity]

def rawIsoOfTyped (e : M.Carrier ≃ N.Carrier)
    (he : ∀ n (s : Language n) a, N.rel n s (e ∘ a) ↔ M.rel n s a) : RawIso M N where
  toEquiv := e
  relates s xs := by
    by_cases hl : xs.length = s.arity
    · have h := he xs.length ⟨s, hl.symm⟩ xs.get
      simpa only [Data.rel, List.ofFn_get, ← List.map_ofFn] using h
    · constructor
      · intro h
        exact (hl ((List.length_map (f := e) (as := xs)).symm.trans (N.rawRel_length s _ h))).elim
      · intro h
        exact (hl (M.rawRel_length s xs h)).elim

structure Presentation (R : RelModel.{u} Language) where
  data : Data.{u}
  equiv : data.Carrier ≃ R.carrier
  relates : ∀ n (s : Language n) a, R.rel n s (equiv ∘ a) ↔ data.rel n s a

namespace Presentation

variable {R T V : RelModel.{u} Language} (P : Presentation R)

def transport (e : R.Iso T) : Presentation T where
  data := P.data
  equiv := P.equiv.trans e.toEquiv
  relates n s a := (e.map_rel n s (P.equiv ∘ a)).symm.trans (P.relates n s a)

theorem relates_symm (n : ℕ) (s : Language n) (a : Fin n → R.carrier) :
    R.rel n s a ↔ P.data.rel n s (P.equiv.symm ∘ a) := by
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using P.relates n s (P.equiv.symm ∘ a)

def comparison (Q : Presentation R) : RawIso P.data Q.data :=
  rawIsoOfTyped (P.equiv.trans Q.equiv.symm) (fun n s a => by
    have h := Q.relates_symm n s (P.equiv ∘ a)
    exact h.symm.trans (P.relates n s a))

@[simp] theorem comparison_onPoint (Q : Presentation R) (x : P.data.Carrier) :
    (P.comparison Q).toMap.onPoint x = Q.equiv.symm (P.equiv x) :=
  (P.comparison Q).toMap_onPoint x

def isoOfMap (Q : Presentation T) (f : Map P.data Q.data)
    (hf : Function.Surjective f.onPoint) : R.Iso T where
  toEquiv := P.equiv.symm.trans ((Equiv.ofBijective f.onPoint ⟨f.injective, hf⟩).trans Q.equiv)
  map_rel n s a := by
    have h := (P.relates_symm n s a).trans (f.rel n s (P.equiv.symm ∘ a)).symm
    exact h.trans (Q.relates n s (f.onPoint ∘ P.equiv.symm ∘ a)).symm

def Inclusion (Q : Presentation T) (f : Map P.data Q.data) : Prop :=
  ∀ x, (Q.equiv (f.onPoint x)).val = (P.equiv x).val

theorem Inclusion.substructure {Q : Presentation T} {f : Map P.data Q.data}
    (hf : P.Inclusion Q f) : R.IsSubstructure T := by
  have hsub : R.carrier ⊆ T.carrier := by
    intro x hx
    have he := hf (P.equiv.symm ⟨x, hx⟩)
    simp only [Equiv.apply_symm_apply] at he
    exact he ▸ (Q.equiv (f.onPoint (P.equiv.symm ⟨x, hx⟩))).property
  refine ⟨hsub, fun n s a => ?_⟩
  have he : (fun i => (⟨(a i).val, hsub (a i).property⟩ : T.carrier)) =
      Q.equiv ∘ f.onPoint ∘ P.equiv.symm ∘ a := by
    funext i
    apply Subtype.ext
    change (a i).val = (Q.equiv (f.onPoint (P.equiv.symm (a i)))).val
    simpa only [Equiv.apply_symm_apply] using (hf (P.equiv.symm (a i))).symm
  rw [he, Q.relates, f.rel, ← P.relates_symm]

end Presentation

variable (hCH : CH.{u})

def classData : ClassData.{u} Language where
  objects R := ∃ P : Presentation R, P.data.IsObject hCH
  strong R T := ∃ (P : Presentation R) (Q : Presentation T),
    P.data.IsObject hCH ∧ Q.data.IsObject hCH ∧
    ∃ f : Map P.data Q.data, f.Strong hCH ∧ P.Inclusion Q f

namespace AEC

variable {hCH : CH.{u}} {R T V : RelModel.{u} Language}

abbrev Object (R : RelModel.{u} Language) := (classData hCH).objects R
abbrev Strong (R T : RelModel.{u} Language) := (classData hCH).strong R T

theorem substructure (h : Strong (hCH := hCH) R T) : R.IsSubstructure T := by
  obtain ⟨P, Q, hp, hq, f, hf, he⟩ := h
  exact he.substructure P

end AEC

namespace Coding

variable {X : Type u} {A : ZFSet.{u}}

def universeEquiv (X : Type u) : X ≃ Ordinal.toZFSet (#X).ord := Classical.choice (by
  apply Cardinal.lift_mk_eq'.1
  simp only [ZFSet.cardinalMk_coe_sort, Cardinal.lift_lift, Ordinal.card_toZFSet, Cardinal.card_ord])

def rangeEquiv (f : X → ZFSet.{u}) (hf : Function.Injective f) : X ≃ ZFSet.range f :=
  Equiv.ofBijective (fun x => ⟨f x, ZFSet.mem_range.2 ⟨x, rfl⟩⟩) ⟨
    fun _ _ h => hf (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha⟩ := ZFSet.mem_range.1 hx
      exact ⟨a, Subtype.ext ha⟩⟩

def model (M : Data.{u}) (A : ZFSet.{u}) (e : M.Carrier ≃ A) : RelModel.{u} Language where
  carrier := A
  rel n s a := M.rel n s (e.symm ∘ a)

def presentation (M : Data.{u}) (A : ZFSet.{u}) (e : M.Carrier ≃ A) : Presentation (model M A e) where
  data := M
  equiv := e
  relates n s a := by
    change M.rel n s (fun i => e.symm (e (a i))) ↔ _
    simp only [Equiv.symm_apply_apply]

def coded (M : Data.{u}) : RelModel.{u} Language := model M _ (universeEquiv M.Carrier)

def codedPresentation (M : Data.{u}) : Presentation (coded M) :=
  presentation M _ (universeEquiv M.Carrier)

end Coding

namespace AEC

section

variable {hCH : CH.{u}} {R : RelModel.{u} Language}

end

variable {hCH : CH.{u}}

end AEC
end Arrays

end CHObstruction

end

end OAI


