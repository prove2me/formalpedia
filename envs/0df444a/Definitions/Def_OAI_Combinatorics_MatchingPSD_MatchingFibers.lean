-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
-- name    : OAI_Combinatorics_MatchingPSD_MatchingFibers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:53:26.4285+00:00
-- url     : https://prove2.me/theorems/db176b15-cb7e-4919-b782-a087f81a52e8
-- title:
--   Transport, disjoint sums and cellwise products of pairings, and the fibre bijection for split pairings
-- statement:
--   This file provides the basic operations for relabelling and gluing perfect matchings, and the bijection that splits a matching which does not mix two parts of the vertex set.
--
--   **Pairings and table coordinates.** A *pairing* of a set $X$ is a permutation $M$ of $X$ with $M(M(a))=a$ and $M(a)\neq a$ for every $a\in X$, that is, a perfect matching of $X$ in which every $a$ is matched to its partner $M(a)$. For a finite set $V$, a colouring $z:V\to K$, a pair of colours $c=(c_1,c_2)\in K\times K$ and a pairing $M$ of $V$, the *table coordinate* is
--   $$
--   T_c(z,M)=\#\{v\in V:\ z(v)=c_1\ \text{and}\ z(M(v))=c_2\},
--   $$
--   the number of vertices of colour $c_1$ whose partner has colour $c_2$.
--
--   1. **Transport.** For a bijection $e:A\to B$ and a pairing $M$ of $A$, the transported pairing of $B$ is $e_*M=e\circ M\circ e^{-1}$, so $(e_*M)(b)=e\bigl(M(e^{-1}(b))\bigr)$. It satisfies $(\mathrm{id}_A)_*M=M$, $(f\circ e)_*M=f_*(e_*M)$ and $(e^{-1})_*(e_*M)=M$, and $M\mapsto e_*M$ is a bijection from the pairings of $A$ onto the pairings of $B$.
--   2. **Disjoint sum.** For a pairing $M$ of $A$ and a pairing $N$ of $B$, $M\oplus N$ is the pairing of the disjoint union $A\sqcup B$ that acts as $M$ on $A$ and as $N$ on $B$.
--   3. **Cellwise pairing.** For a family $(M_i)_{i\in I}$ of pairings of $A$, the cellwise pairing of $I\times A$ is $(i,a)\mapsto(i,M_i(a))$: every cell $\{i\}\times A$ is matched internally by $M_i$.
--   4. **Table coordinates of sums and of constant colourings.** Let $A,B$ be finite, $z:A\to K$, $w:B\to K$, and let $z\sqcup w$ be the colouring of $A\sqcup B$ restricting to $z$ and $w$. Then $T_c(z\sqcup w,M\oplus N)=T_c(z,M)+T_c(w,N)$. Moreover $T_c(z,M)=0$ if and only if no $a\in A$ has $z(a)=c_1$ and $z(M(a))=c_2$; and for a constant colouring $z\equiv\gamma$ one has $T_c(z,M)=|A|$ if $\gamma=c_1$ and $\gamma=c_2$, and $T_c(z,M)=0$ otherwise.
--   5. **Splitting.** The map $(L,R)\mapsto L\oplus R$ from pairs (pairing of $A$, pairing of $B$) to pairings of $A\sqcup B$ is injective, and every pairing of $A\sqcup B$ that maps each element of $A$ into $A$ is of the form $L\oplus R$.
--   6. **Fibre bijection.** Let $\mathcal P$ be a property of pairings of $A\sqcup B$ and $\mathcal Q$ a property of pairings of $A$ such that $\mathcal P(L\oplus R)\Leftrightarrow\mathcal Q(L)$ for all pairings $L$ of $A$ and $R$ of $B$, and such that every pairing satisfying $\mathcal P$ maps each element of $A$ into $A$. Then $(L,R)\mapsto L\oplus R$ is a bijection
--   $$
--   \{L\ \text{pairing of}\ A:\ \mathcal Q(L)\}\times\{R\ \text{pairing of}\ B\}\ \longrightarrow\ \{M\ \text{pairing of}\ A\sqcup B:\ \mathcal P(M)\}.
--   $$
--
--   These operations build matchings of a large vertex set out of matchings of its blocks. The fibre bijection identifies a set of matchings cut out by a local condition with a product of smaller sets of matchings, which is what makes uniform averages over such sets factor into averages over the separate blocks.
--
--   **Formalization Note** `Pairing α` is the subtype of `Equiv.Perm α` consisting of involutions without fixed points. The constructions are `Pairing.transport`, `Pairing.transportEquiv`, `Pairing.sum`, `Pairing.cellwise` and the noncomputable `Pairing.sumFiberEquiv` (built with `Equiv.ofBijective`); they need no finiteness, whereas the table-coordinate lemmas `tableCoordinate_sum`, `tableCoordinate_eq_zero_iff` and `tableCoordinate_constant` assume `Fintype` vertex types. `tableCoordinate z c M` is real-valued (a sum of indicator values). The remaining members (`transport_apply`, `sum_inl`, `sum_inr`, `cellwise_apply`, …) are the defining simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/MatchingFibers.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/MatchingFibers.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingPSD mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
namespace Pairing
variable {A : Type u_1} {B : Type u_2} {C : Type u_3}

def transport (e : A ≃ B) (M : Pairing A) : Pairing B :=
  ⟨e.symm.trans (M.1.trans e), by
    constructor
    · intro b
      simp
    · intro b hb
      apply M.partner_ne (e.symm b)
      simpa using congrArg e.symm hb⟩

@[simp] lemma transport_apply (e : A ≃ B) (M : Pairing A) (b : B) :
    (transport e M).1 b = e (M.1 (e.symm b)) := rfl

@[simp] lemma transport_refl (M : Pairing A) : transport (Equiv.refl A) M = M := by
  ext a
  rfl

@[simp] lemma transport_trans (e : A ≃ B) (f : B ≃ C) (M : Pairing A) :
    transport (e.trans f) M = transport f (transport e M) := by
  ext c
  rfl

@[simp] lemma transport_symm (e : A ≃ B) (M : Pairing A) :
    transport e.symm (transport e M) = M := by
  ext a
  simp

def transportEquiv (e : A ≃ B) : Pairing A ≃ Pairing B where
  toFun := transport e
  invFun := transport e.symm
  left_inv := transport_symm e
  right_inv := transport_symm e.symm

def sum (M : Pairing A) (N : Pairing B) : Pairing (A ⊕ B) :=
  ⟨Equiv.sumCongr M.1 N.1, by
    constructor
    · intro v
      cases v <;> simp
    · intro v hv
      cases v with
      | inl a => exact M.partner_ne a (Sum.inl.inj hv)
      | inr b => exact N.partner_ne b (Sum.inr.inj hv)⟩

@[simp] lemma sum_inl (M : Pairing A) (N : Pairing B) (a : A) :
    (sum M N).1 (.inl a) = .inl (M.1 a) := rfl
@[simp] lemma sum_inr (M : Pairing A) (N : Pairing B) (b : B) :
    (sum M N).1 (.inr b) = .inr (N.1 b) := rfl

def cellwise {I : Type u_4} (M : I → Pairing A) : Pairing (I × A) :=
  ⟨{ toFun := fun v => (v.1,(M v.1).1 v.2)
     invFun := fun v => (v.1,(M v.1).1 v.2)
     left_inv := by intro v; simp
     right_inv := by intro v; simp }, by
    constructor
    · intro v; simp
    · intro v hv
      exact (M v.1).partner_ne v.2 (congrArg Prod.snd hv)⟩

@[simp] lemma cellwise_apply {I : Type u_5} (M : I → Pairing A) (i : I) (a : A) :
    (cellwise M).1 (i,a) = (i,(M i).1 a) := rfl

end Pairing

section Coordinates
variable {A : Type u_6} {B : Type u_7} {C : Type u_8} [Fintype A] [Fintype B]
attribute [local instance] Classical.propDecidable

lemma tableCoordinate_sum (z : A → C) (w : B → C) (c : C × C)
    (M : Pairing A) (N : Pairing B) :
    tableCoordinate (Sum.elim z w) c (Pairing.sum M N) =
      tableCoordinate z c M + tableCoordinate w c N := by
  simp only [tableCoordinate, Fintype.sum_sum_type, Pairing.sum_inl, Pairing.sum_inr,
    Sum.elim_inl, Sum.elim_inr]
  rfl

lemma tableCoordinate_eq_zero_iff (z : A → C) (c : C × C) (M : Pairing A) :
    tableCoordinate z c M = 0 ↔ ∀ a, ¬ (z a = c.1 ∧ z (M.1 a) = c.2) := by
  unfold tableCoordinate
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by split_ifs <;> norm_num)]
  simp

lemma tableCoordinate_constant (z : C) (c : C × C) (M : Pairing A) :
    tableCoordinate (fun _ : A => z) c M =
      if z=c.1 ∧ z=c.2 then (Fintype.card A : ℝ) else 0 := by
  simp only [tableCoordinate]
  split_ifs <;> simp_all

end Coordinates
end MatchingSmoothing

namespace MatchingSmoothing.Pairing
variable {A : Type u_9} {B : Type u_10}

lemma sum_injective : Function.Injective (fun p : Pairing A × Pairing B => sum p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · ext a
    exact Sum.inl.inj (congrArg (fun M : Pairing (A ⊕ B) => M.1 (.inl a)) hpq)
  · ext b
    exact Sum.inr.inj (congrArg (fun M : Pairing (A ⊕ B) => M.1 (.inr b)) hpq)

lemma exists_sum (M : Pairing (A ⊕ B))
    (hl : ∀ a : A, ∃ a' : A, M.1 (.inl a) = .inl a') :
    ∃ L : Pairing A, ∃ R : Pairing B, M = sum L R := by
  classical
  have hr (b : B) : ∃ b' : B, M.1 (.inr b) = .inr b' := by
    cases he : M.1 (.inr b) with
    | inl a =>
      obtain ⟨a',ha⟩ := hl a
      have hh := M.partner_partner (.inr b)
      rw [he, ha] at hh
      cases hh
    | inr b' => exact ⟨b',rfl⟩
  choose f hf using hl
  choose g hg using hr
  have hff : Function.Involutive f := by
    intro a
    apply Sum.inl_injective (β := B)
    rw [← hf, ← hf, M.partner_partner]
  have hgg : Function.Involutive g := by
    intro b
    apply Sum.inr_injective (α := A)
    rw [← hg, ← hg, M.partner_partner]
  let L : Pairing A := ⟨⟨f,f,hff,hff⟩,hff,fun a ha =>
    M.partner_ne (.inl a) ((hf a).trans (congrArg Sum.inl ha))⟩
  let R : Pairing B := ⟨⟨g,g,hgg,hgg⟩,hgg,fun b hb =>
    M.partner_ne (.inr b) ((hg b).trans (congrArg Sum.inr hb))⟩
  refine ⟨L,R,?_⟩
  ext v
  cases v with
  | inl a => exact hf a
  | inr b => exact hg b

noncomputable def sumFiberEquiv (P : Pairing (A ⊕ B) → Prop) (Q : Pairing A → Prop)
    (hs : ∀ L R, P (sum L R) ↔ Q L)
    (hc : ∀ M, P M → ∀ a : A, ∃ a' : A, M.1 (.inl a) = .inl a') :
    {L : Pairing A // Q L} × Pairing B ≃ {M : Pairing (A ⊕ B) // P M} :=
  Equiv.ofBijective (fun p => ⟨sum p.1.1 p.2, (hs _ _).mpr p.1.2⟩) (by
    constructor
    · intro p q he
      have hh : (p.1.1,p.2) = (q.1.1,q.2) :=
        sum_injective (congrArg Subtype.val he)
      apply Prod.ext
      · exact Subtype.ext (congrArg (fun x : Pairing A × Pairing B => x.1) hh)
      · exact congrArg (fun x : Pairing A × Pairing B => x.2) hh
    · intro M
      obtain ⟨L,R,hM⟩ := exists_sum M.1 (hc M.1 M.2)
      refine ⟨(⟨L,(hs L R).mp (hM ▸ M.2)⟩,R),?_⟩
      exact Subtype.ext hM.symm)

end MatchingSmoothing.Pairing

end OAI


