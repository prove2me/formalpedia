-- Prove2me | Definitions.Def_FOMCMonDep_gaifman
-- name    : FOMCMonDep_gaifman
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:12.459368+00:00
-- url     : https://prove2.me/theorems/5dfda230-968b-4155-bb2b-e2ee0651532f
-- title:
--   The Gaifman graph of a structure and induced substructures
-- statement:
--   For a relational structure $A$, the **Gaifman graph** has the elements of $A$ as vertices, and two distinct elements are adjacent iff they occur together in some tuple of some relation of $A$; for unary and binary relations, these are the pairs $uv$ with $(u,v)$ or $(v,u)$ in a binary relation. $\mathrm{dist}^A$ and $\mathrm{Ball}^A_r$ are taken in the Gaifman graph. For a set $B$ of elements, the **induced substructure** $A[B]$ has domain $B$ and the relations of $A$ restricted to tuples from $B$.
--
--   These are the objects of the locality statement Lemma 4.9.
--
--   **Formalization Note** The signature is assumed relational (no function symbols).
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §3, p.12 (PDF 14); App. B, p.60 (PDF 62)

import Mathlib

set_option autoImplicit false

open FirstOrder FirstOrder.Language

namespace FOMCMonDep

/-- **The Gaifman graph of a structure.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.12 (PDF 14): "For a structure A with
domain V equipped with unary and binary relations, the Gaifman graph of A is the graph with vertex set V and edge set
consisting of all pairs uv such that (u, v) or (v, u) is in some binary relation of A." App. B, p.60 (PDF 62), for a
signature of arity `α`: "adj_σ tests for every relation R ∈ σ of arity β with 2 ⩽ β ⩽ α, whether x1 ≠ x2 and there
exist elements x3, . . . , xβ such that some permutation of x1, . . . , xβ satisfies R."

**Formalization Note.** Distinct `u, v` are adjacent iff both occur in one tuple of some relation; for unary and
binary relations this is the definition of §3. -/
def gaifman {L : Language} {M : Type*} (S : L.Structure M) : SimpleGraph M where
  Adj u v := u ≠ v ∧ ∃ (l : ℕ) (R : L.Relations l) (xs : Fin l → M),
    @Structure.RelMap L M S l R xs ∧ u ∈ Set.range xs ∧ v ∈ Set.range xs
  symm := ⟨fun _ _ ⟨h, l, R, xs, hR, hu, hv⟩ => ⟨Ne.symm h, l, R, xs, hR, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- **The induced substructure `A[B]`** of a relational structure on a set `B` of elements (App. B, p.60: "since A[B]
is an induced substructure of A"): every relation of `A` restricted to tuples from `B`. -/
@[instance_reducible]
def inducedStructure {L : Language} [L.IsRelational] {M : Type*} (S : L.Structure M) (B : Set M) :
    L.Structure B where
  funMap := fun f _ => isEmptyElim f
  RelMap := fun R xs => @Structure.RelMap L M S _ R (fun i => (xs i : M))

end FOMCMonDep


