-- Prove2me | Definitions.Def_PolyContract_CutForm
-- name    : PolyContract_CutForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:40:44.275195+00:00
-- url     : https://prove2.me/theorems/12862689-501e-4070-8a72-37cee02619f6
-- title:
--   Cut form $(D,\mathrm{cap},\omega)$ and $f(S)=\mathrm{cut}_D(S)+\omega(S)$
-- statement:
--   A **cut form** on $E$ consists of a loopless digraph $D$ on $E$, capacities $\mathrm{cap}:D\to\mathbb Q_{\ge0}$ and weights $\omega\in\mathbb Q^E$. It defines
--   $$f(S):=\mathrm{cut}_D(S)+\omega(S),\qquad \mathrm{cut}_D(S):=\sum_{(u,v)\in D:\,u\in S,\,v\notin S}\mathrm{cap}(u,v).$$
--
--   The module also defines the total capacity of the arcs entering $e$, and the operations of Lemma C.3(c): replacing $\omega$ by $\omega+y$; adding a new element $b$ as an isolated node of weight $F$; adding a node $b$ with weight $K-d(E)$ and arcs $b\to e$ of capacity $d_e$; and the disjoint union of two cut forms.
--
--   Cut forms are the explicit rank functions of the class $\mathcal C_{\mathrm{cut}}$ on which Theorem 4.1 is stated.
--
--   **Formalization Note** The digraph with its capacities is a list of triples $(u,v,\mathrm{cap}(u,v))$. A cut form is **valid** when every arc has $u\ne v$ and nonnegative capacity and the pairs $(u,v)$ are pairwise distinct. New elements are the extra point of an option type.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Definition C.2, p.49 (PDF p.50), (C.1); Lemma C.3(c), pp.49–50

import Mathlib

set_option autoImplicit false

namespace PolyContract

/-- A **cut form** on `E` (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026,
sha256 18cfc0a5…, Definition C.2, p.49): a digraph `D` on `E` with capacities
`cap : D → ℚ` and weights `ω ∈ ℚ^E`. The conditions that `D` is loopless and that the capacities
are nonnegative are `CutForm.IsValid`.

**Formalization Note** The ground set `E` is the type `ι`. The digraph with its capacities is the
list `arcs` of triples `(u, v, cap(u, v))`; `IsValid` requires the pairs `(u, v)` to be pairwise
distinct, so the list is a set of arcs. Two lists that differ only in order describe the same
cut form and define the same function. -/
structure CutForm (ι : Type) where
  /-- The arcs `(u, v)` with their capacities `cap(u, v)`. -/
  arcs : List (ι × ι × ℚ)
  /-- The weights `ω_e`. -/
  ω : ι → ℚ

namespace CutForm

variable {ι : Type}

/-- The cut form is well formed (arXiv:2611.04934, Definition C.2, p.49): the digraph is
loopless (`u ≠ v` for every arc), its arcs are pairwise distinct, and the capacities are
nonnegative, `cap : D → ℚ_{≥0}`. -/
def IsValid (cf : CutForm ι) : Prop :=
  (∀ a ∈ cf.arcs, a.1 ≠ a.2.1 ∧ 0 ≤ a.2.2) ∧ (cf.arcs.map fun a => (a.1, a.2.1)).Nodup

variable [DecidableEq ι]

/-- `cut_D(S) := Σ_{(u,v) ∈ D : u ∈ S, v ∉ S} cap(u, v)` (arXiv:2611.04934, (C.1), p.49). -/
def cutD (cf : CutForm ι) (S : Finset ι) : ℚ :=
  ((cf.arcs.filter fun a => decide (a.1 ∈ S ∧ a.2.1 ∉ S)).map fun a => a.2.2).sum

/-- The function defined by the cut form, `f(S) := cut_D(S) + ω(S)` (arXiv:2611.04934, (C.1),
p.49). -/
def cutFn (cf : CutForm ι) (S : Finset ι) : ℚ := cf.cutD S + ∑ e ∈ S, cf.ω e

/-- The total capacity of the arcs of `D` that enter `e` (arXiv:2611.04934, Lemma C.3(b), p.49). -/
def inCap (cf : CutForm ι) (e : ι) : ℚ :=
  ((cf.arcs.filter fun a => decide (a.2.1 = e)).map fun a => a.2.2).sum

/-- Lemma C.3(c)(i) (arXiv:2611.04934, p.49): the cut form of `g + y`, obtained by replacing `ω`
by `ω + y`. -/
def addModular (cf : CutForm ι) (y : ι → ℚ) : CutForm ι where
  arcs := cf.arcs
  ω e := cf.ω e + y e

/-- Lemma C.3(c)(ii) (arXiv:2611.04934, p.50): the direct sum with a modular singleton `π_F` on a
new element `b`, obtained by adding `b` as an isolated node of weight `F`.

**Formalization Note** The new element `b` is `none : Option ι`. -/
def addIsolated (cf : CutForm ι) (F : ℚ) : CutForm (Option ι) where
  arcs := cf.arcs.map fun a => (some a.1, some a.2.1, a.2.2)
  ω o := o.elim F cf.ω

/-- Lemma C.3(c)(iii) (arXiv:2611.04934, p.50): the one-element extension, obtained by adding the
node `b` with weight `K − d(E)` and the arcs `b → e` of capacity `d_e` for `e ∈ E`.

**Formalization Note** The new element `b` is `none : Option ι`. The new arcs are listed in the
order of `Finset.univ.toList`; the order of a cut form's arc list does not affect its function. -/
noncomputable def oneElementExt [Fintype ι] (cf : CutForm ι) (K : ℚ) (d : ι → ℚ) :
    CutForm (Option ι) where
  arcs := cf.arcs.map (fun a => (some a.1, some a.2.1, a.2.2)) ++
    (Finset.univ.toList.map fun e => (none, some e, d e))
  ω o := o.elim (K - ∑ e, d e) cf.ω

/-- The disjoint union of two cut forms (arXiv:2611.04934, Lemma C.3, last sentence, p.50), a cut
form on `E₁ ⊔ E₂ = ι₁ ⊕ ι₂`. -/
def disjointUnion {ι₂ : Type} (cf₁ : CutForm ι) (cf₂ : CutForm ι₂) : CutForm (ι ⊕ ι₂) where
  arcs := cf₁.arcs.map (fun a => (Sum.inl a.1, Sum.inl a.2.1, a.2.2)) ++
    cf₂.arcs.map (fun a => (Sum.inr a.1, Sum.inr a.2.1, a.2.2))
  ω := Sum.elim cf₁.ω cf₂.ω

end CutForm

end PolyContract


