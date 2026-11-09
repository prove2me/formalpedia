-- Prove2me | Definitions.Def_PolyContract_CcutInstance
-- name    : PolyContract_CcutInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:47:17.23522+00:00
-- url     : https://prove2.me/theorems/841320e9-aa1a-4c9b-8c60-392ea7986084
-- title:
--   Instances of $\mathcal C_{\mathrm{cut}}$
-- statement:
--   An instance of $\mathcal C_{\mathrm{cut}}$ is an instance $(f,m,\beta)$ with $m,\beta\in\mathbb Q^E_{>0}$ for which $f$ is a rank function given by a cut form $(D,\mathrm{cap},\omega)$, $f(S)=\mathrm{cut}_D(S)+\omega(S)$. Its data are the cut form, $m$ and $\beta$.
--
--   The module defines the instance over $\mathbb R$ given by such data, the membership predicate (nonempty ground set, valid cut form, positive rewards and curvatures, rank function), and the operations used by the reduction: renaming elements, direct sums with the disjoint union of the cut forms, scaling the rewards, and adding a capped linear summand whose cut form is an isolated node of weight $C$.
--
--   **Formalization Note** The data are kept separate from the membership predicate so that codes of arbitrary data can be formed; only members are accepted by the language of Theorem 4.1.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Definition C.2, p.49 (PDF p.50); App. B.2, p.22; Lemma C.3, p.50

import Mathlib
import Definitions.Def_PolyContract_QuadInstance
import Definitions.Def_PolyContract_CutForm

set_option autoImplicit false

namespace PolyContract

/-- The data of an instance of `C_cut` (Klimm, Lippke, Warode, arXiv:2611.04934, version of
November 3, 2026, sha256 18cfc0a5…, Definition C.2, p.49): a cut form `(D, cap, ω)` on `E` and
rational rewards and curvatures `m, β ∈ ℚ^E`. The rank function is the function of the cut form,
`f(S) = cut_D(S) + ω(S)`. Membership in `C_cut` is the predicate `CcutInstance.InCcut`.

**Formalization Note** The ground set `E` is the type `ι`; the decision problem of Theorem 4.1
uses `ι = Fin n`. -/
structure CcutInstance (ι : Type) where
  /-- The cut form `(D, cap, ω)` defining the rank function. -/
  cf : CutForm ι
  /-- The rewards `m_e`. -/
  m : ι → ℚ
  /-- The curvatures `β_e`. -/
  β : ι → ℚ

namespace CcutInstance

variable {ι : Type}

/-- The instance `(f, m, β)` over `ℝ` defined by the data: `f(S) = cut_D(S) + ω(S)` and the
rewards and curvatures cast to `ℝ` (arXiv:2611.04934, Definition C.2, p.49). -/
def toQuad [DecidableEq ι] (D : CcutInstance ι) : QuadInstance ι where
  f S := (D.cf.cutFn S : ℝ)
  m e := (D.m e : ℝ)
  β e := (D.β e : ℝ)

/-- Membership in **`C_cut`** (arXiv:2611.04934, Definition C.2, p.49, with §2, p.5): the ground
set is nonempty, the cut form is valid (loopless digraph, distinct arcs, `cap ≥ 0`),
`m, β ∈ ℚ^E_{>0}`, and the function `f` given by the cut form is a rank function. -/
def InCcut [Fintype ι] [DecidableEq ι] (D : CcutInstance ι) : Prop :=
  Nonempty ι ∧ D.cf.IsValid ∧ (∀ e, 0 < D.m e) ∧ (∀ e, 0 < D.β e) ∧ IsRankFunction D.toQuad.f

/-- Renaming the elements along a bijection `ι ≃ κ`. -/
def relabel {κ : Type} (σ : ι ≃ κ) (D : CcutInstance ι) : CcutInstance κ where
  cf := ⟨D.cf.arcs.map fun a => (σ a.1, σ a.2.1, a.2.2), fun k => D.cf.ω (σ.symm k)⟩
  m k := D.m (σ.symm k)
  β k := D.β (σ.symm k)

/-- The direct sum `I₁ ⊕ I₂` of two `C_cut` instances on disjoint ground sets
(arXiv:2611.04934, App. B.2, p.22), with the disjoint union of the two cut forms as its cut form
(Lemma C.3, last sentence, p.50). -/
def directSum {ι₂ : Type} (D₁ : CcutInstance ι) (D₂ : CcutInstance ι₂) :
    CcutInstance (ι ⊕ ι₂) where
  cf := D₁.cf.disjointUnion D₂.cf
  m := Sum.elim D₁.m D₂.m
  β := Sum.elim D₁.β D₂.β

/-- The instance with the rewards `m` replaced by `s·m` (used with `s = δ₂/δ₁` and `s = 1/σ` in
Definition C.8, arXiv:2611.04934, p.53). -/
def scaleReward (D : CcutInstance ι) (s : ℚ) : CcutInstance ι where
  cf := D.cf
  m e := s * D.m e
  β := D.β

/-- The instance plus a capped linear summand (arXiv:2611.04934, Lemma B.5(c), p.22): a new
element `e` with `f({e}) := C`, `m_e := 1` and `β_e := α◦ / C`, whose cut form is the given one
with `e` added as an isolated node of weight `C` (Lemma C.3(c)(ii), p.50).

**Formalization Note** The new element is `none : Option ι`. -/
def addCapped (D : CcutInstance ι) (C α₀ : ℚ) : CcutInstance (Option ι) where
  cf := D.cf.addIsolated C
  m o := o.elim 1 D.m
  β o := o.elim (α₀ / C) D.β

end CcutInstance

end PolyContract


