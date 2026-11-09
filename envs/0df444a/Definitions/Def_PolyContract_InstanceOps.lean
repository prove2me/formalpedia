-- Prove2me | Definitions.Def_PolyContract_InstanceOps
-- name    : PolyContract_InstanceOps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:46:42.912735+00:00
-- url     : https://prove2.me/theorems/5eb15f25-a0eb-459c-9401-db773587186e
-- title:
--   Direct sum, dilation $m\mapsto m/\sigma$, and capped linear summand of instances
-- statement:
--   Three operations on instances $(f,m,\beta)$:
--
--   1. The **direct sum** $I_1\oplus I_2$ of instances on disjoint ground sets $E_1,E_2$ has rank function $(f_1\oplus f_2)(S):=f_1(S\cap E_1)+f_2(S\cap E_2)$, rewards $(m_1,m_2)$ and curvatures $(\beta_1,\beta_2)$.
--   2. The **dilation** replaces the rewards $m$ by $m/\sigma$.
--   3. A **capped linear summand** with parameters $C,\alpha_\circ$ adds a new element $e$ as a direct summand with $f(\{e\}):=C$, $m_e:=1$ and $\beta_e:=\alpha_\circ/C$.
--
--   These are the operations by which the reduction combines and rescales combs.
--
--   **Formalization Note** Disjoint ground sets are a sum type; the new element of the capped summand is the extra point of an option type.
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), App. B.2, p.22 (PDF p.23); Lemma B.5

import Mathlib
import Definitions.Def_PolyContract_QuadInstance

set_option autoImplicit false

namespace PolyContract

namespace QuadInstance

/-- The **direct sum** `I₁ ⊕ I₂` of instances `Iᵢ = (fᵢ, mᵢ, βᵢ)` on disjoint ground sets
(Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256 18cfc0a5…, App. B.2,
p.22): rank function `(f₁ ⊕ f₂)(S) := f₁(S ∩ E₁) + f₂(S ∩ E₂)`, rewards `(m₁, m₂)` and
curvatures `(β₁, β₂)`.

**Formalization Note** The disjoint union `E₁ ⊔ E₂` is the sum type `ι₁ ⊕ ι₂`; `S ∩ Eᵢ` is
`Finset.toLeft S` / `Finset.toRight S`. -/
def directSum {ι₁ ι₂ : Type} (I₁ : QuadInstance ι₁) (I₂ : QuadInstance ι₂) :
    QuadInstance (ι₁ ⊕ ι₂) where
  f S := I₁.f S.toLeft + I₂.f S.toRight
  m := Sum.elim I₁.m I₂.m
  β := Sum.elim I₁.β I₂.β

/-- The instance `(f, m/σ, β)`: the rewards divided by `σ` (arXiv:2611.04934, Lemma B.5(b),
p.22; "replacing m by m/σ", Lemma C.4(a), p.51). -/
noncomputable def dilate {ι : Type} (I : QuadInstance ι) (σ : ℝ) : QuadInstance ι where
  f := I.f
  m e := I.m e / σ
  β := I.β

/-- `I` plus a **capped linear summand** (arXiv:2611.04934, Lemma B.5(c), p.22): a new element
`e`, added as a direct summand with `f({e}) := C`, `m_e := 1` and `β_e := α◦ / C`.

**Formalization Note** The new element is `none : Option ι`; the old elements are `some e`. The
rank function is `S ↦ f(S ∩ E) + C·[e ∈ S]`, the direct sum of `f` with the one-element rank
function of value `C`. -/
noncomputable def addCappedLinear {ι : Type} [DecidableEq ι] (I : QuadInstance ι) (C α₀ : ℝ) :
    QuadInstance (Option ι) where
  f S := I.f (Finset.eraseNone S) + if none ∈ S then C else 0
  m o := o.elim 1 I.m
  β o := o.elim (α₀ / C) I.β

end QuadInstance

end PolyContract


