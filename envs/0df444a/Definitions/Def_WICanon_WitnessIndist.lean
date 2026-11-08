-- Prove2me | Definitions.Def_WICanon_WitnessIndist
-- name    : WICanon_WitnessIndist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:45.499532+00:00
-- url     : https://prove2.me/theorems/eeb3716d-33a2-4269-bfe7-7a9d2d8d2d4a
-- title:
--   Honest-verifier witness indistinguishability, computational and statistical
-- statement:
--   A protocol is **$\delta$-honest-WI** for $\mathcal R$ if for two witnesses $w_0,w_1$ of $x$, no non-uniform PPT distinguisher tells the honest verifier's two views apart:
--
--   $$\bigl|\Pr[D(\mathrm{View}^P_V(x,w_0))=1]-\Pr[D(\mathrm{View}^P_V(x,w_1))=1]\bigr|<\delta(|x|).$$
--
--   It is **$\delta$-honest-SWI** if the two views have statistical distance at most $\delta(|x|)$. With a negligible $\delta$ the parameter is omitted.
--
--   **Formalization Note** Printed, "for every $x$ … and every non-uniform PPT distinguisher"; universal quantifiers commute, so literally $D$ may depend on $x$, and the machine whose finite control holds the optimal test then makes WI equal SWI at every $x$. The reading is the standard asymptotic one: each $D$ is bound from some length on (`HonestWI`). Negligible WI gives each $D$ its own negligible function (`HonestWINegl`), the weakest form of the hypothesis. The distinguisher sees the view and nothing else; its advice and $1^n$ are indexed by the security parameter $n=|x|$.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Definition 2.9, p.14

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QiOPoQ_NUPPT
import Definitions.Def_OWFLocalDesc_Negligible
import Definitions.Def_WICanon_Law
import Definitions.Def_WICanon_IsNPRelation
import Definitions.Def_WICanon_Protocol

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QiOPoQ OWFLocalDesc

/-- `Pr[D(View^P_V(x, w)) = 1]` for a non-uniform PPT distinguisher `D`, with the advice of length
`|x|`. The distinguisher sees the view and nothing else, as printed. -/
noncomputable def distProb (pv : Protocol) (D : NUPPT) (x w : Str) : ℝ :=
  expect (pv.viewLaw x w) (D.acc x.length)

/-- **`δ`-honest-WI** (Arnon, Mazor, Pass, Silbak, STOC 2027 submission manuscript, sha256
3f78ec3d…, Definition 2.9, p.14), with `V̂` the honest verifier.

**Formalization Note.** Printed, "for every x and every w0, w1 … and every non-uniform PPT
distinguisher D: |…| < δ(|x|)". Universal quantifiers commute, so literally `D` may depend on `x`;
a machine whose finite control holds the optimal test for views of that length is non-uniform PPT,
and the literal definition then equals `δ`-SWI at every `x`, so that Lemma 3.10 would have no
content. The reading here is the standard asymptotic one: every machine is bound from some length
on. It is a weaker hypothesis than the literal one. -/
def HonestWI (pv : Protocol) (R : Relation) (δ : ℕ → ℝ) : Prop :=
  ∀ D : NUPPT, ∃ n₀ : ℕ, ∀ x, n₀ ≤ x.length → ∀ w₀ w₁, R x w₀ → R x w₁ →
    |distProb pv D x w₀ - distProb pv D x w₁| < δ x.length

/-- **Honest-verifier WI** with a negligible advantage ("When δ is a negligible function, we
sometimes omit δ", Definition 2.9, p.14): for each distinguisher one negligible function at all
lengths.

**Formalization Note.** `δ` is chosen after `D`: the weakest form of the hypothesis. It is
equivalent to `HonestWI pv R ((n + 2)^{−c})` for all `c`. -/
def HonestWINegl (pv : Protocol) (R : Relation) : Prop :=
  ∀ D : NUPPT, ∃ δ : ℕ → ℝ, Negligible δ ∧ ∀ x w₀ w₁, R x w₀ → R x w₁ →
    |distProb pv D x w₀ - distProb pv D x w₁| ≤ δ x.length

/-- **`δ`-honest-SWI** (Definition 2.9, p.14: "equivalently, the two distributions above have
statistical distance at most δ"), with `V̂` the honest verifier. -/
def HonestSWI (pv : Protocol) (R : Relation) (δ : ℕ → ℝ) : Prop :=
  ∀ x w₀ w₁, R x w₀ → R x w₁ → SD (pv.viewLaw x w₀) (pv.viewLaw x w₁) ≤ δ x.length

end WICanon


