-- Prove2me | Definitions.Def_UltimateL_Extendible
-- name    : UltimateL_Extendible
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T21:22:54.2833+00:00
-- url     : https://prove2.me/theorems/ae5c4ea6-58bd-42f6-9189-28fcefc67b34
-- title:
--   Extendible cardinals (Woodin, Definition 3.11)
-- statement:
--   A cardinal $\delta$ is **extendible** if for every ordinal $\lambda>\delta$ there is an elementary embedding $\pi:V_{\lambda+1}\to V_{\pi(\lambda)+1}$ whose critical point is $\delta$ (it fixes every ordinal below $\delta$ and moves $\delta$) and such that $\pi(\delta)>\lambda$. This is Woodin's Definition 3.11. The embedding is presented as a function on the ambient universe of sets that maps the rank segment $V_{\lambda+1}$ into $V_{\pi(\lambda)+1}$ and preserves the truth of every first-order formula of set theory on assignments drawn from $V_{\lambda+1}$; the target segment is indexed by $\mu=\pi(\lambda)$. Extendible cardinals are the large-cardinal hypothesis of the Ultimate-$L$ conjecture.
-- source:
--   W. Hugh Woodin, In Search of Ultimate-L, BSL 23(1) (2017) 1-109, doi:10.1017/bsl.2016.34, Definition 3.11 (extendible cardinal), p. 10.

import Mathlib
import Definitions.Def_UltimateL_VHierarchy
import Definitions.Def_OmegaLogic_Semantics

namespace UltimateL

universe u

open ZFSet OmegaLogic

/-- `δ` is an extendible cardinal (Woodin, Definition 3.11): for every `η > δ` there is an
elementary embedding `π : V_{η+1} → V_{π(η)+1}` with critical point `δ` and `π(δ) > η`.
The embedding is represented by a function on the ambient sets that carries `V_{η+1}` into
`V_{π(η)+1}` and preserves every first-order formula on assignments from `V_{η+1}`. -/
def IsExtendible (δ : Ordinal.{u}) : Prop :=
  ∀ η > δ, ∃ (μ : Ordinal.{u}) (π : ZFSet.{u} → ZFSet.{u}),
    (∀ x ∈ vLevel (η + 1), π x ∈ vLevel (μ + 1)) ∧
    π η.toZFSet = μ.toZFSet ∧
    (∀ β < δ, π β.toZFSet = β.toZFSet) ∧
    (∃ ν, η < ν ∧ π δ.toZFSet = ν.toZFSet) ∧
    ∀ (k : ℕ) (φ : setLang.Formula (Fin k))
      (a : Fin k → (vLevel (η + 1) : Set ZFSet.{u}))
      (b : Fin k → (vLevel (μ + 1) : Set ZFSet.{u})),
      (∀ i, (b i).1 = π (a i).1) → (φ.Realize a ↔ φ.Realize b)

end UltimateL


