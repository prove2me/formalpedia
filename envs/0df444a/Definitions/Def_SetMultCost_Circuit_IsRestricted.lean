-- Prove2me | Definitions.Def_SetMultCost_Circuit_IsRestricted
-- name    : SetMultCost_Circuit_IsRestricted
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:56.753641+00:00
-- url     : https://prove2.me/theorems/d0f5e14f-f5d7-4ef5-9994-5870b1e28029
-- title:
--   $\mathbf r$-restricted circuits, and the sequence $(c,\infty,c,\infty,\dots)$
-- statement:
--   Let $\mathbf r=(r_1,r_2,\dots)$ with $r_i\in\mathbb N\cup\{\infty\}$. A circuit of product-depth at most $D$ is **$\mathbf r$-restricted** when some height function bounded by $D$ gives every multiplication gate of height $i$ fan-in at most $r_i$.
--
--   The sequence $(c,\infty,c,\infty,\dots)$ takes the value $c$ at odd heights, counted from the bottom, and $\infty$ at even heights. Over characteristic $p$ with $c=p$ it is the shape produced by set-multilinearization.
--
--   **Formalization Note** The paper states this for formulas and uses it for circuits (Lemma 4.2, proof of Theorem 1.2). It does not define product-height outside layered circuits, so the height function is existentially quantified.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Definition 3.4, p.12

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SetMultCost_Circuit_HasProductDepthLE

namespace SetMultCost

namespace Circuit

variable {σ F : Type*}

/-- **`r`-restricted of product-depth at most `D`.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), Definition 3.4, p.12: "we shall say
that a formula Φ of product-depth ∆ is r-restricted if all product gates at product-height i has
its fanin at most ri."

**Formalization Note.** Stated for circuits, as Lemma 4.2 and the proof of Theorem 1.2 use it. The
paper does not define product-height outside layered circuits: here some height function bounded by
`D` witnesses the fan-in bounds. `r i` is read at heights `1, …, D` and takes values in `ℕ∞`. -/
def IsRestricted (Φ : Circuit σ F) (D : ℕ) (r : ℕ → ℕ∞) : Prop :=
  ∃ h : Fin Φ.numNodes → ℕ, Φ.IsHeightFn h ∧ (∀ v, h v ≤ D) ∧
    ∀ v cs, Φ.gate v = .mul cs → (cs.length : ℕ∞) ≤ r (h v)

end Circuit

/-- The restriction sequence `(c, ∞, c, ∞, …)` of Theorem 3.5 and Lemma 7.3 (pp.12, 23): `c` at odd
heights, counted from the bottom, and `∞` at even heights. -/
noncomputable def altRestriction (c : ℕ) : ℕ → ℕ∞ := fun i => if Odd i then (c : ℕ∞) else ⊤

end SetMultCost


