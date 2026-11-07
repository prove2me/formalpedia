-- Prove2me | Definitions.Def_RandOrderCSP_BasicLPSolves
-- name    : RandOrderCSP_BasicLPSolves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:08:59.388688+00:00
-- url     : https://prove2.me/theorems/33b83729-3d0f-4ee7-98c3-bf843f5818e7
-- title:
--   The basic LP solves $\text{MAX-CSP}_{\beta,\gamma}(\Gamma)$
-- statement:
--   The basic LP **solves** $\text{MAX-CSP}_{\beta,\gamma}(\Gamma)$ if every instance $\Phi$ of $\mathrm{CSP}(\Gamma)$ with $\mathrm{opt}_\Phi<\beta$ has $\mathrm{opt}^{LP}_\Phi<\gamma$. Instances range over all finite vertex sets and all finite nonempty edge sets.
--
--   This is the hypothesis of the upper-bound half of the mission's goal.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §1.2, p.3

import Mathlib
import Definitions.Def_RandOrderCSP_optLP

namespace RandOrderCSP

/-- **"The basic LP solves MAX-CSP_{β,γ}(Γ)"** (§1.2, p.3).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), p.3: "We say that the basic LP (described in
§ 3.3) solves MAX-CSP_{β,γ}(Γ) if for every instance Φ with opt^CSP(Φ) < β, the value of the LP is
less than γ."

**Formalization Note.** "Every instance" ranges over every instance of `CSP(Γ)` with any finite
vertex set and any finite nonempty edge set (p.13: values are normalized by a nonempty edge set). -/
def BasicLPSolves {k : ℕ} {Sig : Type} [Fintype Sig] [DecidableEq Sig]
    (Γ : Set ((Fin k → Sig) → Bool)) (β γ : ℝ) : Prop :=
  ∀ (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [Nonempty E] (Φ : CSP k Sig V E),
    Φ.IsInstanceOf Γ → Φ.opt < β → optLP Φ < γ

end RandOrderCSP


