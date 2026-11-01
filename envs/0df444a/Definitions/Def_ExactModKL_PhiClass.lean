-- Prove2me | Definitions.Def_ExactModKL_PhiClass
-- name    : ExactModKL_PhiClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:55:50.647513+00:00
-- url     : https://prove2.me/theorems/0fae5ac0-0f62-4a30-8673-73b9c59975a4
-- title:
--   The class $\Phi_\eta$ of desingularizing functions
-- statement:
--   For $\eta\in(0,\infty]$, $\Phi_\eta$ is the class of functions $\varphi:[0,\eta)\to\mathbb R_+$ such that
--
--   1. $\varphi$ is right-continuous at $t=0$ and $\varphi(0)=0$;
--   2. $\varphi$ is strictly increasing on $[0,\eta)$.
--
--   Concave members of $\Phi_\eta$ are the candidate desingularizing functions of the generalized concave Kurdyka–Łojasiewicz property. Unlike the classical class, no differentiability is required.
--
--   **Formalization Note** $\varphi$ is a function $\mathbb R\to\mathbb R$ of which only the values on $[0,\eta)$ matter; the codomain $\mathbb R_+$ is the condition $\varphi\ge0$ on $[0,\eta)$. Concavity is not part of the class and is assumed separately where the paper says "concave $\varphi\in\Phi_\eta$".
-- source:
--   Wang–Wang, arXiv:2008.13257v5, §3.1, p.8

import Mathlib
import Definitions.Def_ExactModKL_Ieta

open scoped ENNReal

namespace ExactModKL

/-- The class `Φ_η` (Wang–Wang, arXiv:2008.13257v5 (preprint), §3.1, p.8): for `η ∈ (0, ∞]`,
the functions `ϕ : [0, η) → ℝ₊` that are (i) right-continuous at `t = 0` with `ϕ(0) = 0`, and
(ii) strictly increasing on `[0, η)`.

**Formalization Note.** `ϕ : ℝ → ℝ`; only its values on `[0, η)` (`Ieta η`) matter. The
codomain `ℝ₊` is the clause `0 ≤ ϕ t` on `[0, η)`. Right-continuity at `0` is continuity within
`[0, ∞)` at `0`. Concavity is not part of `Φ_η`; the paper writes "concave `ϕ ∈ Φ_η`" and the
theorems carry `ConcaveOn ℝ (Ieta η) ϕ` separately. -/
def PhiClass (η : ℝ≥0∞) (ϕ : ℝ → ℝ) : Prop :=
  (∀ t ∈ Ieta η, 0 ≤ ϕ t) ∧ ϕ 0 = 0 ∧ ContinuousWithinAt ϕ (Set.Ici 0) 0 ∧
    StrictMonoOn ϕ (Ieta η)

end ExactModKL


