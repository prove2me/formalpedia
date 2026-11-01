-- Prove2me | Definitions.Def_DRORSEquiv_tauBar
-- name    : DRORSEquiv_tauBar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:25.373513+00:00
-- url     : https://prove2.me/theorems/91c4de42-8c34-40f5-88f4-3529336f7efc
-- title:
--   Robust optimum $\bar\tau=\inf_{x}\sup_{z}f(x,z)$
-- statement:
--   The **robust optimum** is
--
--   $$\bar\tau=\inf_{x\in\mathcal X}\ \sup_{z\in\mathcal Z} f(x,z),$$
--
--   the optimal value of classical robust optimization over the whole support. Theorem 1 concerns targets $\tau\in[Z_0,\bar\tau]$ and assumes $\bar\tau$ finite.
--
--   **Formalization Note** Computed in `EReal`; theorems assume $\bar\tau=t$ for a real $t$.
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), §3, p.8 (sentence before Theorem 1)

import Mathlib
import Definitions.Def_DRORSEquiv_Model

namespace DRORSEquiv

/-- **The robust optimum** `τ̄ = inf_{x ∈ X} sup_{z ∈ Z} f(x, z)` (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), §3, p.8, the
sentence before Theorem 1: "Suppose τ̄ := inf_{x∈X} sup_{z∈Z} f(x,z) is finite").

**Formalization Note.** Computed in `EReal`; its finiteness is a hypothesis of the statements that
use it (`M.tauBar = (t : EReal)` with `t : ℝ`). -/
noncomputable def tauBar {E Ω : Type*} {S : ℕ} (M : Model E Ω S) : EReal :=
  ⨅ x ∈ M.X, ⨆ z ∈ M.Z, (M.f x z : EReal)

end DRORSEquiv


