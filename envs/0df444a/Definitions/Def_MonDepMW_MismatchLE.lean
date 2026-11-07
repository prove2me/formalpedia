-- Prove2me | Definitions.Def_MonDepMW_MismatchLE
-- name    : MonDepMW_MismatchLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:45.056798+00:00
-- url     : https://prove2.me/theorems/a7ee3de9-e137-4f64-8bfc-57f94a071ec9
-- title:
--   Mismatch of a relation (§7)
-- statement:
--   Let $\mathcal R$ refine $\mathcal Q$ and let $\rho\subseteq\mathcal Q\times\mathcal Q$, not necessarily symmetric. Put $N_\rho(Q)=\bigcup\{Q'\in\mathcal Q\mid(Q,Q')\in\rho\}$. The **mismatch** of $\rho$ with respect to $\mathcal R$ is the smallest integer $m$ such that for every part $Q$ of $\mathcal Q$ and vertex $v\in Q$, the set $N(v)\triangle N_\rho(Q)$ intersects at most $m$ parts of $\mathcal R$.
--
--   A symmetric relation of small mismatch is a flip with few ways to leave a part of $\mathcal R$.
--
--   **Formalization Note** `MismatchLE G Q R ρ m` says that $m$ has the property. That $\mathcal R$ refines $\mathcal Q$ is a hypothesis where needed.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §7, p.28

import Mathlib
import Definitions.Def_MonDepMW_partsHit

set_option autoImplicit false

namespace MonDepMW

/-- **Mismatch at most `m`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §7, p.28: for `ℛ` refining `𝒬` and `ρ ⊆ 𝒬 × 𝒬`, "N_ρ(Q) := ⋃{Q′ ∈ 𝒬 | (Q, Q′) ∈ ρ}",
and "the mismatch of ρ with respect to ℛ [is] the smallest integer m satisfying the following: For every part Q of 𝒬 and
vertex v ∈ Q, the set N(v) △ N_ρ(Q) intersects at most m parts of ℛ."

**Formalization Note.** `ρ` is a relation on the parts of `Q` (the quotient), not necessarily symmetric. The part `Q`
containing `v` is `Quotient.mk Q v`, and `w ∈ N_ρ(Q)` iff `ρ (part of v) (part of w)`. That `ℛ` refines `𝒬` is a
hypothesis of the statements that use this. -/
def MismatchLE {n : ℕ} (G : SimpleGraph (Fin n)) (Q R : Setoid (Fin n))
    (ρ : Quotient Q → Quotient Q → Prop) (m : ℕ) : Prop :=
  ∀ v : Fin n, partsHit R
    (symmDiff (G.neighborSet v) {w | ρ (Quotient.mk Q v) (Quotient.mk Q w)}) ≤ m

end MonDepMW


