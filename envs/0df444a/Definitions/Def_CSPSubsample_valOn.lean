-- Prove2me | Definitions.Def_CSPSubsample_valOn
-- name    : CSPSubsample_valOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:18:11.615471+00:00
-- url     : https://prove2.me/theorems/0287cd6b-b096-470b-a32d-c9fced006578
-- title:
--   Restricted value $\mathrm{val}_U$, restricted optimum $\mathrm{OPT}(U)$, and the maximum over a family
-- statement:
--   Let $U\subseteq[n]$ be a set of variables and $W(U)=W\cap U^k$ the set of constraints supported entirely on $U$. The **value restricted to $U$** and the **optimum restricted to $U$** are
--   $$
--   \mathrm{val}_U(\phi)=\frac{1}{|U|^k}\sum_{w\in W(U)}P_w(\phi|_w),\qquad \mathrm{OPT}(U)=\max_{\phi\in[q]^n}\mathrm{val}_U(\phi|_U).
--   $$
--   For a finite nonempty family $\Phi$ of assignments, $\max_{\phi\in\Phi}g(\phi)$ denotes the largest value of $g$ on $\Phi$.
--
--   $\mathrm{OPT}(U)$ is the optimum of the sub-instance induced on $U$; the subsampling theorem compares its average over random $U$ with $\mathrm{OPT}$.
--
--   **Formalization Note** Assignments are total maps $[n]\to[q]$; $\mathrm{val}_U$ reads them only on $U$. The normalizer is the power $|U|^k$; for $U=\emptyset$ and $k\ge1$ Lean returns $0$. The maximum over an empty family is set to $0$ in Lean; every statement applies it to a nonempty family.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), p.5 (PDF p.7); max over Ψ in Lemma 3.2, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_CSPSubsample_Instance

set_option autoImplicit false

namespace CSPSubsample

/-- `W(U) = W ∩ U^k`, the constraints supported entirely on `U` (arXiv:2608.00203 (PDF sha256
fd9ae011…), p.5 = PDF p.7). -/
noncomputable def constraintsOn {n k : ℕ} (U : Finset (Fin n)) : Finset (Fin k ↪ Fin n) :=
  Finset.univ.filter fun w => ∀ j, w j ∈ U

/-- The value restricted to `U`, `val_U(ϕ) = (1/|U|^k) ∑_{w ∈ W(U)} P_w(ϕ|_w)` (arXiv:2608.00203
(PDF sha256 fd9ae011…), p.5 = PDF p.7).

**Formalization Note** `ϕ` is a total assignment `Fin n → Fin q`; only its values on `U` are read,
so this is the paper's `val_U(ϕ|_U)`. The normalizer is the power `|U|^k`. For `U = ∅` and `k ≥ 1`
both the sum and the normalizer vanish and Lean's `0/0 = 0` gives `0`. -/
noncomputable def valOn {n k q : ℕ} (I : Instance n k q) (U : Finset (Fin n))
    (ϕ : Fin n → Fin q) : ℝ :=
  (∑ w ∈ constraintsOn U, I.P w (ϕ ∘ w)) / (U.card : ℝ) ^ k

/-- `OPT(U) = max_{ϕ : [q]^n} val_U(ϕ|_U)` (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.5 = PDF p.7).

**Formalization Note** `⨆` over the finite type of total assignments (attained when it is
nonempty, i.e. a maximum). -/
noncomputable def OPTOn {n k q : ℕ} (I : Instance n k q) (U : Finset (Fin n)) : ℝ :=
  ⨆ ϕ : Fin n → Fin q, valOn I U ϕ

/-- The maximum `max_{ϕ ∈ Φ} g(ϕ)` of a function over a finite nonempty family of assignments
(used for `max_{ϕ ∈ Ψ} val_U(ϕ)` in Lemma 3.2 and Theorem 3.3, and for `OPT^bal_Φ(U)`, p.18, of
arXiv:2608.00203 (PDF sha256 fd9ae011…)).

**Formalization Note** For `Φ = ∅` the paper's maximum is undefined; Lean returns `0`. Every
statement of the mission that uses `maxOver` applies it to a nonempty family. -/
noncomputable def maxOver {α : Type} (Φ : Finset α) (g : α → ℝ) : ℝ :=
  if h : Φ.Nonempty then Φ.sup' h g else 0

end CSPSubsample


