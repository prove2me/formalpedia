-- Prove2me | Definitions.Def_PolytopeSchedPF_Supplement_ApproxCertificate
-- name    : PolytopeSchedPF_Supplement_ApproxCertificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:19:30.279194+00:00
-- url     : https://prove2.me/theorems/d1f6dd64-220d-4938-8ec3-62758ac56228
-- title:
--   Support $\mathrm{supp}(p)$ and $c$-approximate certificates (Definition 6.1)
-- statement:
--   For $p\in\mathbb R^n_{\ge0}$, the **support** is $\mathrm{supp}(p):=\{j\in J: p_j>0\}$.
--
--   Let $P$ be a rate polytope with support function $H_\alpha(U)=\max\{\langle\alpha,y\rangle: y\in P_U\}$, let $w\in\mathbb R^n_{>0}$ and $c\in\mathbb R$. A function $\alpha:\mathbb R^n_{\ge0}\to\mathbb R^n_{\ge0}$ is a **$c$-approximate certificate** for $P$ and $w$ if for all $p\in\mathbb R^n_{\ge0}$:
--
--   1. $\langle\alpha(p),p\rangle\ge\mathrm{OPT}_0(p)$, the optimal weighted completion time with processing requirements $p$ and all release dates $0$;
--   2. $\langle\alpha(p),p\rangle\le\langle\alpha(q),p\rangle$ for all $q\in\mathbb R^n_{\ge0}$;
--   3. $H_{\alpha(p)}(\mathrm{supp}(p))\le c\cdot w(\mathrm{supp}(p))$.
--
--   $P$ **admits a $c$-approximate certificate** for $w$ if such a function exists.
--
--   Condition 2 makes $p\mapsto\langle\alpha(p),p\rangle$ a concave upper bound on $\mathrm{OPT}_0$; the certificate is the potential-function device behind the flow-time guarantee of Theorem 6.3.
--
--   **Formalization Note** $\alpha$ is a function on all of $\mathbb R^n$, constrained (and required nonnegative) only on the nonnegative orthant. $\mathrm{OPT}_0$ is the base mission's `opt0`.
-- source:
--   Jäger, Lindermayr, Zondervan, Single-Machine Guarantees on Unrelated Machines and Beyond: Proportional Fairness for Nonclairvoyant Polytope Scheduling, arXiv:2610.32545v1, §6, p.33 (PDF p.35), supp(p) and Definition 6.1

import Mathlib
import Definitions.Def_PolytopeSchedPF_Orders

namespace PolytopeSchedPF

namespace Supplement

/-- The **support** `supp(p) := {j ∈ J | p_j > 0}` of a processing vector
(Jäger, Lindermayr, Zondervan, arXiv:2610.32545v1, §6, p.33). -/
noncomputable def supp {n : ℕ} (p : Fin n → ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => 0 < p j)

/-- **`c`-approximate certificate** (Definition 6.1, p.33). For a rate polytope `P`, weights `w`
and a real `c`, a function `α : ℝⁿ_{≥0} → ℝⁿ_{≥0}` is a `c`-approximate certificate for `P` and `w`
if for every `p ∈ ℝⁿ_{≥0}`: `α(p) ≥ 0`, and
(i) `⟨α(p), p⟩ ≥ OPT₀(p)`,
(ii) `⟨α(p), p⟩ ≤ ⟨α(q), p⟩` for all `q ∈ ℝⁿ_{≥0}`,
(iii) `H_{α(p)}(supp(p)) ≤ c · w(supp(p))`.

**Formalization Note** `α : (Fin n → ℝ) → Fin n → ℝ`; only its values on the nonnegative orthant
are constrained, and there they must be nonnegative (the codomain `ℝⁿ_{≥0}` of the definition).
`OPT₀(p)` is the base `opt0 P w p` (release dates `0`, reading R13); `H` is the base support
function of `P`. -/
def IsApproxCertificate {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (c : ℝ)
    (α : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ p : Fin n → ℝ, (∀ j, 0 ≤ p j) →
    (∀ j, 0 ≤ α p j) ∧
    opt0 P w p ≤ dot (α p) p ∧
    (∀ q : Fin n → ℝ, (∀ j, 0 ≤ q j) → dot (α p) p ≤ dot (α q) p) ∧
    P.H (α p) (supp p) ≤ c * wsum w (supp p)

/-- `P` **admits a `c`-approximate certificate** for `w` (Definition 6.1, p.33) if such a function
exists. -/
def AdmitsApproxCertificate {n D : ℕ} (P : RatePolytope n D) (w : Fin n → ℝ) (c : ℝ) : Prop :=
  ∃ α : (Fin n → ℝ) → Fin n → ℝ, IsApproxCertificate P w c α

end Supplement

end PolytopeSchedPF


