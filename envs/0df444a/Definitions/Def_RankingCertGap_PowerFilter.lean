-- Prove2me | Definitions.Def_RankingCertGap_PowerFilter
-- name    : RankingCertGap_PowerFilter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:49:14.632999+00:00
-- url     : https://prove2.me/theorems/f24ee9e3-4a59-443f-8651-f23abab70fec
-- title:
--   The power-filter gadget $G_{p,q}$, the functionals $H_f(1)$ and $\Psi_{p,q}(f)$, and the kernel $k$ with antiderivative $J$
-- statement:
--   For $p,q\ge0$, the **power-filter gadget** $G_{p,q}$ has a final online node $j^\star$ with neighbourhood $\{i^\star,\tilde i^\star\}$. Before it, each of $p$ filters has neighbourhood $\{i^\star,i_r\}$ and each of $q$ filters has neighbourhood $\{\tilde i^\star,\tilde i_s\}$, with all private offline nodes distinct. The two filter sequences may be interleaved arbitrarily. The associated functionals are $H_f(1)=\int_0^1 f(y)\,dy$ and
--
--   $$
--   \Psi_{p,q}(f):=\frac{p+q+1}{(p+1)(q+1)}+\int_0^1\Bigl(1-y^p-y^q+\frac{y^{p+q+1}}{p+1}\Bigr)f(y)\,dy.
--   $$
--
--   The kernel of the upper bound on $\Gamma_{\mathcal A}(2)$ is
--
--   $$
--   k(y):=\frac{154y^4+63y^3-462y^2+310y-48}{2000},
--   $$
--
--   with antiderivative $J(y):=\frac{154}{10000}y^5+\frac{63}{8000}y^4-\frac{77}{1000}y^3+\frac{31}{400}y^2-\frac{3}{125}y$.
--
--   These functionals are the exact family of constraints that determine $\chi(f;2)$.
--
--   **Formalization Note** Offline, $i^\star=0$, $\tilde i^\star=1$, and the private node of the online vertex $j<p+q$ is $j+2$. The reference order is the $p$ filters, then the $q$ filters, then $j^\star$. $\texttt{powerFilter.reorder}$ gives every other arrival order.
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Fig. 2, p.18; eq. (41), p.19; eq. (43), p.19; eq. (13), p.7; eq. (231), p.86; p.87

import Mathlib
import Definitions.Def_RankingCertGap_Inst

namespace RankingCertGap

/-- The `(p, q)` power-filter gadget `G_{p,q}`. Xu, arXiv:2610.17545 (held file sha256 75896dd9…),
Fig. 2, p.18: the final online node `j★` has neighbourhood `{i★, ĩ★}`; before it, each `j_r`,
`r ∈ [p]`, has neighbourhood `{i★, i_r}` and each `j̃_s`, `s ∈ [q]`, has neighbourhood `{ĩ★, ĩ_s}`;
all private offline nodes are distinct.

**Formalization Note.** Offline: `i★ = 0`, `ĩ★ = 1`, and the private node of the online vertex `j`
(`j < p + q`) is `j + 2`. Online: the `p` filters of `i★`, then the `q` filters of `ĩ★`, then `j★`.
The page says "The two filter sequences may be interleaved arbitrarily"; this is the reference order,
and `powerFilter.reorder` gives the others. -/
def powerFilter (p q : ℕ) : Inst (p + q + 2) (p + q + 1) where
  N j := Finset.univ.filter fun i =>
    if j.val < p then i.val = 0 ∨ i.val = j.val + 2
    else if j.val < p + q then i.val = 1 ∨ i.val = j.val + 2
    else i.val = 0 ∨ i.val = 1

/-- The distinguished offline endpoint `i★` of `G_{p,q}`. -/
def powerFilter.iStar (p q : ℕ) : Fin (p + q + 2) := ⟨0, by omega⟩

/-- The final online node `j★` of `G_{p,q}`. -/
def powerFilter.jStar (p q : ℕ) : Fin (p + q + 1) := ⟨p + q, by omega⟩

/-- `G_{p,q}` with its filters interleaved by `σ`: the online vertex at reference position `j` arrives
at position `σ j`. The final node stays last when `σ j★ = j★`; every interleaving of Fig. 2 has this
form. -/
def powerFilter.reorder (p q : ℕ) (σ : Equiv.Perm (Fin (p + q + 1))) :
    Inst (p + q + 2) (p + q + 1) where
  N a := (powerFilter p q).N (σ.symm a)

/-- `H_f(1) = ∫₀¹ f(y) dy` (eq. (43), p.19; `H_f(t) := F_f(t) + 1 − f(t)` of eq. (13) with
`f(1) = 1`). -/
noncomputable def Hf1 (f : ℝ → ℝ) : ℝ := ∫ y in (0 : ℝ)..1, f y

/-- The filtered-root functional, eq. (41), p.19:
`Ψ_{p,q}(f) := (p + q + 1)/((p + 1)(q + 1)) + ∫₀¹ (1 − y^p − y^q + y^{p+q+1}/(p + 1)) f(y) dy`.
The ordered pair `(p, q)` is not symmetric: `p` belongs to the distinguished `i★`. -/
noncomputable def Psi (p q : ℕ) (f : ℝ → ℝ) : ℝ :=
  ((p : ℝ) + q + 1) / (((p : ℝ) + 1) * ((q : ℝ) + 1)) +
    ∫ y in (0 : ℝ)..1, (1 - y ^ p - y ^ q + y ^ (p + q + 1) / ((p : ℝ) + 1)) * f y

/-- The kernel `k(y) := (154y⁴ + 63y³ − 462y² + 310y − 48)/2000` of eq. (231), p.86. -/
noncomputable def kernelK (y : ℝ) : ℝ :=
  (154 * y ^ 4 + 63 * y ^ 3 - 462 * y ^ 2 + 310 * y - 48) / 2000

/-- The antiderivative `J(y)` of `k`, p.87:
`J(y) := (154/10000)y⁵ + (63/8000)y⁴ − (77/1000)y³ + (31/400)y² − (3/125)y`. -/
noncomputable def kernelJ (y : ℝ) : ℝ :=
  154 / 10000 * y ^ 5 + 63 / 8000 * y ^ 4 - 77 / 1000 * y ^ 3 + 31 / 400 * y ^ 2 - 3 / 125 * y

end RankingCertGap


