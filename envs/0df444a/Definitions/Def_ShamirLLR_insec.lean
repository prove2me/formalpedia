-- Prove2me | Definitions.Def_ShamirLLR_insec
-- name    : ShamirLLR_insec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:09.421344+00:00
-- url     : https://prove2.me/theorems/79821059-56b3-4d05-992f-dd6aa7cfa69e
-- title:
--   Shamir leakage laws $L^{a,f}_s$ and insecurity $\mathrm{Insec}(a;d)$
-- statement:
--   Degree-$d$ Shamir sharing of a secret $s\in\mathbb F_p$ at places $a_1,\dots,a_m$ gives party $i$ the share $P_s(a_i)$, where
--   $$
--   P_s(X)=s+\sum_{j=1}^{d}R_jX^j,\qquad R_1,\dots,R_d\ \text{independent uniform in }\mathbb F_p .
--   $$
--   If party $i$ reveals $f_i(P_s(a_i))$ with $f_i:\mathbb F_p\to\{0,1\}$, the **leakage law** $L^{a,f}_s$ is the law of the profile $(f_i(P_s(a_i)))_{i}$. The **insecurity** is the worst-case distinguishing advantage
--   $$
--   \mathrm{Insec}(a;d)=\sup_{f_1,\dots,f_m:\mathbb F_p\to\{0,1\}}\ \max_{s,s'\in\mathbb F_p}\mathrm{SD}\bigl(L^{a,f}_s,L^{a,f}_{s'}\bigr).
--   $$
--
--   Small insecurity means the leakage profiles of any two secrets are statistically indistinguishable for every choice of local leakage functions, chosen after the places are public.
--
--   **Formalization Note** The law is the proportion of $R\in\mathbb F_p^d$ producing the profile; `R j` is the coefficient of $X^{j+1}$. SD is the published `IsingLTL.BeliefProp.tvDist`; the supremum and maximum are over finite types.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), §1, pp.1–2 (PDF pp.2–3)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist

set_option autoImplicit false

namespace ShamirLLR

/-- The leakage law `L^{a,f}_s` of degree-`d` Shamir sharing (p.1–2): the secret `s ∈ 𝔽_p` is
shared as `P_s(a_i)` with `P_s(X) = s + ∑_{j=1}^{d} R_j X^j`, `R_1, …, R_d` independent uniform
in `𝔽_p`, and party `i` reveals `f_i(P_s(a_i))`. The value at `y ∈ {0,1}^ι` is the probability
that the leaked bits equal `y`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
§1, p.1 and p.2.

**Formalization Note.** Bits are `Bool`; the law is a count over `R ∈ 𝔽_p^d` divided by `p^d`.
`R j` is the coefficient of `X^{j+1}`. -/
noncomputable def shamirLaw {p : ℕ} [NeZero p] {ι : Type*} (a : ι → ZMod p) (d : ℕ) (s : ZMod p)
    (f : ι → ZMod p → Bool) (y : ι → Bool) : ℝ :=
  open Classical in
  ((p : ℝ) ^ d)⁻¹ * ((Finset.univ.filter (fun R : Fin d → ZMod p =>
    ∀ i, f i (s + ∑ j : Fin d, R j * a i ^ (j.val + 1)) = y i)).card : ℝ)

/-- The worst-case local one-bit leakage insecurity (p.2):
`Insec(a; d) = sup_{f_1, …, f_m : 𝔽_p → {0,1}} max_{s, s' ∈ 𝔽_p} SD(L^{a,f}_s, L^{a,f}_{s'})`.

**Formalization Note.** `SD` is the published `IsingLTL.BeliefProp.tvDist`
(`½ ∑ |μ(y) − ν(y)|`, footnote 1, p.1). The supremum and the maximum are real `⨆` over finite
types (for `p ≠ 0`), so they are maxima. -/
noncomputable def insec {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ZMod p) (d : ℕ) : ℝ :=
  ⨆ f : ι → ZMod p → Bool, ⨆ s : ZMod p, ⨆ s' : ZMod p,
    IsingLTL.BeliefProp.tvDist (shamirLaw a d s f) (shamirLaw a d s' f)

end ShamirLLR


