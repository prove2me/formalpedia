-- Prove2me | Definitions.Def_SubspaceConv_fourier
-- name    : SubspaceConv_fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:16:09.501113+00:00
-- url     : https://prove2.me/theorems/71552439-eaa1-40c5-a63a-2f6bbd737fe2
-- title:
--   The finite Fourier transform (6) on $H/B$ and its inverse (7)
-- statement:
--   Let $H=\mathbb F_q^d$, $B\le H$, $S$ a commutative ring and $\psi:\mathbb F_q\to S$. For a table $h_B:H/B\to S$ the Fourier transform is
--   $$\widehat h_\lambda(B)=\sum_{x+B\in H/B}h_B(x+B)\,\psi(\lambda(x)),\qquad\lambda\in B^\circ,\tag{6}$$
--   and, given $q^{-1}\in S$, the inverse formula is
--   $$h_B(x+B)=q^{-(d-\dim B)}\sum_{\lambda\in B^\circ}\widehat h_\lambda(B)\,\psi(-\lambda(x)).\tag{7}$$
--   The paper takes $\psi$ a nontrivial additive character into $\mathbb C$ in §2.1 and $\psi(x)=\zeta^{\operatorname{Tr}(x)}$ in the ring of §3.4; the milestones state which properties of $\psi$ they use.
--
--   **Formalization Note** The definition takes an arbitrary function $\psi$ and an arbitrary element `qinv` playing $q^{-1}$; the theorems assume $q\cdot q^{-1}=1$. Frequencies are indexed by the subtype $B^\circ$.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2.1, eqs. (6)–(7), p.11

import Mathlib
import Definitions.Def_SubspaceConv_annih

namespace SubspaceConv

open Classical in
/-- The finite Fourier transform on `H/B` (`H = F^d`), eq. (6):
`ĥ_λ(B) = ∑_{x + B ∈ H/B} h_B(x + B) ψ(λ(x))` for `λ ∈ B°`
(Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2.1, eq. (6), p.11).

**Formalization Note** The character is any function `ψ : F → S` into a commutative ring `S`
(the paper takes a nontrivial additive character into `ℂ` in §2.1 and `ζ^{Tr(x)}` in §3.4; the
milestones state which properties of `ψ` they use). Frequencies are the subtype `annih B`, and
`λ(x)` on a coset is `annihEval`, which is representative-free. -/
noncomputable def fourier {F : Type*} [Field F] [Fintype F] {d : ℕ} {B : Submodule F (Fin d → F)}
    {S : Type*} [CommRing S] (ψ : F → S) (h : (Fin d → F) ⧸ B → S) (lam : annih B) : S :=
  ∑ c : (Fin d → F) ⧸ B, h c * ψ (annihEval lam c)

open Classical in
/-- The inverse finite Fourier transform, eq. (7):
`h_B(x + B) = q^{−(d − dim B)} ∑_{λ ∈ B°} ĥ_λ(B) ψ(−λ(x))`
(Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §2.1, eq. (7), p.11).

**Formalization Note** `q^{−1}` is passed as an element `qinv : S`; the milestones assume
`q · qinv = 1` in `S` (`q = |F|`), so `q^{−(d − dim B)}` is `qinv ^ (d − dim B)`. The
subtraction `d - finrank B` is never truncated, since `dim B ≤ d`. -/
noncomputable def ifourier {F : Type*} [Field F] [Fintype F] {d : ℕ}
    {B : Submodule F (Fin d → F)} {S : Type*} [CommRing S] (ψ : F → S) (qinv : S)
    (H : annih B → S) (c : (Fin d → F) ⧸ B) : S :=
  qinv ^ (d - Module.finrank F B) * ∑ lam : annih B, H lam * ψ (-(annihEval lam c))

end SubspaceConv


