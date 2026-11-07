-- Prove2me | Definitions.Def_CodeSW_rc
-- name    : CodeSW_rc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:45.456199+00:00
-- url     : https://prove2.me/theorems/ff6ae50b-d1f2-4d59-8804-73d8bfa36fc7
-- title:
--   The random cluster model $\phi$ of a code and its Swendsen-Wang chain $P_{\mathrm{SW}}$
-- statement:
--   The **random cluster model** of the code $h$ with parameter $p$ is the distribution on subsets of checks $A\subseteq E$ given by
--   $$\phi(A)=Z^{-1}p^{|A|}(1-p)^{c-|A|}2^{k(A)},$$
--   that is, $\phi(A)\propto\bigl(\tfrac{p}{1-p}\bigr)^{|A|}2^{k(A)}$. Its **Swendsen-Wang chain** $P_{\mathrm{SW}}$ draws $x$ uniformly from $X(B)$ from the current state $B$, and then keeps each satisfied check of $x$ independently with probability $p$:
--   $$P_{\mathrm{SW}}(B,A)=\sum_x\mathbf 1(x\in X(A)\cap X(B))\,p^{|A|}(1-p)^{|E(x)|-|A|}\,2^{-k(B)}.$$
--
--   This chain is the view of the Code Swendsen-Wang chain on the check side, used in the reduction of §3.3.1 and in the comparison with single-check dynamics.
--
--   **Formalization Note** Rows are the current state and columns the next state. The p.19 form of $\phi$ is used; for $p<1$ it is proportional to the p.16 form. $x\in X(A)$ means $A\subseteq E(x)$, so the exponent $|E(x)|-|A|$ is exact.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), §3.2, p.16; §3.3.1, p.17; proof of Corollary 17, p.19; proof of Lemma 29, eq. (20), p.35

import Definitions.Def_CodeSW_kerA
open Matrix
noncomputable section

namespace CodeSW

/-- The unnormalized **random cluster weight** `p^{|A|} (1−p)^{c−|A|} 2^{k(A)}` of a set of checks
`A ⊆ E = [c]` (Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446,
manuscript sha256 4e4abb5e…, proof of Corollary 17, p.19). -/
def rcWeight {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) (A : Finset (Fin c)) : ℝ :=
  p ^ A.card * (1 - p) ^ (c - A.card) * (2 : ℝ) ^ kDim h A

/-- The **random cluster model on codes** `ϕ(A) = Z^{−1} p^{|A|}(1−p)^{c−|A|} 2^{k(A)}`, i.e.
`ϕ(A) ∝ (p/(1−p))^{|A|} 2^{k(A)}` (arXiv:2510.08446, manuscript sha256 4e4abb5e…, §3.2, p.16;
proof of Corollary 17, p.19).

**Formalization Note** The p.19 form is used; for `p < 1` it is proportional to the p.16 form
`(p/(1−p))^{|A|} 2^{k(A)}`, hence the same distribution. `c − |A|` is exact (`|A| ≤ c`). -/
def rc {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) (A : Finset (Fin c)) : ℝ :=
  rcWeight h p A / ∑ B : Finset (Fin c), rcWeight h p B

open Classical in
/-- The **Swendsen-Wang chain of the random cluster model**, `P_SW` on subsets of checks: from
`B`, draw `x` uniformly from `X(B) = ker(h_B)`, then keep each satisfied check of `x`
independently with probability `p`. Explicitly (eq. (20)),
`P_SW(B, A) = ∑_x 1(x ∈ X(A) ∩ X(B)) p^{|A|} (1−p)^{|E(x)|−|A|} 2^{−k(B)}`
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, §3.3.1, p.17; proof of Lemma 29, eq. (20), p.35).

**Formalization Note** Rows are the current state `B`, columns the next state `A`.
`x ∈ X(A)` is equivalent to `A ⊆ E(x)`, so `|E(x)| − |A|` is exact. -/
def swRC {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) :
    Matrix (Finset (Fin c)) (Finset (Fin c)) ℝ :=
  fun B A => ∑ x : Fin n → ZMod 2,
    if x ∈ kerA h A ∧ x ∈ kerA h B then
      p ^ A.card * (1 - p) ^ ((satChecks h x).card - A.card) * ((2 : ℝ) ^ kDim h B)⁻¹
    else 0

end CodeSW


