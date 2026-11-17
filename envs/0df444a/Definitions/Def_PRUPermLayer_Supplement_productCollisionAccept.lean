-- Prove2me | Definitions.Def_PRUPermLayer_Supplement_productCollisionAccept
-- name    : PRUPermLayer_Supplement_productCollisionAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:37:22.922767+00:00
-- url     : https://prove2.me/theorems/2c6cbe60-c222-4b8e-9401-8c6b1dcd73a8
-- title:
--   Collision test on a product input: $1-\sum_{x\ \mathrm{injective}}\prod_i p_{x_i}$, $p_x=|\langle x|U\psi\rangle|^2$
-- statement:
--   Let $N=2^n$, let $\varphi_1,\dots,\varphi_n\in\mathbb C^2$ and let $\psi=\varphi_1\otimes\cdots\otimes\varphi_n\in\mathbb C^N$ be the product input. Fix an oracle $U$ on $\mathbb C^N$ and a number of queries $k\ge0$. The **$k$-query collision test on $\psi$** queries $\psi$ $k$ times, measures each output $U\psi$ in the computational basis and accepts if two of the $k$ outcomes are equal. For a fixed oracle the outcomes are $k$ independent samples from
--   $$p_x=|\langle x|U\psi\rangle|^2,\qquad x\in\{0,1\}^n,$$
--   so the test accepts with probability
--   $$\mathrm{acc}_{k,\psi}(U)=1-\sum_{\substack{(x_1,\dots,x_k)\\ \text{pairwise distinct}}}\ \prod_{i=1}^k p_{x_i}.$$
--
--   This is the non-adaptive test that attains the lower bound of Theorem 1.3 (with $\psi=|m\rangle^{\otimes n}$ in the paper's proof). It generalizes the mission's collision test on $|0^n\rangle$ to an arbitrary product input.
--
--   **Formalization Note** Basis labels are `Fin (2^n)`, read as bit strings through `bitsEquivFin` (wire $0$ most significant); factor $\varphi_{i+1}$ sits on wire $i$, as in the published product layer. The formula is extended to arbitrary vectors $\varphi_i$ and arbitrary matrices $U$; the theorem that uses it requires unit vectors and integrates only over unitary $U$. On those physical inputs, the test never accepts when $k\le1$.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa33ec861a7e9c10d88cfcefc2794b77ad1674c02661c9298c5ba565bcb), Theorem 1.3, p.3 (PDF p.5); §7.2, collision test with k queries, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace PRUPermLayer.Supplement

/-- The acceptance probability of the `k`-query **collision test on a product input** with a fixed
oracle `U` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Theorem 1.3, p.3 (PDF p.5): "a non-adaptive algorithm that queries one fixed
product state at most min{t, ⌊(3/2)^{n/2}⌋} times and looks for a collision among the measured
outputs"; §7.2, p.24 (PDF p.26): "Query |m⟩^{⊗n} k times, measure all outputs and accept if two of
them are equal. … Conditioned on the oracle, the k outcomes are independent samples from p").

The input is the product state `ψ = φ₀ ⊗ ⋯ ⊗ φ_{n−1}`, `ψ(y) = ∏ᵢ φᵢ(yᵢ)` where `yᵢ` is bit `i`
of the label `y`. Each of the `k` outputs `Uψ` is measured in the computational basis, giving
`k` independent samples of `p_x = |⟨x|Uψ⟩|²`, and the test accepts iff two samples are equal:
`1 − Σ_{x : [k] → [N] injective} ∏ᵢ p_{x_i}`.

**Formalization Note** The label `y : Fin (2 ^ n)` is the bit string
`(QAlgorithms.bitsEquivFin n).symm y`, and factor `φ i` sits on wire `i`, as in the published
`PRUPermLayer.productLayer`. The formula is extended to every `φ` and every matrix `U`; the
statements that use it require unit vectors `φ i` and integrate only over unitary `U`, so `p` is a
probability distribution. On those physical inputs, the test never accepts when `k ≤ 1`. -/
noncomputable def productCollisionAccept (n k : ℕ) (φ : Fin n → Bool → ℂ)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : ℝ :=
  1 - ∑ x ∈ Finset.univ.filter (fun x : Fin k → Fin (2 ^ n) => Function.Injective x),
    ∏ i, ‖Matrix.mulVec U (fun y => ∏ j, φ j ((QAlgorithms.bitsEquivFin n).symm y j)) (x i)‖ ^ 2

end PRUPermLayer.Supplement


