-- Prove2me | Definitions.Def_SubSuperStoch_SuperSpec_Setting
-- name    : SubSuperStoch_SuperSpec_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:25:20.646916+00:00
-- url     : https://prove2.me/theorems/58399cee-3e5d-48fb-9463-28986b135d63
-- title:
--   §2.1, Definition 2.5, pp. 4, 8 — row sums Λ_i, ‖·‖_∞, eigenvalues, non-zero element chains, super-stochastic matrices, ordered products
-- statement:
--   This file fixes the notation of §2.1 and Definition 2.5 of Shi, Zheng, Shao and Cheng for real $n\times n$ matrices $F=[f_{ij}]$, with rows and columns indexed by $\{1,\dots,n\}$.
--
--   1. **Row sum.** $\Lambda_i[F]=\sum_{j=1}^n f_{ij}$ is the sum of the $i$-th row of $F$.
--   2. **Infinity norm.** $\|F\|_\infty=\max_{i}\sum_{j=1}^n |f_{ij}|$, the maximal absolute row sum.
--   3. **Eigenvalues.** The eigenvalues of $F$ are taken as complex numbers: they form the spectrum of $F$ regarded as a complex matrix. A bound $\rho(F)\le b$ on the spectral radius is expressed as $|\mu|\le b$ for every eigenvalue $\mu$, and $\rho(F)<1$ as $|\mu|<1$ for every eigenvalue (the spectrum is finite).
--   4. **Non-zero element chain.** For indices $c_0,c_1,\dots,c_L$, the list of entries
--   $$[F]_{c_L c_{L-1}},\ \dots,\ [F]_{c_2c_1},\ [F]_{c_1c_0}$$
--   is a non-zero element chain of $L$ elements from $c_0$ to $c_L$ if every listed entry is non-zero and consecutive indices differ, $c_{t+1}\neq c_t$. In the paper's notation $\mathcal C_{i\to k}=[F]_{ki_r},\dots,[F]_{i_2i_1},[F]_{i_1 i}$ with $c_0=i$, $c_t=i_t$, $c_L=k$, $L=r+1$, and $|\mathcal C_{i\to k}|=L$.
--   5. **Super-stochastic matrix (Definition 2.5).** $F$ is super-stochastic if $f_{ij}\ge 0$ for all $i,j$, and there is a set $\mathcal W_1\subseteq\{1,\dots,n\}$ with $\Lambda_i[F]\ge 1$ for $i\in\mathcal W_1$ and $\Lambda_i[F]<1$ for $i\notin\mathcal W_1$.
--   6. **Ordered product.** For a sequence of matrices $F_1,F_2,\dots$, the product $\prod_{s=a}^{a+m-1}F_s$ is $F_{a+m-1}\cdots F_{a+1}F_a$, later factors on the left; in particular $\prod_{s=1}^{q}F_s=F_qF_{q-1}\cdots F_1$, and the empty product is the identity.
--
--   These are the objects in which Theorems 2.6, 2.7 and 2.8 are stated: the row sums sort the rows into $\mathcal R_1=\{s\mid\Lambda_s[F]<1\}$ and $\mathcal R_2=\{s\mid\Lambda_s[F]\ge 1\}$, chains connect rows of $\mathcal R_1$ to rows of $\mathcal R_2$, and the conclusions are bounds on eigenvalues.
--
--   **Formalization Note** Indices are $0$-based (`Fin n`), so the paper's row $i$ is Lean's row $i-1$. The infinity norm is a supremum over `Fin n` and equals $0$ for $n=0$. Eigenvalues are the spectrum of the complexified matrix, which coincides with the complex roots of the characteristic polynomial. The entry linking $c_t$ to $c_{t+1}$ is in row $c_{t+1}$, column $c_t$. The set $\mathcal W_1$ of Definition 2.5 is a subset that may be all of $\{1,\dots,n\}$ (the paper's example on p. 11 calls a matrix with row sums $1.02,1,1.02$ super-stochastic); with that reading condition 2) holds for every matrix ($\mathcal W_1$ = rows of sum $\ge 1$), so the definition amounts to entrywise nonnegativity and condition 2) only fixes the vocabulary.
-- source:
--   Shi, Zheng, Shao, Cheng, arXiv:2004.01867v2, p. 4, §2.1 Matrix notations; p. 8, Definition 2.5; p. 9, Theorem 2.6 (chains); pp. 10–11, Theorem 2.8 (products)

import Mathlib
import Definitions.Def_SubSuperStoch_SubSpec_Setting

namespace SubSuperStoch.SuperSpec

/-- Definition 2.5 (p. 8): `F` is super-stochastic if it is entrywise nonnegative and there is a
set `W₁` of rows with `Λ_i[F] ≥ 1` for `i ∈ W₁` and `Λ_i[F] < 1` for `i ∉ W₁`. -/
def IsSuperStochastic {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ F i j) ∧
    ∃ W₁ : Finset (Fin n), (∀ i ∈ W₁, 1 ≤ SubSuperStoch.SubSpec.rowSum F i) ∧ ∀ i ∉ W₁, SubSuperStoch.SubSpec.rowSum F i < 1

/-- The ordered product `F (a + m - 1) * ⋯ * F (a + 1) * F a` of `m` consecutive matrices of a
sequence, later factors on the left; `∏_{s=1}^{q} F_s = F_q ⋯ F_1` is `prodFrom F 1 q`, and the
empty product (`m = 0`) is the identity. -/
def prodFrom {n : ℕ} (F : ℕ → Matrix (Fin n) (Fin n) ℝ) (a m : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ((List.range m).map (fun t => F (a + t))).reverse.prod

end SubSuperStoch.SuperSpec


