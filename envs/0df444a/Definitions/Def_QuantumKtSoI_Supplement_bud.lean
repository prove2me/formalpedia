-- Prove2me | Definitions.Def_QuantumKtSoI_Supplement_bud
-- name    : QuantumKtSoI_Supplement_bud
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:29:34.690977+00:00
-- url     : https://prove2.me/theorems/d5ca82c1-21c3-485e-b548-b3016fa25b7d
-- title:
--   $B(\lambda)$, $\mathrm{bud}(\lambda)$ and $\widehat{\mathrm{bud}}(N)$ of §7.2 and §7.4
-- statement:
--   For $\lambda\ge1$ put
--   $$B(\lambda)=\lambda+\lfloor 2\log(\lambda+1)\rfloor+7+\lceil\log(\lambda+1)\rceil ,$$
--   an upper bound on $\mathrm{qKt}(x)$ for $x\in\{0,1\}^\lambda$. For a gap function $g:\mathbb N\to\mathbb N$,
--   $$\mathrm{bud}(\lambda)=\max\{0,B(\lambda)-g(\lambda)\},\qquad \widehat{\mathrm{bud}}(N)=\max\big(\{\mathrm{bud}(\ell):1\le\ell\le N,\ \nu(\ell)=N\}\cup\{0\}\big),$$
--   where $\nu(\ell)$ is the length of the encoded queries $q(x,s)$ with $|x|=\ell$.
--
--   These are the budgets in the time and advice bounds of Theorem 7.10.
--
--   **Formalization Note** Truncated subtraction is the maximum with $0$; the maximum over the compatible lengths is a finite supremum, which is $0$ on the empty set.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), p.104 (B); p.110 (bud, b̂ud)

import Mathlib
import Definitions.Def_QuantumKtSoI_Supplement_query

namespace QuantumKtSoI.Supplement

/-- `B(λ) = λ + ⌊2 log(λ+1)⌋ + 7 + ⌈log(λ+1)⌉` (§7.2, p.104 of Myrisiotis, STOC 2027 submission,
held version sha256 6616571c…), an upper bound on `qKt(x)` for `x ∈ {0,1}^λ`. -/
noncomputable def Bnd (lam : ℕ) : ℕ :=
  lam + ⌊2 * Real.logb 2 ((lam : ℝ) + 1)⌋₊ + 7 + Nat.clog 2 (lam + 1)

/-- `bud(λ) = max{0, B(λ) − g(λ)}` (p.110). Truncated subtraction is this maximum. -/
noncomputable def bud (g : ℕ → ℕ) (lam : ℕ) : ℕ := Bnd lam - g lam

/-- `b̂ud(N) = max({bud(ℓ) : ℓ ∈ ℕ, 1 ≤ ℓ ≤ N, ν(ℓ) = N} ∪ {0})` (p.110). -/
noncomputable def budHat (g : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun l => nu l = N).sup (bud g)

end QuantumKtSoI.Supplement


