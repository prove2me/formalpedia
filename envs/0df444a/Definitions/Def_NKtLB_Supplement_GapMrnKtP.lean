-- Prove2me | Definitions.Def_NKtLB_Supplement_GapMrnKtP
-- name    : NKtLB_Supplement_GapMrnKtP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:24:23.137916+00:00
-- url     : https://prove2.me/theorems/51fffb92-10b1-408a-9c9e-faf88621064d
-- title:
--   Gap-MrnKtP$[s_1,s_2]$ — the promise problem of estimating rnKt
-- statement:
--   For functions $s_1,s_2$, **Gap-MrnKtP$[s_1,s_2]$** is the promise problem: given $x\in\{0,1\}^*$, decide whether
--   $$
--   rn\mathrm{Kt}(x)\le s_1(|x|)\quad(\text{yes}) \qquad\text{or}\qquad rn\mathrm{Kt}(x)>s_2(|x|)\quad(\text{no}).
--   $$
--   It is used with $(s_1,s_2)=(\gamma n,\,n-1)$, $(2^{\log^\gamma n},\,n-1)$ and $(n-\mathrm{poly}(\log n),\,n-1)$ in Theorems 5, 7 and 9.
--
--   **Formalization Note** $rn\mathrm{Kt}=rn\mathrm{Kt}_{2/3}$, unrelativized. The thresholds are real-valued, so $\gamma n$ is not rounded. The no-side inequality is strict, as printed.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12

import Mathlib
import Definitions.Def_NKtLB_Supplement_rnKt
import Definitions.Def_NKtLB_toEReal

namespace NKtLB.Supplement

/-- **Gap-MrnKtP[s₁, s₂]** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12): "Fix two functions `s₁, s₂ : ℕ → ℕ`. We let
Gap-MrnKtP[s₁, s₂] be the following promise problem: Given `x ∈ {0,1}^*`, decide whether
`rnKt(x) ≤ s₁(|x|)` ("yes" case) or `rnKt(x) > s₂(|x|)` ("no" case)."

The pair `(YES, NO)`.

**Formalization Note.** `rnKt = rnKt_{2/3}` (p.22), unrelativized. Thresholds are real-valued
(`γ·n`, `2^{log^γ n}`, `n − d log n`), so no rounding is introduced; for integer thresholds this is
the printed problem. The NO side is strict (`>`), as printed. -/
noncomputable def GapMrnKtP (U : Machine) (s₁ s₂ : ℕ → ℝ) : Set (List Bool) × Set (List Bool) :=
  ({x | toEReal (rnKt U ∅ (2 / 3) x []) ≤ ((s₁ x.length : ℝ) : EReal)},
   {x | ((s₂ x.length : ℝ) : EReal) < toEReal (rnKt U ∅ (2 / 3) x [])})

end NKtLB.Supplement


