-- Prove2me | Definitions.Def_NKtLB_Supplement_GapMnKtP
-- name    : NKtLB_Supplement_GapMnKtP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:24:51.257206+00:00
-- url     : https://prove2.me/theorems/5cf1245c-376e-4382-8f0e-d8c34b0df7b0
-- title:
--   Gap-MnKtP$[\alpha,\beta]$ — the promise problem of estimating nKt
-- statement:
--   **Gap-MnKtP$[\alpha,\beta]$** is the promise problem on inputs $x\in\{0,1\}^*$ with
--   $$
--   \mathrm{YES}=\{x : n\mathrm{Kt}(x)\le\alpha(|x|)\},\qquad \mathrm{NO}=\{x : n\mathrm{Kt}(x)\ge\beta(|x|)\}.
--   $$
--   Theorem 123 shows that Gap-MnKtP$[0.6n,0.9n]$ is not in $\mathsf{DTIME}[2^{\varepsilon n}]$.
--
--   **Formalization Note** $n\mathrm{Kt}$ is the base `NKtLB.nKt` with oracle $\emptyset$; thresholds real-valued; the no-side inequality is non-strict, as printed on p.24.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.4, p.24

import Mathlib
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_toEReal

namespace NKtLB.Supplement

/-- **Gap-MnKtP[α, β]** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.4, p.24): "the promise problem GapMnKtP[α, β] on inputs
`x ∈ {0,1}^*` defined by `YES ≜ {x : nKt(x) ≤ α(|x|)}`, `NO ≜ {x : nKt(x) ≥ β(|x|)}`."

**Formalization Note.** `nKt` is the base `nKt U ∅ ⊤ x [] []`; thresholds real-valued (`0.6n`,
`0.9n`). The NO side is `≥`, as printed on p.24. -/
noncomputable def GapMnKtP (U : Machine) (α β : ℕ → ℝ) : Set (List Bool) × Set (List Bool) :=
  ({x | toEReal (nKt U ∅ ⊤ x [] []) ≤ ((α x.length : ℝ) : EReal)},
   {x | ((β x.length : ℝ) : EReal) ≤ toEReal (nKt U ∅ ⊤ x [] [])})

end NKtLB.Supplement


