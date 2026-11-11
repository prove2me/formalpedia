-- Prove2me | Definitions.Def_ShamirLLR_deltaClass
-- name    : ShamirLLR_deltaClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:50.302145+00:00
-- url     : https://prove2.me/theorems/82003604-afa8-4df8-ab77-406b23b75e79
-- title:
--   Comparisons $\Delta_{\mathcal H}(a;r)$ and $\Delta(a;r)$
-- statement:
--   For a class $\mathcal H$ of probability maps $\mathbb F_p\to[0,1]$, places $a=(a_i)_{i\in\iota}$ and $r\ge1$, the **codeword versus independent-input comparison** is
--   $$
--   \Delta_{\mathcal H}(a;r)=\sup_{f_i\in\mathcal H}\ \frac12\sum_{y\in\{0,1\}^\iota}\bigl|P_{a,f}(y)-Q_f(y)\bigr| ,
--   $$
--   and $\Delta(a;r)$ is the same supremum taken over all one-bit leakage functions $f_i:\mathbb F_p\to\{0,1\}$:
--   $$
--   \Delta(a;r)=\sup_{f_1,\dots,f_m:\mathbb F_p\to\{0,1\}}\mathrm{SD}\bigl((f_i(L_i(x)))_{i},(f_i(U_i))_{i}\bigr).
--   $$
--
--   $\Delta(a;r)$ measures how far local bits of a uniform Reed–Solomon codeword are from local bits of independent uniform field elements; it controls Shamir leakage through Eq. (2).
--
--   **Formalization Note** The statistical distance $\tfrac12\sum|\mu-\nu|$ is the published `IsingLTL.BeliefProp.tvDist`. The suprema are real suprema of values in $[0,1]$ (the class supremum is over a nonempty class in every statement), so no junk value enters.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Eq. (1), p.3; Eq. (7), p.13 (PDF pp.4, 14); SD: footnote 1, p.1

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_ShamirLLR_leakageLaws

set_option autoImplicit false

namespace ShamirLLR

/-- The codeword versus independent-input comparison for a class `𝓗` of probability maps,
Eq. (7), p.13 (and §1.2, p.5):
`Δ_𝓗(a; r) = sup_{f_1, …, f_m ∈ 𝓗} ½ ∑_{y ∈ {0,1}^m} |P_{a,f}(y) − Q_f(y)|`.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Eq. (7), p.13.

**Formalization Note.** The statistical distance `½ ∑ |μ(y) − ν(y)|` (footnote 1, p.1) is the
published `IsingLTL.BeliefProp.tvDist`. The supremum is the real `⨆` over maps `ι → 𝓗`; for a
class of probability maps the family is bounded by `1`, so it is a genuine supremum when `𝓗`
is nonempty (every statement using it has a nonempty class). -/
noncomputable def deltaClass {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Set (ZMod p → ℝ))
    (a : ι → ZMod p) (r : ℕ) : ℝ :=
  ⨆ f : ι → H, IsingLTL.BeliefProp.tvDist (codeLaw a r (fun i => (f i : ZMod p → ℝ)))
    (indepLaw (fun i => (f i : ZMod p → ℝ)))

/-- The codeword versus independent-input comparison `Δ(a; r)` of Eq. (1), p.3: the supremum
over all one-bit leakage functions `f_1, …, f_m : 𝔽_p → {0, 1}` of the statistical distance
between `(f_i(L_i(x)))_i`, `x` uniform in `𝔽_p^r`, and `(f_i(U_i))_i`, `U_i` independent
uniform ("The quantity Δ(a; r) is given by the same formula with the supremum taken over all
maps f_i : 𝔽_p → {0, 1}", p.13).

**Formalization Note.** Bits are `Bool`; the supremum ranges over the finite type of maps
`ι → ZMod p → Bool` (for `p ≠ 0`), so it is a maximum. -/
noncomputable def delta {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ZMod p) (r : ℕ) : ℝ :=
  ⨆ f : ι → ZMod p → Bool, IsingLTL.BeliefProp.tvDist (codeLaw a r (fun i => bitMap (f i)))
    (indepLaw (fun i => bitMap (f i)))

end ShamirLLR


