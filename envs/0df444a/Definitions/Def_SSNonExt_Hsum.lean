-- Prove2me | Definitions.Def_SSNonExt_Hsum
-- name    : SSNonExt_Hsum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:58:24.456519+00:00
-- url     : https://prove2.me/theorems/206b8617-4dac-4f24-bb3f-7787211e8beb
-- title:
--   Signs $h(k)=(-1)^{\mathrm{Ext}(k)}$, sums $H_T$, $v_i$ and the set $\{i:v_i>0\}$
-- statement:
--   For a one-bit function $\mathrm{Ext}:\mathcal K\to\{0,1\}$ on the key set of $\Pi_b$ let
--
--   $$h(k)=(-1)^{\mathrm{Ext}(k)},\qquad H_T=\sum_{k\in\Omega_T}h(k)\ (T\subseteq V),\qquad v_i=h(C_i)-h(L_i)-h(R_i)\ (i\in V),$$
--
--   and let $T^\star=\{i\in V:v_i>0\}$.
--
--   These are the quantities of the parity argument in the proof of Lemma 3.3: the error of $\mathrm{Ext}$ on $P_T$ is $|H_T|/(2Z_T)$, and $T^\star$ is the set on which the argument is run.
--
--   **Formalization Note** The bit $1$ is `true`, so $h(k)=-1$ exactly when `Ext k = true`; $h$, $H_T$, $v_i$ are integers.
-- source:
--   Aggarwal, Secret Sharing Despite Non-Extractable Randomness, arXiv:2610.20173 (version of 2026-11-03, sha256 438a7f71…), proof of Lemma 3.3, p.7 (PDF p.7)

import Mathlib
import Definitions.Def_SSNonExt_sourceClass

namespace SSNonExt

/-- The sign `h(k) = (−1)^{Ext(k)}` of a one-bit extractor `Ext : 𝒦 → {0,1}` (proof of Lemma 3.3,
p.7). D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*, arXiv:2610.20173 (version of
2026-11-03, sha256 438a7f71…), proof of Lemma 3.3, p.7.

**Formalization Note.** The output bit `1` is `true`, so `h(k) = −1` when `Ext k = true` and `1`
otherwise. -/
def hSign {b : ℕ} (Ext : Key b → Bool) (k : Key b) : ℤ :=
  if Ext k then -1 else 1

/-- `H_T = ∑_{k ∈ Ω_T} h(k)` (proof of Lemma 3.3, p.7). -/
noncomputable def Hsum {b : ℕ} (Ext : Key b → Bool) (T : Finset (V b)) : ℤ :=
  ∑ k ∈ Omega T, hSign Ext k

/-- `v_i = h(Cᵢ) − h(Lᵢ) − h(Rᵢ)` (proof of Lemma 3.3, p.7). -/
def vDiff {b : ℕ} (Ext : Key b → Bool) (i : V b) : ℤ :=
  hSign Ext (Branch.C, i) - hSign Ext (Branch.L, i) - hSign Ext (Branch.R, i)

/-- The set `T = {i : v_i > 0}` chosen in the proof of Lemma 3.3 (p.7). -/
noncomputable def posSet {b : ℕ} (Ext : Key b → Bool) : Finset (V b) :=
  Finset.univ.filter fun i => 0 < vDiff Ext i

end SSNonExt


