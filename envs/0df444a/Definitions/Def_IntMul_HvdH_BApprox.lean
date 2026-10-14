-- Prove2me | Definitions.Def_IntMul_HvdH_BApprox
-- name    : IntMul_HvdH_BApprox
-- status  : Definition
-- author  : @xuanji
-- created : 2026-10-12T00:38:15.877174+00:00
-- url     : https://prove2.me/theorems/1fbf3f0e-aef6-40fa-90e8-b26fc13c1752
-- title:
--   Fixed-point approximation $\tilde{\mathcal B}$ of the inverse resampling map (Harvey–van der Hoeven Proposition 4.7(ii))
-- statement:
--   The computable map $\tilde{\mathcal B}=\tilde P_s^{-1}\tilde{\mathcal D}'\tilde{\mathcal J}'\tilde{\mathcal C}\tilde P_t$ from the proof of Proposition 4.7(ii) of Harvey–van der Hoeven. It approximates
--   $$\mathcal B=P_s^{-1}\mathcal D'\mathcal J'\mathcal CP_t:\mathbb C^t\to\mathbb C^s.$$
--   The maps $\tilde P_t$, $\tilde{\mathcal C}$ and $\tilde P_s^{-1}$ only rearrange data. The vector entries $0,\dots,n-1$ of $V:\mathbb N\to\mathbb Z[i]$ hold a vector of $\mathbb C^n$.
--
--   * `ptPerm s t V k` $=V_{-sk\bmod t}$.
--   * `cSel s t V ℓ` $=V_{[t\ell'/s]}$ with $\ell'=\ell\bmod s$ and $[x]=\lfloor x+1/2\rfloor$. The output is $s$-periodic.
--   * `psInvPerm s t W j` $=W_{t^{-1}j\bmod s}$.
--   * `Bapprox p s t α V` composes these with `Japprox` (Lemma 4.12) and `Dapprox` (Lemma 4.8).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Proposition 4.7

import Definitions.Def_IntMul_HvdH_JApprox
import Definitions.Def_IntMul_HvdH_DiagApprox

/-! The fixed-point approximation `B̃ = P̃_s⁻¹ D̃' J̃' C̃ P̃_t` of the map `B` in Gaussian resampling
(Harvey–van der Hoeven Proposition 4.7(ii)). Gaussian integers are pairs `(re, im) : ℤ × ℤ`, and
a fixed-point vector of precision `p` is `U : ℕ → ℤ × ℤ` standing for `2^{-p} U`; a vector in
`ℂ^n` is stored in the entries `0, …, n - 1`. -/

namespace IntMul.HvdH

/-- `(P̃_t V)_k = V_{-sk mod t}`. -/
def ptPerm (s t : ℕ) (V : ℕ → ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  V (-((s : ZMod t) * (k : ZMod t))).val

/-- `(C̃ V)_ℓ = V_{round(tℓ'/s) mod t}` with `ℓ' = ℓ mod s` (the output is `s`-periodic). -/
def cSel (s t : ℕ) (V : ℕ → ℤ × ℤ) (l : ℕ) : ℤ × ℤ :=
  V ((((2 * t * (l % s) + s) / (2 * s) : ℕ) : ZMod t)).val

/-- `(P̃_s⁻¹ W)_j = W_{t⁻¹ j mod s}`. -/
def psInvPerm (s t : ℕ) (W : ℕ → ℤ × ℤ) (j : ℕ) : ℤ × ℤ :=
  W ((t : ZMod s)⁻¹ * (j : ZMod s)).val

/-- `B̃ = P̃_s⁻¹ D̃' J̃' C̃ P̃_t` (Lemmas 4.8 and 4.12 and data rearrangements). -/
def Bapprox (p s t α : ℕ) (V : ℕ → ℤ × ℤ) : ℕ → ℤ × ℤ :=
  psInvPerm s t (Dapprox p s t α (Japprox p s t α (cSel s t (ptPerm s t V))))

end IntMul.HvdH


