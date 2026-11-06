-- Prove2me | Definitions.Def_FastMinority_upperRegion
-- name    : FastMinority_upperRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:05:23.846758+00:00
-- url     : https://prove2.me/theorems/1cde8dfb-4d75-458a-8736-0a20444ba785
-- title:
--   Upper region $\mathcal U=[R,\lfloor n/2\rfloor]$
-- statement:
--   The **upper region** is the set of minority sizes $\mathcal U=[R,\lfloor n/2\rfloor]$, with $R=\lfloor n/2-n\sqrt{(2D\log n)/k}\rfloor$: the nearly balanced configurations. Lemma 3.4 bounds the time to leave it, $\tau_{\mathcal U}=\inf\{t\ge0:X_t<R\}$.
--
--   **Formalization Note** The source writes $\mathcal U=[R',\lfloor n/2\rfloor]$ for an undefined $R'\ge R$ and says it is enough to work with $R$; Lemma 3.4 and its proof use $[R, n/2]$. This mission takes $R'=R$.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.6 (PDF p.8), and Lemma 3.4, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_FastMinority_upThr

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The **upper region** `𝓤 = [R, ⌊n/2⌋]` (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.6 = PDF p.8, and Lemma 3.4, p.9 = PDF p.11:
"`τ_U = inf{t ≥ 0 : X_t < R}` be the first exit time from `U`").

**Formalization Note** The page writes `𝓤 = [R′, ⌊n/2⌋]` with an undefined `R′ ≥ R` and says that it
is enough to work with `R`; this mission takes `R′ := R`, as Lemma 3.4 and its proof (p.16: "`U =
[n/2 − n√((2D log n)/k), n/2]`") do. -/
noncomputable def upperRegion (n k : ℕ) (D : ℝ) : Set (Fin (n + 1)) :=
  {x | upThr n k D ≤ (x : ℕ) ∧ 2 * (x : ℕ) ≤ n}

end FastMinority


