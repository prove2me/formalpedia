-- Prove2me | Definitions.Def_FastMinority_coreRegion
-- name    : FastMinority_coreRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:51.651226+00:00
-- url     : https://prove2.me/theorems/ecd5ebd2-4375-4462-8327-580f116b1259
-- title:
--   Core region $\mathcal C=[L,R-1]\setminus\mathcal H$
-- statement:
--   The **core region** consists of the minority sizes between the lower and the upper region that are not good:
--   $$
--   \mathcal C=[L,R-1]\setminus\mathcal H ,
--   $$
--   with $L=\lceil n/(4k)\rceil$, $R=\lfloor n/2-n\sqrt{(2D\log n)/k}\rfloor$ and $\mathcal H$ the good set (3.1) for the constant $b$. The weighted return bound of Proposition 3.7 is stated for returns of the chain to $\mathcal C$.
--
--   **Formalization Note** The source writes $\mathcal C=[L,M']$ and $\mathcal H=[M'+1,R'-1]$ with $M'\le M$ and $R'\ge R$ never defined, and defines $\mathcal H$ also by (3.1). With $\mathcal H$ the good set and $R'=R$, the core is the rest of $[L,R-1]$; the four regions then cover $\{1,\dots,\lfloor n/2\rfloor\}$. For large $n$, $\mathcal U=[R,\lfloor n/2\rfloor]$ overlaps the top of $\mathcal H$, since $R$ itself is good.
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Section 3, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_FastMinority_lowThr
import Definitions.Def_FastMinority_upThr
import Definitions.Def_FastMinority_goodSet

set_option autoImplicit false

open Classical

namespace FastMinority

/-- The **core region** `𝓒` (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), §3, p.6 = PDF p.8): the states of `[L, R − 1]` that are not
good, `𝓒 = [L, R − 1] \ 𝓗`.

**Formalization Note** The page writes `𝓒 = [L, M′]`, `𝓗 = [M′ + 1, R′ − 1]` with `M′ ≤ M`, `R′ ≥ R`
never defined, and also defines `𝓗` as the good set (3.1). Reading: `𝓗` is the good set (3.1),
`R′ := R`, and the core is what remains of `[L, R − 1]`, so that `𝓛, 𝓒, 𝓗, 𝓤` cover the state space
(for large `n`, `𝓛` is disjoint from `𝓗`, while `𝓤 = [R, ⌊n/2⌋]` overlaps the top of `𝓗`, since `R`
itself is good). -/
noncomputable def coreRegion (n k : ℕ) (D b : ℝ) : Set (Fin (n + 1)) :=
  {x | lowThr n k ≤ (x : ℕ) ∧ (x : ℕ) < upThr n k D ∧ x ∉ goodSet n k b}

end FastMinority


