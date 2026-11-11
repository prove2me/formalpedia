-- Prove2me | Definitions.Def_IPEComm1531_Main_Extractor
-- name    : IPEComm1531_Main_Extractor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:26.279496+00:00
-- url     : https://prove2.me/theorems/8af9384f-bdf3-4d6c-832a-534f6cf71815
-- title:
--   Seeded extractor families and the conclusions of Fact 2.3
-- statement:
--   An extractor family is raw data: for every $(r,\ell)$ a seed length $d(r,\ell)$ and a map $\mathrm{Ext}:\{0,1\}^r\times\{0,1\}^{d}\to\{0,1\}^\ell$.
--
--   With constant $C$ and threshold $R$, the family satisfies the extraction clauses of Fact 2.3 if for every $r\ge R$ and every integer $1\le\ell\le r/3$: the seed length is a positive integer with $d\le C\log_2 r$, and $\mathrm{Ext}$ is a strong $(r/2,1/r)$-extractor in the sense of Definition 2.2, i.e. for every random variable $u$ on $\{0,1\}^r$ with $H_\infty(u)\ge r/2$ and an independent uniform seed $\sigma$,
--   $$\mathrm{TV}\big((\sigma,\mathrm{Ext}(u,\sigma)),(\sigma,c)\big)\le\frac1r,$$
--   with $c$ uniform on $\{0,1\}^\ell$ and independent of $\sigma$. It is effective if one polynomial-time machine, given $r$ and $\ell$ in unary and the bits of $u$ and $\sigma$, outputs $\mathrm{Ext}(u,\sigma)$ for all such $(r,\ell)$.
--
--   **Formalization Note** The strong-extractor property is the published `QCSepTotal.IsStrongExtractor` (all distributions on the source, half-$L^1$ total variation, base-2 min-entropy, the seed retained); no linearity or flatness is imposed. Time is polynomial in the input code length, which lies between $r$ and a constant multiple of $r$ for these parameters.
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Definition 2.2 and Fact 2.3, p.7

import Mathlib
import Definitions.Def_IPEComm1531_Main_Basic
import Definitions.Def_QCSepTotal_IsStrongExtractor
import Definitions.Def_PPSLattice_PolyTimeOn

set_option autoImplicit false

namespace IPEComm1531.Main

open QAlgorithms.Complexity

/-- Raw data: a seed length `d(r, ℓ)` and a map `Ext : {0,1}^r × {0,1}^d → {0,1}^ℓ`
for every `(r, ℓ)`. No property is built in. -/
structure Extractors where
  seedLength : ℕ → ℕ → ℕ
  eval : (r l : ℕ) → Bits r → Bits (seedLength r l) → Bits l

/-- The extraction clauses of Fact 2.3 (p.7) with seed constant `C` and size threshold `R`: for
every `r ≥ R` and every `1 ≤ ℓ ≤ r/3`, the seed length is a positive integer at most
`C log₂ r`, and `Ext` is a strong `(r/2, 1/r)`-extractor (Definition 2.2). -/
def Extractors.GoodFrom (E : Extractors) (C : ℝ) (R : ℕ) : Prop :=
  ∀ r l : ℕ, R ≤ r → 1 ≤ l → 3 * l ≤ r →
    1 ≤ E.seedLength r l ∧ (E.seedLength r l : ℝ) ≤ C * Real.logb 2 r ∧
    QCSepTotal.IsStrongExtractor (E.eval r l) ((r : ℝ) / 2) (1 / (r : ℝ))

/-- Some positive constant and threshold witness `GoodFrom`. -/
def Extractors.Good (E : Extractors) : Prop := ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, E.GoodFrom C R

/-- Admissible evaluation inputs `(r, ℓ, u, σ)` with `r ≥ R`, `1 ≤ ℓ ≤ r/3`. -/
def Extractors.Domain (E : Extractors) (R : ℕ) : Type :=
  Σ rl : {rl : ℕ × ℕ // R ≤ rl.1 ∧ 1 ≤ rl.2 ∧ 3 * rl.2 ≤ rl.1},
    Bits rl.1.1 × Bits (E.seedLength rl.1.1 rl.1.2)

/-- Input code: `r` and `ℓ` in unary, then the bits of `u` and of the seed `σ`. -/
def Extractors.inputCode (E : Extractors) (R : ℕ) (a : E.Domain R) : Str :=
  encNat a.1.1.1 ++ encNat a.1.1.2 ++ bitList a.2.1 ++ bitList a.2.2

/-- "Deterministic evaluation in poly(r) time" (Fact 2.3, p.7): one polynomial-time machine
outputs `Ext(u, σ)` on every admissible input. -/
def Extractors.EffectiveFrom (E : Extractors) (R : ℕ) : Prop :=
  PPSLattice.PolyTimeOn (E.inputCode R) (fun a => bitList (E.eval a.1.1.1 a.1.1.2 a.2.1 a.2.2))

end IPEComm1531.Main


