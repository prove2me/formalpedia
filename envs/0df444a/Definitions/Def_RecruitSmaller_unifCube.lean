-- Prove2me | Definitions.Def_RecruitSmaller_unifCube
-- name    : RecruitSmaller_unifCube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:08:58.355169+00:00
-- url     : https://prove2.me/theorems/97c1f9e9-23bd-4402-bfe4-635ab1dfd8e8
-- title:
--   Law of $m$ i.i.d. Uniform$(0,1)$ variables
-- statement:
--   The joint law of $U_1,\dots,U_m$ i.i.d. Uniform$(0,1)$: the $m$-fold product of Lebesgue measure restricted to $(0,1)$.
--
--   It is the coupling space of Lemma A.1, where buyer values are realized as $F_B^{-1}(U_j)$.
--
--   **Formalization Note** `Measure.pi` of `volume.restrict (Set.Ioo 0 1)`; each factor has mass $1$.
-- source:
--   Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, The Power of Recruiting the Smaller Side: Two Additional Traders Suffice in Two-Sided Markets, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma A.1, p.26

import Mathlib

open MeasureTheory

namespace RecruitSmaller

/-- The law of `m` i.i.d. **Uniform(0, 1)** variables `U₁, …, U_m` (Cai–Gupta–Jiang–Liaw–Mehta–Velegkas–Wang–Zhao, *The Power of Recruiting the Smaller Side*, arXiv:2609.27304 (held version, sha256 82900bb2…932a), Lemma A.1,
p.26): the product of `m` copies of Lebesgue measure restricted to `(0, 1)`.

**Formalization Note** Lebesgue measure on `(0, 1)` has total mass `1`, so this is the uniform
probability law; endpoints have measure zero. -/
noncomputable def unifCube (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ : Fin m => (volume : Measure ℝ).restrict (Set.Ioo 0 1)

end RecruitSmaller


