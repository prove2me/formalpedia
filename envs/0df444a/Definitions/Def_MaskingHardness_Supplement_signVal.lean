-- Prove2me | Definitions.Def_MaskingHardness_Supplement_signVal
-- name    : MaskingHardness_Supplement_signVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:27:11.44253+00:00
-- url     : https://prove2.me/theorems/4c20ae05-2538-4809-bd67-0090b84eae95
-- title:
--   Binary labels $y\in\{\pm1\}$ as reals
-- statement:
--   In the binary setting the label set is $\mathcal Y=\{\pm1\}$, and the label enters formulas such as $(1-c(x)y)_+$, $|y-c(x)|$ and $y-p(x)$ through its real value. Here the two labels are the two elements of a two-element type, mapped to
--
--   $$
--   \mathrm{signVal}(\mathsf{true})=+1,\qquad \mathrm{signVal}(\mathsf{false})=-1 .
--   $$
--
--   This is the label convention of Theorems 1.10 and 6.7.
--
--   **Formalization Note** The two-element label type is `Bool`; only the real values $\pm1$ are ever used.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), binary setting of Theorem 1.10, p.7 (PDF p.9), and Theorem 6.7, p.33 (PDF p.35)

import Mathlib

namespace MaskingHardness.Supplement

/-- **Binary labels `y ∈ {±1}` as reals** (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*, arXiv:2611.05296, held version sha256 31134e8d…3e8d, binary setting of Theorem 1.10, printed p.7 =
PDF p.9, and Theorem 6.7, printed p.33 = PDF p.35): the label type `{±1}` is `Bool`, and
`signVal y` is the real value `+1` (for `true`) or `−1` (for `false`) that enters every
formula (`(1 − c(x)y)₊`, `|y − c(x)|`, `y − p(x)`).

**Formalization Note** Using `Bool` gives a two-element finite label type; only its real value
`±1` is ever used. -/
def signVal (y : Bool) : ℝ := if y then 1 else -1

end MaskingHardness.Supplement


