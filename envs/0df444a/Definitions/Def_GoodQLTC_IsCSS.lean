-- Prove2me | Definitions.Def_GoodQLTC_IsCSS
-- name    : GoodQLTC_IsCSS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:36:52.774476+00:00
-- url     : https://prove2.me/theorems/d31f32ac-0ba7-426f-ac17-065ffff8309e
-- title:
--   Binary CSS code: $H_XH_Z^{\top}=0$
-- statement:
--   A **CSS code** on $N$ physical qubits is specified by binary matrices $H_X\in\mathbb F_2^{m_X\times N}$ and $H_Z\in\mathbb F_2^{m_Z\times N}$ with
--   $$
--   H_XH_Z^{\top}=0 .
--   $$
--   The rows $h^X_a$, $h^Z_b$ give the commuting checks $X^{h^X_a}$, $Z^{h^Z_b}$.
--
--   **Formalization Note** Qubits and checks are indexed by finite types; every row is a listed check, including zero and repeated rows.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §3.2, p.13 (PDF p.16)

import Mathlib
open Matrix

namespace GoodQLTC

/-- **Binary CSS code**, Gay–Jeronimo, arXiv:2609.20780 (held version), §3.2, p.13: a pair of
binary check matrices `H_X ∈ F_2^{m_X × N}`, `H_Z ∈ F_2^{m_Z × N}` with `H_X H_Z^⊺ = 0`.

**Formalization Note.** The qubits are indexed by a finite type `ι` and the X- and Z-checks by
finite types `κX`, `κZ` (so `N = |ι|`, `m_X = |κX|`, `m_Z = |κZ|`). Every row is a listed check,
including zero and repeated rows. -/
def IsCSS {ι κX κZ : Type} [Fintype ι] (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) :
    Prop :=
  HX * HZᵀ = 0

end GoodQLTC


