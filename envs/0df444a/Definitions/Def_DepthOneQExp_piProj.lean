-- Prove2me | Definitions.Def_DepthOneQExp_piProj
-- name    : DepthOneQExp_piProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:52:34.444279+00:00
-- url     : https://prove2.me/theorems/a0699ca7-4337-409e-9d3c-ae27d03b9217
-- title:
--   The operator $\Pi$ of Eq. (2.44)
-- statement:
--   The operator of Eq. (2.44) is
--   $$
--   \Pi = \mathbb E_{P\sim\mu(G_n)}P\otimes P - \mathbb E_{U\sim\mu(U(2^n))} U\otimes\overline U = \mathbb E_{P\sim\mu(G_n)}P\otimes P - \frac{|a_1\rangle\langle a_1|}{2^n},
--   $$
--   using Eq. (2.41) for the Haar term. By Eq. (2.43) it equals $\sum_{i=2}^5|b_i\rangle\langle b_i|$.
--
--   **Formalization Note** The Haar average over $U(2^n)$ is written as its value $|a_1\rangle\langle a_1|/\||a_1\rangle\|^2$ from Eq. (2.41).
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Eq. (2.44) with Eq. (2.41), p.13

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_DepthOneQExp_maxEnt
import Definitions.Def_DepthOneQExp_cnotAvg

namespace DepthOneQExp

/-- The operator `Π = E_{P∼µ(G_n)} P ⊗ P − E_{U∼µ(U(2ⁿ))} U ⊗ Ū` of Eq. (2.44)
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, Eq. (2.44), p.13), with
the Haar term written as `|a_1⟩⟨a_1| / 2ⁿ` by Eq. (2.41): `Π = cnotAvg n − |a_1⟩⟨a_1| / 2ⁿ`.

**Formalization Note** The Haar average over `U(2ⁿ)` is replaced by its value
`|a_1⟩⟨a_1|/‖a_1‖²` from Eq. (2.41), `‖a_1‖² = 2ⁿ`. By Eq. (2.43) (`eq_2_43`), `Π` equals
`Σ_{i=2}^5 |b_i⟩⟨b_i|`. -/
noncomputable def piProj (n : ℕ) :
    Matrix (MITMSynthesis.Q n × MITMSynthesis.Q n) (MITMSynthesis.Q n × MITMSynthesis.Q n) ℂ :=
  cnotAvg n - (1 / (2 ^ n : ℂ)) • Matrix.vecMulVec (maxEnt n) (star (maxEnt n))

end DepthOneQExp


