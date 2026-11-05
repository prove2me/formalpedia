-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_InPmZ
-- name    : ShallowShadows_ShadowNorm_InPmZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:54.898488+00:00
-- url     : https://prove2.me/theorems/ed96ea03-67b2-43e1-8d05-ae358d735fe0
-- title:
--   The set $\pm\mathcal Z$ of signed $Z$-type Pauli strings
-- statement:
--   A $2^n\times 2^n$ matrix $A$ **lies in** $\pm\mathcal Z$ when $A = P^{(0^n,z)}$ or $A = -P^{(0^n,z)}$ for some $z \in \{0,1\}^n$, that is, when $A$ is a tensor product of $\mathbb I$ and $Z$ factors up to a sign:
--
--   $$
--   \pm\mathcal Z = \{\pm P^{(0^n, z)} : z \in \{0,1\}^n\}.
--   $$
--
--   The identity and its negative ($z = 0$) belong to $\pm\mathcal Z$. These are exactly the signed Pauli strings with a nonzero $(0,0)$ entry, which is why the eigenvalues $t_{\lambda,d}$ of the measurement channel are probabilities of landing in $\pm\mathcal Z$.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §II, p. 3

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_pauli

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §II, p. 3: "we use
`±𝒵` to denote `{±P^(0ⁿ, z) | z ∈ {0,1}ⁿ}` i.e., the set of Pauli strings consisting only of `𝕀`
and `Z` factors up to a phase factor of `±1`." `InPmZ A` is the statement `A ∈ ±𝒵`.

**Formalization Note.** `±𝒵` contains `±𝕀` (the case `z = 0`). The Pauli strings are
`ShallowShadows.ShadowNorm.pauli` of Eq. (1). -/
def InPmZ {n : ℕ} (A : Op n) : Prop :=
  ∃ z : Bits n, A = pauli (0, z) ∨ A = -pauli (0, z)

end ShallowShadows.ShadowNorm


