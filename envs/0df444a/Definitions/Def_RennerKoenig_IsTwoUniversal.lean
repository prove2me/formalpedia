-- Prove2me | Definitions.Def_RennerKoenig_IsTwoUniversal
-- name    : RennerKoenig_IsTwoUniversal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:44:50.580868+00:00
-- url     : https://prove2.me/theorems/f30b93b9-297a-473d-b1ec-46e6c6cb5d83
-- title:
--   Two-universal random function
-- statement:
--   A random function $F$ from $\mathcal Z$ to a finite set $\mathcal S$ is two-universal if
--
--   $$
--   \Pr[F(z)=F(z')]\le\frac1{|\mathcal S|}\qquad\text{for all distinct }z,z'\in\mathcal Z.
--   $$
--
--   **Formalization Note** A random function is a map $F:\Omega\to(\mathcal Z\to\mathcal S)$ on the probability space. The condition covers all pairs in $\mathcal Z$, including values a random variable on $\mathcal Z$ never takes.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §2.1, p.3

import Mathlib
import Definitions.Def_RennerKoenig_prob

namespace RennerKoenig

/-- **Two-universal random function**: `Pr[F(z) = F(z')] ≤ 1/|S|` for any distinct `z, z'`.
Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §2.1, p.3.

**Formalization Note** A random function is a map `F : Ω → Z → S` on the probability space; `z, z'`
range over the whole domain `Z`, including values a random variable on `Z` never takes. -/
def IsTwoUniversal {Ω Z S : Type*} [Fintype S] (P : PMF Ω) (F : Ω → Z → S) : Prop :=
  ∀ z z' : Z, z ≠ z' → prob P {ω | F ω z = F ω z'} ≤ (Fintype.card S : ℝ)⁻¹

end RennerKoenig


