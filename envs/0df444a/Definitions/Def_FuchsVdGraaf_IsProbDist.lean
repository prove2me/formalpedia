-- Prove2me | Definitions.Def_FuchsVdGraaf_IsProbDist
-- name    : FuchsVdGraaf_IsProbDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:13.889993+00:00
-- url     : https://prove2.me/theorems/3bbfa7e9-d89d-40a0-ab3c-7533a869957e
-- title:
--   Probability distribution on a finite set
-- statement:
--   Let $\mathcal X$ be a finite set. A function $p : \mathcal X \to \mathbb R$ is a **probability distribution** on $\mathcal X$ if
--
--   $$
--   p(x) \ge 0 \quad\text{for every } x\in\mathcal X, \qquad \sum_{x\in\mathcal X} p(x) = 1 .
--   $$
--
--   In Fuchs and van de Graaf's setting a stochastic variable $X_t$ over a finite set induces the distribution $p_t(x) = \mathrm{Prob}[X_t = x]$; every classical distinguishability measure of the paper compares two such distributions $p_0, p_1$ on the same set, with equal prior probabilities $\pi_0 = \pi_1 = \tfrac12$.
--
--   **Formalization Note** The finite set is an arbitrary finite type. Total mass one forces it to be nonempty.
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, §2, p.4

import Mathlib

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, *Cryptographic Distinguishability Measures for Quantum Mechanical
States*, arXiv:quant-ph/9712042v2, §2, p.4: a stochastic variable over a finite set `X` induces a
probability distribution `p` on `X`, with `p(x) ≥ 0` and `∑_{x∈X} p(x) = 1`.

**Formalization Note.** A distribution is a function `p : X → ℝ` on a finite type `X`; the
predicate records nonnegativity and total mass one. Mass one forces `X` to be nonempty. -/
def IsProbDist {X : Type} [Fintype X] (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

end FuchsVdGraaf


