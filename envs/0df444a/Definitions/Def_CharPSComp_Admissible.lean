-- Prove2me | Definitions.Def_CharPSComp_Admissible
-- name    : CharPSComp_Admissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:16.283072+00:00
-- url     : https://prove2.me/theorems/e6bd27ff-aa02-4364-a33e-c2a1a07d969a
-- title:
--   Admissible multiplication costs $M$ and the logarithm $\log x=\max\{1,\log_2x\}$
-- statement:
--   Two conventions of the paper's complexity bounds.
--
--   1. **The logarithm.** In complexity bounds the paper writes $\log x\triangleq\max\{1,\log_2 x\}$ (§2.1); this is `lg`. In particular $\log\log\sigma\ge1$ for every $\sigma$, so the bound of Theorem 1 never divides by zero.
--   2. **Admissible multiplication costs.** A function $M:\mathbb N\to\mathbb N$ is *admissible* when
--   $$\ell\le M(\ell)\quad(\ell\ge1),\qquad M(\ell)\,\ell'\le M(\ell')\,\ell\quad(1\le\ell\le\ell').$$
--   The second condition is "$M(n)/n$ is nondecreasing" (§2.3) written without division; it implies $M(\ell)\le(\ell/n)M(n)$ for $1\le\ell\le n$, the form used in the paper. The first condition holds for every actual multiplication algorithm, whose $2\ell-1$ outputs each need an operation.
--
--   The polynomial-multiplication instruction of the machine is charged $M(\ell)$, and the cost theorems of the mission hold for every admissible $M$.
-- source:
--   Zhu, Faster Power Series Composition in Fixed Positive Characteristic, STOC 2027 submission (manuscript sha256 e63e0527228218d0d0b04691cbfb8b92cc1c9c7abddec6972d71bbab231c6361), §2.1 Notation, p.4 (PDF p.5); §2.3, p.5 (PDF p.6)

import Mathlib

namespace CharPSComp

/-- The paper's logarithm in complexity bounds (Zhu, *Faster Power Series Composition in Fixed
Positive Characteristic*, STOC 2027 submission (manuscript sha256 e63e0527…), §2.1, p.4, PDF p.5):
"In complexity bounds we write log x ≜ max{1, log₂ x}". -/
noncomputable def lg (x : ℝ) : ℝ := max 1 (Real.logb 2 x)

/-- An admissible multiplication cost `M` (ibid., §2.3, p.5, PDF p.6): the instruction `pmul` on
length `ℓ` is charged `M ℓ`, and

1. `ℓ ≤ M ℓ` for every `ℓ ≥ 1` (a product of two length-`ℓ` arrays has `2ℓ − 1` distinct
   outputs, each needing at least one ring operation);
2. `M(ℓ)/ℓ` is nondecreasing on `ℓ ≥ 1`, written without division as
   `M ℓ * ℓ' ≤ M ℓ' * ℓ` for `1 ≤ ℓ ≤ ℓ'` ("As in Bernstein's multiplication bound, M(n)/n is
   nondecreasing").

**Formalization Note** The paper fixes one deterministic multiplication algorithm with cost `M(n)`;
here the multiplication is an instruction and every statement quantifies over all admissible `M`. -/
def Admissible (M : ℕ → ℕ) : Prop :=
  (∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ M ℓ) ∧ (∀ ℓ ℓ' : ℕ, 1 ≤ ℓ → ℓ ≤ ℓ' → M ℓ * ℓ' ≤ M ℓ' * ℓ)

end CharPSComp


