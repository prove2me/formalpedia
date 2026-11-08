-- Prove2me | Definitions.Def_QuadraticRE_SD
-- name    : QuadraticRE_SD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:00:07.343084+00:00
-- url     : https://prove2.me/theorems/b7ede924-0f4e-45a7-bfbc-2c3c5e611313
-- title:
--   Probability by counting, laws and statistical distance $\mathrm{SD}$
-- statement:
--   All probability spaces are finite. For a finite set $\Omega$ and an event $A\subseteq\Omega$, $\Pr_{\omega\leftarrow\Omega}[A]=|A|/|\Omega|$, the probability under the uniform distribution; the law of a map $g:\Omega\to Z$ is $z\mapsto\Pr_\omega[g(\omega)=z]$. A **law** on a finite set $Z$ is a nonnegative function of total mass one. The **statistical distance** between two laws $D,D'$ on $Z$ is
--   $$\mathrm{SD}(D,D')=\tfrac12\sum_{z\in Z}\bigl|D(z)-D'(z)\bigr| .$$
--   The field $\mathbb F_2$ is identified with the bits $\{0,1\}$.
--
--   These are the probabilistic primitives of every statement of the mission.
--
--   **Formalization Note** $\mathbb F_2$ is `ZMod 2`. Probabilities are real numbers computed as counts. The equality of $\mathrm{SD}$ with $\max_E(D(E)-D'(E))$, also printed on p.13, is a fact and is not part of the definition.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13

import Mathlib

namespace QuadraticRE

/-- The field `F₂` of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13; bits and `F₂` are identified. -/
abbrev F2 : Type := ZMod 2

open Classical in
/-- Probability over a uniform sample from a finite set, as a count: `#{ω | A ω} / #Ω`, in `ℝ`
(Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13).

**Formalization Note.** Every use has `Ω` nonempty (a tape `Fin ρ → F₂` is nonempty also at
`ρ = 0`, when it has one point); on an empty `Ω` the value is `0`. -/
noncomputable def prob {Ω : Type} [Fintype Ω] (A : Ω → Prop) : ℝ :=
  ((Finset.univ.filter A).card : ℝ) / (Fintype.card Ω : ℝ)

/-- The law of a map on a uniform sample: `z ↦ Pr_ω[g ω = z]`. -/
noncomputable def law {Ω Z : Type} [Fintype Ω] (g : Ω → Z) (z : Z) : ℝ :=
  prob (fun ω => g ω = z)

/-- A distribution on a finite set, as a nonnegative function of total mass one. -/
def IsLaw {Z : Type} [Fintype Z] (D : Z → ℝ) : Prop :=
  (∀ z, 0 ≤ D z) ∧ ∑ z, D z = 1

/-- Statistical distance Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), §3.1, p.13:
`SD(D, D′) = ½ ∑_z |D(z) − D′(z)|`.

**Formalization Note.** This is the first expression of the printed display; its equality with
`max_E (D(E) − D′(E))` is a fact about laws, checked in the verification file. -/
noncomputable def SD {Z : Type} [Fintype Z] (D D' : Z → ℝ) : ℝ :=
  (1 / 2) * ∑ z, |D z - D' z|

end QuadraticRE


