-- Prove2me | Definitions.Def_ReplParity_Supplement_MeasureLearning
-- name    : ReplParity_Supplement_MeasureLearning
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:58:14.258168+00:00
-- url     : https://prove2.me/theorems/538179cb-597f-4823-9705-e7f70739773a
-- title:
--   Error, replicability (Definition 2.1) and realizable PAC learning (Definition 2.2) on an arbitrary measurable domain
-- statement:
--   Let $X$ be a measurable space and $D$ a probability measure on $X\times\{0,1\}$ (a labeled distribution). The error of $h:X\to\{0,1\}$ is $\mathrm{err}_D(h)=D\{(x,y):h(x)\ne y\}$.
--
--   A learner $A$ with sample size $m$ and a seed $r$ uniform on a nonempty finite set $\Omega$ is **$\rho$-replicable on every labeled distribution** if for every such $D$,
--   $$\frac1{|\Omega|}\sum_{r\in\Omega}(D^m\otimes D^m)\big\{(S,S'):A(S;r)\ne A(S';r)\big\}\le\rho .$$
--   It is **realizably $(\varepsilon,\delta)$-PAC** for a class $H$ if for every $D$ with $\mathrm{err}_D(h^\star)=0$ for some $h^\star\in H$,
--   $$\frac1{|\Omega|}\sum_{r\in\Omega}D^m\big\{S:A(S;r)=\bot\text{ or }\mathrm{err}_D(A(S;r))>\varepsilon\big\}\le\delta .$$
--
--   These are Definitions 2.1 and 2.2 for a general domain, as Theorem 7.1 requires.
--
--   **Formalization Note** The base mission's versions assume a finite domain; these take any measurable space and any probability measure. Measures of sets are outer measures, which agree with the measures for the measurable learners to which they are applied.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, Definitions 2.1-2.2, pp.10-11 (PDF pp.12-13)

import Mathlib

set_option autoImplicit false

namespace ReplParity

namespace Supplement

open MeasureTheory

/-- The error `err_D(h) = Pr_{(x,y)∼D}[h(x) ≠ y]` of `h : X → {0, 1}` under a labeled distribution
`D`, a probability measure on `X × ZMod 2` (§2.1, p.10). -/
noncomputable def errM {X : Type*} [MeasurableSpace X] (D : Measure (X × ZMod 2))
    (h : X → ZMod 2) : ℝ :=
  D.real {p | h p.1 ≠ p.2}

/-- **Definition 2.1 on an arbitrary measurable domain.** Shen, Zhong, *Replicable Parity Learning:
Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), Definition 2.1, p.10 (PDF p.12): "A learner A is ρ-replicable on every labeled
distribution if for every labeled distribution D, Pr_{S,S′∼D^m, r}[A(S; r) ≠ A(S′; r)] ≤ ρ, where S
and S′ are independent and the seed r is shared by the two runs. Outputs are compared exactly, as
elements of the output set."

`IsReplicableM A ρ`: for every probability measure `D` on `X × ZMod 2`,
`(1/|Ω|) ∑_r (D^m ⊗ D^m){(S, S′) : A(S; r) ≠ A(S′; r)} ≤ ρ`, the seed `r` uniform on the finite
nonempty finite type `Ω` and independent of `S, S′`.

**Formalization Note.** `X` is any measurable space (the base mission's `ReplParity.IsReplicable`
needs a finite `X`); `D^m` is `Measure.pi`. The measure of a set is `Measure.real`; the learners
this mission applies it to are measurable in the sample. -/
def IsReplicableM {X Ω β : Type*} [MeasurableSpace X] [Fintype Ω] [Nonempty Ω] {m : ℕ}
    (A : (Fin m → X × ZMod 2) → Ω → β) (ρ : ℝ) : Prop :=
  ∀ (D : Measure (X × ZMod 2)) [IsProbabilityMeasure D],
    (∑ r : Ω, ((Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => D)).real
        {p | A p.1 r ≠ A p.2 r}) / Fintype.card Ω ≤ ρ

/-- **Definition 2.2 on an arbitrary measurable domain.** Shen, Zhong, *Replicable Parity Learning:
Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), Definition 2.2, p.11 (PDF p.13): "Let H be a class of functions X → {0, 1}. A learner
is realizably (ε, δ)-PAC for H if for every labeled distribution D such that err_D(h⋆) = 0 for some
h⋆ ∈ H, Pr_{S∼D^m, r}[A(S; r) = ⊥ or err_D(A(S; r)) > ε] ≤ δ."

The learner returns `none` for `⊥` and `some h` for a hypothesis `h`; the seed is uniform on the
nonempty finite type `Ω`.

**Formalization Note.** `X` is any measurable space and `D` any probability measure on
`X × ZMod 2`. -/
def IsRealizablyPACM {X Ω : Type*} [MeasurableSpace X] [Fintype Ω] [Nonempty Ω]
    (H : Set (X → ZMod 2))
    {m : ℕ} (A : (Fin m → X × ZMod 2) → Ω → Option (X → ZMod 2)) (ε δ : ℝ) : Prop :=
  ∀ (D : Measure (X × ZMod 2)) [IsProbabilityMeasure D], (∃ h ∈ H, errM D h = 0) →
    (∑ r : Ω, (Measure.pi fun _ : Fin m => D).real
        {S | A S r = none ∨ ∃ h, A S r = some h ∧ ε < errM D h}) / Fintype.card Ω ≤ δ

end Supplement

end ReplParity


