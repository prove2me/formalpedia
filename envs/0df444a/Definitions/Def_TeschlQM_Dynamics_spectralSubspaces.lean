-- Prove2me | Definitions.Def_TeschlQM_Dynamics_spectralSubspaces
-- name    : TeschlQM_Dynamics_spectralSubspaces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T06:32:52.143434+00:00
-- url     : https://prove2.me/theorems/126ddb5e-8f4c-447d-9d4e-2c27f6722f32
-- title:
--   Spectral subspaces ℌ_ac, ℌ_sc, ℌ_pp, ℌ_c (3.83) and their projectors
-- statement:
--   Let $P$ be a projection-valued measure on $\mathfrak H$ with spectral measures $\mu_\psi$. Following the decomposition of a Borel measure into absolutely continuous, singularly continuous and pure point parts, define
--   $$\mathfrak H_{ac} = \{\psi \mid \mu_\psi \text{ is absolutely continuous}\},\quad \mathfrak H_{sc} = \{\psi \mid \mu_\psi \text{ is singularly continuous}\},\quad \mathfrak H_{pp} = \{\psi \mid \mu_\psi \text{ is pure point}\}.$$
--   Here $\mu_\psi$ is absolutely continuous if it is absolutely continuous with respect to Lebesgue measure; singularly continuous if it is singular with respect to Lebesgue measure and has no atoms ($\mu_\psi(\{x\}) = 0$ for all $x$); and pure point if it is supported on a countable set. The **continuous subspace** is $\mathfrak H_c = \mathfrak H_{ac} \oplus \mathfrak H_{sc}$, the set of sums $a + s$ with $a \in \mathfrak H_{ac}$, $s \in \mathfrak H_{sc}$. These subspaces are closed and $\mathfrak H = \mathfrak H_{ac} \oplus \mathfrak H_{sc} \oplus \mathfrak H_{pp}$ (Lemma 3.19). The projectors $P^{ac}, P^{c}, P^{pp}$ are the orthogonal projections onto $\mathfrak H_{ac}, \mathfrak H_c, \mathfrak H_{pp}$.
--
--   **Formalization Note.** `hac`, `hsc`, `hpp`, `hc` are sets of vectors defined from the spectral measures only. `orthProj S` is the orthogonal projection onto the closed linear span of a set `S`; for the four spectral subspaces, which are closed subspaces, this is the orthogonal projection onto the subspace itself.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 105, Section 3.3, Eq. (3.83); p. 102, Eqs. (3.72)–(3.73); p. 127

import Mathlib
import Definitions.Def_TeschlQM_Shared_spectralMeasure

open MeasureTheory

namespace TeschlQM.Dynamics

/-- Teschl, p. 105, (3.83): `ℌ_ac = {ψ ∈ ℌ | μ_ψ is absolutely continuous}` (with respect to
Lebesgue measure, p. 102, (3.72)). -/
def hac {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Set H :=
  {ψ | TeschlQM.Shared.spectralMeasure P ψ ≪ volume}

/-- Teschl, p. 105, (3.83): `ℌ_sc = {ψ ∈ ℌ | μ_ψ is singularly continuous}`: by pp. 102,
(3.72)–(3.73), `μ_ψ` is singular with respect to Lebesgue measure and continuous, i.e. it has
no atoms. -/
def hsc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Set H :=
  {ψ | TeschlQM.Shared.spectralMeasure P ψ ⟂ₘ volume ∧ ∀ x : ℝ, TeschlQM.Shared.spectralMeasure P ψ {x} = 0}

/-- Teschl, p. 105, (3.83): `ℌ_pp = {ψ ∈ ℌ | μ_ψ is pure point}`: by p. 102, (3.73), `μ_ψ` is a
pure point (step function) measure, i.e. it is supported on a countable set. -/
def hpp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Set H :=
  {ψ | ∃ S : Set ℝ, S.Countable ∧ TeschlQM.Shared.spectralMeasure P ψ Sᶜ = 0}

/-- Teschl, p. 127: the **continuous subspace** `ℌ_c = ℌ_ac ⊕ ℌ_sc`, the set of sums of a vector
of `ℌ_ac` and a vector of `ℌ_sc` (the two subspaces are orthogonal by Lemma 3.19, p. 105). -/
def hc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) : Set H :=
  {ψ | ∃ a ∈ hac P, ∃ s ∈ hsc P, ψ = a + s}

/-- The orthogonal projection of `ℌ` onto the closed linear span of a set `S ⊆ ℌ`. Applied to
`ℌ_ac`, `ℌ_c`, `ℌ_pp`, which are closed subspaces (Lemma 3.19, p. 105), this is the projector
`P^ac`, `P^c`, `P^pp` of Teschl, pp. 102–105. -/
noncomputable def orthProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set H) : H →L[ℂ] H :=
  ((Submodule.span ℂ S).closure : Submodule ℂ H).starProjection

end TeschlQM.Dynamics


