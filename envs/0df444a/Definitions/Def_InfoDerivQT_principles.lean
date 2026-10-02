-- Prove2me | Definitions.Def_InfoDerivQT_principles
-- name    : InfoDerivQT_principles
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T09:01:15.003985+00:00
-- url     : https://prove2.me/theorems/aa8cb6e0-a5dc-4fb3-90ac-0e3307a0e793
-- title:
--   The six principles: Axioms 1–5 and the purification postulate
-- statement:
--   The six principles of the paper, for an operational-probabilistic theory $T$.
--
--   1. **Causality (Axiom 1).** For every preparation test $\{\rho_i\}$ and observation tests $\{a_j\}$, $\{b_k\}$ of the same system, $\sum_j(a_j|\rho_i)=\sum_k(b_k|\rho_i)$ for every $i$.
--   2. **Perfect distinguishability (Axiom 2).** Every normalized state that is not completely mixed is perfectly distinguishable from some other normalized state.
--   3. **Ideal compression (Axiom 3).** For every normalized state $\rho$ of $A$ there are a system $C$ with $D_C\le D_A$, an encoding $\mathcal E\in\mathrm{Transf}(A,C)$ and a decoding $\mathcal D\in\mathrm{Transf}(C,A)$ with $\mathcal D\mathcal E\sigma=\sigma$ for all $\sigma\in F_\rho$ (lossless) and such that every normalized state of $C$ equals $\mathcal E\sigma$ for some $\sigma\in F_\rho$ (maximally efficient).
--   4. **Local distinguishability (Axiom 4).** If $\rho\neq\sigma$ are normalized states of $AB$, there are effects $a$ of $A$ and $b$ of $B$ with $(a\otimes b|\rho)\neq(a\otimes b|\sigma)$.
--   5. **Pure conditioning (Axiom 5).** If $\Psi$ is a pure normalized state of $AB$ and $\{a_i\}$ is an observation test on $A$ made of atomic effects, every induced state $(a_i|_A|\Psi)_{AB}$ of $B$ is pure; and symmetrically for atomic observation tests on $B$.
--   6. **Purification (Postulate 1).** Every normalized state $\rho$ of $A$ has a purification: a pure normalized state $\Psi$ of some $AB$ whose marginal $(e|_B|\Psi)_{AB}$ under a deterministic effect $e$ of $B$ is $\rho$. If $\Psi,\Psi'$ are purifications of the same $\rho$ with the same purifying system $B$, then $\Psi'=(\mathcal I_A\otimes\mathcal U)\Psi$ for some reversible transformation $\mathcal U$ of $B$.
--
--   `SatisfiesPrinciples` is the conjunction of the six.
--
--   **Formalization Note** The marginal in Postulate 1 is taken with any deterministic effect of $B$; under causality the deterministic effect is unique.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), pp. 012311-7 to 012311-9, Sec. III: Axioms 1–5 and Postulate 1

import Mathlib
import Definitions.Def_InfoDerivQT_framework

namespace InfoDerivQT

namespace OPT

variable (T : OPT)

/-- Axiom 1 (Causality): the marginal probability `∑ⱼ (aⱼ|ρᵢ)` of a preparation outcome does
not depend on the choice of the observation test `{aⱼ}`. -/
def Causal : Prop :=
  ∀ (A : T.Sys) (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
    (ρ : X → Vec (T.size A)) (a : Y → Module.Dual ℝ (Vec (T.size A)))
    (b : Z → Module.Dual ℝ (Vec (T.size A))),
    ρ ∈ T.PrepTest A X → a ∈ T.ObsTest A Y → b ∈ T.ObsTest A Z →
    ∀ i, ∑ j, a j (ρ i) = ∑ k, b k (ρ i)

/-- Axiom 2 (Perfect distinguishability): every normalized state that is not completely mixed
can be perfectly distinguished from some other normalized state. -/
def PerfectDistinguishabilityAxiom : Prop :=
  ∀ (A : T.Sys) (ρ : Vec (T.size A)), ρ ∈ T.St1 A → ¬ T.IsCompletelyMixed A ρ →
    ∃ σ ∈ T.St1 A, T.PerfectlyDistinguishable A ![ρ, σ]

/-- An ideal compression scheme for the normalized state `ρ` of `A` into the system `C`:
an encoding `E ∈ Transf(A,C)` and a decoding `D ∈ Transf(C,A)` with `D_C ≤ D_A`, which is
lossless (`D E σ = σ` for all `σ ∈ F_ρ`) and maximally efficient (every normalized state of
`C` is `E σ` for some `σ ∈ F_ρ`). -/
def IsIdealCompression (A C : T.Sys) (ρ : Vec (T.size A))
    (E : Vec (T.size A) →ₗ[ℝ] Vec (T.size C)) (D : Vec (T.size C) →ₗ[ℝ] Vec (T.size A)) :
    Prop :=
  E ∈ T.Transf A C ∧ D ∈ T.Transf C A ∧ T.size C ≤ T.size A ∧
    (∀ σ ∈ T.face A ρ, D (E σ) = σ) ∧
    (∀ τ ∈ T.St1 C, ∃ σ ∈ T.face A ρ, E σ = τ)

/-- Axiom 3 (Ideal compression): every normalized state admits an ideal compression scheme. -/
def IdealCompressionAxiom : Prop :=
  ∀ (A : T.Sys) (ρ : Vec (T.size A)), ρ ∈ T.St1 A →
    ∃ (C : T.Sys) (E : Vec (T.size A) →ₗ[ℝ] Vec (T.size C))
      (D : Vec (T.size C) →ₗ[ℝ] Vec (T.size A)), T.IsIdealCompression A C ρ E D

/-- Axiom 4 (Local distinguishability): two different normalized states of `AB` give
different probabilities for at least one product effect `a ⊗ b`. -/
def LocalDistinguishability : Prop :=
  ∀ (A B : T.Sys) (ρ σ : Vec (T.size (T.comp A B))), ρ ∈ T.St1 (T.comp A B) →
    σ ∈ T.St1 (T.comp A B) → ρ ≠ σ →
    ∃ a ∈ T.Eff A, ∃ b ∈ T.Eff B, T.tensorEff (A := A) (B := B) a b ρ ≠ T.tensorEff (A := A) (B := B) a b σ

/-- Axiom 5 (Pure conditioning): if `Ψ` is a pure normalized state of `AB` and `{aᵢ}` is an
atomic observation test on one side, then each induced state on the other side is pure. -/
def PureConditioning : Prop :=
  ∀ (A B : T.Sys) (Ψ : Vec (T.size (T.comp A B))) (X : Type) [Fintype X],
    Ψ ∈ T.St1 (T.comp A B) → T.IsPure (T.comp A B) Ψ →
    (∀ a : X → Module.Dual ℝ (Vec (T.size A)), a ∈ T.ObsTest A X →
      (∀ i, T.IsAtomicEff A (a i)) → ∀ i, T.IsPure B (T.condL (A := A) (B := B) (a i) Ψ)) ∧
    (∀ b : X → Module.Dual ℝ (Vec (T.size B)), b ∈ T.ObsTest B X →
      (∀ i, T.IsAtomicEff B (b i)) → ∀ i, T.IsPure A (T.condR (A := A) (B := B) (b i) Ψ))

/-- `Ψ ∈ St₁(AB)` is a purification of `ρ ∈ St₁(A)` (with purifying system `B`): `Ψ` is pure
and its marginal on `A`, obtained by applying a deterministic effect on `B`, is `ρ`. -/
def IsPurification (A B : T.Sys) (ρ : Vec (T.size A)) (Ψ : Vec (T.size (T.comp A B))) :
    Prop :=
  Ψ ∈ T.St1 (T.comp A B) ∧ T.IsPure (T.comp A B) Ψ ∧ ∃ e ∈ T.DetEff B, T.condR (A := A) (B := B) e Ψ = ρ

/-- Postulate 1 (Purification): every normalized state has a purification, and, for a fixed
purifying system `B`, any two purifications of the same state are connected by a reversible
transformation on `B`. -/
def Purification : Prop :=
  (∀ (A : T.Sys) (ρ : Vec (T.size A)), ρ ∈ T.St1 A →
    ∃ (B : T.Sys) (Ψ : Vec (T.size (T.comp A B))), T.IsPurification A B ρ Ψ) ∧
  (∀ (A B : T.Sys) (ρ : Vec (T.size A)) (Ψ Ψ' : Vec (T.size (T.comp A B))),
    T.IsPurification A B ρ Ψ → T.IsPurification A B ρ Ψ' →
    ∃ U : Vec (T.size B) →ₗ[ℝ] Vec (T.size B), T.IsReversible B B U ∧
      T.tensorT (A := A) (B := A) (A' := B) (B' := B) LinearMap.id U Ψ = Ψ')

/-- The six principles of the paper: Axioms 1–5 and Postulate 1. -/
structure SatisfiesPrinciples : Prop where
  causal : T.Causal
  perfectDistinguishability : T.PerfectDistinguishabilityAxiom
  idealCompression : T.IdealCompressionAxiom
  localDistinguishability : T.LocalDistinguishability
  pureConditioning : T.PureConditioning
  purification : T.Purification

end OPT

end InfoDerivQT


