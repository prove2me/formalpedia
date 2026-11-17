-- Prove2me | Definitions.Def_KAQROM_Supplement_Sampler
-- name    : KAQROM_Supplement_Sampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:52:07.518681+00:00
-- url     : https://prove2.me/theorems/30f0eda2-de77-456d-8ddd-5a6431d6e432
-- title:
--   Classical-query samplers, quantum distinguishers and $\mathrm{Adv}^{\mathrm{dist}}_{S_0,S_1,D}$
-- statement:
--   A **classical-query sampler** makes at most $q_S$ classical queries to $H$, may compute quantumly, and outputs a classical string $z$ in a finite sample space $Z$. A **quantum distinguisher** $D$ is, for each input $z$, a $q_D$-query quantum algorithm with an output bit. For two samplers and a distinguisher with acceptance probability $\Pr[D^H(z)=1]$,
--   $$
--   \mathrm{Adv}^{\mathrm{dist}}_{S_0,S_1,D}=\bigl|\Pr[D^H(S_1^H)=1]-\Pr[D^H(S_0^H)=1]\bigr|,
--   $$
--   where each probability samples a uniform $H$ and uses independent private randomness for the sampler and the distinguisher. The same formula applies to classical (randomized) distinguishers.
--
--   These are the objects of Theorem 7.3.
--
--   **Formalization Note** A sampler is a classical-query stage with trivial input, started in an arbitrary oracle-independent state.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.3, p.74

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_Supplement_CStage
import Definitions.Def_KAQROM_Supplement_DetAttacker

namespace KAQROM.Supplement

open Matrix
open KAQROM

/-- A **classical-query sampler** (Theorem 7.3, p.74): an algorithm that makes classical queries
to `H` (its local computation may be quantum) and outputs a classical string in the finite sample
space `Z`; a classical-query stage with trivial input, started in an oracle-independent state.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Theorem 7.3, p.74.

**Formalization Note.** The initial state is an arbitrary density operator (all-zero registers
followed by local preparation and private randomness). -/
structure Sampler (X : Type) [Fintype X] (ℓ : ℕ) (Z : Type) [Fintype Z] where
  /-- The sampler's register. -/
  R : Type
  /-- Kraus index type. -/
  ι : Type
  [fR : Fintype R] [dR : DecidableEq R] [fι : Fintype ι]
  /-- The number of classical query steps. -/
  D : ℕ
  /-- Initial state. -/
  ρ0 : Matrix R R ℂ
  ρ0_density : WildeQIT.IsDensityOperator ρ0
  /-- The sampling stage. -/
  S : CStage X ℓ Unit Z R ι D

attribute [instance] Sampler.fR Sampler.dR Sampler.fι

/-- `Pr[S^H = z]` given the oracle `H`. -/
noncomputable def Sampler.prob {X : Type} [Fintype X] {ℓ : ℕ} {Z : Type} [Fintype Z]
    (S : Sampler X ℓ Z) (H : Oracle X ℓ) (z : Z) : ℝ :=
  ∑ oq : Fin S.D → Option X, (S.S.run H () oq z S.ρ0).1.trace.re

/-- The sampler makes at most `q` classical queries on every oracle and every branch of positive
probability. -/
def Sampler.QueriesLe {X : Type} [Fintype X] {ℓ : ℕ} {Z : Type} [Fintype Z] (S : Sampler X ℓ Z)
    (q : ℕ) : Prop :=
  S.S.QueriesLe S.ρ0 q

/-- A **quantum distinguisher** on the sampled string: for each input `z` a `q`-query quantum
oracle algorithm with output bit, started from the trivial register. -/
structure QDist (X : Type) [Fintype X] [DecidableEq X] (ℓ : ℕ) (Z : Type) where
  /-- Work register. -/
  W : Type
  /-- Kraus index type. -/
  ι : Type
  [fW : Fintype W] [dW : DecidableEq W] [fι : Fintype ι]
  /-- The number of quantum queries `q_D`. -/
  q : ℕ
  /-- The algorithm run on input `z`. -/
  D : Z → QAlg X ℓ Unit W Unit Bool ι q

attribute [instance] QDist.fW QDist.dW QDist.fι

/-- `Pr[D^H(z) = 1]`. -/
noncomputable def QDist.prob {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Z : Type}
    (D : QDist X ℓ Z) (H : Oracle X ℓ) (z : Z) : ℝ :=
  ((D.D z).run H (1 : Matrix Unit Unit ℂ) true).trace.re

/-- **`Adv^{dist}_{S₀,S₁,D} = |Pr[D^H(S₁^H) = 1] − Pr[D^H(S₀^H) = 1]|`** (Theorem 7.3, p.74) for a
distinguisher given by its acceptance probability `acc H z`: each probability samples a uniform
`H` and uses independent private randomness for the sampler and the distinguisher. -/
noncomputable def advDist {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Z : Type} [Fintype Z]
    (S0 S1 : Sampler X ℓ Z) (acc : Oracle X ℓ → Z → ℝ) : ℝ :=
  |(Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ z : Z, S1.prob H z * acc H z -
    (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ z : Z, S0.prob H z * acc H z|

end KAQROM.Supplement


