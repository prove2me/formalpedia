-- Prove2me | Definitions.Def_PersistQMem_Supplement_Achievable
-- name    : PersistQMem_Supplement_Achievable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:13:58.963205+00:00
-- url     : https://prove2.me/theorems/feafdccf-caa6-4944-b25c-7c64b5feef03
-- title:
--   Achievable copy cap for simultaneous signed estimation
-- statement:
--   Fix a finite family of Hermitian observables $G=(G_j)_{j\in J}$ on a $D$-dimensional source. A worst-case copy cap $N$ is **achievable** with retained quantum dimension at most $K$ and error $\epsilon$ if there is a source-independent persistent-memory protocol using $N$ accesses, followed by a measurable terminal POVM whose real-vector output is $\widehat\mu=(\widehat\mu_j)_{j\in J}$, such that for every density matrix $\rho$,
--
--   $$
--   \Pr_\rho\!\left[\max_{j\in J}|\widehat\mu_j-\operatorname{Tr}(\rho G_j)|\le\epsilon\right]\ge\frac23.
--   $$
--
--   The protocol may use an arbitrary measurable classical record space, adaptive complete instruments, and unlimited classical records. Every quantum register retained between accesses counts toward the single dimension cap $K$.
--
--   **Formalization Note** The published `PersistQMem.Protocol` supplies the adaptive receiver. As for the round instruments, the final POVM is represented by a jointly measurable positive density against an s-finite reference kernel, now on the full real-vector output space. Integrability is required explicitly, preventing a Bochner integral from defaulting to zero.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Definition 5.1, p.15 (PDF p.18)

import Mathlib
import Definitions.Def_PersistQMem_Protocol

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder

namespace PersistQMem
namespace Supplement

/-- A measurable real-vector estimator attached to a published persistent-memory protocol.

After `N` source accesses, the classical history and retained memory are measured with a POVM
density `Q`; the outcome `muHat : J -> Real` is the requested real output vector.  This is
Definition 5.1 in Tao--Shen, *Structural Lower Bounds for Quantum Property Estimation with
Persistent Memory*, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24...), p.15
(PDF p.18).

**Formalization Note.** The terminal POVM is represented, just like the round instruments in
`Protocol`, by a jointly measurable positive density against an s-finite reference kernel.  Taking
the output space itself to be `J -> Real` retains Definition 5.1's unrestricted real outputs rather
than imposing a finite-output restriction.  The integrability fields prevent Lean's Bochner integral
from silently taking the value zero. -/
structure SignedEstimator (J X L : Type) [Fintype J] [MeasurableSpace X] [Fintype L]
    (K D N : Nat) where
  protocol : Protocol X L K D
  terminalKernel : Kernel (Fin N -> X) (J -> Real)
  terminal_sfinite : IsSFiniteKernel terminalKernel
  Q : (Fin N -> X) -> (J -> Real) -> Matrix (Fin K) (Fin K) Complex
  Q_measurable : forall i j,
    Measurable (fun q : (Fin N -> X) × (J -> Real) => Q q.1 q.2 i j)
  Q_effect : forall h muHat, (Q h muHat).PosSemidef
  Q_complete_integrable : forall h i j,
    Integrable (fun muHat => Q h muHat i j) (terminalKernel h)
  Q_complete : forall h i j,
    ∫ muHat, Q h muHat i j ∂(terminalKernel h) =
      (1 : Matrix (Fin K) (Fin K) Complex) i j
  Q_integrable : forall rho : Matrix (Fin D) (Fin D) Complex,
    WildeQIT.IsDensityOperator rho ->
    Integrable
      (fun q : (Fin N -> X) × (J -> Real) =>
        (Q q.1 q.2 * branch protocol rho N q.1).trace.re)
      ((refMeasure protocol N) ⊗ₘ (terminalKernel))

variable {J X L : Type} [Fintype J] [MeasurableSpace X] [Fintype L]
variable {K D N : Nat}

/-- Probability that every requested expectation is estimated to additive error at most `epsilon`. -/
noncomputable def simultaneousSuccess (E : SignedEstimator J X L K D N)
    (G : J -> Matrix (Fin D) (Fin D) Complex) (epsilon : Real)
    (rho : Matrix (Fin D) (Fin D) Complex) : Real :=
  ∫ q, if (forall j, abs (q.2 j - (rho * G j).trace.re) <= epsilon)
    then (E.Q q.1 q.2 * branch E.protocol rho N q.1).trace.re else 0
    ∂((refMeasure E.protocol N) ⊗ₘ (E.terminalKernel))

/-- The estimator solves the simultaneous signed task with success probability at least `2/3` for
every density matrix, as in Definition 5.1 and the standing convention of Sections 2.2--2.4. -/
def SolvesSignedTask (E : SignedEstimator J X L K D N)
    (G : J -> Matrix (Fin D) (Fin D) Complex) (epsilon : Real) : Prop :=
  forall rho, WildeQIT.IsDensityOperator rho ->
    (2 : Real) / 3 <= simultaneousSuccess E G epsilon rho

/-- A worst-case copy cap `N` is achievable for the simultaneous signed-estimation task with retained
dimension at most `K`.  The existential record space, adaptive instrument, terminal POVM and decoder
are all chosen before the unknown source state.

**Formalization Note.** `Protocol` uses exactly `N` rounds; early stopping is represented by idle
rounds, as on p.15.  A receiver of smaller retained dimension embeds into `C^K`; theorem statements
also record the dimension-one upper-bound witnesses explicitly. -/
def Achievable (G : J -> Matrix (Fin D) (Fin D) Complex) (K : Nat) (epsilon : Real)
    (N : Nat) : Prop :=
  exists (X : Type) (mX : MeasurableSpace X) (L : Type) (fL : Fintype L),
    exists E : @SignedEstimator J X L inferInstance mX fL K D N,
      @SolvesSignedTask J X L inferInstance mX fL K D N E G epsilon

end Supplement
end PersistQMem


