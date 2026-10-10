-- Prove2me | Definitions.Def_FirstLawThermo_Defs
-- name    : FirstLawThermo_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:25:03.145242+00:00
-- url     : https://prove2.me/theorems/e7afd934-50b5-425f-bde8-db9bd6000bb3
-- title:
--   First law of thermodynamics: processes, adiabatic work, internal energy and heat
-- statement:
--   This definition file fixes the vocabulary for the mission. Throughout, $\sigma$ is the type of states of a closed system.
--
--   1. **Process.** A process $p$ consists of an initial state $p_{\mathrm{start}}\in\sigma$, a final state $p_{\mathrm{finish}}\in\sigma$, the net work $W(p)\in\mathbb R$ done *by* the system on its surroundings (Clausius sign convention), and a proposition "$p$ is adiabatic" (the process takes place inside an adiabatic enclosure).
--   2. **Composition.** For processes $p,q$, the composite $p\cdot q$ ("first $p$, then $q$") starts at $p_{\mathrm{start}}$, ends at $q_{\mathrm{finish}}$, has work $W(p)+W(q)$, and is adiabatic iff both $p$ and $q$ are.
--   3. **Null process** at $A$: start and finish $A$, work $0$, adiabatic.
--   4. **Cyclic**: $p_{\mathrm{start}}=p_{\mathrm{finish}}$. **Adynamic**: $W(p)=0$.
--   5. For a set $\mathcal P$ of processes (the realizable ones):
--      * $\mathcal P$ is *closed under composition* if $p,q\in\mathcal P$ and $p_{\mathrm{finish}}=q_{\mathrm{start}}$ imply $p\cdot q\in\mathcal P$;
--      * $\mathcal P$ *contains the null processes* if the null process at every state lies in $\mathcal P$;
--      * *adiabatic work is path independent* in $\mathcal P$ if any two adiabatic $p,q\in\mathcal P$ with the same start and the same finish have $W(p)=W(q)$;
--      * $\mathcal P$ *adiabatically links every state to $O$* if for every $A$ there is an adiabatic $p\in\mathcal P$ going from $O$ to $A$ or from $A$ to $O$.
--   6. **Internal energy.** $U:\sigma\to\mathbb R$ is an internal energy for $\mathcal P$ if
--   $$U(p_{\mathrm{finish}})-U(p_{\mathrm{start}})=-W(p)\quad\text{for every adiabatic } p\in\mathcal P.$$
--   7. **Heat** (Born's definition, as a residual): for $U:\sigma\to\mathbb R$,
--   $$Q_U(p)=U(p_{\mathrm{finish}})-U(p_{\mathrm{start}})+W(p).$$
--
--   These are the objects in terms of which all theorems of the mission are stated.
--
--   **Formalization Note** Work is work done *by* the system, so the Clausius form $\Delta U=Q-W$ is the one that holds. "Adiabatic" is a primitive proposition attached to each process, and heat is a derived quantity depending on the chosen internal energy $U$.
-- source:
--   Wikipedia, "First law of thermodynamics", revision oldid=1366986255, https://en.wikipedia.org/w/index.php?title=First_law_of_thermodynamics&oldid=1366986255; Section "Conceptual revision: the mechanical approach" and "Conceptually revised statement, according to the mechanical approach" (adiabatic walls primitive; heat defined as a residual, following Born); Section "Definition" (Clausius sign convention, $\Delta U = Q - W$); Section "Evidence for the first law of thermodynamics for closed systems", subsections "Adiabatic processes" and "Adynamic processes"; Section "Description: Cyclic processes".

import Mathlib

namespace FirstLawThermo

/-- A process undergone by a closed system (no transfer of matter) whose states form the type
`σ`. It records the initial state `start`, the final state `finish`, the net work `work` done
*by* the system on its surroundings during the process (Clausius sign convention: work done by
the system is positive), and whether the process is `adiabatic`, i.e. carried out with the
system enclosed by adiabatic walls, so that energy is transferred only as work. -/
structure Process (σ : Type*) where
  /-- The initial state of the process. -/
  start : σ
  /-- The final state of the process. -/
  finish : σ
  /-- The net work done by the system on its surroundings (Clausius sign convention). -/
  work : ℝ
  /-- The process takes place inside an adiabatic enclosure. -/
  adiabatic : Prop

namespace Process

variable {σ : Type*}

/-- Sequential composition of two stages: first `p`, then `q`. It is intended for
`p.finish = q.start`; the composite starts where `p` starts, ends where `q` ends, the work done
is the sum of the works of the stages, and it is adiabatic exactly when both stages are. -/
def comp (p q : Process σ) : Process σ where
  start := p.start
  finish := q.finish
  work := p.work + q.work
  adiabatic := p.adiabatic ∧ q.adiabatic

/-- The null process at the state `A`: the system is left in state `A`, no work is done, and
no energy is exchanged (so it is in particular adiabatic). -/
def null (A : σ) : Process σ where
  start := A
  finish := A
  work := 0
  adiabatic := True

/-- A process is cyclic if it returns the system to its initial state. -/
def IsCyclic (p : Process σ) : Prop :=
  p.start = p.finish

/-- A process is adynamic if no energy is transferred as work. -/
def IsAdynamic (p : Process σ) : Prop :=
  p.work = 0

end Process

variable {σ : Type*}

/-- The set `procs` of physically realizable processes is closed under sequential composition
of consecutive stages. -/
def ClosedUnderComp (procs : Set (Process σ)) : Prop :=
  ∀ p ∈ procs, ∀ q ∈ procs, p.finish = q.start → p.comp q ∈ procs

/-- Every null process belongs to `procs` (leaving the system alone is realizable). -/
def ContainsNull (procs : Set (Process σ)) : Prop :=
  ∀ A : σ, Process.null A ∈ procs

/-- Path independence of adiabatic work: any two adiabatic processes in `procs` with the same
initial state and the same final state involve the same net work, however the work is done. -/
def AdiabaticWorkPathIndependent (procs : Set (Process σ)) : Prop :=
  ∀ p ∈ procs, ∀ q ∈ procs, p.adiabatic → q.adiabatic →
    p.start = q.start → p.finish = q.finish → p.work = q.work

/-- Every state `A` is linked to the reference state `O` by an adiabatic process in `procs`,
in at least one of the two directions (from `O` to `A`, or from `A` to `O`). -/
def AdiabaticallyLinkedTo (procs : Set (Process σ)) (O : σ) : Prop :=
  ∀ A : σ, ∃ p ∈ procs, p.adiabatic ∧
    ((p.start = O ∧ p.finish = A) ∨ (p.start = A ∧ p.finish = O))

/-- `U : σ → ℝ` is an internal energy function for `procs`: for every adiabatic process in
`procs`, the change of `U` equals minus the work done by the system,
`U(finish) - U(start) = -W`. -/
def IsInternalEnergy (procs : Set (Process σ)) (U : σ → ℝ) : Prop :=
  ∀ p ∈ procs, p.adiabatic → U p.finish - U p.start = -p.work

/-- The heat supplied to the system in the process `p`, defined (following Born) as the residual
`Q = ΔU + W`: the change of the internal energy `U` not accounted for by the work `W` done by
the system. -/
def heat (U : σ → ℝ) (p : Process σ) : ℝ :=
  U p.finish - U p.start + p.work

end FirstLawThermo


