-- Prove2me | Definitions.Def_CoverTime537_SpecifiedStart_Supplement_OracleClasses
-- name    : CoverTime537_SpecifiedStart_Supplement_OracleClasses
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:36:17.325761+00:00
-- url     : https://prove2.me/theorems/ccec7ab7-959e-4b8d-b1e3-c3d73a2cd625
-- title:
--   The class $\mathrm P^{\mathrm{NP}^{\mathrm{PP}}}$ on published oracle machines
-- statement:
--   On the published finite multitape oracle machines (with charged query writing), a language $L$ is in $\mathrm{NP}^A$ when one machine, with time bound $p(n)$ and certificate length $q(n)$ fixed polynomials, halts within $p(|x|)$ steps on every input $x$ and every certificate of length $q(|x|)$, and
--
--   $$x\in L\iff \exists w\in\{0,1\}^{q(|x|)}:\ \text{the machine with oracle }A\text{ accepts }(x,w).$$
--
--   A language $L$ is in $\mathrm P^{\mathrm{NP}^{\mathrm{PP}}}$ when there are languages $A\in\mathrm{PP}$ (no oracle) and $B\in\mathrm{NP}^A$ such that $L\in\mathrm P^B$. Here $\mathrm{PP}$ (strict majority) and $\mathrm P^B$ are the published definitions, and the counting hierarchy is the published one: $C_0\mathrm P=\mathrm P$, $C_{i+1}\mathrm P=\mathrm{PP}^{C_i\mathrm P}$, $\mathrm{CH}=\bigcup_i C_i\mathrm P$.
--
--   These classes state Theorem 3 of the paper.
--
--   **Formalization Note** Only the relativized NP predicate is new; it uses the same machines, configurations and polynomial bounds as the published PP and P predicates.
-- source:
--   Ryan Aghazadeh, How Hard Is It to Compute Cover Time?, STOC 2027 submission #537 (October 2026), papers/stoc2027-537/source.pdf, SHA-256 4487efe2e616b5ed1b0e9a8a4172a4b53fd492c5d9ad4717ed4921b088564fd8, p.3 (Theorem 3 and 'Here P^{NP^{PP}} denotes deterministic polynomial time with an NP^{PP} oracle'), Appendix C p.23 (definition of CH)

import Mathlib
import Definitions.Def_APSCounting893_Main_CountingHierarchy

namespace CoverTime537.SpecifiedStart.Supplement
open APSCounting893.Main

/-- NP relative to an oracle `A`, on the published finite oracle machines:
a uniform polynomial-time verifier with certificates of one exact polynomial
length (written on the random tape); `x ∈ L` iff some certificate is accepted. -/
def InOracleNP (A L : Language) : Prop :=
  ∃ (M : APSCounting893.Main.OracleMachine) (c d a b : ℕ), RunsInTime M A c d a b ∧
    ∀ x : Word, L x ↔ ∃ w : Word, w.length = polyBound a b x.length ∧
      (machineRun M A x w (polyBound c d x.length)).answer = some true

/-- `L ∈ P^{NP^{PP}}`: a deterministic polynomial-time decider with oracle `B`,
where `B ∈ NP^A` and `A ∈ PP` (unrelativized: the empty oracle). -/
def InPNPPP (L : Language) : Prop :=
  ∃ A B : Language, InOraclePP (fun _ => False) A ∧ InOracleNP A B ∧ InOracleP B L

end CoverTime537.SpecifiedStart.Supplement


