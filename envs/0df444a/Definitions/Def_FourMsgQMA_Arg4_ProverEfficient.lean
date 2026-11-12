-- Prove2me | Definitions.Def_FourMsgQMA_Arg4_ProverEfficient
-- name    : FourMsgQMA_Arg4_ProverEfficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:37:16.727193+00:00
-- url     : https://prove2.me/theorems/b9942094-8034-45ad-a053-630fae600ee9
-- title:
--   Honest prover efficiency: polynomial work and polynomially many witness copies
-- statement:
--   An argument's honest prover is **efficient** for $F$ if there is a polynomial $p$ with two properties. For every $\lambda$, admissible $u$ and authorized $y$, the generated core has size (qubits, tape, rounds, wires, gates) at most $p(\lambda,t(X),k,s)$. The copy count satisfies $N(\lambda,t)\le p(\lambda,t,0,0)$.
--
--   This is "The honest prover has polynomial total work and uses polynomially many copies of the selected QMA witnesses" (Corollary 5.15) and "The honest prover has work $\mathrm{poly}(\lambda,T,k,s)$" (§5.1).
--
--   **Formalization Note** Pinned-down version (operator request). The controllers' work is polynomial by uniformity.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.3, p.12 (PDF 14); §5.1, p.38 (PDF 40); Corollary 5.15, p.44 (PDF 46)

import Mathlib
import Definitions.Def_FourMsgQMA_Arg4

namespace FourMsgQMA

open QAlgorithms.Complexity TightPQRepetition.Main

/-- Honest prover efficiency (§3.3, p.12; Corollary 5.15, p.44: "The honest prover has polynomial
total work and uses polynomially many copies of the selected QMA witnesses"; §5.1, p.38: "The
honest prover has work poly(λ, T, k, s)"). There is a polynomial `p` such that the honest core
generated for any admissible instance and authorized `y` has size at most `p(λ, t(X), k, s)`, and
the number of copies of each selected witness is `N(λ, t) ≤ p(λ, t, 0, 0)`.

**Formalization Note** Pinned-down version (operator request): work is the size of the quantum
core (qubits, tape, rounds, wires, gates); the controllers' work is polynomial by
`Arg4.IsUniform`. -/
def Arg4.ProverEfficient (A : Arg4) (F : QMAFamily) : Prop :=
  ∃ p : MvPolynomial (Fin 4) ℕ,
    (∀ (lam : ℕ) (u : Inst) (y : Fin u.k → Bool), u.Admissible → u.C.eval y = true →
      (A.core lam u.encode (u.classicalWitness y)).size ≤ eval4 p lam (batchCost F u) u.k u.s) ∧
    ∀ lam t : ℕ, A.copies lam t ≤ eval4 p lam t 0 0

end FourMsgQMA


