-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_NUProver
-- name    : QAdvFew_PoQOracle_NUProver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:51:16.014113+00:00
-- url     : https://prove2.me/theorems/cfadb1b7-51a9-4412-b291-bf0710e43715
-- title:
--   Nonuniform PPT classical prover
-- statement:
--   A **nonuniform PPT classical prover** draws coins $r\in\{0,1\}^{\rho(n)}$ and computes its message of round $j$ by an oracle circuit from $r$ and all messages so far, every circuit of size at most $p(n)$ for a polynomial $p$. Its likelihood $w_P(\tau)$ is the fraction of coin strings with which it sends exactly its messages of $\tau$.
--
--   The circuits are quantified after the oracle, so they may depend on it.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Definition 3.26, p. 19 (PDF p. 21); §3.2.1, p. 12 (PDF p. 14)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Circuit
import Definitions.Def_QAdvFew_PoQOracle_Protocol

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A **nonuniform PPT classical prover** for a protocol with message length `ℓ(n)` (Goldin,
Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
Definition 3.26, p. 19 (PDF p. 21): "For every nonuniform PPT classical prover `P^{∗O}`"; §3.2.1,
p. 12): at length `n` it draws coins `r ∈ {0,1}^{ρ(n)}` and computes its message of round `j` with
an oracle circuit `C n j` from `r` and the `(2j + 1)ℓ(n)` bits of the messages so far, every
circuit of size at most `p(n)`.

**Formalization Note** The circuits are quantified after the oracle and may depend on it. Giving
the circuit all earlier messages (its own included) loses nothing. -/
structure NUProver (ℓ : ℕ → ℕ) where
  /-- number of coins at length `n` -/
  ρ : ℕ → ℕ
  /-- the circuit computing the message of round `j` at length `n` -/
  C : (n j : ℕ) → Circuit (Fin (ρ n) ⊕ Fin ((2 * j + 1) * ℓ n))
  /-- the size bound -/
  p : Polynomial ℕ
  size_le : ∀ n j : ℕ, (C n j).size ≤ p.eval n

namespace NUProver

variable {ℓ : ℕ → ℕ}

/-- The prover's likelihood `w_P(τ)`: the fraction of coin strings with which it sends exactly its
messages of `τ`. -/
noncomputable def lik (P : NUProver ℓ) (O : Oracle) (n : ℕ) {R : ℕ} (τ : Transcript R (ℓ n)) : ℝ :=
  ((Finset.univ.filter (fun r : Fin (P.ρ n) → Bool =>
      ∀ j : Fin R, (P.C n j).eval O
          (Sum.elim r (fun i => ((τ.prefixP j).flatten).getD i false)) = List.ofFn (τ j).2)).card :
      ℝ) / (2 ^ P.ρ n : ℝ)

end NUProver

end QAdvFew.PoQOracle


