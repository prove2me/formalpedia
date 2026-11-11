-- Prove2me | Definitions.Def_KAQROM_QAlg
-- name    : KAQROM_QAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:42.791224+00:00
-- url     : https://prove2.me/theorems/b080120d-9a9d-44c8-a401-4d8f69f3a0c8
-- title:
--   $q$-query quantum oracle algorithms
-- statement:
--   A **$q$-query quantum oracle algorithm** from an input register $R_{\mathrm{in}}$ to an output register $R_{\mathrm{out}}$ with classical outcomes in $O$ consists of an initial channel $\Phi_0$ from $R_{\mathrm{in}}$ into a query register $X$, a response register $Y$ and a work register $W$; channels $\Phi_1,\dots,\Phi_q$ on $XYW$; and a final instrument $\mathcal M$ from $XYW$ to $R_{\mathrm{out}}$ with outcomes in $O$. With oracle $H$ and input $\rho$, outcome $o$ occurs with the unnormalized output state
--   $$
--   \mathcal M_o\bigl(\Phi_q(U_H\cdots\Phi_1(U_H\,\Phi_0(\rho)\,U_H^\dagger)\cdots U_H^\dagger)\bigr).
--   $$
--
--   This is the paper's quantum oracle algorithm (Definition 3.1) with query bound $q$, used for Bob's final stage $\mathcal B_{\mathsf q}$, Alice's final stage $\mathcal A_{\mathsf{fin}}$, Eve's final stage, and the distinguisher of the reprogramming lemma.
--
--   **Formalization Note** Arbitrary channels between queries stand for the oracle-independent operations of unbounded algorithms. An algorithm making at most $q$ queries is represented with exactly $q$ query rounds: a query on the response state $|+\rangle^{\otimes\ell}$ acts as the identity, so idle queries pad.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.1, p.16

import Mathlib
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle

namespace KAQROM

open Matrix

/-- A **`q`-query quantum oracle algorithm** (Definition 3.1, p.16) from input register `Rin` to
output register `Rout`, with classical output in `O`: an initial channel into the query register
`X`, the response register `Y = {0,1}^ℓ` and a work register `W`; then `q` rounds, each one query
`U_H` followed by an oracle-independent channel; then a final instrument with outcomes `O`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.1,
p.16.

**Formalization Note.** Arbitrary channels between queries stand for the paper's
oracle-independent operations (computationally unbounded parties; Stinespring). An algorithm
with "at most `q`" queries is one with exactly `q` query rounds: a query on the response state
`|+⟩^{⊗ℓ}` acts as the identity, so idle queries can pad any algorithm to exactly `q`. -/
structure QAlg (X : Type) [Fintype X] (ℓ : ℕ) (Rin W Rout O ι : Type) [Fintype Rin] [Fintype W]
    [Fintype Rout] [Fintype O] [Fintype ι] [DecidableEq Rin] [DecidableEq X] [DecidableEq W]
    (q : ℕ) where
  /-- Initial channel from the input register into the query, response and work registers. -/
  init : Instrument Unit Rin (X × Bits ℓ × W) ι
  /-- The channel applied after the `k`-th query. -/
  step : Fin q → Instrument Unit (X × Bits ℓ × W) (X × Bits ℓ × W) ι
  /-- The final measurement, with classical outcome in `O` and remaining register `Rout`. -/
  final : Instrument O (X × Bits ℓ × W) Rout ι

/-- The unnormalized output of a `q`-query algorithm run with oracle `H` on input state `ρ`, for
classical outcome `o`: `final_o (Φ_{q-1}(U_H ⋯ Φ_0(U_H init(ρ) U_H†) ⋯ U_H†))`. Its trace is the
probability of outcome `o`. -/
noncomputable def QAlg.run {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Rin W Rout O ι : Type}
    [Fintype Rin] [Fintype W] [Fintype Rout] [Fintype O] [Fintype ι] [DecidableEq Rin]
    [DecidableEq W] {q : ℕ} (A : QAlg X ℓ Rin W Rout O ι q) (H : Oracle X ℓ)
    (ρ : Matrix Rin Rin ℂ) (o : O) : Matrix Rout Rout ℂ :=
  A.final.apply o
    ((List.finRange q).foldl
      (fun σ k => (A.step k).apply ()
        (oracleUnitary H W * σ * (oracleUnitary H W)ᴴ))
      (A.init.apply () ρ))

end KAQROM


