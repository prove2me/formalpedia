-- Prove2me | Definitions.Def_KAQROM_Protocol_J1
-- name    : KAQROM_Protocol_J1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:36:17.389548+00:00
-- url     : https://prove2.me/theorems/ed33f1f9-b3aa-44c3-9497-78ff32f2abb7
-- title:
--   The hybrids $J_1$–$J_5$ of the proof of Theorem 5.14
-- statement:
--   Fix a prefix learner. All hybrids run the honest prefix and the learner on its complete transcript $m$; a learner abort counts as failure; success means that the two recorded keys agree and are not $\bot$.
--
--   1. $J_1$: then $\mathcal B^{H}_{\mathsf q}$ and $\mathcal A^{H}_{\mathsf{fin}}$ on the real registers.
--   2. $J_2$: keep only $(m,h)$; prepare $(T'_A,S'_A)\leftarrow\omega^A_{m,h}$, $(T'_B,S'_B)\leftarrow\omega^B_{m,h}$; sample $\hat H\leftarrow\mathrm{Unif}(\mathcal H(h,T'_B))$, set $\tilde H=\hat H[T'_A]$; run $\mathcal B^{\tilde H}_{\mathsf q}(m,S'_B)$ and $\mathcal A^{\tilde H}_{\mathsf{fin}}(m,S'_A,\Psi)$.
--   3. $J_3$: as $J_2$, but Bob uses $\hat H$.
--   4. $J_4$: as $J_3$ with Eve's Alice view $(T^E_A,S^E_A)$ and an independent second Alice view $(T^B_A,S^B_A)$, both from $\omega^A_{m,h}$; $H^B=\hat H[T^B_A]$, $H^E=H^B[T^E_A]$; Bob uses $H^B$ and Alice's final stage $H^E$.
--   5. $J_5$: the real interception attack; Bob's real register with $H$, and $\mathcal A^{H[T'_A]}_{\mathsf{fin}}(m,S'_A,\Psi)$ with $(T'_A,S'_A)\leftarrow\omega^A_{m,h}$.
--
--   For $J_2$–$J_4$, $\Pr[J_i\text{ succeeds}]=\sum_{(m,h)}\pi(m,h)\,s_i(m,h)$, with $\pi(m,h)=\Pr[M=m,\ L^H(m)=h]$ and $s_i$ the success probability given $(m,h)$.
--
--   **Formalization Note** Unused registers (Alice's real register in $J_5$, $S^B_A$ in $J_4$) contribute their traces.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), proof of Theorem 5.14, pp.38–42

import Mathlib
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_CQ
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_Protocol
import Definitions.Def_KAQROM_QueryTree
import Definitions.Def_KAQROM_Protocol_Omega
import Definitions.Def_KAQROM_IsBMPrefixLearner

namespace KAQROM

open Matrix
open scoped Kronecker

namespace Protocol

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype K]

/-- **Hybrid J1** (proof of Theorem 5.14, p.38): the honest execution with `H₁ ← ℋ`, the learner
run on the complete prefix transcript before Bob's final stage, and a learner abort counted as
failure. Success: `K_A = K_B ≠ ⊥`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), proof of
Theorem 5.14, pp.38–42 (hybrids J1–J5). -/
noncomputable def J1 (P : Protocol X ℓ Msg K) (L : PrefixLearner (Fin P.n → Msg) X ℓ) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
    if (L.result H (P.msgs o)).isSome then
      ∑ k : K, ((P.Afin (P.msgs o)).run H
        ((P.aliceRun H o).1 ⊗ₖ (P.Bq (P.msgs o)).run H (P.bobRun H o).1 (some k))
        (some k)).trace.re
    else 0

/-- Hybrid J2's success probability given the realized pair `(m, h)`: independently prepare
`(T'_A, S'_A) ← ω^A_{m,h}` and `(T'_B, S'_B) ← ω^B_{m,h}`, sample `Ĥ ← Unif(ℋ(h, T'_B))`, set
`H̃ = Ĥ[T'_A]`, run `(Ψ, K_B) ← B_q^{H̃}(m, S'_B)` and `K* ← A_fin^{H̃}(m, S'_A, Ψ)`; success is
`K* = K_B ≠ ⊥`. -/
noncomputable def s2 (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) : ℝ :=
  (P.omegaA m h).sum (fun tA A => (P.omegaB m h).sum (fun tB B =>
    ∑ Hh ∈ oraclesExt h [tB], (((oraclesExt h [tB]).card : ℝ))⁻¹ *
      ∑ k : K, ((P.Afin m).run (reprogram Hh tA)
        (A ⊗ₖ (P.Bq m).run (reprogram Hh tA) B (some k)) (some k)).trace.re))

/-- **Hybrid J2** (p.38–39): the real prefix and learner as in J1, keeping only `(m, h)` (abort is
failure), then the resampled run of `s2`. -/
noncomputable def J2 (P : Protocol X ℓ Msg K) (L : PrefixLearner (Fin P.n → Msg) X ℓ) : ℝ :=
  ∑ m : Fin P.n → Msg, ∑ h : PartialOracle X ℓ, P.probReach L m h * P.s2 m h

/-- Hybrid J3's success probability given `(m, h)`: as in J2, but Bob's final stage uses `Ĥ`
instead of `H̃ = Ĥ[T'_A]` (Alice's final stage still uses `H̃`). -/
noncomputable def s3 (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) : ℝ :=
  (P.omegaA m h).sum (fun tA A => (P.omegaB m h).sum (fun tB B =>
    ∑ Hh ∈ oraclesExt h [tB], (((oraclesExt h [tB]).card : ℝ))⁻¹ *
      ∑ k : K, ((P.Afin m).run (reprogram Hh tA)
        (A ⊗ₖ (P.Bq m).run Hh B (some k)) (some k)).trace.re))

/-- **Hybrid J3** (p.39). -/
noncomputable def J3 (P : Protocol X ℓ Msg K) (L : PrefixLearner (Fin P.n → Msg) X ℓ) : ℝ :=
  ∑ m : Fin P.n → Msg, ∑ h : PartialOracle X ℓ, P.probReach L m h * P.s3 m h

/-- Hybrid J4's success probability given `(m, h)`: independently prepare Eve's Alice view
`(T^E_A, S^E_A) ← ω^A_{m,h}`, Bob's view `(T'_B, S'_B) ← ω^B_{m,h}`, `Ĥ ← Unif(ℋ(h, T'_B))`, and a
second Alice view `(T^B_A, S^B_A) ← ω^A_{m,h}`; set `H^B = Ĥ[T^B_A]`, `H^E = H^B[T^E_A]`; run
`(Ψ, K_B) ← B_q^{H^B}(m, S'_B)` and `K* ← A_fin^{H^E}(m, S^E_A, Ψ)`; success is `K* = K_B ≠ ⊥`.
The unused register `S^B_A` contributes its trace. -/
noncomputable def s4 (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) : ℝ :=
  (P.omegaA m h).sum (fun tE AE => (P.omegaA m h).sum (fun tAB AB => (P.omegaB m h).sum
    (fun tB B => ∑ Hh ∈ oraclesExt h [tB], (((oraclesExt h [tB]).card : ℝ))⁻¹ * AB.trace.re *
      ∑ k : K, ((P.Afin m).run (reprogram (reprogram Hh tAB) tE)
        (AE ⊗ₖ (P.Bq m).run (reprogram Hh tAB) B (some k)) (some k)).trace.re)))

/-- **Hybrid J4** (pp.40–41). -/
noncomputable def J4 (P : Protocol X ℓ Msg K) (L : PrefixLearner (Fin P.n → Msg) X ℓ) : ℝ :=
  ∑ m : Fin P.n → Msg, ∑ h : PartialOracle X ℓ, P.probReach L m h * P.s4 m h

/-- **Hybrid J5 (the real interception attack)** (pp.41–42): `H₅ ← ℋ`, the honest prefix, the
learner on the complete transcript (abort is failure), Eve's independent Alice view
`(T'_A, S'_A) ← ω^A_{m,h}`, `(Ψ, K_B) ← B_q^{H₅}(m, S_B)` on Bob's real register, and
`K* ← A_fin^{H₅[T'_A]}(m, S'_A, Ψ)`; success is `K* = K_B ≠ ⊥`. Alice's real register is unused
and contributes its trace. -/
noncomputable def J5 (P : Protocol X ℓ Msg K) (L : PrefixLearner (Fin P.n → Msg) X ℓ) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
    match L.result H (P.msgs o) with
    | none => 0
    | some h => (P.omegaA (P.msgs o) h).sum (fun tA A => (P.aliceRun H o).1.trace.re *
        ∑ k : K, ((P.Afin (P.msgs o)).run (reprogram H tA)
          (A ⊗ₖ (P.Bq (P.msgs o)).run H (P.bobRun H o).1 (some k)) (some k)).trace.re)

end Protocol

end KAQROM


