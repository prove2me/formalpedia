-- Prove2me | Definitions.Def_KAQROM_Protocol_Omega
-- name    : KAQROM_Protocol_Omega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:19.046042+00:00
-- url     : https://prove2.me/theorems/f9a40851-6f8f-4a42-94db-351ebb978db7
-- title:
--   §5.2.1: $\mathsf F_{m,h}$, $\Omega_{m,h}$, $\omega^{AB}_{m,h}$, $\omega^A_{m,h}$, $\omega^B_{m,h}$, and Lemma 5.12's $\tilde\Omega_{m,h}$
-- statement:
--   For a complete public prefix transcript $m$ and a partial oracle $h$, let $\mathsf F_{m,h}=\{M=m,\ h\preceq H\}$ in the honest prefix.
--
--   1. $\Omega_{m,h}$ is the real conditional state on $HT_AS_AT_BS_B$ given $\mathsf F_{m,h}$, classical on $(H,T_A,T_B)$.
--   2. $\omega^{AB}_{m,h}$ is its $T_AS_AT_BS_B$-marginal, and $\omega^A_{m,h}$, $\omega^B_{m,h}$ are the marginals on $T_AS_A$ and $T_BS_B$.
--   3. $\tilde\Omega_{m,h}$ (Lemma 5.12) is the state on $HT'_AS'_AT'_BS'_B$ obtained by independently preparing $(T'_A,S'_A)\leftarrow\omega^A_{m,h}$ and $(T'_B,S'_B)\leftarrow\omega^B_{m,h}$, sampling $H_0\leftarrow\mathrm{Unif}(\mathcal H(h,T'_B))$ and setting $\tilde H=H_0[T'_A]$.
--
--   Also included: $\Pr[\mathsf F_{m,h},T_A=t_A,T_B=t_B]$ with the conditional state of $(H,S_A,S_B)$ given that event (display (4)), and $\Pr[x\in\mathrm{Dom}(T_A)\mid\mathsf F_{m,h}]$ (Lemma 5.11 (iii)).
--
--   These are the states compared in Lemmas 5.11 and 5.12 and used to build the hybrids.
--
--   **Formalization Note** The paper defines $\omega^{AB}_{m,h}$ through the exact classical simulation of the prefix and the channels $\Phi_A\otimes\Phi_B$, and observes that it is precisely the marginal of $\Omega_{m,h}$; the marginal is taken as the definition. The classical register $M$, fixed to $m$, is left out. When the conditioning event has probability $0$ the conditional states are $0$; they are used only at events of positive probability. A transcript inconsistent with $h$, which has probability zero under $\omega^B_{m,h}$, contributes nothing to $\tilde\Omega_{m,h}$.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §5.2.1, p.33; Lemma 5.12, pp.36–37; Lemma 5.11 (iii), p.35

import Mathlib
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_CQ
import Definitions.Def_KAQROM_Protocol

namespace KAQROM

open Matrix
open scoped Kronecker

namespace Protocol

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ : ℕ} {Msg K : Type} [Fintype Msg]
  [DecidableEq Msg] [Fintype K]

/-- `Pr[F_{m,h}]` for the event `F_{m,h} := {M = m, h ⪯ H}` of the honest prefix (§5.2.1, p.33). -/
noncomputable def probF (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) :
    ℝ := by
  classical
  exact (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ *
    ∑ H : Oracle X ℓ, ∑ o : P.Outcome, if P.msgs o = m ∧ h.Le H then P.weight H o else 0

/-- **`Ω_{m,h}`** (§5.2.1, p.33): the real conditional state on `H T_A S_A T_B S_B` given
`F_{m,h}`, a classical–quantum state with classical register `(H, T_A, T_B)` and quantum register
`S_A S_B`. The block of a branch is `ρ_A ⊗ ρ_B / (|ℋ| Pr[F_{m,h}])`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), §5.2.1, p.33.

**Formalization Note.** The classical register `M` is fixed to `m` by the conditioning and is left
out. When `Pr[F_{m,h}] = 0` the state is `0` (the paper defines it only for positive probability). -/
noncomputable def Omega (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) :
    CQ (Oracle X ℓ × Transcript X ℓ × Transcript X ℓ) (P.RA × P.RB) := by
  classical
  exact ((Fintype.card (Oracle X ℓ) : ℂ)⁻¹ * ((P.probF m h : ℝ) : ℂ)⁻¹) •
    ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
      if P.msgs o = m ∧ h.Le H then
        Finsupp.single (H, (P.aliceRun H o).2, (P.bobRun H o).2)
          ((P.aliceRun H o).1 ⊗ₖ (P.bobRun H o).1)
      else 0

/-- **`ω^{AB}_{m,h}`** (§5.2.1, p.33): the state of the two prefix views `T_A S_A T_B S_B` given
`F_{m,h}`, the `T_A S_A T_B S_B`-marginal of `Ω_{m,h}`.

**Formalization Note.** The paper defines `ω^{AB}_{m,h}` through the exact classical simulation of
the prefix and the channels `Φ_A ⊗ Φ_B`, and states that it is precisely this marginal; the
marginal is taken as the definition. -/
noncomputable def omegaAB (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) :
    CQ (Transcript X ℓ × Transcript X ℓ) (P.RA × P.RB) :=
  (P.Omega m h).sum (fun c M => Finsupp.single (c.2.1, c.2.2) M)

/-- **`ω^A_{m,h}`**: Alice's marginal `T_A S_A` of `ω^{AB}_{m,h}` (§5.2.1, p.33). -/
noncomputable def omegaA (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) :
    CQ (Transcript X ℓ) P.RA :=
  (P.omegaAB m h).sum (fun c M => Finsupp.single c.1 (ptraceRight M))

/-- **`ω^B_{m,h}`**: Bob's marginal `T_B S_B` of `ω^{AB}_{m,h}` (§5.2.1, p.33). -/
noncomputable def omegaB (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ) :
    CQ (Transcript X ℓ) P.RB :=
  (P.omegaAB m h).sum (fun c M => Finsupp.single c.2 (ptraceLeft M))

/-- **`Ω̃_{m,h}`** (Lemma 5.12, pp.36–37): the state on `H T'_A S'_A T'_B S'_B` produced by
independently preparing `(T'_A, S'_A) ← ω^A_{m,h}` and `(T'_B, S'_B) ← ω^B_{m,h}`, sampling
`H₀ ← Unif(ℋ(h, T'_B))` and setting `H̃ = H₀[T'_A]`, with `H` holding `H̃`.

**Formalization Note.** If `ℋ(h, t'_B)` is empty (a transcript inconsistent with `h`, which has
probability zero under `ω^B_{m,h}`), the branch contributes nothing. -/
noncomputable def OmegaTilde (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg)
    (h : PartialOracle X ℓ) :
    CQ (Oracle X ℓ × Transcript X ℓ × Transcript X ℓ) (P.RA × P.RB) :=
  (P.omegaA m h).sum (fun tA A => (P.omegaB m h).sum (fun tB B =>
    ∑ H0 ∈ oraclesExt h [tB],
      Finsupp.single (reprogram H0 tA, tA, tB)
        ((((oraclesExt h [tB]).card : ℂ))⁻¹ • (A ⊗ₖ B))))

/-- `Pr[F_{m,h}, T_A = t_A, T_B = t_B]` in the honest prefix. -/
noncomputable def probFT (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg) (h : PartialOracle X ℓ)
    (tA tB : Transcript X ℓ) : ℝ := by
  classical
  exact (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ *
    ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
      if P.msgs o = m ∧ h.Le H ∧ (P.aliceRun H o).2 = tA ∧ (P.bobRun H o).2 = tB then
        P.weight H o else 0

/-- The conditional state of `(H, S_A, S_B)` given `(F_{m,h}, T_A = t_A, T_B = t_B)` (§5.2.1,
display (4), p.33), as a function of the oracle value `H`: the block of `H` is
`∑ ρ_A ⊗ ρ_B / (|ℋ| Pr[F_{m,h}, T_A = t_A, T_B = t_B])` over the branches with this oracle. -/
noncomputable def condPrefixState (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg)
    (h : PartialOracle X ℓ) (tA tB : Transcript X ℓ) (H : Oracle X ℓ) :
    Matrix (P.RA × P.RB) (P.RA × P.RB) ℂ := by
  classical
  exact ((Fintype.card (Oracle X ℓ) : ℂ)⁻¹ * ((P.probFT m h tA tB : ℝ) : ℂ)⁻¹) •
    ∑ o : P.Outcome,
      if P.msgs o = m ∧ h.Le H ∧ (P.aliceRun H o).2 = tA ∧ (P.bobRun H o).2 = tB then
        (P.aliceRun H o).1 ⊗ₖ (P.bobRun H o).1 else 0

/-- `Pr[x ∈ Dom(T_A) | F_{m,h}]` in the honest prefix (Lemma 5.11 (iii), p.35). -/
noncomputable def probQueriedA (P : Protocol X ℓ Msg K) (m : Fin P.n → Msg)
    (h : PartialOracle X ℓ) (x : X) : ℝ := by
  classical
  exact (P.probF m h)⁻¹ * ((Fintype.card (Oracle X ℓ) : ℝ)⁻¹ *
    ∑ H : Oracle X ℓ, ∑ o : P.Outcome,
      if P.msgs o = m ∧ h.Le H ∧ x ∈ (P.aliceRun H o).2.dom then P.weight H o else 0)

end Protocol

end KAQROM


