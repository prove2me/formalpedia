-- Prove2me | Definitions.Def_LocalSweepFT_Supplement_idealDecodeFailProb
-- name    : LocalSweepFT_Supplement_idealDecodeFailProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:34:18.757579+00:00
-- url     : https://prove2.me/theorems/9958ed0e-f09d-45e3-b40c-bdd37a1850dd
-- title:
--   Local stochastic Pauli errors on one register and the failure probability of ideal sweep decoding
-- statement:
--   Fix integers $d,d'$ and a side length $n\ge1$, and consider one register of the $(d,d')$-Toric code: one qubit for every $d'$-cell $q$ of the cubical torus $\mathcal T^d_n$.
--
--   1. An **error pattern** $E$ assigns to each qubit $q$ a pair $E(q)=(e_q,f_q)\in\mathbb F_2^2$; its **Pauli error** is
--   $$P_E=\Big(\bigotimes_q X^{e_q}\Big)\Big(\bigotimes_q Z^{f_q}\Big).$$
--   2. A probability distribution $\nu$ of error patterns is **local stochastic with rate $p$** if for every finite set $S$ of qubits
--   $$\Pr_{E\sim\nu}\big[E(q)\ne(0,0)\ \text{for all } q\in S\big]\le p^{|S|}.$$
--   3. For sweep rules $r_1$ (on the $d'$-cells) and $r_2$ (on the $(d-d')$-cells of the dual code), let $\mathcal S$ be the sweep-cycle channel of the mission, $\mathcal S(\rho)=\sum_K K\rho K^\dagger$. The **failure probability of ideal sweep decoding** of a vector $|\psi\rangle$ of the register is
--   $$\Pr_{E\sim\nu}\Big[\mathcal S^{\,n^{d+1}}\big(P_E|\psi\rangle\langle\psi|P_E^\dagger\big)\ne|\psi\rangle\langle\psi|\Big],$$
--   the probability that $n^{d+1}$ noiseless sweep cycles do not return the corrupted state exactly to $|\psi\rangle\langle\psi|$.
--
--   These objects state Theorem 7.3: the sweep rule, run without faults, decodes a local stochastic initial error.
--
--   **Formalization Note** The local stochastic condition is Def 3.7 with the locations of a single initial fault layer, which are the qubits of the register. The error operator applies the $X$ part after the $Z$ part, as the mission's fault layer does; the order changes $P_E$ only by a sign, which cancels in $P_E\rho P_E^\dagger$. The cycle is the published sweep-cycle Kraus family, iterated with `Nat.iterate`. The vector $\psi$ need not be normalized: rescaling it does not change the event, and for $\psi=0$ the event is empty.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5bbb5cb9a66ee05f2fa2953fc49add2665da350a30afceb79503cca41), Definition 3.7, p.14 (local stochastic noise); Claim 7.2, p.62 (single initial fault layer); Definition 4.9, p.21 (sweep cycle); Theorem 7.3, p.62

import Mathlib
import Definitions.Def_LocalSweepFT_liftOn
import Definitions.Def_LocalSweepFT_encMat
import Definitions.Def_LocalSweepFT_IsSweepRule
import Definitions.Def_LocalSweepFT_sweepCycleKraus

open Matrix

namespace LocalSweepFT.Supplement

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…), §7 (pp.60–62): ideal decoding by the sweep rule. A Pauli error
on one register of the `(d, d′)`-Toric code, local stochastic noise on that register (Def 3.7, p.14,
for the single initial fault layer of Claim 7.2, p.62), and the probability that `n^{d+1}` noiseless
sweep cycles (Def 4.9, p.21) fail to return the codeword (Theorem 7.3, p.62). -/

variable {d d' n : ℕ} [NeZero n]

/-- The Pauli error `P_E = X^{E.1} Z^{E.2}` of the error pattern `E` on one register: qubit `q`
(a `d′`-cell) carries `X^{(E q).1} Z^{(E q).2}`. The `X` part is applied after the `Z` part, in the
same order as the base fault layer `LocalSweepFT.faultOp`; the order changes `P_E` only by a global
sign, which cancels in `P_E ρ P_E†`. -/
noncomputable def pauliErr (E : QCell d d' n → ZMod 2 × ZMod 2) : Op (QCell d d' n) :=
  xOn (fun q => (E q).1) * zOn (fun q => (E q).2)

/-- A distribution `ν` of Pauli error patterns on one register is **local stochastic with rate `p`**
(Def 3.7, p.14, with the locations of the single initial fault layer, i.e. the qubits of the
register): for every finite set `S` of qubits, the probability that every qubit of `S` carries a
non-identity Pauli (`E q ≠ (0, 0)`) is at most `p^{|S|}`. -/
def IsRegLocalStochastic (ν : PMF (QCell d d' n → ZMod 2 × ZMod 2)) (p : ℝ) : Prop :=
  ∀ S : Finset (QCell d d' n),
    ν.toOuterMeasure {E | ∀ q ∈ S, E q ≠ 0} ≤ ENNReal.ofReal (p ^ S.card)

/-- `N` noiseless sweep cycles: the channel `ρ ↦ Σ_K K ρ K†` of the base sweep cycle
`LocalSweepFT.sweepCycleKraus` (Def 4.9, p.21) with the rules `rule₁` (sector `d′`) and `rule₂`
(sector `d − d′`), iterated `N` times, with no faults inside or between the cycles. -/
noncomputable def idealSweeps (h : d' + (d - d') = d) (rule₁ : LocalRule d d')
    (rule₂ : LocalRule d (d - d')) (N : ℕ) : Op (QCell d d' n) → Op (QCell d d' n) :=
  (fun ρ => applyK (sweepCycleKraus h rule₁ rule₂) ρ)^[N]

/-- The failure probability of ideal sweep decoding (Theorem 7.3, p.62): the probability under `ν`
of an error pattern `E` for which `n^{d+1}` noiseless sweep cycles applied to the corrupted state
`P_E |ψ⟩⟨ψ| P_E†` do not return exactly `|ψ⟩⟨ψ|`.

**Formalization Note.** `|ψ⟩⟨ψ|` is `Matrix.vecMulVec ψ (star ψ)`; `ψ` is not required to be
normalized (rescaling `ψ` rescales both sides by the same factor, so the event is unchanged, and for
`ψ = 0` it is empty). The comparison is exact equality of operators, so a residual logical error
that changes `|ψ⟩⟨ψ|` counts as failure, and one that leaves it unchanged does not. -/
noncomputable def idealDecodeFailProb (h : d' + (d - d') = d) (rule₁ : LocalRule d d')
    (rule₂ : LocalRule d (d - d')) (ψ : (QCell d d' n → ZMod 2) → ℂ)
    (ν : PMF (QCell d d' n → ZMod 2 × ZMod 2)) : ENNReal :=
  ν.toOuterMeasure {E | idealSweeps h rule₁ rule₂ (n ^ (d + 1))
      (pauliErr E * vecMulVec ψ (star ψ) * (pauliErr E).conjTranspose) ≠ vecMulVec ψ (star ψ)}

end LocalSweepFT.Supplement


