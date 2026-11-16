-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_IsSoundLDPIP
-- name    : DoublyEffIP_Supplement_IsSoundLDPIP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:43:22.624201+00:00
-- url     : https://prove2.me/theorems/9a9f8fd7-85b3-47b8-a185-dfb22644726b
-- title:
--   $2^{-\sigma}$-sound LDP-IP, with output bounds
-- statement:
--   Let $\ell,a$ be the protocol's round count and message length at the public parameters $\mathrm{pp}$, and let $\mathbb F$ be the binary field the protocol chooses from $\mathrm{pp}$. The verifier never sees the input $x\in\{0,1\}^N$; it rejects or outputs a description $\langle\Psi\rangle$, and $\Psi(x)=1$ means that the circuit $C_\Psi$ generated (by $T_\Psi$) for the shape $(1^N,1^{|\langle\Psi\rangle|})$ gives $C_\Psi(x,\langle\Psi\rangle)=1$ over $\mathbb F$. The protocol is a **$2^{-\sigma}$-sound LDP-IP** for the language $L$ within the given bounds if:
--
--   1. the parameter machine computes $\ell$, $a$ and the presentation of $\mathbb F$ from $\mathrm{pp}$ within $V_B$ steps, $\mathbb F$ has characteristic $2$, and $\ell\le\ell_B$, $a\le a_B$;
--   2. on every coin and answer sequence the verifier halts within $V_B$ steps;
--   3. every output $\langle\Psi\rangle\ne\bot$ has $|\langle\Psi\rangle|\le\mathrm{desc}_B$, $\mathrm{size}(C_\Psi)\le\mathrm{size}_B$, $\mathrm{depth}(C_\Psi)\le\mathrm{depth}_B$;
--
--   and for every $x\in\{0,1\}^N$:
--
--   4. the prover machine answers every round, in total at most $P_B$ steps;
--   5. (completeness) if $x\in L$, then on every coin sequence with the prover machine's answers the verifier outputs a $\langle\Psi\rangle$ with $\Psi(x)=1$;
--   6. (soundness) if $x\notin L$, then for every prover strategy $P^*$, $\Pr_q[\text{the output is }\langle\Psi\rangle\text{ with }\Psi(x)=1]\le 2^{-\sigma}$.
--
--   This is Definition 8 together with the output bounds of Theorems 6 and 7.
--
--   **Formalization Note** Probabilities are counts over the uniform coins; completeness is by the protocol's own prover machine, whose total time is $\mathrm{Ptime}$; the verifier's time bound holds on every coin and answer sequence. The field is chosen by the protocol and output by the parameter machine, so the reader of $\langle\Psi\rangle$ knows it.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4.1, p.11, Definition 8; Theorems 6 and 7, pp.15, 19

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit
import Definitions.Def_DoublyEffIP_Supplement_circuitDepth
import Definitions.Def_DoublyEffIP_Supplement_IsImpl
import Definitions.Def_DoublyEffIP_Supplement_implShape
import Definitions.Def_DoublyEffIP_Supplement_bitsIn
import Definitions.Def_DoublyEffIP_Supplement_PredHolds
import Definitions.Def_DoublyEffIP_Supplement_OProtocol
import Definitions.Def_DoublyEffIP_Supplement_Outputs
import Definitions.Def_DoublyEffIP_Supplement_encFieldPres
import Definitions.Def_DoublyEffIP_encBin
import Definitions.Def_DoublyEffIP_HaltsAt
import Definitions.Def_DoublyEffIP_ComputesIn
import Definitions.Def_DoublyEffIP_msgs
import Definitions.Def_DoublyEffIP_Supplement_proverWord
import Definitions.Def_DoublyEffIP_Supplement_verifierWord
import Definitions.Def_AvgCaseTI_FieldPres
import Definitions.Def_TreeEdgeRankPC_Transducer

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open TreeEdgeRankPC

namespace DoublyEffIP.Supplement

/-- **A `2^{-σ}`-sound `(ℓ, a, Ptime, Vtime)`-LDP-IP, with output bounds** — Definition 8 of
Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), p.11: "An low-depth-predicate-interactive-proof (LDP-IP) with respect to a field F for a
language L is a protocol with public parameters pp, where the prover is given some input
x ∈ {0,1}^n, and the verifier receives no input … At the end of the protocol, the verifier either
rejects (outputs ⊥) or outputs the description of a low-depth predicate Ψ", with the bounds that
Theorems 6 and 7 (pp.15, 19) place on `C_Ψ` and `|⟨Ψ⟩|`.

With `ℓ`, `a` the values of `prot.rounds`, `prot.msgLen` at `pp`, and `F` the binary field
`field pp` (`Ψ` is evaluated over `F` by the circuit `TΨ` outputs on the shape `(N, |⟨Ψ⟩|)`):
1. (parameters) `paramM` outputs `ℓ`, `a` and the presentation of `F` within `VB` steps; `F` has
   characteristic `2`; `ℓ ≤ ℓB`, `a ≤ aB`;
2. (verifier time) on every coin and answer sequence the verifier halts within `VB` steps;
3. (outputs) every output `⟨Ψ⟩ ≠ ⊥` has `|⟨Ψ⟩| ≤ descB`, `size(C_Ψ) ≤ sizeB`,
   `depth(C_Ψ) ≤ depthB`;

and for every `x ∈ {0,1}^N`:

4. (prover time) the prover machine answers every round, in total at most `PB` steps;
5. (completeness) if `x ∈ L`, on every coin sequence with the prover machine's answers the verifier
   outputs a `⟨Ψ⟩` with `Ψ(x) = 1`;
6. (soundness) if `x ∉ L`, for every prover strategy `P*` the verifier outputs a `⟨Ψ⟩` with
   `Ψ(x) = 1` on at most a `2^{-σ}` fraction of the coin sequences.

**Formalization Note.** As `DoublyEffIP.IsSoundIP`, with the parties'
inputs `proverWord`, `verifierWord`: probabilities are counts over the coins, the
completeness prover is the protocol's own machine (whose total time is `Ptime`), and the verifier's
time bound holds on every coin and answer sequence. The verifier's input holds `pp` and the
transcript but no `x` ("the verifier never accesses x"). The field is chosen by the protocol from
`pp` and output by `paramM`, so the reader of `⟨Ψ⟩` knows it. -/
def IsSoundLDPIP (prot : OProtocol) (field : List Bool → AvgCaseTI.FieldPres) (TΨ : Transducer)
    (pp : List Bool) (N : ℕ) (L : Set (List Bool)) (σ : ℕ)
    (ℓB aB PB VB sizeB depthB descB : ℝ) : Prop :=
  let ℓ := prot.rounds pp
  let a := prot.msgLen pp
  let P := field pp
  let α : P.F := AdjoinRoot.root P.f
  let vin : (Fin ℓ → List.Vector Bool a) → (Fin ℓ → List.Vector Bool a) → List Bool :=
    fun qs as => verifierWord pp (msgs qs) (msgs as)
  -- parameters and field, computed from `pp` within the verifier's budget
  (∃ t : ℕ, ComputesIn prot.paramM prot.paramOut pp (encBin ℓ ++ encBin a ++ encFieldPres P) t ∧
    (t : ℝ) ≤ VB) ∧
  P.p = 2 ∧ (ℓ : ℝ) ≤ ℓB ∧ (a : ℝ) ≤ aB ∧
  -- verifier time, on every coin sequence and every answer sequence
  (∀ qs as : Fin ℓ → List.Vector Bool a,
    ∃ (t : ℕ) (final : SqrtLogSpace.LocatedCfg prot.verifierM),
      HaltsAt prot.verifierM (vin qs as) t final ∧ (t : ℝ) ≤ VB) ∧
  -- every output `⟨Ψ⟩ ≠ ⊥` is within the bounds
  (∀ (qs as : Fin ℓ → List.Vector Bool a) (y : List Bool),
    Outputs prot.verifierM prot.verifierOut (vin qs as) y →
    (y.length : ℝ) ≤ descB ∧
    ∃ C : Circuit, IsImpl TΨ (implShape N y.length) C ∧ (C.gates.length : ℝ) ≤ sizeB ∧
      (circuitDepth (N + y.length) C : ℝ) ≤ depthB) ∧
  ∀ x : List Bool, x.length = N →
    -- honest prover: answers every round, in total time at most `PB`
    (∀ qs : Fin ℓ → List.Vector Bool a, ∃ (as : Fin ℓ → List.Vector Bool a) (t : Fin ℓ → ℕ),
      (∑ j, (t j : ℝ)) ≤ PB ∧
      ∀ j : Fin ℓ, ComputesIn prot.proverM prot.proverOut
        (proverWord pp x j.val ((msgs qs).take (j.val + 1))) (as j).toList (t j)) ∧
    -- perfect completeness, by the prover machine's answers
    (x ∈ L → ∀ qs as : Fin ℓ → List.Vector Bool a,
      (∀ j : Fin ℓ, ∃ t : ℕ, ComputesIn prot.proverM prot.proverOut
        (proverWord pp x j.val ((msgs qs).take (j.val + 1))) (as j).toList t) →
      ∃ y, Outputs prot.verifierM prot.verifierOut (vin qs as) y ∧
        PredHolds α TΨ (bitsIn P.F x) y) ∧
    -- soundness error `2^{-σ}` against every prover strategy
    (x ∉ L → ∀ Pstar : List (List Bool) → List.Vector Bool a,
      Nat.card {qs : Fin ℓ → List.Vector Bool a // ∃ y,
          Outputs prot.verifierM prot.verifierOut
            (vin qs fun j => Pstar ((msgs qs).take (j.val + 1))) y ∧
          PredHolds α TΨ (bitsIn P.F x) y} *
        2 ^ σ ≤ 2 ^ (ℓ * a))

end DoublyEffIP.Supplement


