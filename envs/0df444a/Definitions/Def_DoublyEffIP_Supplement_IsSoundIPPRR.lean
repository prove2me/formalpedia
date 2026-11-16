-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_IsSoundIPPRR
-- name    : DoublyEffIP_Supplement_IsSoundIPPRR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:37:39.366281+00:00
-- url     : https://prove2.me/theorems/90d282d9-e32c-4c69-9e6f-7fc7783db676
-- title:
--   $2^{-\sigma}$-sound IPP with row reduction, with output bounds
-- statement:
--   Let $\Phi$ be the predicate on $\mathbb F^{k\times L}$ described by $\langle\Phi\rangle$ (via the generator $T_\Phi$), $L_\Phi=\{M:\Phi(M)=1\}$, and let $\ell,a$ be the protocol's round count and message length at the public parameters $\mathrm{pp}=[\sigma,\mathbb F,d,k,L,\langle\Phi\rangle]$. The verifier sees only $\mathrm{pp}$, its coins and the answers; an output other than $\bot$ is a word $\langle m\rangle\langle Q\rangle\langle\Psi\rangle$ in which $\langle Q\rangle$ describes rows $s_0,\dots,s_{m-1}$ (via $T_Q$) and $\langle\Psi\rangle$ describes a predicate $\Psi$ on $\mathbb F^{m\times L}$ (via $T_\Psi$). The protocol is a **$2^{-\sigma}$-sound IPP with row reduction** within the given bounds if:
--
--   1. the parameter machine computes $\ell,a$ from $\mathrm{pp}$ within $V_B$ steps, and $\ell\le\ell_B$, $a\le a_B$;
--   2. on every coin and answer sequence the verifier halts within $V_B$ steps;
--   3. every output $\ne\bot$ (on any coins and answers) has the above form with $Q\subsetneq[k]$ (distinct rows $s_i<k$, $m<k$), $|Q|\le q_B$, and the bounds on $|\langle Q\rangle|$, $|\langle\Psi\rangle|$, $\mathrm{size}(G)$, $\mathrm{depth}(G)$, $\mathrm{size}(C_\Psi)$ (a function of $|Q|$) and $\mathrm{depth}(C_\Psi)$;
--
--   and for every $M\in\{0,1\}^{k\times L}$:
--
--   4. the prover machine answers every round, in total at most $P_B$ steps;
--   5. (completeness) if $\Phi(M)=1$, then on every coin sequence with the prover machine's answers the verifier outputs $(\langle Q\rangle,\langle\Psi\rangle)$ with $\Psi(M[Q,:])=1$;
--   6. (soundness) if $M$ is $d$-$\Delta_c$-far from $L_\Phi$, then for every prover strategy $P^*$, $\Pr_q\big[\text{the output is }(\langle Q\rangle,\langle\Psi\rangle)\text{ with }\Psi(M[Q,:])=1\big]\le 2^{-\sigma}$.
--
--   This is Definition 9 together with the output bounds of Theorem 4.
--
--   **Formalization Note** Probabilities over the uniform coins are counts ($\#\{q\}\cdot 2^\sigma\le 2^{\ell a}$). Completeness is by the protocol's own prover machine, whose total running time is $\mathrm{Ptime}$; a cheating prover is any function from the queries so far to an answer. Circuits over $\mathbb F=\mathbb F_p[X]/(f)$ read the generator gate as the class of $X$; the bit matrix is embedded by $0,1$. The output carries $m=|Q|$, the first shape parameter of $Q$'s implementation circuit.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4.2, p.12, Definition 9; Theorem 4, p.13

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit
import Definitions.Def_DoublyEffIP_Supplement_circuitDepth
import Definitions.Def_DoublyEffIP_Supplement_IsImpl
import Definitions.Def_DoublyEffIP_Supplement_implShape
import Definitions.Def_DoublyEffIP_Supplement_setShape
import Definitions.Def_DoublyEffIP_Supplement_bitsIn
import Definitions.Def_DoublyEffIP_Supplement_PredHolds
import Definitions.Def_DoublyEffIP_Supplement_OProtocol
import Definitions.Def_DoublyEffIP_Supplement_Outputs
import Definitions.Def_DoublyEffIP_Supplement_DeltaCClose
import Definitions.Def_DoublyEffIP_Supplement_flatMat
import Definitions.Def_DoublyEffIP_Supplement_subMatBits
import Definitions.Def_DoublyEffIP_Supplement_DescribesRows
import Definitions.Def_DoublyEffIP_Supplement_ppIPP
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

/-- **A `2^{-σ}`-sound `(ℓ, a, Ptime, Vtime)`-IPP with row reduction, with output bounds** —
Definition 9 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), p.12, for the input matrices `M ∈ {0,1}^{k×L}` of Theorem 4 (p.13), with
the bounds that Theorem 4 places on the output.

The protocol has public parameters `pp = ppIPP σ F ⟨Φ⟩ d k L`; `Φ` is the predicate on `F^{k×L}`
whose implementation circuit `TΦ` outputs, `L_Φ = {M | Φ(M) = 1}`; `ℓ`, `a` are `prot.rounds pp`,
`prot.msgLen pp`. The verifier gets only `pp`, the coins and the answers. Its output `≠ ⊥` is a word
`⟨m⟩ ⟨Q⟩ ⟨Ψ⟩`; `⟨Q⟩` describes (via `TQ`, `DescribesRows`) the rows `s 0, …, s (m−1)` of `Q`, and
`⟨Ψ⟩` describes (via `TΨ`) a predicate `Ψ` on `F^{m×L}`. Then:
1. (parameters) `paramM` outputs `ℓ`, `a` within `VB` steps; `ℓ ≤ ℓB`, `a ≤ aB`;
2. (verifier time) on every coin and answer sequence the verifier halts within `VB` steps;
3. (outputs) every output `≠ ⊥` (on any coins and answers) has this form, with `Q ⊊ [k]` (distinct
   rows `s i < k`, `m < k`), `|Q| = m ≤ qB`, `|⟨Q⟩| ≤ descQB`, `|⟨Ψ⟩| ≤ descΨB`, `size(G) ≤ sizeGB`,
   `depth(G) ≤ depthGB`, `size(C_Ψ) ≤ sizeCB m`, `depth(C_Ψ) ≤ depthCB`;

and for every `M ∈ {0,1}^{k×L}`:

4. (prover time) the prover machine answers every round, in total at most `PB` steps;
5. (completeness) if `Φ(M) = 1`, on every coin sequence with the prover machine's answers the
   verifier outputs `(⟨Q⟩, ⟨Ψ⟩)` with `Ψ(M[Q, :]) = 1`;
6. (soundness) if `M` is `d`-`Δc`-far from `L_Φ` (no matrix over `F` that is `Δc`-`d`-close to `M`
   satisfies `Φ`), then for every prover strategy `P*`, the verifier outputs `(⟨Q⟩, ⟨Ψ⟩)` with
   `Ψ(M[Q, :]) = 1` on at most a `2^{-σ}` fraction of the coin sequences.

**Formalization Note.**
* Probabilities over the uniform coins `q ∈ ({0,1}^a)^ℓ` are counts, as in the published
  `DoublyEffIP.IsSoundIP` (with the parties' inputs `proverWord`, `verifierWord`); a cheating prover is any function from the queries so far to an answer.
* Completeness is by the protocol's own prover machine, whose total time is `Ptime`.
* `F = F_p[X]/(f)` is the presented field `P`; circuits over `F` read `gen` as the class of `X`.
  The bit matrix `M` is embedded in `F^{k×L}` by `0, 1`.
* The output carries `m = |Q|`, the first shape parameter of `Q`'s implementation circuit
  (Definition 4). -/
def IsSoundIPPRR (prot : OProtocol) (TQ TΨ : Transducer) (σ : ℕ) (P : AvgCaseTI.FieldPres)
    (TΦ : Transducer) (descΦ : List Bool) (d k L qB : ℕ)
    (ℓB aB PB VB descQB descΨB sizeGB depthGB : ℝ) (sizeCB : ℕ → ℝ) (depthCB : ℝ) : Prop :=
  let pp := ppIPP σ P descΦ d k L
  let ℓ := prot.rounds pp
  let a := prot.msgLen pp
  let α : P.F := AdjoinRoot.root P.f
  let vin : (Fin ℓ → List.Vector Bool a) → (Fin ℓ → List.Vector Bool a) → List Bool :=
    fun qs as => verifierWord pp (msgs qs) (msgs as)
  let accepted : (Fin k → Fin L → Bool) → List Bool → Prop := fun M y =>
    ∃ (m : ℕ) (descQ descΨ : List Bool) (s : Fin m → ℕ),
      y = encBin m ++ Encoding.frame descQ ++ Encoding.frame descΨ ∧
      DescribesRows TQ k m descQ s ∧ PredHolds α TΨ (bitsIn P.F (subMatBits M s)) descΨ
  -- parameters, computed from `pp` within the verifier's budget
  (∃ t : ℕ, ComputesIn prot.paramM prot.paramOut pp (encBin ℓ ++ encBin a) t ∧ (t : ℝ) ≤ VB) ∧
  (ℓ : ℝ) ≤ ℓB ∧ (a : ℝ) ≤ aB ∧
  -- verifier time, on every coin sequence and every answer sequence
  (∀ qs as : Fin ℓ → List.Vector Bool a,
    ∃ (t : ℕ) (final : SqrtLogSpace.LocatedCfg prot.verifierM),
      HaltsAt prot.verifierM (vin qs as) t final ∧ (t : ℝ) ≤ VB) ∧
  -- every output `≠ ⊥` is a valid `(⟨Q⟩, ⟨Ψ⟩)` within the bounds
  (∀ (qs as : Fin ℓ → List.Vector Bool a) (y : List Bool),
    Outputs prot.verifierM prot.verifierOut (vin qs as) y →
    ∃ (m : ℕ) (descQ descΨ : List Bool) (s : Fin m → ℕ),
      y = encBin m ++ Encoding.frame descQ ++ Encoding.frame descΨ ∧
      DescribesRows TQ k m descQ s ∧ (∀ i, s i < k) ∧ Function.Injective s ∧ m < k ∧ m ≤ qB ∧
      (descQ.length : ℝ) ≤ descQB ∧ (descΨ.length : ℝ) ≤ descΨB ∧
      (∃ G : Circuit, IsImpl TQ (setShape m descQ.length (Nat.clog 2 k)) G ∧
        (G.gates.length : ℝ) ≤ sizeGB ∧
        (circuitDepth (Nat.clog 2 k + descQ.length) G : ℝ) ≤ depthGB) ∧
      (∃ C : Circuit, IsImpl TΨ (implShape (m * L) descΨ.length) C ∧
        (C.gates.length : ℝ) ≤ sizeCB m ∧
        (circuitDepth (m * L + descΨ.length) C : ℝ) ≤ depthCB)) ∧
  ∀ M : Fin k → Fin L → Bool,
    -- honest prover: answers every round, in total time at most `PB`
    (∀ qs : Fin ℓ → List.Vector Bool a, ∃ (as : Fin ℓ → List.Vector Bool a) (t : Fin ℓ → ℕ),
      (∑ j, (t j : ℝ)) ≤ PB ∧
      ∀ j : Fin ℓ, ComputesIn prot.proverM prot.proverOut
        (proverWord pp (flatMat M) j.val ((msgs qs).take (j.val + 1))) (as j).toList (t j)) ∧
    -- perfect completeness, by the prover machine's answers
    (PredHolds α TΦ (bitsIn P.F (flatMat M)) descΦ → ∀ qs as : Fin ℓ → List.Vector Bool a,
      (∀ j : Fin ℓ, ∃ t : ℕ, ComputesIn prot.proverM prot.proverOut
        (proverWord pp (flatMat M) j.val ((msgs qs).take (j.val + 1))) (as j).toList t) →
      ∃ y, Outputs prot.verifierM prot.verifierOut (vin qs as) y ∧ accepted M y) ∧
    -- soundness error `2^{-σ}` against every prover strategy, for `M` `d`-`Δc`-far from `L_Φ`
    ((∀ M' : Fin k → Fin L → P.F,
        DeltaCClose d (fun i j => if M i j then (1 : P.F) else 0) M' →
        ¬ PredHolds α TΦ (flatMat M') descΦ) →
      ∀ Pstar : List (List Bool) → List.Vector Bool a,
        Nat.card {qs : Fin ℓ → List.Vector Bool a // ∃ y,
            Outputs prot.verifierM prot.verifierOut
              (vin qs fun j => Pstar ((msgs qs).take (j.val + 1))) y ∧ accepted M y} *
          2 ^ σ ≤ 2 ^ (ℓ * a))

end DoublyEffIP.Supplement


