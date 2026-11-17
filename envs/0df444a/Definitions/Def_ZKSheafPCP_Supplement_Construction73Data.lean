-- Prove2me | Definitions.Def_ZKSheafPCP_Supplement_Construction73Data
-- name    : ZKSheafPCP_Supplement_Construction73Data
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:55:57.815204+00:00
-- url     : https://prove2.me/theorems/bdb62f13-5744-4a23-9889-ac246b9e9532
-- title:
--   The sheaf-code PCPP of Construction 7.3
-- statement:
--   The explicit datum of Construction 7.3 consists of a finite coded space, a sheaf of linear codes, an input local code $\mathcal F_\sigma$, one common testable and extendable cover, the recursive test tree, and an encoding of these data.
--
--   The implicit-input language is $\mathcal F_\sigma$. On an honest input $c\in\mathcal F_\sigma$, the prover samples uniformly from the global extension code $\mathcal F_{\sigma=c}(P)$. The verifier tests the virtual word $\hat g$ that equals the implicit input on $P_\sigma$ and the purported proof away from $P_\sigma$; consequently, a conflicting proof symbol can never overwrite an input symbol.
--
--   The fixed-prover PCPP predicate exposes this uniform-extension prover while retaining the published efficiency, completeness, soundness, black-box locality, exact simulation and query-bound clauses of `IsPZKPCPP`; it also records that soundness and proximity parameters lie in $[0,1]$, as Definition 3.25 requires.
--
--   **Formalization Note** Words on finite sets and finite fields are transported to `Fin`-indexed strings by equivalences. The proof stores a full word on $P^*$, but its coordinates in $P_\sigma$ are ignored by the virtual word, exactly as in Construction 7.3.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definition 6.6, p.26; Construction 7.3, p.32

import Mathlib
import Definitions.Def_ZKSheafPCP_PCPPFamily
import Definitions.Def_ZKSheafPCP_TestTree
import Definitions.Def_ZKSheafPCP_Supplement_IsLocallySimulatable

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace ZKSheafPCP.Supplement

open Classical

/-- The explicit data used by Construction 7.3 (Zeilberger, O'Connor, Gur, Spooner,
*Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC
2027 submission, manuscript sha256 ac5e528f…, p.32): the finite coded space, sheaf,
input local code, common testable/extendable cover, recursive test tree and an encoding
of this fixed datum for the verifier and simulator clocks. -/
structure Construction73Data (F D : Type) [Field F] where
  /-- Encoding of the explicit datum. -/
  encoding : Str
  /-- The coded space. -/
  PP : CodedSpace D
  /-- The sheaf of local linear codes. -/
  sheaf : LocalCodes F D
  /-- The local code containing the implicit input. -/
  sigma : Finset D
  /-- The common cover used for testing and local simulation. -/
  cover : Finset (Finset D)
  /-- The recursive tester of Construction 5.6. -/
  test : TestTree D

/-- Decode the implicit input word on `P_σ`, padding it by zero outside `P_σ`. -/
noncomputable def decodeInput {F D : Type} [Field F] [Fintype F] [Fintype D]
    (I : Construction73Data F D) (y : Fin I.sigma.card → Fin (Fintype.card F)) : D → F :=
  fun x => if hx : x ∈ I.sigma then
    (Fintype.equivFin F).symm (y (Finset.equivFin I.sigma ⟨x, hx⟩)) else 0

/-- Encode a word on the whole point set as a proof string. -/
noncomputable def encodeProof {F D : Type} [Field F] [Fintype F] [Fintype D]
    (g : D → F) : Fin (Fintype.card D) → Fin (Fintype.card F) :=
  fun j => Fintype.equivFin F (g ((Fintype.equivFin D).symm j))

/-- Decode a proof string as a word on the whole point set. -/
noncomputable def decodeProof {F D : Type} [Field F] [Fintype F] [Fintype D]
    (π : Fin (Fintype.card D) → Fin (Fintype.card F)) : D → F :=
  fun x => (Fintype.equivFin F).symm (π (Fintype.equivFin D x))

/-- The pair language `F_σ` of Construction 7.3. The sole explicit instance is the
encoded sheaf datum; its implicit inputs are exactly the words in the local code. -/
noncomputable def construction73Family {F D : Type} [Field F] [Fintype F] [Fintype D]
    (I : Construction73Data F D) : PCPPFamily where
  Inst := Unit
  enc := fun _ => I.encoding
  N := fun _ => I.sigma.card
  a := fun _ => Fintype.card F
  Lang := fun _ => {y | decodeInput I y ∈ I.sheaf.code I.sigma}

/-- The prover of Construction 7.3: on the input `c ∈ F_σ`, sample uniformly from
the global extension code `F_{σ=c}(P)`. -/
noncomputable def construction73Prover {F D : Type} [Field F] [Fintype F] [Fintype D]
    (I : Construction73Data F D) :
    ∀ _ : (construction73Family I).Inst,
      (Fin ((construction73Family I).N ()) → Fin ((construction73Family I).a ())) →
        PMF (Fin (Fintype.card D) → Fin ((construction73Family I).a ())) :=
  fun _ y =>
    (uniformOn 0 (Finset.univ.filter fun g : D → F =>
      g ∈ I.sheaf.relSections (I.PP.geq I.sigma) (decodeInput I y) I.PP.P)).map encodeProof

/-- The virtual word tested by Construction 7.3. The implicit input always supplies
the coordinates in `P_σ`; a purported proof is used only off `P_σ`. -/
noncomputable def construction73VirtualWord {F D : Type} [Field F] [Fintype F] [Fintype D]
    (I : Construction73Data F D)
    (y : Fin I.sigma.card → Fin (Fintype.card F))
    (π : Fin (Fintype.card D) → Fin (Fintype.card F)) : D → F :=
  fun x => if x ∈ I.sigma then decodeInput I y x else decodeProof π x

/-- The published `IsPZKPCPP` interface with the prover exposed and fixed. This is the
same completeness, soundness, efficiency and black-box perfect-zero-knowledge contract as
`ZKSheafPCP.IsPZKPCPP`, but it permits Construction 7.3's uniform-extension prover to be
named rather than hidden behind the leading existential. -/
def IsPZKPCPPWithProver {D : Type} [Fintype D] (Φ : PCPPFamily)
    (P : ∀ i, (Fin (Φ.N i) → Fin (Φ.a i)) → PMF (Fin (Fintype.card D) → Fin (Φ.a i)))
    (q : Φ.Inst → ℕ) (ε δ : Φ.Inst → ℝ) (b l : Φ.Inst → ℕ) : Prop :=
  (∀ i, 0 ≤ ε i ∧ ε i ≤ 1 ∧ 0 ≤ δ i ∧ δ i ≤ 1) ∧
  ∃ (V : OTM) (ρ τ : ℕ → ℕ),
    PolyBdd ρ ∧ PolyBdd τ ∧
    (∀ (i : Φ.Inst) (r : Fin (ρ (Φ.enc i).length) → Bool)
      (y : Fin (Φ.N i) → Fin (Φ.a i)) (π : Fin (Fintype.card D) → Fin (Φ.a i)),
      let O := pcppOracle y π
      let log := queryLog V O (tup [Φ.enc i, coinStr r]) (τ (Φ.enc i).length)
      V.result O (tup [Φ.enc i, coinStr r]) (τ (Φ.enc i).length) ≠ none ∧
      (inputPositions (Φ.N i) log).ncard +
        (proofPositions (Fintype.card D) log).ncard ≤ q i) ∧
    (∀ (i : Φ.Inst), ∀ y ∈ Φ.Lang i, ∀ π ∈ (P i y).support,
      ∀ r : Fin (ρ (Φ.enc i).length) → Bool,
      V.result (pcppOracle y π) (tup [Φ.enc i, coinStr r]) (τ (Φ.enc i).length) = some true) ∧
    (∀ (i : Φ.Inst) (y : Fin (Φ.N i) → Fin (Φ.a i)), IsFar (δ i) y (Φ.Lang i) →
      ∀ π : Fin (Fintype.card D) → Fin (Φ.a i),
        acceptProb V (pcppOracle y π) (Φ.enc i) (ρ (Φ.enc i).length)
          (τ (Φ.enc i).length) ≤ ε i) ∧
    ∃ (S : OTM) (coin clock : ℕ → ℕ), PolyBdd coin ∧ PolyBdd clock ∧
      (∀ (i : Φ.Inst) (m : ℕ) (s : Fin (coin ((Φ.enc i).length + b i + m)) → Bool)
        (O : Oracle),
        S.result O (simInput (Φ.enc i) m s) (clock ((Φ.enc i).length + b i + m)) ≠ none) ∧
      ∀ (i : Φ.Inst), ∀ y ∈ Φ.Lang i, ∀ (m : ℕ)
        (Vs : MVerifier m (Fin (Φ.N i) ⊕ Fin (Fintype.card D)) (Φ.a i)),
        Vs.Bounded (b i) →
        (PMF.uniformOfFintype (Fin (coin ((Φ.enc i).length + b i + m)) → Bool)).map
            (fun s => S.output (pcppSimOracle y (Vs.oracle sumCode))
              (simInput (Φ.enc i) m s) (clock ((Φ.enc i).length + b i + m))) =
          (Vs.viewLaw ((P i y).map fun π => Sum.elim y π) (b i)).map viewCode ∧
        ∀ s : Fin (coin ((Φ.enc i).length + b i + m)) → Bool,
          (inputPositions (Φ.N i) (queryLog S (pcppSimOracle y (Vs.oracle sumCode))
            (simInput (Φ.enc i) m s) (clock ((Φ.enc i).length + b i + m)))).ncard ≤ b i * l i

end ZKSheafPCP.Supplement


