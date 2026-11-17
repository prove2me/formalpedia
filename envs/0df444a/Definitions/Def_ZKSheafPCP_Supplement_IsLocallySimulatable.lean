-- Prove2me | Definitions.Def_ZKSheafPCP_Supplement_IsLocallySimulatable
-- name    : ZKSheafPCP_Supplement_IsLocallySimulatable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:55:21.941207+00:00
-- url     : https://prove2.me/theorems/872e2f8a-ed05-40d1-b468-9da54931289e
-- title:
--   Linear randomized encodings and algorithmic local simulatability
-- statement:
--   A **linear randomized encoding** over a finite field is obtained by applying a deterministic linear map jointly to a message and a finite uniform field-valued seed.
--
--   A randomized encoding is **$(t,l,q)$-locally simulatable** when one oracle Turing machine handles every history of fewer than $q$ local-code queries that occurs in the encoding's support. On a history of size $k$, every run halts within $t(k)$ actual machine steps and reads at most $l(k)$ distinct message positions. Its decoded output distribution is exactly the conditional distribution of the encoded local word given the recorded history.
--
--   This interface preserves the computational and exact-distribution content of Definitions 6.1–6.2 and is reusable for finite-field randomized encodings beyond sheaf codes.
--
--   **Formalization Note** Field-valued random seeds represent uniform affine-space sampling exactly over every finite field. A finite-coordinate presentation supplies oracle access to an abstract message space. Validity is witnessed by a global encoded word in the PMF support, so no merely local but globally impossible history is admitted. The extension encoding is the uniform law of Definition 6.6.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definitions 6.1–6.2, p.25; Construction 6.8, p.26

import Mathlib
import Definitions.Def_ZKSheafPCP_simLaw
import Definitions.Def_ZKSheafPCP_IsPolynomial
import Definitions.Def_ZKSheafPCP_queryLog

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace ZKSheafPCP.Supplement

open Classical

/-- A linear randomized encoding (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge
PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission,
manuscript sha256 ac5e528f…, Definition 6.1, p.25): a deterministic linear map of a
message and a finite uniform field-valued seed. -/
structure LinearRandomizedEncoding (F M D : Type) [Field F] [AddCommMonoid M]
    [Module F M] where
  /-- Number of independent field elements in the random seed. -/
  seedLength : ℕ
  /-- The deterministic map, linear jointly in the message and random seed. -/
  encode : (M × (Fin seedLength → F)) →ₗ[F] (D → F)

/-- The output law of a linear randomized encoding on a fixed message. -/
noncomputable def LinearRandomizedEncoding.law {F M D : Type} [Field F] [Fintype F]
    [AddCommMonoid M] [Module F M] (E : LinearRandomizedEncoding F M D) (m : M) : PMF (D → F) :=
  (PMF.uniformOfFintype (Fin E.seedLength → F)).map fun r => E.encode (m, r)

/-- A canonical finite string representation of a word over a finite alphabet. -/
noncomputable def wordString {A F : Type} [Fintype A] [Fintype F] (w : A → F) : Str :=
  tup ((List.finRange (Fintype.card A)).map fun i =>
    binN (Fintype.equivFin F (w ((Fintype.equivFin A).symm i))))

/-- The bit oracle for a finite-alphabet word. One queried position is counted once even
if the machine reads several bits of its symbol. -/
noncomputable def wordOracle {A F : Type} [Fintype A] [Fintype F] (w : A → F) : Oracle :=
  proofOracle fun i => Fintype.equivFin F (w ((Fintype.equivFin A).symm i))

/-- Encode a finite subset by its membership vector. -/
noncomputable def finsetString {A : Type} [Fintype A] (s : Finset A) : Str :=
  List.ofFn fun i : Fin (Fintype.card A) => decide ((Fintype.equivFin A).symm i ∈ s)

/-- Encode a finite family of finite subsets by its membership vector. -/
noncomputable def finsetFamilyString {A : Type} [Fintype A]
    (S : Finset (Finset A)) : Str :=
  List.ofFn fun i : Fin (Fintype.card (Finset A)) =>
    decide ((Fintype.equivFin (Finset A)).symm i ∈ S)

/-- Decode a canonical word string; malformed output is sent to the zero word. -/
noncomputable def decodeWordString {A F : Type} [Fintype A] [Fintype F] [Zero F]
    (s : Str) : A → F :=
  if h : ∃ w : A → F, wordString w = s then h.choose else 0

/-- The explicit input received by the local-simulator machine: the recorded word,
queried local codes, fresh local code, and its field-valued random seed. -/
noncomputable def localSimulatorInput {F D : Type} [Fintype F] [Fintype D]
    {r : ℕ} (f : D → F) (Q : Finset (Finset D)) (ρ : Finset D)
    (seed : Fin r → F) : Str :=
  tup [wordString f, finsetFamilyString Q, finsetString ρ, wordString seed]

/-- A valid history is one that actually occurs in the support of the randomized
encoding, as required by Definition 6.2. -/
def ConsistentHistory {F M D : Type} [Zero F]
    (ENC : M → PMF (D → F)) (S : Finset (Finset D)) (q : ℕ)
    (m : M) (f : D → F) (Q : Finset (Finset D)) (ρ : Finset D) : Prop :=
  Q ⊆ S ∧ Q.card < q ∧ ρ ∈ S ∧
    ∃ g : D → F, restr (supp Q) g = f ∧ g ∈ (ENC m).support

/-- The conditional law in Definition 6.2: condition the encoding on the recorded
history and restrict the fresh answer to `ρ`. The history witness makes the
conditioning event nonempty. -/
noncomputable def conditionalLocalLaw {F M D : Type} [Zero F]
    (ENC : M → PMF (D → F)) (m : M) (f : D → F)
    (Q : Finset (Finset D)) (ρ : Finset D)
    (h : ∃ g : D → F, restr (supp Q) g = f ∧ g ∈ (ENC m).support) : PMF (D → F) :=
  ((ENC m).filter {g | restr (supp Q) g = f} (by
    rcases h with ⟨g, hg, hgs⟩
    exact ⟨g, hg, hgs⟩)).map (restr ρ)

/-- `(ENC,S)` is `(t,l,q)`-locally simulatable (Definition 6.2, p.25).

One finite oracle Turing machine is fixed before the message and history. Its actual
execution halts within `t(k)` steps and its query log contains at most `l(k)` distinct
message positions on every field-valued random seed. Its decoded output law is exactly
the encoding law conditioned on the recorded history.

**Formalization Note** The paper gives the simulator oracle access to a message in an
abstract space `M`; `read : M → I → F` is its finite-coordinate presentation. Random
seeds are field-valued, as in Definition 6.1, so exact uniform affine-space sampling is
available over finite fields of non-power-of-two order. -/
def IsLocallySimulatable {F I M D : Type} [Fintype F] [Fintype I] [Fintype D] [Zero F]
    (read : M → I → F) (ENC : M → PMF (D → F))
    (S : Finset (Finset D)) (t l : ℕ → ℕ) (q : ℕ) : Prop :=
  ∃ (Sim : OTM) (coins : ℕ → ℕ),
    ∀ (m : M) (f : D → F) (Q : Finset (Finset D)) (ρ : Finset D),
      ∀ h : ConsistentHistory ENC S q m f Q ρ,
        (∀ seed : Fin (coins Q.card) → F,
          let input := localSimulatorInput f Q ρ seed
          Sim.result (wordOracle (read m)) input (t Q.card) ≠ none ∧
            (queriedPositions (Fintype.card I)
              (queryLog Sim (wordOracle (read m)) input (t Q.card))).ncard ≤ l Q.card) ∧
        (PMF.uniformOfFintype (Fin (coins Q.card) → F)).map
            (fun seed => decodeWordString
              (Sim.output (wordOracle (read m)) (localSimulatorInput f Q ρ seed) (t Q.card))) =
          conditionalLocalLaw ENC m f Q ρ h.2.2.2

/-- The uniform extension encoding `ENC_σ` of Definition 6.6. Its message type is
the local code `F_σ`, so invalid local words are not silently admitted as messages. -/
noncomputable def extensionEncoding {F D : Type} [Field F] [Fintype F] [Fintype D]
    (PP : CodedSpace D) (𝓕 : LocalCodes F D) (σ : Finset D)
    (c : 𝓕.code σ) : PMF (D → F) :=
  uniformOn 0 (Finset.univ.filter fun g : D → F =>
    g ∈ 𝓕.relSections (PP.geq σ) (c : D → F) PP.P)

/-- `t(k)` is polynomially bounded in a size function `s(k)`, with explicit natural
constant and exponent. This is the paper's `t(k) ∈ poly(s(k))`. -/
def PolyBddIn (t s : ℕ → ℕ) : Prop :=
  ∃ C e : ℕ, ∀ k, t k ≤ C * (s k + 2) ^ e

end ZKSheafPCP.Supplement


