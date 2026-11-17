-- Prove2me | Definitions.Def_KAQROM_Supplement_QPKE1
-- name    : KAQROM_Supplement_QPKE1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:50:53.301955+00:00
-- url     : https://prove2.me/theorems/09af5b9d-7dc0-4f36-8bdd-59c637bc11fa
-- title:
--   QPKE with classical-query key generation (Definition 3.12), quantum IND-CPA attackers, and the classical-Gen/Dec variant
-- statement:
--   A **QPKE scheme with classical-query key generation** $\Sigma=(\mathrm{Gen},\mathrm{Enc},\mathrm{Dec})$ for messages $\{0,1\}^\mu$, $\mu\ge1$, consists of:
--
--   1. $\mathrm{Gen}^H$, which has classical oracle access (at most $q_{\mathrm{Gen}}$ queries) and outputs classical keys $(pk,sk)$;
--   2. $\mathrm{Enc}^H(pk,m)$, a $q_{\mathrm{Enc}}$-query quantum algorithm with a possibly quantum ciphertext register;
--   3. $\mathrm{Dec}^H(sk,C)$, a $q_{\mathrm{Dec}}$-query quantum algorithm with output in $\{0,1\}^\mu\cup\{\bot\}$.
--
--   Its **minimum correct-decryption probability** is
--   $$
--   \alpha_\Sigma=\min_m\Pr[\mathrm{Dec}^H(sk,\mathrm{Enc}^H(pk,m))=m].
--   $$
--   A **quantum IND-CPA attacker** $D=(D_0,D_1)$ (Definition 3.14) has a $q_0$-query first stage $(Z_D,m_0,m_1)\leftarrow D_0^H(pk)$ and a $q_1$-query second stage $b'\leftarrow D_1^H(Z_D,C)$ that receives the challenge register. Its advantage is $\mathrm{Adv}^{\mathrm{IND\text{-}CPA}}_{\Sigma,D}=|\Pr[b'=b]-1/2|$.
--
--   The variant `QPKE1c` is the case where key generation and decryption are classical algorithms and the ciphertext is classical, while encryption may still compute quantumly. Its $\alpha_\Sigma$ is defined in the same way, and its attackers are the classical attackers `CINDAttacker`.
--
--   These are the objects of Theorem 7.1.
--
--   **Formalization Note** The security parameter is fixed, so $\mu$ is a number. `Gen` starts from an arbitrary oracle-independent state, and `Enc`, `Dec` and the attacker stages start from the trivial register. Classical algorithms are classical-query stages on a one-dimensional register.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definitions 3.12 and 3.14, p.23; Theorem 7.1, pp.71–72

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_Supplement_CStage
import Definitions.Def_KAQROM_Supplement_CINDAttacker

namespace KAQROM.Supplement

open Matrix
open scoped Kronecker
open KAQROM

/-- **Definition 3.12 (QPKE with classical-query key generation).** A scheme
`Σ = (Gen, Enc, Dec)` for messages `M = {0,1}^μ` (`μ ≥ 1`) relative to `H : X → {0,1}^ℓ`:

* `(pk, sk) ← Gen^H` outputs classical keys in `PK × SK`, with classical oracle access (its ordered
  query–answer transcript is `T_Gen`);
* `C ← Enc^H(pk, m)` is a `q_Enc`-query quantum algorithm with a possibly quantum ciphertext
  register `C`;
* `m̂ ← Dec^H(sk, C)` is a `q_Dec`-query quantum algorithm with output in `M ∪ {⊥}`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.12,
p.23.

**Formalization Note.** The security parameter is fixed, so `μ` is a number with `1 ≤ μ`;
messages are bit strings `Fin μ → ZMod 2`. `Enc` starts from the trivial one-dimensional input
register (all-zero work registers); `Gen` starts from an arbitrary oracle-independent state on its
register (all-zero registers followed by local preparation give exactly these). `q_Enc`, `q_Dec`
are the query rounds of the published `KAQROM.QAlg`s. -/
structure QPKE1 (X : Type) [Fintype X] [DecidableEq X] (ℓ μ : ℕ) where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- The ciphertext register. -/
  C : Type
  /-- `Gen`'s register. -/
  RG : Type
  /-- Work register of `Enc`. -/
  WE : Type
  /-- Work register of `Dec`. -/
  WD : Type
  /-- Kraus index type. -/
  ι : Type
  [fPK : Fintype PK] [fSK : Fintype SK]
  [fC : Fintype C] [dC : DecidableEq C]
  [fRG : Fintype RG] [dRG : DecidableEq RG]
  [fWE : Fintype WE] [dWE : DecidableEq WE]
  [fWD : Fintype WD] [dWD : DecidableEq WD]
  [fι : Fintype ι]
  one_le_μ : 1 ≤ μ
  /-- `Gen`'s initial state. -/
  ρG0 : Matrix RG RG ℂ
  ρG0_density : WildeQIT.IsDensityOperator ρG0
  /-- The number of classical query steps of `Gen`. -/
  DG : ℕ
  /-- Key generation, with classical oracle access. -/
  Gen : CStage X ℓ Unit (PK × SK) RG ι DG
  /-- The query bound `q_Enc`. -/
  qEnc : ℕ
  /-- The query bound `q_Dec`. -/
  qDec : ℕ
  /-- `C ← Enc^H(pk, m)`. -/
  Enc : PK → Bits μ → QAlg X ℓ Unit WE C Unit ι qEnc
  /-- `m̂ ← Dec^H(sk, C)`. -/
  Dec : SK → QAlg X ℓ C WD Unit (Option (Bits μ)) ι qDec

attribute [instance] QPKE1.fPK QPKE1.fSK QPKE1.fC QPKE1.dC QPKE1.fRG QPKE1.dRG QPKE1.fWE
  QPKE1.dWE QPKE1.fWD QPKE1.dWD QPKE1.fι

namespace QPKE1

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ μ : ℕ}

/-- `q_Gen` bounds key generation's classical queries (worst case, every branch of positive
probability). -/
def GenQueriesLe (S : QPKE1 X ℓ μ) (q : ℕ) : Prop :=
  S.Gen.QueriesLe S.ρG0 q

/-- The probability weight of `Gen`'s branch `(oq, pk, sk)` under `H`. -/
noncomputable def genW (S : QPKE1 X ℓ μ) (H : Oracle X ℓ) (oq : Fin S.DG → Option X) (pk : S.PK)
    (sk : S.SK) : ℝ :=
  (S.Gen.run H () oq (pk, sk) S.ρG0).1.trace.re

/-- `Pr[Dec^H(sk, C) = m : H ← ℋ, (pk, sk) ← Gen^H, C ← Enc^H(pk, m)]`. -/
noncomputable def corrProb (S : QPKE1 X ℓ μ) (m : Bits μ) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ oq : Fin S.DG → Option X,
    ∑ pk : S.PK, ∑ sk : S.SK, S.genW H oq pk sk *
      ((S.Dec sk).run H ((S.Enc pk m).run H (1 : Matrix Unit Unit ℂ) ()) (some m)).trace.re

/-- **The minimum correct-decryption probability** `α_Σ = min_{m ∈ M} Pr[Dec(sk, Enc(pk, m)) = m]`
(Definition 3.12, p.23). -/
noncomputable def alpha (S : QPKE1 X ℓ μ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty S.corrProb

end QPKE1

/-- A **quantum two-stage IND-CPA attacker** `D = (D₀, D₁)` against a Definition 3.12 scheme
(Definition 3.14, p.23): `(Z_D, m₀, m₁) ← D₀^H(pk)` is a `q0`-query quantum algorithm with
classical output `(m₀, m₁)` and quantum state `Z_D`; `b' ← D₁^H(Z_D, C)` is a `q1`-query quantum
algorithm on `Z_D` and the transferred ciphertext register. It makes `q0 + q1` oracle queries.

**Formalization Note.** `D₁` is chosen by the classical data `(pk, m₀, m₁)` that `D₀` holds (it
could equally be kept in `Z_D`). Classical queries are special quantum queries. -/
structure INDAttacker {X : Type} [Fintype X] [DecidableEq X] {ℓ μ : ℕ} (S : QPKE1 X ℓ μ) where
  /-- The register `Z_D`. -/
  RZ : Type
  /-- Work register of `D₀`. -/
  W0 : Type
  /-- Work register of `D₁`. -/
  W1 : Type
  /-- Kraus index type. -/
  ι : Type
  [fRZ : Fintype RZ] [dRZ : DecidableEq RZ]
  [fW0 : Fintype W0] [dW0 : DecidableEq W0]
  [fW1 : Fintype W1] [dW1 : DecidableEq W1]
  [fι : Fintype ι]
  /-- Query bound of `D₀`. -/
  q0 : ℕ
  /-- Query bound of `D₁`. -/
  q1 : ℕ
  /-- `(Z_D, m₀, m₁) ← D₀^H(pk)`. -/
  D0 : S.PK → QAlg X ℓ Unit W0 RZ (Bits μ × Bits μ) ι q0
  /-- `b' ← D₁^H(Z_D, C)`. -/
  D1 : S.PK → Bits μ → Bits μ → QAlg X ℓ (RZ × S.C) W1 Unit Bool ι q1

attribute [instance] INDAttacker.fRZ INDAttacker.dRZ INDAttacker.fW0 INDAttacker.dW0
  INDAttacker.fW1 INDAttacker.dW1 INDAttacker.fι

namespace QPKE1

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ μ : ℕ}

/-- **`Adv^{IND-CPA}_{Σ,D} = |Pr[IND_{Σ,D} = 1] − 1/2|`** (Definition 3.14, p.23): `H ← ℋ`,
`(pk, sk) ← Gen^H`, `(Z_D, m₀, m₁) ← D₀^H(pk)`, `b ← {0,1}`, `C ← Enc^H(pk, m_b)` transferred to
`D₁`, `b' ← D₁^H(Z_D, C)`; success iff `b' = b`. -/
noncomputable def adv (S : QPKE1 X ℓ μ) (D : INDAttacker S) : ℝ :=
  |(Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ oq : Fin S.DG → Option X,
      ∑ pk : S.PK, ∑ sk : S.SK, S.genW H oq pk sk * ∑ m0 : Bits μ, ∑ m1 : Bits μ, ∑ b : Bool,
        (1 / 2 : ℝ) * ((D.D1 pk m0 m1).run H
          ((D.D0 pk).run H (1 : Matrix Unit Unit ℂ) (m0, m1) ⊗ₖ
            (S.Enc pk (if b then m1 else m0)).run H (1 : Matrix Unit Unit ℂ) ()) b).trace.re
    - 1 / 2|

end QPKE1

/-- **A Definition 3.12 scheme whose key generation and decryption are classical algorithms and
whose ciphertext is classical** (Theorem 7.1, last sentence, p.72): `Gen` and `Dec` are classical
randomized algorithms with classical oracle access (classical-query stages on a one-dimensional
register), and `Enc` is a `q_Enc`-query quantum algorithm whose output is a classical ciphertext in
`Ct`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.12,
p.23, and Theorem 7.1, p.72.

**Formalization Note.** A classical-query stage on the register `Unit` carries no quantum state:
each step is a probability distribution over the next query given the input and the answers so
far, and the output is a distribution given the whole record, which is exactly a classical
randomized algorithm with classical oracle access. -/
structure QPKE1c (X : Type) [Fintype X] [DecidableEq X] (ℓ μ : ℕ) where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- Classical ciphertexts. -/
  Ct : Type
  /-- Work register of `Enc`. -/
  WE : Type
  /-- Kraus index type. -/
  ι : Type
  [fPK : Fintype PK] [fSK : Fintype SK] [fCt : Fintype Ct]
  [fWE : Fintype WE] [dWE : DecidableEq WE]
  [fι : Fintype ι]
  one_le_μ : 1 ≤ μ
  /-- Classical query steps of `Gen` and `Dec`. -/
  DG : ℕ
  DD : ℕ
  /-- Classical key generation. -/
  Gen : CStage X ℓ Unit (PK × SK) Unit ι DG
  /-- The query bound `q_Enc`. -/
  qEnc : ℕ
  /-- `c ← Enc^H(pk, m)`, quantum with classical output. -/
  Enc : PK → Bits μ → QAlg X ℓ Unit WE Unit Ct ι qEnc
  /-- Classical decryption `m̂ ← Dec^H(sk, c)`. -/
  Dec : CStage X ℓ (SK × Ct) (Option (Bits μ)) Unit ι DD

attribute [instance] QPKE1c.fPK QPKE1c.fSK QPKE1c.fCt QPKE1c.fWE QPKE1c.dWE QPKE1c.fι

namespace QPKE1c

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ μ : ℕ}

/-- `q_Gen` bounds `Gen`'s queries. -/
def GenQueriesLe (S : QPKE1c X ℓ μ) (q : ℕ) : Prop := S.Gen.QueriesLe 1 q

/-- `q_Dec` bounds `Dec`'s queries. -/
def DecQueriesLe (S : QPKE1c X ℓ μ) (q : ℕ) : Prop := S.Dec.QueriesLe 1 q

/-- `Pr[(pk, sk) ← Gen^H]` given `H`, on the branch `oq`. -/
noncomputable def genW (S : QPKE1c X ℓ μ) (H : Oracle X ℓ) (oq : Fin S.DG → Option X)
    (pk : S.PK) (sk : S.SK) : ℝ :=
  (S.Gen.run H () oq (pk, sk) 1).1.trace.re

/-- `Pr[Enc^H(pk, m) = c]`. -/
noncomputable def encP (S : QPKE1c X ℓ μ) (H : Oracle X ℓ) (pk : S.PK) (m : Bits μ) (c : S.Ct) :
    ℝ :=
  ((S.Enc pk m).run H (1 : Matrix Unit Unit ℂ) c).trace.re

/-- `Pr[Dec^H(sk, c) = m̂]`. -/
noncomputable def decP (S : QPKE1c X ℓ μ) (H : Oracle X ℓ) (sk : S.SK) (c : S.Ct)
    (m' : Option (Bits μ)) : ℝ :=
  ∑ oq : Fin S.DD → Option X, (S.Dec.run H (sk, c) oq m' 1).1.trace.re

/-- `Pr[Dec(sk, Enc(pk, m)) = m]`. -/
noncomputable def corrProb (S : QPKE1c X ℓ μ) (m : Bits μ) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ oq : Fin S.DG → Option X,
    ∑ pk : S.PK, ∑ sk : S.SK, S.genW H oq pk sk *
      ∑ c : S.Ct, S.encP H pk m c * S.decP H sk c (some m)

/-- **`α_Σ`** (Definition 3.12, p.23). -/
noncomputable def alpha (S : QPKE1c X ℓ μ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty S.corrProb

/-- The law of the public key given `H`. -/
noncomputable def pkP (S : QPKE1c X ℓ μ) (H : Oracle X ℓ) (pk : S.PK) : ℝ :=
  ∑ oq : Fin S.DG → Option X, ∑ sk : S.SK, S.genW H oq pk sk

/-- **`Adv^{IND-CPA}_{Σ,D}`** of a classical attacker (Definition 3.14, p.23). -/
noncomputable def advC (S : QPKE1c X ℓ μ) (D : CINDAttacker S.PK S.Ct X ℓ μ) : ℝ :=
  |D.success S.pkP S.encP - 1 / 2|

end QPKE1c

end KAQROM.Supplement


