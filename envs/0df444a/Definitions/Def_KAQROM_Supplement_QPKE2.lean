-- Prove2me | Definitions.Def_KAQROM_Supplement_QPKE2
-- name    : KAQROM_Supplement_QPKE2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:51:43.129949+00:00
-- url     : https://prove2.me/theorems/6615b76d-fafd-438e-b587-886907fafc61
-- title:
--   QPKE with classical-query encryption and classical ciphertexts (Definition 3.13)
-- statement:
--   A **QPKE scheme with classical-query encryption** $\Sigma=(\mathrm{Gen},\mathrm{Enc},\mathrm{Dec})$ for messages $\{0,1\}^\mu$, $\mu\ge1$, has classical keys and the following parts:
--
--   1. $\mathrm{Gen}^H$, a $q_{\mathrm{Gen}}$-query quantum algorithm;
--   2. $\mathrm{Enc}^H(pk,m)$, which makes only classical oracle queries (at most $q_{\mathrm{Enc}}$), may compute quantumly, and outputs a classical ciphertext;
--   3. $\mathrm{Dec}^H(sk,c)$, a $q_{\mathrm{Dec}}$-query quantum algorithm.
--
--   Its minimum correct-decryption probability $\alpha_\Sigma$ is as in Definition 3.12. The IND-CPA advantage of a classical attacker is $|\Pr[\mathsf{IND}_{\Sigma,D}=1]-1/2|$ (Definition 3.14).
--
--   This is the object of Theorem 7.2.
--
--   **Formalization Note** Encryption is a classical-query stage started in an arbitrary oracle-independent state. $q_{\mathrm{Enc}}$ is a hypothesis (`EncQueriesLe`) over every oracle, every input and every branch of positive probability.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definitions 3.12–3.14, p.23

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_KAQROM_Instrument
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_QAlg
import Definitions.Def_KAQROM_Supplement_CStage
import Definitions.Def_KAQROM_Supplement_CINDAttacker

namespace KAQROM.Supplement

open Matrix
open KAQROM

/-- **Definition 3.13 (QPKE with classical-query encryption).** A scheme `Σ = (Gen, Enc, Dec)` for
messages `{0,1}^μ` (`μ ≥ 1`) with classical keys: `(pk, sk) ← Gen^H` is a `q_Gen`-query quantum
algorithm with classical output; `c ← Enc^H(pk, m)` makes only classical oracle queries (its local
computation may be quantum) and outputs a classical ciphertext `c ∈ Ct`; `m̂ ← Dec^H(sk, c)` is a
`q_Dec`-query quantum algorithm with output in `{0,1}^μ ∪ {⊥}`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.13
(with the syntax and correctness of Definition 3.12), p.23.

**Formalization Note.** `Gen` and `Dec` start from the trivial input register; `Enc` is a
classical-query stage started in an arbitrary oracle-independent state on its register. `q_Gen`,
`q_Dec` are query rounds of the published `KAQROM.QAlg`s; `q_Enc` is a hypothesis
(`EncQueriesLe`). -/
structure QPKE2 (X : Type) [Fintype X] [DecidableEq X] (ℓ μ : ℕ) where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- Classical ciphertexts. -/
  Ct : Type
  /-- `Enc`'s register. -/
  RE : Type
  /-- Work register of `Gen`. -/
  WG : Type
  /-- Work register of `Dec`. -/
  WD : Type
  /-- Kraus index type. -/
  ι : Type
  [fPK : Fintype PK] [fSK : Fintype SK] [fCt : Fintype Ct]
  [fRE : Fintype RE] [dRE : DecidableEq RE]
  [fWG : Fintype WG] [dWG : DecidableEq WG]
  [fWD : Fintype WD] [dWD : DecidableEq WD]
  [fι : Fintype ι]
  one_le_μ : 1 ≤ μ
  /-- The query bound `q_Gen`. -/
  qGen : ℕ
  /-- The query bound `q_Dec`. -/
  qDec : ℕ
  /-- `(pk, sk) ← Gen^H`. -/
  Gen : QAlg X ℓ Unit WG Unit (PK × SK) ι qGen
  /-- `Enc`'s initial state. -/
  ρE0 : Matrix RE RE ℂ
  ρE0_density : WildeQIT.IsDensityOperator ρE0
  /-- Classical query steps of `Enc`. -/
  DE : ℕ
  /-- `c ← Enc^H(pk, m)`, classical queries, classical ciphertext. -/
  Enc : CStage X ℓ (PK × Bits μ) Ct RE ι DE
  /-- `m̂ ← Dec^H(sk, c)`. -/
  Dec : SK → Ct → QAlg X ℓ Unit WD Unit (Option (Bits μ)) ι qDec

attribute [instance] QPKE2.fPK QPKE2.fSK QPKE2.fCt QPKE2.fRE QPKE2.dRE QPKE2.fWG QPKE2.dWG
  QPKE2.fWD QPKE2.dWD QPKE2.fι

namespace QPKE2

variable {X : Type} [Fintype X] [DecidableEq X] {ℓ μ : ℕ}

/-- `q_Enc` bounds encryption's classical queries (worst case). -/
def EncQueriesLe (S : QPKE2 X ℓ μ) (q : ℕ) : Prop := S.Enc.QueriesLe S.ρE0 q

/-- `Pr[Gen^H = (pk, sk)]`. -/
noncomputable def genP (S : QPKE2 X ℓ μ) (H : Oracle X ℓ) (pk : S.PK) (sk : S.SK) : ℝ :=
  (S.Gen.run H (1 : Matrix Unit Unit ℂ) (pk, sk)).trace.re

/-- `Pr[Enc^H(pk, m) = c]`. -/
noncomputable def encP (S : QPKE2 X ℓ μ) (H : Oracle X ℓ) (pk : S.PK) (m : Bits μ) (c : S.Ct) :
    ℝ :=
  ∑ oq : Fin S.DE → Option X, (S.Enc.run H (pk, m) oq c S.ρE0).1.trace.re

/-- `Pr[Dec^H(sk, c) = m̂]`. -/
noncomputable def decP (S : QPKE2 X ℓ μ) (H : Oracle X ℓ) (sk : S.SK) (c : S.Ct)
    (m' : Option (Bits μ)) : ℝ :=
  ((S.Dec sk c).run H (1 : Matrix Unit Unit ℂ) m').trace.re

/-- `Pr[Dec(sk, Enc(pk, m)) = m]`. -/
noncomputable def corrProb (S : QPKE2 X ℓ μ) (m : Bits μ) : ℝ :=
  (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ pk : S.PK, ∑ sk : S.SK,
    S.genP H pk sk * ∑ c : S.Ct, S.encP H pk m c * S.decP H sk c (some m)

/-- **`α_Σ`**, the minimum correct-decryption probability (Definitions 3.12–3.13, p.23). -/
noncomputable def alpha (S : QPKE2 X ℓ μ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty S.corrProb

/-- The law of the public key given `H`. -/
noncomputable def pkP (S : QPKE2 X ℓ μ) (H : Oracle X ℓ) (pk : S.PK) : ℝ :=
  ∑ sk : S.SK, S.genP H pk sk

/-- **`Adv^{IND-CPA}_{Σ,D}`** of a classical attacker (Definition 3.14, p.23). -/
noncomputable def advC (S : QPKE2 X ℓ μ) (D : CINDAttacker S.PK S.Ct X ℓ μ) : ℝ :=
  |D.success S.pkP S.encP - 1 / 2|

end QPKE2

end KAQROM.Supplement


