-- Prove2me | Definitions.Def_KAQROM_Supplement_CINDAttacker
-- name    : KAQROM_Supplement_CINDAttacker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:50:05.395562+00:00
-- url     : https://prove2.me/theorems/5d4039bf-7ec3-43ce-aa4f-9e0266eafdd2
-- title:
--   Classical two-stage IND-CPA attackers and $\Pr[\mathsf{IND}=1]$ for classical ciphertexts
-- statement:
--   A **classical IND-CPA attacker** $D=(D_0,D_1)$ against a scheme with public keys in $PK$, classical ciphertexts in $C$ and messages $\{0,1\}^\mu$ draws coins $\omega$ (finitely many values, probabilities $w(\omega)$). Then $D_0$, a deterministic classical-query algorithm on $pk$, outputs $(m_0,m_1)$, and $D_1$, a deterministic classical-query algorithm on $pk$, $D_0$'s query–answer list and the ciphertext, outputs $b'$. In the experiment of Definition 3.14 the challenger samples $H\leftarrow\mathcal H$ and the public key, runs $D_0$, picks $b\leftarrow\{0,1\}$ and $C\leftarrow\mathrm{Enc}^H(pk,m_b)$, runs $D_1$, and the attacker succeeds iff $b'=b$. Its worst-case query bound is the total number of queries of both stages for every coin, oracle, key and ciphertext.
--
--   These attackers appear in the classical clause of Theorem 7.1 and in Theorem 7.2.
--
--   **Formalization Note** A classical state $Z_D$ can always be taken to be $D_0$'s whole view, which is what $D_1$ receives. The success probability is defined from the law of $pk$ given $H$ and the encryption law, so that it serves both scheme types.
-- source:
--   Kitagawa–Nishimaki–Villányi–Yamakawa, Towards the Impossibility of Imperfectly Complete Key Agreement in the QROM, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.14, p.23; p.46 (classical attackers)

import Mathlib
import Definitions.Def_KAQROM_Oracle
import Definitions.Def_KAQROM_Supplement_DetAttacker

namespace KAQROM.Supplement

open KAQROM

/-- A **classical two-stage IND-CPA attacker** `D = (D₀, D₁)` (Definition 3.14, p.23) against a
scheme with public keys in `PK`, classical ciphertexts in `Ct` and messages `{0,1}^μ`: coins
`ω ∈ Ω` with probabilities `w ω`; `D₀ = A0 ω` is a deterministic classical-query algorithm on `pk`
outputting `(m₀, m₁)`; `D₁ = A1 ω` is a deterministic classical-query algorithm on
`(pk, D₀'s query–answer list, C)` outputting the guess `b'`.

Kitagawa–Nishimaki–Villányi–Yamakawa, *Towards the Impossibility of Imperfectly Complete Key
Agreement in the QROM*, arXiv:2608.17610 (held version, sha256 ab8528fe…2c10), Definition 3.14,
p.23; "classical computation and classical oracle queries", p.46.

**Formalization Note.** A classical state `Z_D` can always be taken to be `D₀`'s whole view
(coins, `pk`, its queries and answers), which is what `D₁` receives here. Finitely many coin values
restrict the class; the class is used only under "there is a classical attacker". -/
structure CINDAttacker (PK Ct X : Type) (ℓ μ : ℕ) where
  /-- The coin space. -/
  Ω : Type
  [fΩ : Fintype Ω]
  /-- The coin distribution. -/
  w : Ω → ℝ
  w_nonneg : ∀ ω, 0 ≤ w ω
  w_sum : ∑ ω, w ω = 1
  /-- First stage: `(m₀, m₁)` from `pk`. -/
  A0 : Ω → DetAttacker PK X ℓ (Bits μ × Bits μ)
  /-- Second stage: `b'` from `pk`, the first stage's query–answer list and the ciphertext. -/
  A1 : Ω → DetAttacker (PK × Transcript X ℓ × Ct) X ℓ Bool

attribute [instance] CINDAttacker.fΩ

namespace CINDAttacker

variable {PK Ct X : Type} [Fintype PK] [Fintype Ct] [Fintype X] {ℓ μ : ℕ}

/-- Worst-case total query bound: for every coin value, oracle, public key and ciphertext, the two
stages together make at most `N` classical queries. -/
def QueriesLe (D : CINDAttacker PK Ct X ℓ μ) (N : ℕ) : Prop :=
  ∀ ω (H : Oracle X ℓ) (pk : PK) (c : Ct),
    ((D.A0 ω).learned H pk).length +
      ((D.A1 ω).learned H (pk, (D.A0 ω).learned H pk, c)).length ≤ N

/-- `Pr[IND_{Σ,D} = 1]` (Definition 3.14, p.23) for a scheme whose public key has law
`genP H pk` given `H` and whose encryption of `m` under `pk` outputs ciphertext `c` with probability
`encP H pk m c`: `H ← ℋ`, `pk`, the coins `ω`, `(m₀, m₁) ← D₀`, `b ← {0,1}`, `C ← Enc(pk, m_b)`,
`b' ← D₁`; success iff `b' = b`. -/
noncomputable def success (D : CINDAttacker PK Ct X ℓ μ) (genP : Oracle X ℓ → PK → ℝ)
    (encP : Oracle X ℓ → PK → Bits μ → Ct → ℝ) : ℝ := by
  classical
  exact (Fintype.card (Oracle X ℓ) : ℝ)⁻¹ * ∑ H : Oracle X ℓ, ∑ pk : PK, genP H pk *
    ∑ ω, D.w ω * ∑ b : Bool, (1 / 2 : ℝ) * ∑ c : Ct,
      encP H pk (if b then ((D.A0 ω).out H pk).2 else ((D.A0 ω).out H pk).1) c *
        (if (D.A1 ω).out H (pk, (D.A0 ω).learned H pk, c) = b then 1 else 0)

end CINDAttacker

end KAQROM.Supplement


