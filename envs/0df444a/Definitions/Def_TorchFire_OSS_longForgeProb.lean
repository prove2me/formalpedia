-- Prove2me | Definitions.Def_TorchFire_OSS_longForgeProb
-- name    : TorchFire_OSS_longForgeProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:39:17.385335+00:00
-- url     : https://prove2.me/theorems/74092bdd-9f37-4be0-a1c6-1c20864e40dc
-- title:
--   Correctness (2) and strong one-shot security (3) of Definition 4.1 for Constructions 4.7 and 4.13
-- statement:
--   The experiments of Definition 4.1 for the one-bit scheme (Construction 4.7) and the long-message scheme (Construction 4.13).
--
--   1. **Correctness probability** for a message: sample $O$, run $\mathrm{OSS.GenQKey}^O$, sign the message with the signing register, and verify (2).
--   2. **Strong forging probability**: an adversary is an oracle algorithm with no quantum input and query access to the public collection; it outputs $(y,b_0,u_0,b_1,u_1)$ (one-bit) or $(a,M_0,\sigma_0,M_1,\sigma_1)$ (long-message), and wins if the two message–signature pairs differ and both verify under the same key:
--   $$\Pr[(m_0,\sigma_0)\ne(m_1,\sigma_1)\wedge\mathrm{Ver}(y,m_0,\sigma_0)=\mathrm{Ver}(y,m_1,\sigma_1)=1].$$
--
--   All probabilities are averages over the uniform oracle distribution and include measurement outcomes.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Definition 4.1 (2)–(3) p.19; Theorem 4.11 p.22; Theorem 4.14 p.23

import Mathlib
import Definitions.Def_TorchFire_OSS_LongSample
import Definitions.Def_TorchFire_Model_OracleAlg

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model

namespace TorchFire.OSS

/-- The adversary's classical output `(y, b_0, u_0, b_1, u_1)` in the one-bit strong-security game
(Theorem 4.11, p.22). -/
abbrev OneForgeOut (lam : ℕ) : Type :=
  Bits (r lam) × ZMod 2 × Bits (k lam) × ZMod 2 × Bits (k lam)

/-- A forger against the one-bit scheme: an oracle algorithm with no quantum input, query access to
the public collection `(P, P⁻¹, D)`, and classical output `(y, b_0, u_0, b_1, u_1)`. -/
abbrev OneForger (lam : ℕ) : Type 1 :=
  OracleAlg Unit (OneForgeOut lam) (PubDom lam) (PubAns lam)

variable {lam : ℕ}

open Classical in
/-- **The one-bit strong forging probability** (Theorem 4.11, p.22; Chatterjee–Mukherjee–Pathak–
Podder, *Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256
4e43d2f2…afd593):

  `Pr[(b_0, u_0) ≠ (b_1, u_1) ∧ OSS.Ver^O(y, b_0, u_0) = OSS.Ver^O(y, b_1, u_1) = 1 :
      O ← OSS.GenOracles(1^λ), (y, b_0, u_0, b_1, u_1) ← A^O(1^λ)]`. -/
noncomputable def oneForgeProb (A : OneForger lam) : ℝ :=
  avg (OneSample lam) fun ω =>
    ∑ o : OneForgeOut lam,
      if (o.2.1, o.2.2.1) ≠ (o.2.2.2.1, o.2.2.2.2) ∧ verBits ω o.1 o.2.1 o.2.2.1 ∧
          verBits ω o.1 o.2.2.2.1 o.2.2.2.2
      then (A.run (pubOracle ω) (1 : Matrix Unit Unit ℂ) o o).re else 0

/-- **One-bit correctness probability** for the message bit `b` (Definition 4.1 (2), p.19, for
Construction 4.7; Theorem 4.10, p.22): sample `O`, run `OSS.GenQKey^O` (Construction 4.6 and a
measurement of `Y`), sign `b` with the signing register, and verify. -/
noncomputable def oneCorrProb (lam : ℕ) (b : ZMod 2) : ℝ :=
  avg (OneSample lam) fun ω =>
    ∑ y : Bits (r lam), ∑ σ : Sig lam,
      if ver ω y b σ then (signOut ω y b (block (genQKeyCQ ω) y) σ σ).re else 0


/-- The adversary's classical output `(a, M_0, σ_0, M_1, σ_1)` in the long-message strong-security
game (Definition 4.1 (3) with `(m_0, σ_0) ≠ (m_1, σ_1)`, p.19). -/
abbrev LongForgeOut (lam : ℕ) (Msg : Type) : Type :=
  (Fin (L lam) → Bits (r lam)) × Msg × (Fin (L lam) → Sig lam) × Msg × (Fin (L lam) → Sig lam)

/-- A forger against the long-message scheme, with query access to `(O_1, …, O_L, Dig)`. -/
abbrev LongForger (lam : ℕ) (Msg : Type) [Fintype Msg] [DecidableEq Msg] : Type 1 :=
  OracleAlg Unit (LongForgeOut lam Msg) (LongDom lam Msg) (LongAns lam)

open Classical in
/-- **The long-message strong forging probability** (Definition 4.1 (3), strong version, p.19, for
Construction 4.13):
`Pr[(M_0, σ_0) ≠ (M_1, σ_1) ∧ OSS.Ver^O(a, M_0, σ_0) = OSS.Ver^O(a, M_1, σ_1) = 1]`. -/
noncomputable def longForgeProb {Msg : Type} [Fintype Msg] [DecidableEq Msg]
    (A : LongForger lam Msg) : ℝ :=
  avg (LongSample lam Msg) fun ω =>
    ∑ o : LongForgeOut lam Msg,
      if (o.2.1, o.2.2.1) ≠ (o.2.2.2.1, o.2.2.2.2) ∧ longVer ω o.1 o.2.1 o.2.2.1 ∧
          longVer ω o.1 o.2.2.2.1 o.2.2.2.2
      then (A.run (longPubOracle ω) (1 : Matrix Unit Unit ℂ) o o).re else 0

/-- **Long-message correctness probability** for the message `M` (Definition 4.1 (2), p.19, for
Construction 4.13): sample `O`, generate `(a, R_1 ⋯ R_L)`, sign `M`, verify. -/
noncomputable def longCorrProb (lam : ℕ) {Msg : Type} [Fintype Msg] [DecidableEq Msg] (M : Msg) : ℝ :=
  avg (LongSample lam Msg) fun ω =>
    ∑ a : Fin (L lam) → Bits (r lam), ∑ σ : Fin (L lam) → Sig lam,
      if longVer ω a M σ then (longSignOut ω a M (block (longGenQKeyCQ ω) a) σ σ).re else 0

end TorchFire.OSS


