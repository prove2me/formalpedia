-- Prove2me | Definitions.Def_QuantumPRC_Supplement_PKQScheme
-- name    : QuantumPRC_Supplement_PKQScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:34:15.01989+00:00
-- url     : https://prove2.me/theorems/d8f46e11-e788-4e58-9b5c-9b0dab9bea93
-- title:
--   Public-key QPRCs for the completely depolarizing channel (Definition 4.1)
-- statement:
--   The **completely depolarizing channel** from $a$ to $b$ qubits is $\Delta(\rho)=\operatorname{Tr}(\rho)\,I/2^{b}$.
--
--   A **public-key channel code** from $n_L$ to $n_P$ qubits (the syntax of Definition 4.1) consists of a key generator that maps uniformly random coins $r\in\{0,1\}^{k(\lambda)}$ to a pair $(\mathsf{sk},\mathsf{pk})$ of classical keys (with classical codes), an encoding channel $\mathrm{Enc}_{\mathsf{pk}}$ from $n_L(\lambda)$ to $n_P(\lambda)$ qubits, and a decoding map $\mathrm{Dec}_{\mathsf{sk}}$ back. It is a **public-key QPRC robust to every $t$-local noise**, with the completely depolarizing channel as ideal distribution, if
--
--   1. (syntax) KeyGen is PPT and $\mathrm{Enc}$, $\mathrm{Dec}$ are QPT: polynomial-time machines print, from $(1^\lambda,\mathsf{pk})$ and from $(1^\lambda,\mathsf{sk})$, circuits whose channels are exactly $\mathrm{Enc}_{\mathsf{pk}}$ and $\mathrm{Dec}_{\mathsf{sk}}$;
--   2. (robustness (41)) for every $t$-local noise family $\mathcal E$ on $n_P(\lambda)$ qubits there is a negligible $\nu$ with
--   $$
--   \Big\|\mathop{\mathbb E}_{(\mathsf{pk},\mathsf{sk})\leftarrow\mathrm{KeyGen}(1^\lambda)}\mathrm{Dec}_{\mathsf{sk}}\circ\mathcal E_\lambda\circ\mathrm{Enc}_{\mathsf{pk}}-\mathrm{id}\Big\|_\diamond\le\nu(\lambda);
--   $$
--   3. (pseudorandomness (42)) for every uniform QPT adversary $\mathcal A$ with quantum oracle access there is a negligible $\nu$ with
--   $$
--   \Big|\Pr_{(\mathsf{pk},\mathsf{sk})}\big[1\leftarrow\mathcal A^{\mathrm{Enc}_{\mathsf{pk}}}(1^\lambda,\mathsf{pk})\big]-\Pr_{(\mathsf{pk},\mathsf{sk})}\big[1\leftarrow\mathcal A^{\Delta}(1^\lambda,\mathsf{pk})\big]\Big|\le\nu(\lambda).
--   $$
--
--   These are the notions in which Theorem 5.2 is stated.
--
--   **Formalization Note** KeyGen is a function of fair coins (a PPT key generator, a special case of the printed QPT one). Adversaries are the base mission's uniform oracle-circuit families (adaptive, possibly entangled quantum queries), reading the code of $\mathsf{pk}$ as classical input.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Definition 4.1, Eqs. (41)-(42), pp.24-25; §5, p.28

import Mathlib
import Definitions.Def_QuantumPRC_IsLocalNoise
import Definitions.Def_QuantumPRC_Assumption5

open Matrix

namespace QuantumPRC.Supplement

/-- **The completely depolarizing channel from `a` to `b` qubits**, `ρ ↦ Tr(ρ) · I/2^b`.
Hsieh, Yamada, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d…), p.25 ("the ideal
distribution outputs the completely depolarizing channel with probability one") and §5, p.28 ("As
the ideal distribution `D`, we consider the distribution that outputs the completely depolarizing
channel with probability one"). -/
noncomputable def depolarizing (a b : ℕ) : Superop (Bits a) (Bits b) :=
  fun ρ => Matrix.diagonal fun _ => ((2 : ℂ) ^ b)⁻¹ * Matrix.trace ρ

/-- **Public-key channel-level code from `nL` to `nP` qubits** (syntax of Definition 4.1).
Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), Definition 4.1, p.24: KeyGen outputs a classical
secret key `sk` and a classical public key `pk`; `Enc`, given `pk`, implements a CPTP map `Enc_pk` from
`nL` to `nP` qubits; `Dec`, given `sk`, implements a CPTP map `Dec_sk` from `nP` to `nL` qubits.

`keyGen λ r` is the key pair produced from the coin string `r ∈ {0,1}^{kc(λ)}`; `skCode`, `pkCode` are
the classical strings of the keys (`pkCode` is the adversary's input in (42)).

**Formalization Note.** KeyGen is modelled as a function of uniform coins (a PPT KeyGen, a special
case of the printed QPT KeyGen). Efficiency is the separate predicate `Implementable`. -/
structure PKQScheme (nL nP : ℕ → ℕ) where
  SK : ℕ → Type
  PK : ℕ → Type
  skCode : ∀ lam, SK lam → List Bool
  pkCode : ∀ lam, PK lam → List Bool
  kc : ℕ → ℕ
  keyGen : ∀ lam, Bits (kc lam) → SK lam × PK lam
  enc : ∀ lam, PK lam → Superop (Bits (nL lam)) (Bits (nP lam))
  dec : ∀ lam, SK lam → Superop (Bits (nP lam)) (Bits (nL lam))

namespace PKQScheme

variable {nL nP : ℕ → ℕ} (S : PKQScheme nL nP)

/-- `𝔼_{(pk,sk)←KeyGen(1^λ)} (Dec_sk ∘ N ∘ Enc_pk)` for a map `N` on `nP(λ)` qubits. -/
noncomputable def avgDecNEnc (lam : ℕ) (N : Superop (Bits (nP lam)) (Bits (nP lam))) :
    Superop (Bits (nL lam)) (Bits (nL lam)) :=
  fun ρ => ((2 : ℂ) ^ S.kc lam)⁻¹ •
    ∑ r : Bits (S.kc lam), S.dec lam (S.keyGen lam r).1 (N (S.enc lam (S.keyGen lam r).2 ρ))

/-- **Robustness (41)**, Definition 4.1, p.24:
`‖𝔼_{(pk,sk)←KeyGen(1^λ)}(Dec_sk ∘ E_λ ∘ Enc_pk) − id‖⋄ ≤ negl(λ)` for the noise family `E`. -/
def Robust (E : ∀ lam, WildeQIT.QChannel (Bits (nP lam)) (Bits (nP lam))) : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
    diamondDist (S.avgDecNEnc lam (E lam).apply) id ≤ ν lam

/-- **Pseudorandomness (42) with the completely depolarizing ideal channel**, Definition 4.1,
p.25, and §5, p.28: for any QPT adversary `A^{(·)}`,
`|Pr_{(pk,sk)}[1 ← A^{Enc_pk}(1^λ, pk)] − Pr_{(pk,sk), I←D_λ}[1 ← A^I(1^λ, pk)]| ≤ negl(λ)`, with `D_λ` the
point mass on the completely depolarizing channel from `nL(λ)` to `nP(λ)` qubits.

**Formalization Note.** Adversaries are uniform families of oracle circuits with one oracle from
`nL(λ)` to `nP(λ)` qubits (`QuantumPRC.OCirc`: adaptive quantum queries, possibly entangled with the
adversary's other wires); the `λ`-th circuit reads `pk` (its code) as classical input. `Enc_pk` is one
fixed channel, queried as often as the adversary likes. -/
def Pseudorandom : Prop :=
  ∀ A : ∀ lam, OCirc (nL lam) (nP lam) 1, IsUniformAdv A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |avg (fun r : Bits (S.kc lam) =>
          (A lam).accept (fun _ => S.enc lam (S.keyGen lam r).2) (S.pkCode lam (S.keyGen lam r).2)) -
        avg (fun r : Bits (S.kc lam) =>
          (A lam).accept (fun _ => depolarizing (nL lam) (nP lam))
            (S.pkCode lam (S.keyGen lam r).2))| ≤ ν lam

/-- **Implementability** (syntax of Definition 4.1, p.24): KeyGen is PPT (a polynomial-time map from
`1^λ` and polynomially many fair coins to the codes of `sk` and `pk`), and Enc and Dec are QPT: one
polynomial-time machine prints from `(1^λ, pk)` a circuit whose channel is exactly `Enc_pk`, and one
prints from `(1^λ, sk)` a circuit whose channel is exactly `Dec_sk`. -/
def Implementable : Prop :=
  PolyBounded S.kc ∧
  IsPolyFamily (α := fun lam => Bits (S.kc lam)) (fun lam r => (S.keyGen lam r).1)
    (fun _ r => [bits r]) S.skCode ∧
  IsPolyFamily (α := fun lam => Bits (S.kc lam)) (fun lam r => (S.keyGen lam r).2)
    (fun _ r => [bits r]) S.pkCode ∧
  ∃ (encC : ∀ lam, S.PK lam → Circuit (nL lam) (nP lam))
    (decC : ∀ lam, S.SK lam → Circuit (nP lam) (nL lam)),
    IsPolyFamily (α := S.PK) (β := fun lam => Circuit (nL lam) (nP lam)) encC
      (fun lam pk => [S.pkCode lam pk]) (fun _ C => C.encode) ∧
    IsPolyFamily (α := S.SK) (β := fun lam => Circuit (nP lam) (nL lam)) decC
      (fun lam sk => [S.skCode lam sk]) (fun _ C => C.encode) ∧
    (∀ lam pk, (encC lam pk).channel = S.enc lam pk) ∧
    (∀ lam sk, (decC lam sk).channel = S.dec lam sk)

/-- **Public-key QPRC (completely depolarizing ideal) robust to every `t`-local noise**,
Definition 4.1 with Definition 3.7 (the conclusion of Theorem 5.2, p.28): the syntax with efficiency,
robustness (41) for every `t`-local noise family on `nP(λ)` qubits (`∃ negl` after the family), and
pseudorandomness (42). -/
def IsQPRCLocal (t : ℕ → ℕ) : Prop :=
  S.Implementable ∧
    (∀ E : ∀ lam, WildeQIT.QChannel (Bits (nP lam)) (Bits (nP lam)),
      IsLocalNoise t nP E → S.Robust E) ∧
    S.Pseudorandom

end PKQScheme

end QuantumPRC.Supplement


