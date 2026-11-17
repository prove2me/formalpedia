-- Prove2me | Definitions.Def_QuantumPRC_Supplement_C51
-- name    : QuantumPRC_Supplement_C51
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:34:46.334024+00:00
-- url     : https://prove2.me/theorems/6bf2edf3-fc9b-4511-af6a-25e9593347a2
-- title:
--   Construction 5.1: Pauli one-time pad on a QECC, keyed by a public-key PRC
-- statement:
--   Let $(\mathrm{QECC.Enc},\mathrm{QECC.Dec})$ encode $n_L$ qubits into $\ell$ qubits, with isometry $V$, and let $(\mathrm{PRC.KeyGen},\mathrm{PRC.Enc},\mathrm{PRC.Dec})$ be a $(2\ell,m)$ public-key pseudorandom code. **Construction 5.1** builds a public-key code from $n_L$ to $n_P:=\ell+m$ qubits, on a register $\mathbf B$ of $\ell$ qubits followed by a register $\mathbf C$ of $m$ qubits:
--
--   1. **KeyGen**: run $(\mathsf{sk},\mathsf{pk})\leftarrow\mathrm{PRC.KeyGen}(1^\lambda)$.
--   2. **Enc**: choose $x,z\leftarrow\{0,1\}^\ell$ and coins $r$ for PRC.Enc uniformly, and apply the isometry
--   $$
--   |\psi\rangle_{\mathbf A}\ \mapsto\ (X^xZ^z)_{\mathbf B}\,V|\psi\rangle\otimes|\mathrm{PRC.Enc}(\mathsf{pk},x\|z;r)\rangle_{\mathbf C}. \tag{51}
--   $$
--   As a channel, $\mathrm{Enc}_{\mathsf{pk}}$ is the uniform average over $x,z,r$ of these isometric channels.
--   3. **Dec**: measure $\mathbf C$ in the computational basis, obtaining $c$; let $x\|z:=\mathrm{PRC.Dec}(\mathsf{sk},c)$, or $0^{2\ell}$ if the decoder outputs $\bot$; apply $(X^xZ^z)^\dagger$ to $\mathbf B$; apply $\mathrm{QECC.Dec}$ and output the result.
--
--   This is the scheme that Theorem 5.2 shows to be a public-key QPRC for the completely depolarizing channel.
--
--   **Formalization Note** $x\|z$ is $x$ followed by $z$; the PRC is the base mission's `PKPRC` with message length $2\ell$.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Construction 5.1, Eq. (51), p.28

import Mathlib
import Definitions.Def_QuantumPRC_Supplement_QECC
import Definitions.Def_QuantumPRC_Supplement_PKQScheme
import Definitions.Def_QuantumPRC_SKPRC
import Definitions.Def_QuantumPRC_PRF

open Matrix

namespace QuantumPRC.Supplement

/-- `x∥z`: the string `x` followed by the string `z`, of length `2ℓ`. -/
def catB {l : ℕ} (x z : Bits l) : Bits (2 * l) :=
  fun i => if h : i.val < l then x ⟨i.val, h⟩ else z ⟨i.val - l, by omega⟩

/-- The first half `x` of a string `x∥z` of length `2ℓ`. -/
def fstHalf {l : ℕ} (s : Bits (2 * l)) : Bits l := fun i => s ⟨i.val, by omega⟩

/-- The second half `z` of a string `x∥z` of length `2ℓ`. -/
def sndHalf {l : ℕ} (s : Bits (2 * l)) : Bits l := fun i => s ⟨l + i.val, by omega⟩

namespace C51

variable {nL ℓ m : ℕ → ℕ}

/-- **The isometry (51)** of Construction 5.1 for fixed `pk`, `x, z ∈ {0,1}^ℓ` and PRC coins `r`:
`|ψ⟩_A ↦ (X^x Z^z)_B · QECC.Enc_{A→B} |ψ⟩_A ⊗ |PRC.Enc(pk, x∥z; r)⟩_C`. Register order of the
`ℓ + m` physical qubits: `B` is the first `ℓ` qubits, `C` the last `m`. -/
noncomputable def encIso (Q : QECC nL ℓ) (P : PKPRC (fun lam => 2 * ℓ lam) m) (lam : ℕ)
    (pk : P.PK lam) (x z : Bits (ℓ lam)) (r : Bits (P.ec lam)) :
    Matrix (Bits (ℓ lam + m lam)) (Bits (nL lam)) ℂ :=
  fun y a => if rightPart y = P.enc lam pk (catB x z) r then (pauliXZ x z * Q.iso lam) (leftPart y) a
    else 0

/-- **Enc of Construction 5.1**, p.28: "Choose `x, z ← {0,1}^ℓ` and internal randomness `r` for
PRC.Enc, and apply the isometry (51)". As a channel, `Enc_pk` is the uniform average over `x`, `z`,
`r` of `ρ ↦ V_{x,z,r} ρ V_{x,z,r}†`, with fresh `x, z, r` at every use. -/
noncomputable def encCh (Q : QECC nL ℓ) (P : PKPRC (fun lam => 2 * ℓ lam) m) (lam : ℕ)
    (pk : P.PK lam) : Superop (Bits (nL lam)) (Bits (ℓ lam + m lam)) :=
  fun ρ => (((2 : ℂ) ^ ℓ lam)⁻¹ * ((2 : ℂ) ^ ℓ lam)⁻¹ * ((2 : ℂ) ^ P.ec lam)⁻¹) •
    ∑ x : Bits (ℓ lam), ∑ z : Bits (ℓ lam), ∑ r : Bits (P.ec lam),
      conjMap (encIso Q P lam pk x z r) ρ

/-- **Dec of Construction 5.1**, p.28: "1. Measure `C` in the computational basis to get
`c ∈ {0,1}^m`. Run `PRC.Dec(sk_PRC, c)`. If the result is a string `x∥z ∈ {0,1}^{2ℓ}`, use it; if the
result is `⊥`, set `x∥z := 0^{2ℓ}`. Apply the unitary `(X^x Z^z)†` to register `B`. 2. Apply
`QECC.Dec_{B→A}` and output register `A`." As a channel:
`Dec_sk(ρ) = Σ_c QECC.Dec((X^xZ^z)† ⟨c|_C ρ |c⟩_C (X^xZ^z))` with `x∥z` decoded from `c`. -/
noncomputable def decCh (Q : QECC nL ℓ) (P : PKPRC (fun lam => 2 * ℓ lam) m) (lam : ℕ)
    (sk : P.SK lam) : Superop (Bits (ℓ lam + m lam)) (Bits (nL lam)) :=
  fun ρ => ∑ c : Bits (m lam),
    let s : Bits (2 * ℓ lam) := (P.dec lam sk c).getD (fun _ => false)
    let U : Matrix (Bits (ℓ lam)) (Bits (ℓ lam)) ℂ := (pauliXZ (fstHalf s) (sndHalf s))ᴴ
    let ρc : Matrix (Bits (ℓ lam)) (Bits (ℓ lam)) ℂ := fun b b' => ρ (Fin.append b c) (Fin.append b' c)
    Q.dec lam (U * ρc * Uᴴ)

/-- **Construction 5.1 (public-key QPRC)**, Hsieh, Yamada, arXiv:2609.38986 (version of October 29,
2026, sha256 6901b59d…), p.28: from a QECC `(QECC.Enc, QECC.Dec)` encoding `nL` qubits into `ℓ` qubits
and a `(2ℓ, m)` public-key PRC, a public-key code from `nL` to `nP := ℓ + m` qubits. "KeyGen: On input
`1^λ`, run `(sk_PRC, pk_PRC) ← PRC.KeyGen(1^λ)`. Output the pair `(sk, pk)`, where `sk := sk_PRC` and
`pk := pk_PRC`." Enc and Dec are `encCh` and `decCh`.

**Formalization Note.** Keys, their codes and KeyGen's coins are those of the PRC. Physical qubits:
`B` (first `ℓ`) then `C` (last `m`); `x∥z` is `x` followed by `z` (`catB`). -/
noncomputable def scheme (Q : QECC nL ℓ) (P : PKPRC (fun lam => 2 * ℓ lam) m) :
    PKQScheme nL (fun lam => ℓ lam + m lam) where
  SK := P.SK
  PK := P.PK
  skCode := P.skCode
  pkCode := P.pkCode
  kc := P.kc
  keyGen := P.keyGen
  enc := encCh Q P
  dec := decCh Q P

end C51

end QuantumPRC.Supplement


