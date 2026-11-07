-- Prove2me | Definitions.Def_QuantumPRC_PRFC
-- name    : QuantumPRC_PRFC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:48.741245+00:00
-- url     : https://prove2.me/theorems/db1fd30f-be83-4858-93b0-2b6f138db11c
-- title:
--   Pseudorandom functional codes (Definition 6.1) and Construction 6.5
-- statement:
--   An **$(n,m)$ PRFC robust to $\mathcal E$** (Definition 6.1) is a triple where $\mathsf{KeyGen}$ is PPT and outputs $\mathsf{sk}$, $\mathrm{Enc}$ is deterministic polynomial-time and maps $(\mathsf{sk},x\in\{0,1\}^{n(\lambda)})$ to $c\in\{0,1\}^{m(\lambda)}$, and $\mathrm{Dec}$ is deterministic polynomial-time and maps $(\mathsf{sk},c)$ to $x\in\{0,1\}^{n(\lambda)}$, such that
--
--   1. **robustness (80)**: for every $x$, $\Pr_{\mathsf{sk}}[\mathrm{Dec}(\mathsf{sk},c')=x : c'\leftarrow\mathcal E_\lambda(\mathrm{Enc}(\mathsf{sk},x))]\ge1-\mathsf{negl}(\lambda)$;
--   2. **pseudorandomness (81)**: every QPT adversary distinguishes quantum oracle access (82) to $\mathrm{Enc}(\mathsf{sk},\cdot)$ from quantum oracle access to a uniformly random function $\{0,1\}^n\to\{0,1\}^m$ with advantage $\mathsf{negl}(\lambda)$.
--
--   **Construction 6.5** builds a PRFC from an $(n,m)$ secret-key PRC whose encoder uses an $\ell(\lambda)$-bit random string, a PRP $\Pi$ on $n$ bits and a PRF $F:\{0,1\}^\lambda\times\{0,1\}^{n(\lambda)}\to\{0,1\}^{\ell(\lambda)}$:
--
--   - $\mathsf{KeyGen}$: $\mathsf{sk}'\leftarrow\mathsf{PRC.KeyGen}(1^\lambda)$, $k,k'\leftarrow\{0,1\}^\lambda$, $r\leftarrow\{0,1\}^{\ell(\lambda)}$; output $\mathsf{sk}=(\mathsf{sk}',k,k',r)$;
--   - $\mathrm{Enc}(\mathsf{sk},x):=\mathsf{PRC.Enc}(\mathsf{sk}',\pi_k(x);f_{k'}(x)\oplus r)$ (83);
--   - $\mathrm{Dec}(\mathsf{sk},c)$: run $\mathsf{PRC.Dec}(\mathsf{sk}',c)$; output $\pi_k^{-1}(v)$ if it returns $v$, and $0^{n(\lambda)}$ if it returns $\bot$.
--
--   **Formalization Note** KeyGen's coins are split, in this order, into those of $\mathsf{PRC.KeyGen}$, $k$, $k'$ and $r$; the key code is the tuple code of the four components.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Definition 6.1, p.33; Construction 6.5, p.34

import Mathlib
import Definitions.Def_QuantumPRC_SKPRC
import Definitions.Def_QuantumPRC_PRF

open Matrix

namespace QuantumPRC

/-- **PRFC syntax**, Definition 6.1. Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), p.33:
KeyGen is a PPT algorithm that takes `1^λ` and outputs a secret key `sk`; Enc is a deterministic
polynomial-time algorithm that takes `sk` and `x ∈ {0,1}^{n(λ)}` and outputs `c ∈ {0,1}^{m(λ)}`; Dec is a
deterministic polynomial-time algorithm that takes `sk` and `c ∈ {0,1}^{m(λ)}` and outputs
`x ∈ {0,1}^{n(λ)}`. Keys live in `Key λ` with the classical code `keyCode`; `keyGen` reads
`kc(λ)` fair coins. -/
structure PRFC (n m : ℕ → ℕ) where
  Key : ℕ → Type
  keyCode : ∀ lam, Key lam → List Bool
  kc : ℕ → ℕ
  keyGen : ∀ lam, Bits (kc lam) → Key lam
  enc : ∀ lam, Key lam → Bits (n lam) → Bits (m lam)
  dec : ∀ lam, Key lam → Bits (m lam) → Bits (n lam)

namespace PRFC

variable {n m : ℕ → ℕ} (S : PRFC n m)

/-- KeyGen is PPT; Enc and Dec are deterministic polynomial-time (Definition 6.1, syntax). -/
def Efficient : Prop :=
  PolyBounded S.kc ∧
  IsPolyFamily (α := fun lam => Bits (S.kc lam)) S.keyGen (fun _ r => [bits r]) S.keyCode ∧
  IsPolyFamily (α := fun lam => S.Key lam × Bits (n lam)) (fun lam a => S.enc lam a.1 a.2)
    (fun lam a => [S.keyCode lam a.1, bits a.2]) (fun _ c => bits c) ∧
  IsPolyFamily (α := fun lam => S.Key lam × Bits (m lam)) (fun lam a => S.dec lam a.1 a.2)
    (fun lam a => [S.keyCode lam a.1, bits a.2]) (fun _ x => bits x)

/-- **Robustness (80)**: for any `x ∈ {0,1}^{n(λ)}`,
`Pr_{sk←KeyGen(1^λ)}[Dec(sk, c′) = x : c′ ← E_λ(Enc(sk, x))] ≥ 1 − negl(λ)` (one `negl` for all `x`). -/
def Robust (E : CNoise m) : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam (x : Bits (n lam)),
    1 - ν lam ≤ avg fun r : Bits (S.kc lam) =>
      ∑ c', E lam (S.enc lam (S.keyGen lam r) x) c' *
        (if S.dec lam (S.keyGen lam r) c' = x then 1 else 0)

/-- **Pseudorandomness (81)**: for any QPT adversary `A`,
`|Pr_{sk←KeyGen(1^λ)}[1 ← A^{Enc(sk,·)}(1^λ)] − Pr_f[1 ← A^f(1^λ)]| ≤ negl(λ)`, with quantum queries
(82) and `f` a uniformly random function `{0,1}^n → {0,1}^m`. -/
def Pseudorandom : Prop :=
  ∀ A : ∀ lam, OCirc (n lam + m lam) (n lam + m lam) 1, IsUniformAdv A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |avg (fun r : Bits (S.kc lam) =>
          (A lam).accept (fun _ => xorOracle (S.enc lam (S.keyGen lam r))) []) -
        avg (fun f : Bits (n lam) → Bits (m lam) => (A lam).accept (fun _ => xorOracle f) [])|
        ≤ ν lam

/-- **`(n, m)` PRFC robust to `E`**, Definition 6.1, p.33. -/
def IsPRFC (E : CNoise m) : Prop :=
  S.Efficient ∧ S.Robust E ∧ S.Pseudorandom

end PRFC

/-- **Construction 6.5 (PRFCs)**. Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), p.34, from an
`(n, m)` secret-key PRC whose Enc uses an `ℓ(λ)`-bit string as internal randomness (`ℓ = S.ec`), a PRP
`Π` on `n` bits and a PRF `F : {0,1}^λ × {0,1}^{n(λ)} → {0,1}^{ℓ(λ)}`:
* KeyGen: `sk′ ← PRC.KeyGen(1^λ)`, `k, k′ ← {0,1}^λ`, `r ← {0,1}^{ℓ(λ)}`; `sk := (sk′, k, k′, r)`;
* Enc: `Enc(sk, x) := PRC.Enc(sk′, π_k(x); f_{k′}(x) ⊕ r)` (83);
* Dec: run `PRC.Dec(sk′, c)` to get `v`; if `v ∈ {0,1}^{n(λ)}` output `π_k⁻¹(v)`, otherwise `0^{n(λ)}`.

**Formalization Note.** KeyGen's coins are split, in this order, into those of `PRC.KeyGen`, `k`,
`k′` and `r`; the key code is the `tupleCode` of the four components. -/
def construction65 {n m : ℕ → ℕ} (S : SKPRC n m) (Pm : PRP n) (F : PRF n S.ec) : PRFC n m where
  Key lam := S.Key lam × Bits lam × Bits lam × Bits (S.ec lam)
  keyCode lam sk := tupleCode [S.keyCode lam sk.1, bits sk.2.1, bits sk.2.2.1, bits sk.2.2.2]
  kc lam := S.kc lam + lam + lam + S.ec lam
  keyGen lam r :=
    (S.keyGen lam (leftPart (leftPart (leftPart r))), rightPart (leftPart (leftPart r)),
      rightPart (leftPart r), rightPart r)
  enc lam sk x := S.enc lam sk.1 (Pm.P lam sk.2.1 x) (xorB (F.F lam sk.2.2.1 x) sk.2.2.2)
  dec lam sk c :=
    match S.dec lam sk.1 c with
    | some v => Pm.Pinv lam sk.2.1 v
    | none => fun _ => false

end QuantumPRC


