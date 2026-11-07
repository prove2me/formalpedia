-- Prove2me | Definitions.Def_QuantumPRC_SKPRC
-- name    : QuantumPRC_SKPRC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:27.493345+00:00
-- url     : https://prove2.me/theorems/a6bd1fb3-bd76-475c-a8f7-c7563f5d1fd9
-- title:
--   Classical noise, $p$-bounded noise (Definition 3.6), secret-key and public-key PRCs (Definitions 3.19, 3.24)
-- statement:
--   A **classical noise channel** on $m(\lambda)$-bit strings is a possibly inefficient probabilistic map, given by transition probabilities $\Pr[\mathcal E_\lambda(c)=c']$. It is **$p$-bounded** (Definition 3.6) if
--
--   $$
--   \Pr_{x\leftarrow\{0,1\}^{m(\lambda)}}\big[\mathrm{wt}(\mathcal E_\lambda(x)\oplus x)>p\cdot m(\lambda)\big]\le\mathsf{negl}(\lambda),
--   $$
--
--   the probability being over a uniform $x$ and the randomness of $\mathcal E_\lambda$.
--
--   An **$(n,m)$ secret-key PRC robust to $\mathcal E$** (Definition 3.24) is a triple $(\mathsf{KeyGen},\mathrm{Enc},\mathrm{Dec})$ where $\mathsf{KeyGen}$ is PPT and outputs $\mathsf{sk}$, $\mathrm{Enc}$ is PPT and maps $(\mathsf{sk},x\in\{0,1\}^{n(\lambda)})$ to $c\in\{0,1\}^{m(\lambda)}$, and $\mathrm{Dec}$ is deterministic polynomial-time and maps $(\mathsf{sk},c)$ to $x$ or $\bot$, such that
--
--   1. **robustness (38)**: for every $x$, $\Pr[x\leftarrow\mathrm{Dec}(\mathsf{sk},\mathcal E_\lambda(c)) : \mathsf{sk}\leftarrow\mathsf{KeyGen}(1^\lambda),\ c\leftarrow\mathrm{Enc}(\mathsf{sk},x)]\ge1-\mathsf{negl}(\lambda)$;
--   2. **soundness (39)**: for every fixed $c$, $\Pr[\bot\leftarrow\mathrm{Dec}(\mathsf{sk},c)]\ge1-\mathsf{negl}(\lambda)$;
--   3. **pseudorandomness (40)**: every QPT adversary making only classical queries distinguishes the oracle $x\mapsto\mathrm{Enc}(\mathsf{sk},x)$ (fresh randomness per query) from the oracle returning a fresh uniform $y\in\{0,1\}^{m(\lambda)}$ with advantage $\mathsf{negl}(\lambda)$.
--
--   A **public-key PRC** (Definition 3.19) is the same with $\mathsf{KeyGen}$ outputting $(\mathsf{sk},\mathsf{pk})$, $\mathrm{Enc}$ using $\mathsf{pk}$, and the adversary receiving $\mathsf{pk}$.
--
--   **Formalization Note** Keys live in a key type with a classical code read by the machines; Enc's internal randomness is an explicit coin string (the "$\ell(\lambda)$-bit string" of Construction 6.5). A classical-query oracle is the channel that measures its input in the computational basis and outputs a sample (Kraus operators $\sqrt{p(y|x)}\,|y\rangle\langle x|$). "For any $x$" and "for any fixed $c$" are uniform: one negligible function for all $x$ (resp. $c$).
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), §3.4 and Definition 3.6, p.17; Definition 3.19, p.22; Definition 3.24, p.23

import Mathlib
import Definitions.Def_QuantumPRC_Assumption5

open Matrix

namespace QuantumPRC

/-- A **classical noise channel** on `m(λ)`-bit strings: a family of (possibly inefficient)
probabilistic maps, given by transition probabilities `E λ c c' = Pr[E_λ(c) = c']`
(arXiv:2609.38986, §3.4, p.17: "A classical noise channel is a (possibly inefficient) classical
probabilistic algorithm `E`"). -/
abbrev CNoise (m : ℕ → ℕ) : Type := ∀ lam, Bits (m lam) → Bits (m lam) → ℝ

/-- The transition probabilities of a classical noise channel are a Markov kernel. -/
def IsCNoise {m : ℕ → ℕ} (E : CNoise m) : Prop :=
  (∀ lam c c', 0 ≤ E lam c c') ∧ ∀ lam c, ∑ c', E lam c c' = 1

/-- **`p`-bounded noise channel**, Definition 3.6. Hsieh, Yamada, arXiv:2609.38986 (sha256
6901b59d…), p.17: "For `p ∈ [0, 1]` and a function `m : ℕ → ℕ`, a family `{E_λ}_{λ∈ℕ}` of channels
`E_λ : {0,1}^{m(λ)} → {0,1}^{m(λ)}` is called a `p`-bounded noise channel if
`Pr_{x←{0,1}^{m(λ)}} [wt(E_λ(x) ⊕ x) > p · m(λ)] ≤ negl(λ)`, where the probability is taken over the
choice of `x` and the internal randomness of `E_λ`."

**Formalization Note.** `x` is uniform, as printed (not a codeword). -/
def IsPBounded {m : ℕ → ℕ} (p : ℝ) (E : CNoise m) : Prop :=
  IsCNoise E ∧ ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
    avg (fun x : Bits (m lam) => ∑ y, if p * (m lam : ℝ) < wt (xorB y x) then E lam x y else 0)
      ≤ ν lam

/-- The **classical-query oracle** of a probabilistic map with transition probabilities `p x y`: it
measures its input in the computational basis and outputs `y` with probability `p x y`. Querying it
is a classical query (Definitions 3.19 and 3.24: "allowed to make only classical queries"); it is
the channel with Kraus operators `√(p x y) |y⟩⟨x|`. -/
def classOracle {a b : Type} [Fintype a] [DecidableEq b] (p : a → b → ℝ) : Superop a b :=
  fun ρ => Matrix.diagonal fun y => ∑ x, (p x y : ℂ) * ρ x x

/-- The code of an optional message: `⊥ ↦ []`, `x ↦ 1 :: x`. -/
def optCode {n : ℕ} : Option (Bits n) → List Bool
  | none => []
  | some x => true :: bits x

/-- **Secret-key PRC syntax**, Definition 3.24. Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
p.23: KeyGen is a PPT algorithm that outputs a secret key `sk`; Enc is a PPT algorithm that takes `sk`
and `x ∈ {0,1}^{n(λ)}` and outputs `c ∈ {0,1}^{m(λ)}`; Dec is a deterministic polynomial-time algorithm
that takes `sk` and `c` and outputs `x ∈ {0,1}^{n(λ)}` or `⊥`.

Keys live in `Key λ` with a classical code `keyCode`; `keyGen λ r` and `enc λ sk x r'` read the
coin strings `r ∈ {0,1}^{kc(λ)}` and `r' ∈ {0,1}^{ec(λ)}` (Enc's internal randomness, the `ℓ(λ)`-bit
string of Construction 6.5); `dec` returns `none` for `⊥`. -/
structure SKPRC (n m : ℕ → ℕ) where
  Key : ℕ → Type
  keyCode : ∀ lam, Key lam → List Bool
  kc : ℕ → ℕ
  keyGen : ∀ lam, Bits (kc lam) → Key lam
  ec : ℕ → ℕ
  enc : ∀ lam, Key lam → Bits (n lam) → Bits (ec lam) → Bits (m lam)
  dec : ∀ lam, Key lam → Bits (m lam) → Option (Bits (n lam))

namespace SKPRC

variable {n m : ℕ → ℕ} (S : SKPRC n m)

/-- KeyGen and Enc are PPT and Dec is deterministic polynomial-time (Definition 3.24, syntax). -/
def Efficient : Prop :=
  PolyBounded S.kc ∧ PolyBounded S.ec ∧
  IsPolyFamily (α := fun lam => Bits (S.kc lam)) S.keyGen (fun _ r => [bits r]) S.keyCode ∧
  IsPolyFamily (α := fun lam => S.Key lam × Bits (n lam) × Bits (S.ec lam))
    (fun lam a => S.enc lam a.1 a.2.1 a.2.2)
    (fun lam a => [S.keyCode lam a.1, bits a.2.1, bits a.2.2]) (fun _ c => bits c) ∧
  IsPolyFamily (α := fun lam => S.Key lam × Bits (m lam)) (fun lam a => S.dec lam a.1 a.2)
    (fun lam a => [S.keyCode lam a.1, bits a.2]) (fun _ o => optCode o)

/-- `Pr_{r'}[Enc(sk, x; r') = c]`. -/
noncomputable def encProb (lam : ℕ) (sk : S.Key lam) (x : Bits (n lam)) (c : Bits (m lam)) : ℝ :=
  avg fun r : Bits (S.ec lam) => if S.enc lam sk x r = c then 1 else 0

/-- **Robustness (38)**: for any `x ∈ {0,1}^{n(λ)}`,
`Pr[x ← Dec(sk, E_λ(c)) : sk ← KeyGen(1^λ), c ← Enc(sk, x)] ≥ 1 − negl(λ)` (one `negl` for all `x`). -/
def Robust (E : CNoise m) : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam (x : Bits (n lam)),
    1 - ν lam ≤ avg fun r : Bits (S.kc lam) => ∑ c, S.encProb lam (S.keyGen lam r) x c *
      ∑ c', E lam c c' * (if S.dec lam (S.keyGen lam r) c' = some x then 1 else 0)

/-- **Soundness (39)**: for any fixed `c ∈ {0,1}^{m(λ)}`, `Pr[⊥ ← Dec(sk, c) : sk ← KeyGen(1^λ)] ≥ 1 − negl(λ)`. -/
def Sound : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam (c : Bits (m lam)),
    1 - ν lam ≤ avg fun r : Bits (S.kc lam) => if S.dec lam (S.keyGen lam r) c = none then 1 else 0

/-- **Pseudorandomness (40)**: for any QPT adversary `A` that makes only classical queries,
`|Pr_{sk←KeyGen(1^λ)}[1 ← A^{Enc_sk}(1^λ)] − Pr[1 ← A^U(1^λ)]| ≤ negl(λ)`, where `Enc_sk` answers `x` with
a fresh `Enc(sk, x)` and `U` answers every query with a fresh uniform `y ∈ {0,1}^{m(λ)}`. -/
def Pseudorandom : Prop :=
  ∀ A : ∀ lam, OCirc (n lam) (m lam) 1, IsUniformAdv A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |avg (fun r : Bits (S.kc lam) =>
          (A lam).accept (fun _ => classOracle (S.encProb lam (S.keyGen lam r))) []) -
        (A lam).accept (fun _ => classOracle fun _ _ => ((2 : ℝ) ^ m lam)⁻¹) []| ≤ ν lam

/-- **`(n, m)` secret-key PRC robust to `E`**, Definition 3.24, p.23: syntax (with efficiency),
robustness, soundness and pseudorandomness. -/
def IsPRC (E : CNoise m) : Prop :=
  S.Efficient ∧ S.Robust E ∧ S.Sound ∧ S.Pseudorandom

end SKPRC

/-- **Public-key PRC syntax**, Definition 3.19. Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
p.22: KeyGen (PPT) outputs a pair `(sk, pk)`; Enc (PPT) takes `pk` and `x ∈ {0,1}^{n(λ)}` and outputs
`c ∈ {0,1}^{m(λ)}`; Dec (deterministic polynomial time) takes `sk` and `c` and outputs `x` or `⊥`. -/
structure PKPRC (n m : ℕ → ℕ) where
  SK : ℕ → Type
  PK : ℕ → Type
  skCode : ∀ lam, SK lam → List Bool
  pkCode : ∀ lam, PK lam → List Bool
  kc : ℕ → ℕ
  keyGen : ∀ lam, Bits (kc lam) → SK lam × PK lam
  ec : ℕ → ℕ
  enc : ∀ lam, PK lam → Bits (n lam) → Bits (ec lam) → Bits (m lam)
  dec : ∀ lam, SK lam → Bits (m lam) → Option (Bits (n lam))

namespace PKPRC

variable {n m : ℕ → ℕ} (S : PKPRC n m)

/-- KeyGen and Enc are PPT and Dec is deterministic polynomial-time (Definition 3.19, syntax). -/
def Efficient : Prop :=
  PolyBounded S.kc ∧ PolyBounded S.ec ∧
  IsPolyFamily (α := fun lam => Bits (S.kc lam)) (fun lam r => (S.keyGen lam r).1)
    (fun _ r => [bits r]) S.skCode ∧
  IsPolyFamily (α := fun lam => Bits (S.kc lam)) (fun lam r => (S.keyGen lam r).2)
    (fun _ r => [bits r]) S.pkCode ∧
  IsPolyFamily (α := fun lam => S.PK lam × Bits (n lam) × Bits (S.ec lam))
    (fun lam a => S.enc lam a.1 a.2.1 a.2.2)
    (fun lam a => [S.pkCode lam a.1, bits a.2.1, bits a.2.2]) (fun _ c => bits c) ∧
  IsPolyFamily (α := fun lam => S.SK lam × Bits (m lam)) (fun lam a => S.dec lam a.1 a.2)
    (fun lam a => [S.skCode lam a.1, bits a.2]) (fun _ o => optCode o)

/-- `Pr_{r'}[Enc(pk, x; r') = c]`. -/
noncomputable def encProb (lam : ℕ) (pk : S.PK lam) (x : Bits (n lam)) (c : Bits (m lam)) : ℝ :=
  avg fun r : Bits (S.ec lam) => if S.enc lam pk x r = c then 1 else 0

/-- **Robustness (35)**. -/
def Robust (E : CNoise m) : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam (x : Bits (n lam)),
    1 - ν lam ≤ avg fun r : Bits (S.kc lam) => ∑ c, S.encProb lam (S.keyGen lam r).2 x c *
      ∑ c', E lam c c' * (if S.dec lam (S.keyGen lam r).1 c' = some x then 1 else 0)

/-- **Soundness (36)**. -/
def Sound : Prop :=
  ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam (c : Bits (m lam)),
    1 - ν lam ≤ avg fun r : Bits (S.kc lam) =>
      if S.dec lam (S.keyGen lam r).1 c = none then 1 else 0

/-- **Pseudorandomness (37)**: the adversary also receives `pk` as its classical input:
`|Pr_{(sk,pk)}[1 ← A^{Enc_pk}(1^λ, pk)] − Pr_{(sk,pk)}[1 ← A^U(1^λ, pk)]| ≤ negl(λ)`. -/
def Pseudorandom : Prop :=
  ∀ A : ∀ lam, OCirc (n lam) (m lam) 1, IsUniformAdv A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |avg (fun r : Bits (S.kc lam) =>
          (A lam).accept (fun _ => classOracle (S.encProb lam (S.keyGen lam r).2))
            (S.pkCode lam (S.keyGen lam r).2)) -
        avg (fun r : Bits (S.kc lam) =>
          (A lam).accept (fun _ => classOracle fun _ _ => ((2 : ℝ) ^ m lam)⁻¹)
            (S.pkCode lam (S.keyGen lam r).2))| ≤ ν lam

/-- **`(n, m)` public-key PRC robust to `E`**, Definition 3.19, p.22. -/
def IsPRC (E : CNoise m) : Prop :=
  S.Efficient ∧ S.Robust E ∧ S.Sound ∧ S.Pseudorandom

end PKPRC

end QuantumPRC


