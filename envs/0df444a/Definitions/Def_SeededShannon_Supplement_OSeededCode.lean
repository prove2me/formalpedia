-- Prove2me | Definitions.Def_SeededShannon_Supplement_OSeededCode
-- name    : SeededShannon_Supplement_OSeededCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:41:58.614+00:00
-- url     : https://prove2.me/theorems/a7968fe7-32eb-4425-b3a5-ce9bf2444a19
-- title:
--   Seeded codes with random-oracle access, adaptive correctness and Construction 7.17
-- statement:
--   1. An **oracle seeded code** is a seeded code (Definition 3.15) whose algorithms at $(\lambda,k)$ may query a random oracle $\mathcal O:\{0,1\}^{o_{\mathrm{in}}}\to\{0,1\}^{o_{\mathrm{out}}}$. Its *list size* $L$ holds for every oracle, seed and received word. It **selectively $p$-corrects in the random-oracle model** if for every message sequence $x^*_\lambda$ of polynomial length and every polynomial-size oracle adversary $\mathcal A_2$, $\Pr[\Delta(\mathrm{Encode}_{\mathrm{crs}}(x^*),y)\le pN\wedge x^*\notin\mathrm{Decode}_{\mathrm{crs}}(y)]$ is negligible over a uniform oracle and the setup coins, where $y=\mathcal A_2^{\mathcal O}(1^\lambda,\mathrm{crs})$; with unique decoding the failure condition is $\mathrm{Decode}_{\mathrm{crs}}(y)\ne x^*$.
--   2. **Construction 7.17.** With $\ell_{\mathrm{tag}}=\lambda$, $d=k+\ell_{\mathrm{tag}}$, a random oracle $H:\{0,1\}^k\to\{0,1\}^{\ell_{\mathrm{tag}}}$ and an ideal permutation $P$ of $\{0,1\}^d$ (with $P^{-1}$ public): $\mathrm{Setup}_{ad}(1^\lambda,1^k)$ samples $\sigma\leftarrow\Pi_{\mathrm{base}}.\mathrm{Setup}(1^\lambda,1^d)$ and publishes $\mathrm{crs}_{ad}=(\sigma,k,\ell_{\mathrm{tag}})$; $\mathrm{Encode}_{ad}(\mathrm{crs}_{ad},x)=\Pi_{\mathrm{base}}.\mathrm{Encode}(\sigma,P((x,H(x))))$; $\mathrm{Decode}_{ad}$ runs the base decoder, computes $P^{-1}(u)=(x,z)$ for each candidate $u$, keeps $x$ exactly when $z=H(x)$, and returns the deduplicated list.
--   3. **Adaptive correctness (Definition 7.16).** The adversary announces a supported length $1^k$ before any oracle query, receives $\mathrm{crs}\leftarrow\mathrm{Setup}(1^\lambda,1^k)$, and with oracle access throughout outputs $x^*\in\{0,1\}^k$ and $y\in\{0,1\}^N$; the experiment outputs $1$ if $\Delta(\mathrm{Encode}_{\mathrm{crs}}(x^*),y)\le pN$ and $x^*\notin\mathrm{Decode}_{\mathrm{crs}}(y)$ (with unique decoding, $\mathrm{Decode}_{\mathrm{crs}}(y)\ne x^*$). The code adaptively $p$-corrects if this probability is negligible for every polynomial-size adversary.
--
--   **Formalization Note** The oracle of the base code is a uniformly random function on fixed-length strings at each $(\lambda,k)$. In the adaptive experiment for Construction 7.17 the adversary queries $H$, $P$, $P^{-1}$ and the base oracle through one interface separated by a two-bit prefix; $H$, $P$ and the base oracle are independent and uniform. The first stage of the selective notion makes no oracle query (a fixed message sequence).
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 7.18 and Construction 7.17, p.54 (PDF p.57); Definition 7.16, p.54; Definition 3.15, p.22

import Mathlib
import Definitions.Def_SeededShannon_SeededCode
import Definitions.Def_SeededShannon_Supplement_OAdv

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC SeededShannon

/-- A **seeded code with random-oracle access** (Dujmovic, Lu, Silbak, Wichs, STOC 2027 submission
(manuscript sha256 52f4b606…a769709), Theorem 7.18, p.54: "The base code may itself use a random
oracle"): a seeded code (Definition 3.15) whose algorithms at `(λ, k)` may query an oracle
`O : {0,1}^{oIn(λ,k)} → {0,1}^{oOut(λ,k)}`.

**Formalization Note** The oracle is given to the algorithms as a function; `setup λ k O r` is the
seed under coins `r`. A code without an oracle is the case `oIn = oOut = 0`. -/
structure OSeededCode where
  /-- the codeword length `N(λ, k)` -/
  N : ℕ → ℕ → ℕ
  /-- the number of coins of `Setup(1^λ, 1^k)` -/
  setupCoins : ℕ → ℕ → ℕ
  /-- the oracle input length -/
  oIn : ℕ → ℕ → ℕ
  /-- the oracle output length -/
  oOut : ℕ → ℕ → ℕ
  /-- `Setup^O(1^λ, 1^k; r)` -/
  setup : (lam k : ℕ) → ((Fin (oIn lam k) → Bool) → Fin (oOut lam k) → Bool) →
    (Fin (setupCoins lam k) → Bool) → List Bool
  /-- `Encode^O(crs, x)` -/
  encode : (lam k : ℕ) → ((Fin (oIn lam k) → Bool) → Fin (oOut lam k) → Bool) →
    List Bool → List Bool → List Bool
  /-- `Decode^O(crs, y)` -/
  decode : (lam k : ℕ) → ((Fin (oIn lam k) → Bool) → Fin (oOut lam k) → Bool) →
    List Bool → List Bool → List (List Bool)

/-- The oracle of the base code at `(λ, k)`. -/
abbrev OSeededCode.Orc (C : OSeededCode) (lam k : ℕ) : Type :=
  (Fin (C.oIn lam k) → Bool) → Fin (C.oOut lam k) → Bool

/-- An oracle on fixed-length strings answering string queries: the query `w` is read as its first
`i` bits (`0`-padded). -/
def orcAns {i o : ℕ} (O : (Fin i → Bool) → Fin o → Bool) (w : List Bool) : List Bool :=
  bits (O (fun j => w.getD j.val false))

/-- **List size `L`** of an oracle seeded code (Definition 3.15, p.22), for every oracle, every seed
and every `y ∈ {0,1}^N` at a supported `(λ, k)`; listed messages have length `k`. -/
def OSeededCode.ListBound (C : OSeededCode) (supp : ℕ → ℕ → Prop) (L : ℕ → ℕ → ℕ) : Prop :=
  ∀ lam k, supp lam k → ∀ (O : C.Orc lam k) (r : Fin (C.setupCoins lam k) → Bool) (y : List Bool),
    y.length = C.N lam k →
      (C.decode lam k O (C.setup lam k O r) y).length ≤ L lam k ∧
      ∀ x ∈ C.decode lam k O (C.setup lam k O r) y, x.length = k

/-- **Selective `p`-correction in the random-oracle model** (Definition 3.15, p.22, with oracle
access; Definition 7.16, p.54: "In the random-oracle model, the adversary has oracle access
throughout"): for every message sequence `x*_λ` of polynomially bounded length and every
polynomial-size oracle adversary `A₂` there is a negligible `ν` with
`Pr[Δ(Encode_crs(x*), y) ≤ p · N ∧ x* ∉ Decode_crs(y)] ≤ ν(λ)` at supported lengths, over a uniformly
random oracle `O` and `crs ← Setup^O(1^λ, 1^k)`, where `y = A₂^O(1^λ, crs)`.

**Formalization Note** The first stage `A₁` is a fixed message sequence (best coins hard-wired)
that makes no oracle query; its state is hard-wired into `A₂`. A first stage querying the oracle is
the more general notion; Theorem 7.18 needs only this one. An output `y` of the wrong length makes
the experiment output `0`. -/
def OSeededCode.SelectivelyCorrect (C : OSeededCode) (supp : ℕ → ℕ → Prop) (p : ℝ) : Prop :=
  ∀ xs : ℕ → List Bool, PolyBounded (fun lam => (xs lam).length) →
  ∀ A : OAdv, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, supp lam (xs lam).length →
    wprob (unifW (C.Orc lam (xs lam).length × (Fin (C.setupCoins lam (xs lam).length) → Bool)))
      (fun ω =>
        let crs := C.setup lam (xs lam).length ω.1 ω.2
        let y := A.run lam (orcAns ω.1) (QAdvFew.PoQOracle.tup [unary lam, crs])
        y.length = C.N lam (xs lam).length ∧
          (ldist (C.encode lam (xs lam).length ω.1 crs (xs lam)) y : ℝ) ≤
            p * C.N lam (xs lam).length ∧
          xs lam ∉ C.decode lam (xs lam).length ω.1 crs y) ≤ ν lam

/-- **Selective `p`-correction with unique decoding in the random-oracle model**: as
`OSeededCode.SelectivelyCorrect`, with the failure condition `Decode_crs(y) ≠ x*` (Definition 3.15,
p.22). -/
def OSeededCode.SelectivelyCorrectUnique (C : OSeededCode) (supp : ℕ → ℕ → Prop) (p : ℝ) : Prop :=
  ∀ xs : ℕ → List Bool, PolyBounded (fun lam => (xs lam).length) →
  ∀ A : OAdv, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam, supp lam (xs lam).length →
    wprob (unifW (C.Orc lam (xs lam).length × (Fin (C.setupCoins lam (xs lam).length) → Bool)))
      (fun ω =>
        let crs := C.setup lam (xs lam).length ω.1 ω.2
        let y := A.run lam (orcAns ω.1) (QAdvFew.PoQOracle.tup [unary lam, crs])
        y.length = C.N lam (xs lam).length ∧
          (ldist (C.encode lam (xs lam).length ω.1 crs (xs lam)) y : ℝ) ≤
            p * C.N lam (xs lam).length ∧
          C.decode lam (xs lam).length ω.1 crs y ≠ [xs lam]) ≤ ν lam

/-! ### Construction 7.17 (hashing and permuting the message) -/

/-- The random oracle `H : {0,1}^k → {0,1}^{ℓtag}`, `ℓtag = λ` (p.54). -/
abbrev TagOrc (lam k : ℕ) : Type := (Fin k → Bool) → Fin lam → Bool

/-- The ideal permutation `P` of `{0,1}^d`, `d = k + ℓtag` (p.54). -/
abbrev IdealPerm (lam k : ℕ) : Type := Equiv.Perm (Fin (k + lam) → Bool)

/-- **`Encode_ad(crs_ad, x) = Π_base.Encode(σ, P((x, H(x))))`** (Construction 7.17, p.54), on
`x ∈ {0,1}^k`. -/
def enc717 (C : OSeededCode) (lam k : ℕ) (H : TagOrc lam k) (P : IdealPerm lam k)
    (O : C.Orc lam (k + lam)) (σ x : List Bool) : List Bool :=
  let xv : Fin k → Bool := fun i => x.getD i.val false
  if x.length = k then C.encode lam (k + lam) O σ (bits (P (Fin.append xv (H xv)))) else []

/-- **`Decode_ad(crs_ad, y)`** (Construction 7.17, p.54): run the base decoder; for each candidate
`u`, compute `P^{−1}(u) = (x, z)` and retain `x` exactly when `z = H(x)`; return the deduplicated
list (for a uniquely decodable base code, the recovered message or `⊥`, i.e. a list of length at
most one). -/
def dec717 (C : OSeededCode) (lam k : ℕ) (H : TagOrc lam k) (P : IdealPerm lam k)
    (O : C.Orc lam (k + lam)) (σ y : List Bool) : List (List Bool) :=
  ((C.decode lam (k + lam) O σ y).filterMap (fun u =>
    let w := P.symm (fun i => u.getD i.val false)
    let x : Fin k → Bool := fun i => w (Fin.castAdd lam i)
    if u.length = k + lam ∧ (fun j => w (Fin.natAdd k j)) = H x then some (bits x) else none)).dedup

/-- The public oracle interfaces of the adaptive experiment, by domain separation on a two-bit
prefix: `00‖x ↦ H(x)`, `01‖u ↦ P(u)`, `10‖u ↦ P^{−1}(u)`, `11‖w ↦ O(w)` (the base code's oracle). -/
def orc717 {C : OSeededCode} {lam k : ℕ} (H : TagOrc lam k) (P : IdealPerm lam k)
    (O : C.Orc lam (k + lam)) : List Bool → List Bool
  | false :: false :: x => bits (H (fun i => x.getD i.val false))
  | false :: true :: u => bits (P (fun i => u.getD i.val false))
  | true :: false :: u => bits (P.symm (fun i => u.getD i.val false))
  | true :: true :: w => orcAns O w
  | _ => []

/-- **Adaptive `p`-correction of Construction 7.17** (Definition 7.16, p.54, in the model with a
random oracle `H`, an ideal permutation `(P, P^{−1})` and the base code's random oracle `O`, all
independent and uniform): for every message-length sequence `k(λ)` (announced before any oracle
query) of polynomial size and every polynomial-size oracle adversary `A` there is a negligible `ν`
such that at every `λ` with `k(λ) + λ` supported by the base code,
`Pr[Δ(Encode_ad(crs_ad, x*), y) ≤ p · N ∧ x* ∉ Decode_ad(crs_ad, y)] ≤ ν(λ)`, where
`σ ← Π_base.Setup^O(1^λ, 1^{k+λ})`, `crs_ad = (σ, k, ℓtag)`, and `A` (oracle access to `H`, `P`, `P^{−1}`,
`O`) outputs `x* ‖ y` with `x* ∈ {0,1}^k`, `y ∈ {0,1}^N`.

**Formalization Note** The adversary's announced length is a fixed sequence (best coins). An output
of the wrong length makes the experiment output `0`. With `unique := true` the failure condition is
`Decode_ad(crs_ad, y) ≠ x*` ("adaptively `p`-corrects with unique decoding"). -/
def Adaptive717 (C : OSeededCode) (supp : ℕ → ℕ → Prop) (p : ℝ) (unique : Bool) : Prop :=
  ∀ kf : ℕ → ℕ, PolyBounded kf → ∀ A : OAdv, A.IsPoly → ∃ ν : ℕ → ℝ, Negligible ν ∧
    ∀ lam, supp lam (kf lam + lam) →
      wprob (unifW (TagOrc lam (kf lam) × IdealPerm lam (kf lam) × C.Orc lam (kf lam + lam) ×
          (Fin (C.setupCoins lam (kf lam + lam)) → Bool)))
        (fun ω =>
          let σ := C.setup lam (kf lam + lam) ω.2.2.1 ω.2.2.2
          let crs := QAdvFew.PoQOracle.tup [σ, unary (kf lam), unary lam]
          let out := A.run lam (orc717 ω.1 ω.2.1 ω.2.2.1) (QAdvFew.PoQOracle.tup [unary lam, crs])
          let x := out.take (kf lam)
          let y := out.drop (kf lam)
          out.length = kf lam + C.N lam (kf lam + lam) ∧
            (ldist (enc717 C lam (kf lam) ω.1 ω.2.1 ω.2.2.1 σ x) y : ℝ) ≤
              p * C.N lam (kf lam + lam) ∧
            (if unique then dec717 C lam (kf lam) ω.1 ω.2.1 ω.2.2.1 σ y ≠ [x]
             else x ∉ dec717 C lam (kf lam) ω.1 ω.2.1 ω.2.2.1 σ y)) ≤ ν lam

/-- **List size `L`** of Construction 7.17 at message length `k` (base length `k + λ`): for all
oracles, seeds and `y ∈ {0,1}^N`, `|Decode_ad(crs_ad, y)| ≤ L(λ, k + λ)`, each listed message of
length `k`. -/
def ListBound717 (C : OSeededCode) (supp : ℕ → ℕ → Prop) (L : ℕ → ℕ → ℕ) : Prop :=
  ∀ lam k, supp lam (k + lam) → ∀ (H : TagOrc lam k) (P : IdealPerm lam k)
    (O : C.Orc lam (k + lam)) (r : Fin (C.setupCoins lam (k + lam)) → Bool) (y : List Bool),
    y.length = C.N lam (k + lam) →
      (dec717 C lam k H P O (C.setup lam (k + lam) O r) y).length ≤ L lam (k + lam) ∧
      ∀ x ∈ dec717 C lam k H P O (C.setup lam (k + lam) O r) y, x.length = k

end SeededShannon.Supplement


