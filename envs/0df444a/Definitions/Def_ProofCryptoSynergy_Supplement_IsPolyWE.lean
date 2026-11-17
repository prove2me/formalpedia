-- Prove2me | Definitions.Def_ProofCryptoSynergy_Supplement_IsPolyWE
-- name    : ProofCryptoSynergy_Supplement_IsPolyWE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:49:12.561197+00:00
-- url     : https://prove2.me/theorems/77a7bcb9-76bd-457a-afd2-71ec5898bf54
-- title:
--   Polynomially secure witness encryption for SAT and its full-support, verifiable and extractable strengthenings
-- statement:
--   A **polynomially secure witness encryption scheme for SAT** (Definition 13) consists of polynomial-time $\mathrm{Enc}(x,b;r)\in\{0,1\}^{\ell(n)}$ and $\mathrm{Dec}(x,w,c)\in\{0,1,\bot\}$ with correctness for all large $n$ ($\mathrm{Dec}(x,w,\mathrm{Enc}(x,b;r))=b$ whenever $x(w)=1$) and security: for every $c\ge1$, for all large $n$ and unsatisfiable $x\in\{0,1\}^n$, $(x,\mathrm{Enc}(x,1;r))\approx_{n^{-c}}(x,\mathrm{Enc}(x,0;r))$. With $\mathrm{range}(\mathrm{Enc}(x,-;-))$ the set of ciphertexts of $x$, the scheme is
--
--   1. **full-support** (Definition 70) if $\mathrm{range}(\mathrm{Enc}(x,-;-))=\{0,1\}^{\ell(n)}$ for all $n$ and $x\in\{0,1\}^n$;
--   2. **publicly verifiable** (Definition 68) if $\{(x,ct): ct\in\mathrm{range}(\mathrm{Enc}(x,-;-))\}\in\mathsf P$;
--   3. **privately verifiable** (Definition 69) if $\mathrm{Dec}(x,w,z)=\bot$ for every satisfying $w$ and every $z\notin\mathrm{range}(\mathrm{Enc}(x,-;-))$;
--   4. **extractable** (Definition 67) if there is a PPT extractor $\mathcal E$ such that for every polynomial $q$, circuit $A$ of size $\le q(n)$ and $x\in\{0,1\}^n$: if $\Pr_{b,r}[A(x,\mathrm{Enc}(x,b;r))=b]\ge\frac12+\frac1{q(n)}$ then $\Pr[\mathcal E(x,A)\text{ satisfies }x]\ge\frac23$.
--
--   These are the strong forms of witness encryption characterized and refuted in Section 6.
--
--   **Formalization Note** The data is the published `WEForSAT`. Witnesses in Definition 69 satisfy $|w|\le|x|$ (the SAT relation of the mission). In Definition 67, $q(n)=n^c$ with real $c\ge1$, the hypothesis is written $(\Pr-\frac12)\,q(n)\ge1$ (nothing is required at $q(n)=0$), adversaries read $(x,ct)$ through `padIn`, and for each $q$ the condition is required for all sufficiently large $n$ (the convention of Definition 13, which Definition 67 extends; read for every $n$, it would force identically distributed encryptions of every unsatisfiable $x$ with $|x|\ge2$).
-- source:
--   Goldberg, Juvekar, Kabanets, Synergies between Proof Complexity and Cryptography, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 13, p.20 (PDF 22); Definitions 67–70, p.52 (PDF 54)

import Mathlib
import Definitions.Def_ProofCryptoSynergy_SubexpWEForSATExists
import Definitions.Def_KarpLiptonOM_Circuit_eval
import Definitions.Def_LaconicBarrier_IOScheme

open KarpLiptonOM LaconicBarrier

namespace ProofCryptoSynergy.Supplement

/-- A **polynomially secure witness encryption scheme for SAT** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 13, p.20 (PDF 22)):
uniform polynomial-time `Enc`, `Dec` (published `WEForSAT` data), ciphertexts of length `ℓ(n)`; correctness:
for all large `n`, all `b`, `x ∈ {0,1}ⁿ ∩ SAT` and `w` with `φ(w) = 1`, `Pr_r[Dec(x, w, Enc(x, b; r)) = b] = 1`;
security: for every inverse polynomial `ε`, for all large `n` and `x ∈ {0,1}ⁿ \ SAT`,
`(x, Enc(x, 1; r)) ≈_ε (x, Enc(x, 0; r))`.

**Formalization Note** The clauses other than security are those of the published `IsSubexpWE`. "Inverse
polynomial `ε`" is `ε(n) = n^{-c}` for each `c ≥ 1`, the `∀ᶠ n` taken after `c` (published `Indist`,
nonuniform adversaries). -/
def IsPolyWE (E : WEForSAT) : Prop :=
  (∃ c : ℕ, ∀ n, E.coins n ≤ (n + 2) ^ c) ∧
  PolyTimeOn (ι := {i : List Bool × Bool × List Bool // i.2.2.length = E.coins i.1.length})
    (fun i => [i.1.1, [i.1.2.1], i.1.2.2]) (fun i => E.enc i.1.1 i.1.2.1 i.1.2.2) ∧
  PolyTimeOn (ι := List Bool × List Bool × List Bool)
    (fun i => [i.1, i.2.1, i.2.2]) (fun i => (E.dec i.1 i.2.1 i.2.2).toList) ∧
  (∀ (x : List Bool) (b : Bool) (r : List Bool), r.length = E.coins x.length →
    (E.enc x b r).length = E.ell x.length) ∧
  (∀ᶠ n : ℕ in Filter.atTop, ∀ (b : Bool) (x w r : List Bool), x.length = n → holds x w →
    r.length = E.coins n → E.dec x w (E.enc x b r) = some b) ∧
  ∀ c : ℕ, 1 ≤ c → ∀ᶠ n : ℕ in Filter.atTop, ∀ x : List Bool, x.length = n → x ∉ SAT →
    Indist (((n : ℝ) ^ c)⁻¹)
      ⟨E.coins n, fun r => x ++ E.enc x true r⟩ ⟨E.coins n, fun r => x ++ E.enc x false r⟩

/-- `range(Enc(x, −; −)) = {Enc(x, b; r) : b ∈ {0,1}, |r| = coins(|x|)}` (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definitions 68–70,
p.52 (PDF 54)). -/
def encRange (E : WEForSAT) (x : List Bool) : Set (List Bool) :=
  {z | ∃ (b : Bool) (r : List Bool), r.length = E.coins x.length ∧ E.enc x b r = z}

/-- **Full-support** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 70, p.52 (PDF 54)): for all `n` and `x ∈ {0,1}ⁿ`,
`range(Enc(x, −; −)) = {0,1}^{ℓ(n)}`. -/
def FullSupportWE (E : WEForSAT) : Prop :=
  ∀ x : List Bool, encRange E x = {z | z.length = E.ell x.length}

open Classical in
/-- **Publicly verifiable** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 68, p.52 (PDF 54)): the language
`{(x, ct) | ct ∈ range(Enc(x, −; −))}` is in P: one machine decides it on the pair `(x, ct)` in polynomial
time (published `PolyTimeOn`, output bit `1` for members). -/
def PubVerifiableWE (E : WEForSAT) : Prop :=
  PolyTimeOn (ι := List Bool × List Bool) (fun i => [i.1, i.2])
    (fun i => [if i.2 ∈ encRange E i.1 then true else false])

/-- **Privately verifiable** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 69, p.52 (PDF 54)): for all `n`, `x ∈ {0,1}ⁿ`, witnesses `w`
with `(x, w) ∈ R_SAT`, and `z ∉ range(Enc(x, −; −))`, `Dec(x, w, z) = ⊥`.

**Formalization Note** `w ∈ {0,1}^{poly(n)}` with `(x, w) ∈ R_L` is the SAT relation of the mission
(`φ(w) = 1`, `|w| ≤ |x|`, as in `SATRel`). -/
def PrivVerifiableWE (E : WEForSAT) : Prop :=
  ∀ x w z : List Bool, holds x w → w.length ≤ x.length → z ∉ encRange E x → E.dec x w z = none

open Classical in
/-- **Extractable** (Goldberg, Juvekar, Kabanets, *Synergies between Proof Complexity and Cryptography*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 a39bb3f0…), Definition 67, p.52 (PDF 54)): there is a PPT extractor `Ext` such that for any
polynomial `q`, any circuit `A` of size at most `q(n)` and any `x ∈ {0,1}ⁿ`, if
`Pr_{b∼U, Enc}[A(x, Enc(x, b)) = b] ≥ 1/2 + 1/q(n)` then `Pr_Ext[Ext(x, A) = w with (x, w) ∈ R_L] ≥ 2/3`.

**Formalization Note**
1. `Ext(x, A; r)` reads `x`, the description of `A` and `exc(|x|, |A|)` coins, polynomially many, and runs
   in polynomial time in its input length.
2. `q(n) = n^c` with `c ≥ 1` real; the hypothesis is written `(Pr − 1/2) · q(n) ≥ 1`.
3. `A` has any number `k` of inputs and reads the pair `(x, ct)` as `padIn k (x ++ ct)`, as adversaries do in
   the published `Indist`; its size is its number of gates.
4. For each `q` the condition is required for all sufficiently large `n`, the convention of Definition 13,
   which Definition 67 extends ("a witness encryption scheme as in Definition 13"). Read for every `n`, it
   would force, at each fixed `n ≥ 2` (where `n^c` and `n^{-c}` range over all sizes and advantages),
   `Enc(x, 0)` and `Enc(x, 1)` to be identically distributed for every unsatisfiable `x`; with correctness
   this gives short certificates of unsatisfiability (`NP = coNP`), and the proof of Lemma 75 (Item 1)
   only yields extraction for large `n`. -/
def ExtractableWE (E : WEForSAT) : Prop :=
  ∃ (ex : List Bool → (Σ k : ℕ, Circuit k) → List Bool → List Bool) (exc : ℕ → ℕ → ℕ),
    (∃ c : ℕ, ∀ a b, exc a b ≤ (a + b + 2) ^ c) ∧
    PolyTimeOn (ι := {i : List Bool × (Σ k : ℕ, Circuit k) × List Bool //
        i.2.2.length = exc i.1.length (circCode i.2.1.2).length})
      (fun i => [i.1.1, circCode i.1.2.1.2, i.1.2.2]) (fun i => ex i.1.1 i.1.2.1 i.1.2.2) ∧
    ∀ (c : ℝ), 1 ≤ c → ∀ᶠ n : ℕ in Filter.atTop, ∀ (x : List Bool), x.length = n →
      ∀ (k : ℕ) (A : Circuit k), (A.gates.length : ℝ) ≤ (n : ℝ) ^ c →
      1 ≤ ((1 / 2 : ℝ) * ∑ b : Bool, coinAvg (E.coins n)
          (fun r => if A.eval (padIn k (x ++ E.enc x b (bits r))) = b then 1 else 0) - 1 / 2) *
        (n : ℝ) ^ c →
      (2 / 3 : ℝ) ≤ coinAvg (exc n (circCode A).length)
        (fun r => if holds x (ex x ⟨k, A⟩ (bits r)) then 1 else 0)

end ProofCryptoSynergy.Supplement


