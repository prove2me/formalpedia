-- Prove2me | Definitions.Def_QuantumPRC_Assumption5
-- name    : QuantumPRC_Assumption5
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:27.89455+00:00
-- url     : https://prove2.me/theorems/cc49ca13-87f1-4f2b-9c3a-265927ad17f3
-- title:
--   LPN, LWE, planted XOR, planted $t$-SUM, and Assumption 5
-- statement:
--   All four assumptions are indistinguishability statements against QPT algorithms (uniform circuit families indexed by the number of samples $n$), with advantage $\mathsf{negl}(n)$.
--
--   1. **$\mathsf{LPN}_{g,\eta}$** (Assumption 1): $(A,As\oplus e)$ with $A\leftarrow\mathbb F_2^{n\times g(n)}$, $s\leftarrow\mathbb F_2^{g(n)}$, $e\leftarrow\mathrm{Ber}(n,\eta)$ is indistinguishable from $(A,u)$ with $u\leftarrow\mathbb F_2^n$.
--   2. **$\mathsf{LWE}_{g,q,\alpha}$** (Assumption 2): $(A,As+e \bmod q(n))$ with $A\leftarrow\mathbb Z_{q(n)}^{n\times g(n)}$, $s\leftarrow\mathbb Z_{q(n)}^{g(n)}$, $e\leftarrow D_{\mathbb Z,\alpha q(n)}^n$ is indistinguishable from $(A,u)$, $u\leftarrow\mathbb Z_{q(n)}^n$, where $D_{\mathbb Z,\sigma}$ gives $x\in\mathbb Z$ probability proportional to $\exp(-\pi x^2/\sigma^2)$.
--   3. **$\mathsf{XOR}_{m,t}$** (Assumption 3): a uniform $G\in\mathbb F_2^{n\times m(n)}$ is indistinguishable from $G$ sampled uniformly subject to $s^\top G=0$ for a uniform $s$ of Hamming weight $t(n)$.
--   4. **$\mathsf{SUM}_{g,q,t}$** (Assumption 4): a uniform $G\in\mathbb Z_{q(n)}^{n\times g(n)}$ is indistinguishable from $G$ sampled uniformly subject to $v^\top G=0$ for a uniform $v\in\{0,1\}^n$ of weight $t(n)$.
--
--   **Assumption 5** holds if at least one of the following holds:
--
--   - there is $\eta\in(0,\tfrac12)$ such that $\mathsf{LPN}_{g,\eta}$ holds for every $g(n)=\Omega(\log^2n)$;
--   - there are $\eta,\epsilon\in(0,\tfrac12)$ such that for every $t(n)=\Theta(\log n)$ both $\mathsf{LPN}_{n^\epsilon,\eta}$ and $\mathsf{XOR}_{2n^\epsilon,t}$ hold;
--   - $\mathsf{LWE}_{g,q,1/4}$ holds for $g(n)=\lfloor(\log n)^2/(2\log\log n)\rfloor$ and $q(n)=4\lceil2\sqrt{g(n)}\rceil+2$;
--   - both $\mathsf{LWE}_{g,q,1/4}$ and $\mathsf{SUM}_{g,q,t}$ hold for $g(n)=\lfloor\sqrt n\rfloor$, $q(n)=4\lceil2\sqrt{g(n)}\rceil+2$ and $t(n)=\lceil\log n\rceil$.
--
--   **Formalization Note** $n^\epsilon$ is $\lfloor n^\epsilon\rfloor$; $\log$ in items 3 and 4 is $\log_2$; $\Omega$ and $\Theta$ quantify over every function, computable or not, as printed. Elements of $\mathbb Z_q$ are written one-hot; only $e\bmod q$ enters, so $e$ is sampled through its residue law (the two Gaussian series converge). The planted distributions are uniform over the solution sets; where no planted vector exists (finitely many $n$) the planted probability is $0$, which $\mathsf{negl}$ ignores.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Assumptions 1–4, pp.19–20; Assumption 5, pp.20–21

import Mathlib
import Definitions.Def_QuantumPRC_OCirc
import Definitions.Def_QuantumPRC_Negligible

open Matrix

namespace QuantumPRC

/-- The uniform average `𝔼_{x ← S} f(x)` over a finite type. -/
noncomputable def avg {S : Type} [Fintype S] (f : S → ℝ) : ℝ :=
  (Fintype.card S : ℝ)⁻¹ * ∑ x, f x

/-- The uniform average over the elements of a finite set satisfying `P` (`0` if there are none). -/
noncomputable def avgOn {S : Type} [Fintype S] (P : S → Prop) [DecidablePred P] (f : S → ℝ) : ℝ :=
  ((Finset.univ.filter P).card : ℝ)⁻¹ * ∑ x ∈ Finset.univ.filter P, f x

/-- Code of a matrix over `𝔽₂` with `n` rows: its rows, in order. -/
def matCode {n g : ℕ} (M : Fin n → Bits g) : List Bool := (List.ofFn fun i => bits (M i)).flatten

/-- Matrix–vector product over `𝔽₂`. -/
def matVecB {n g : ℕ} (M : Fin n → Bits g) (s : Bits g) : Bits n := fun i => dotB (M i) s

/-- One-hot code of a residue `a < q`: the string of length `q` with a single `1` at position `a`. -/
def oneHot (q a : ℕ) : List Bool := List.ofFn fun i : Fin q => decide (i.val = a)

/-- Code of a vector over `ℤ_q` given by residues. -/
def zqVecCode {n : ℕ} (q : ℕ) (b : Fin n → ℕ) : List Bool := (List.ofFn fun i => oneHot q (b i)).flatten

/-- `Pr_{e ← Ber(n, η)}[e]`: each bit independently `1` with probability `η` (§3.7, p.19). -/
noncomputable def berProb {n : ℕ} (η : ℝ) (e : Bits n) : ℝ := η ^ wt e * (1 - η) ^ (n - wt e)

/-- **`LPN_{g,η}` assumption**, Assumption 1. Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
p.19: "For any QPT algorithm `A`, `| Pr_{A←𝔽₂^{n×g(n)}, s←𝔽₂^{g(n)}, e←Ber(n,η)} [1 ← A(A, As ⊕ e)] −
Pr_{A←𝔽₂^{n×g(n)}, u←𝔽₂^n} [1 ← A(A, u)] | ≤ negl(n)`."

**Formalization Note.** A QPT algorithm is a uniform family of oracle-free circuits indexed by the
number of samples `n`; its classical input is the code of `(A, b)` (rows of `A`, then `b`), of which
it reads as many bits as it has wires. -/
def LPN (g : ℕ → ℕ) (η : ℝ) : Prop :=
  ∀ A : ℕ → OCirc 0 0 0, IsUniformAdv (nIn := fun _ => 0) (nOut := fun _ => 0) A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n,
      |avg (fun M : Fin n → Bits (g n) => avg fun s : Bits (g n) => ∑ e : Bits n,
            berProb η e * (A n).accept Fin.elim0 (matCode M ++ bits (xorB (matVecB M s) e))) -
        avg (fun M : Fin n → Bits (g n) => avg fun u : Bits n =>
            (A n).accept Fin.elim0 (matCode M ++ bits u))| ≤ ν n

/-- The Gaussian weight `exp(−π x² / σ²)` of `D_{ℤ,σ}` (p.19). -/
noncomputable def gaussWeight (σ : ℝ) (x : ℤ) : ℝ := Real.exp (-Real.pi * (x : ℝ) ^ 2 / σ ^ 2)

/-- `Pr_{e ← D_{ℤ,σ}}[e ≡ a (mod q)]`: "For `σ > 0`, let `D_{ℤ,σ}` denote the distribution on `ℤ` that
assigns probability proportional to `exp(−πx²/σ²)` to each `x ∈ ℤ`" (p.19), reduced modulo `q`.

**Formalization Note.** Both series converge (Gaussian tails), so `tsum` is the true sum. -/
noncomputable def gaussModProb (q : ℕ) (σ : ℝ) (a : ℕ) : ℝ :=
  (∑' x : ℤ, if x % (q : ℤ) = (a : ℤ) then gaussWeight σ x else 0) / ∑' x : ℤ, gaussWeight σ x

/-- **`LWE_{g,q,α}` assumption**, Assumption 2. Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
p.20: "For any QPT algorithm `A`, `| Pr_{A←ℤ_{q(n)}^{n×g(n)}, s←ℤ_{q(n)}^{g(n)}, e←D^n_{ℤ,αq(n)}}
[1 ← A(A, As + e)] − Pr_{A←ℤ_{q(n)}^{n×g(n)}, u←ℤ_{q(n)}^n} [1 ← A(A, u)] | ≤ negl(n)`, where `As + e`
is reduced modulo `q(n)`."

**Formalization Note.** `ℤ_q` is `Fin q`; only `e mod q` enters `As + e mod q`, so `e` is sampled
through the law of `e mod q` coordinatewise. Elements of `ℤ_q` are written one-hot (length `q`); this
code and binary are interconvertible in time polynomial in `q`, which is polynomial in `n` in every
use. -/
def LWE (g q : ℕ → ℕ) (α : ℝ) : Prop :=
  ∀ A : ℕ → OCirc 0 0 0, IsUniformAdv (nIn := fun _ => 0) (nOut := fun _ => 0) A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n,
      |avg (fun M : Fin n → Fin (g n) → Fin (q n) => avg fun s : Fin (g n) → Fin (q n) =>
            ∑ e : Fin n → Fin (q n), (∏ i, gaussModProb (q n) (α * q n) (e i).val) *
              (A n).accept Fin.elim0
                ((List.ofFn fun i => zqVecCode (q n) fun j => (M i j).val).flatten ++
                  zqVecCode (q n) fun i => ((∑ j, (M i j).val * (s j).val) + (e i).val) % q n)) -
        avg (fun M : Fin n → Fin (g n) → Fin (q n) => avg fun u : Fin n → Fin (q n) =>
            (A n).accept Fin.elim0
              ((List.ofFn fun i => zqVecCode (q n) fun j => (M i j).val).flatten ++
                zqVecCode (q n) fun i => (u i).val))| ≤ ν n

/-- **`XOR_{m,t}` (planted XOR) assumption**, Assumption 3. Hsieh, Yamada, arXiv:2609.38986
(sha256 6901b59d…), p.20: uniform `G ∈ 𝔽₂^{n×m(n)}` versus `D(n, m(n), t(n))`: "1. Sample
`s ← {s ∈ 𝔽₂^n : wt(s) = t(n)}` […] 2. Sample a uniformly random matrix `G ∈ 𝔽₂^{n×m(n)}` subject to
`s⊤G = 0`. 3. Output `G`."

**Formalization Note.** `G` is stored by rows (`Fin n → Bits (m n)`), `s⊤G = 0` says that every
column has even weight on `supp(s)`. When `t(n) > n` there is no `s` and the planted probability is
`0`; this affects finitely many `n` in every use, which `negl` ignores. -/
def XORAssumption (m t : ℕ → ℕ) : Prop :=
  ∀ A : ℕ → OCirc 0 0 0, IsUniformAdv (nIn := fun _ => 0) (nOut := fun _ => 0) A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n,
      |avg (fun G : Fin n → Bits (m n) => (A n).accept Fin.elim0 (matCode G)) -
        avgOn (fun s : Bits n => wt s = t n) (fun s =>
          avgOn (fun G : Fin n → Bits (m n) => ∀ j, dotB s (fun i => G i j) = false)
            (fun G => (A n).accept Fin.elim0 (matCode G)))| ≤ ν n

/-- **`SUM_{g,q,t}` (planted `t`-SUM) assumption**, Assumption 4. Hsieh, Yamada, arXiv:2609.38986
(sha256 6901b59d…), p.20: "For functions `g, q, t : ℕ → ℕ` with `q(n) ≥ 2` and `1 ≤ t(n) ≤ n`", uniform
`G ∈ ℤ_{q(n)}^{n×g(n)}` versus `D_SUM(n, g(n), q(n), t(n))`: "1. Sample `v ← {v ∈ {0,1}^n : wt(v) = t(n)}`
[…] 2. Sample a uniformly random matrix `G ∈ ℤ_{q(n)}^{n×g(n)}` subject to `v⊤G = 0`. 3. Output `G`."

**Formalization Note.** The printed side conditions `q(n) ≥ 2`, `1 ≤ t(n) ≤ n` are where the
distribution is meaningful; outside them the planted probability is the average over an empty set,
`0`. In Assumption 5 they fail only for finitely many `n` (`n ≤ 1`), which `negl` ignores. -/
def SUMAssumption (g q t : ℕ → ℕ) : Prop :=
  ∀ A : ℕ → OCirc 0 0 0, IsUniformAdv (nIn := fun _ => 0) (nOut := fun _ => 0) A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ n,
      |avg (fun G : Fin n → Fin (g n) → Fin (q n) =>
            (A n).accept Fin.elim0 ((List.ofFn fun i => zqVecCode (q n) fun j => (G i j).val).flatten)) -
        avgOn (fun v : Bits n => wt v = t n) (fun v =>
          avgOn (fun G : Fin n → Fin (g n) → Fin (q n) =>
              ∀ j, (∑ i, (if v i then (G i j).val else 0)) % q n = 0)
            (fun G => (A n).accept Fin.elim0
              ((List.ofFn fun i => zqVecCode (q n) fun j => (G i j).val).flatten)))| ≤ ν n

/-- **Assumption 5** (post-quantum versions of [CG24, Lee26]). Hsieh, Yamada, arXiv:2609.38986
(sha256 6901b59d…), pp.20–21: "At least one of the following four statements is true.
• There exists a constant `η ∈ (0, 1/2)` such that, for any function `g(n) = Ω(log² n)`, the `LPN_{g,η}`
assumption holds.
• There exist constants `η ∈ (0, 1/2)` and `ϵ ∈ (0, 1/2)` such that, for any function `t(n) = Θ(log n)`,
both the `LPN_{n^ϵ,η}` assumption and the `XOR_{2n^ϵ,t}` assumption hold.
• There exist functions `g(n) = ⌊(log n)²/(2 log log n)⌋` and `q(n) = 4⌈2√g(n)⌉ + 2` such that the
`LWE_{g,q,1/4}` assumption holds.
• There exist functions `g(n) = ⌊√n⌋`, `q(n) = 4⌈2√g(n)⌉ + 2`, and `t(n) = ⌈log n⌉` such that both the
`LWE_{g,q,1/4}` assumption and the `SUM_{g,q,t}` assumption hold."

**Formalization Note.** `Ω(log² n)`: `∃ c > 0, ∀ᶠ n, c log² n ≤ g(n)`; `Θ(log n)`: two such constants.
Both quantify over every function, computable or not, as printed. `n^ϵ` is `⌊n^ϵ⌋` (a dimension).
In items 3 and 4, `log` is `log₂` (the base of [Lee26]); `log log n` uses Lean's `Real.logb`, whose
values at `n ≤ 2` are conventions that the asymptotic statement ignores. -/
def Assumption5 : Prop :=
  (∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∀ g : ℕ → ℕ,
      (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, c * Real.log n ^ 2 ≤ g n) → LPN g η) ∨
  (∃ η ϵ : ℝ, 0 < η ∧ η < 1 / 2 ∧ 0 < ϵ ∧ ϵ < 1 / 2 ∧ ∀ t : ℕ → ℕ,
      (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ᶠ n : ℕ in Filter.atTop, c₁ * Real.log n ≤ t n ∧ (t n : ℝ) ≤ c₂ * Real.log n) →
      LPN (fun n => ⌊(n : ℝ) ^ ϵ⌋₊) η ∧ XORAssumption (fun n => 2 * ⌊(n : ℝ) ^ ϵ⌋₊) t) ∨
  (let g : ℕ → ℕ := fun n =>
      ⌊Real.logb 2 n ^ 2 / (2 * Real.logb 2 (Real.logb 2 n))⌋₊
    let q : ℕ → ℕ := fun n => 4 * ⌈2 * Real.sqrt (g n)⌉₊ + 2
    LWE g q (1 / 4)) ∨
  (let g : ℕ → ℕ := fun n => Nat.sqrt n
    let q : ℕ → ℕ := fun n => 4 * ⌈2 * Real.sqrt (g n)⌉₊ + 2
    let t : ℕ → ℕ := fun n => ⌈Real.logb 2 n⌉₊
    LWE g q (1 / 4) ∧ SUMAssumption g q t)

end QuantumPRC


