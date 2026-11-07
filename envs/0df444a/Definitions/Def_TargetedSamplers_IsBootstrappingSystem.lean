-- Prove2me | Definitions.Def_TargetedSamplers_IsBootstrappingSystem
-- name    : TargetedSamplers_IsBootstrappingSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:31.590979+00:00
-- url     : https://prove2.me/theorems/41c0d49c-c1e4-471c-894c-f699296e8628
-- title:
--   $(d^\prime\times T^\prime)$ bootstrapping systems with block locality
-- statement:
--   Fix $d,T,\ell$, $f$, $d'$ and strings $B_1(x),\dots,B_{d'+1}(x)\in[A]^{T'}$ with $A=T'=2T(n)$, $n=|x|$. They form a **$(d'\times T')$ bootstrapping system** for $f$ if:
--
--   0. every entry lies in $\{0,\dots,2T-1\}$;
--   1. **Input layer.** An algorithm $A_{\mathrm{in}}(x,j)$ outputs $B_1(x)_j$ in time $O(\log T)$.
--   2. **Downward self-reducibility.** A nondeterministic algorithm $A_{\mathrm{DSR}}(x,i,j;w)$, $2\le i\le d'+1$, with witness $w\in\{0,1\}^{\log T}$ and oracle access to $B_{i-1}(x)$, outputs $\bot$ or $B_i(x)_j$ for every $w$, and outputs $B_i(x)_j$ for some $w$, in time $\mathrm{polylog}(T)$.
--   3. **Batch computability.** $A_{\mathrm{prep}}(1^n)$ outputs an advice string $\mathrm{adv}_n$ of length $\tilde O(d\cdot T)$ in time $\tilde O(d\cdot T)$. $A_{\mathrm{batch}}(1^n,i)$, given $\mathrm{adv}_n$ and oracle access to $B_{i-1}(x)$, outputs the whole layer $B_i(x)$ in time $\tilde O(T)$.
--   4. **Output layer.** $B_{d'+1}(x)_{2(i-1)}=B_{d'+1}(x)_{2(i-1)+1}=f(x)_i$ for $i\in[\ell(n)]$.
--   5. **Block locality.** For every block size $s\ge1$ and $2\le i\le d'+1$, running $A_{\mathrm{DSR}}$ of item 2 on all entries of a block of $B_i(x)$ queries positions of $B_{i-1}(x)$ that are covered by at most $5$ blocks.
--
--   **Formalization Note** Arguments are encoded with $\mathrm{enc}$ and outputs are in binary. $O(\log T)$ and $\tilde O$ are $\mathrm{budget}$, and $\mathrm{polylog}(T)$ is $K(\log_2T+1)^k$. Item 3 is stated for $i\ge2$ (printed $i\in[d'+1]$, but $B_0$ does not exist). Item 4 is stated for $i\in[\ell(n)]$ (printed $[n]$), since $f(x)_i$ is defined only for $i\le\ell(n)$. In item 5 the queried positions range over every witness, and blocks are those with index below $\lceil T'/s\rceil$.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Theorem 4.23, pp.30–31 (pdf pp.32–33)

import Mathlib
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers

/-- The oracle giving access to a string `B` over the alphabet `ℕ`: the query `q` (a position `j` in
little-endian binary) is answered by the entry `B_j`. -/
def entryOracle (B : ℕ → ℕ) : List Bool → ℕ := fun q => B (ofBitsLE q)

/-- A layer `B ∈ [2T]^{2T}` written out: entries `B_0, …, B_{2T−1}`, each in `log₂(2T)` bits. -/
def layerEncoding (T : ℕ) (B : ℕ → ℕ) : List Bool :=
  (List.range (2 * T)).flatMap fun j => bitsFixed (Nat.log 2 (2 * T)) (B j)

/-- `B` is a `(d′ × T′)` bootstrapping system for `f`, with `T′ = 2T`, alphabet `[A]`, `A = 2T`, and
circuit depth `d` (Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript
sha256 599d0a59…, Theorem 4.23, pp.30–31). Here `B x i j` is the entry `j` of the string `Bᵢ(x)`,
`i ∈ [d′(n) + 1]`, `j ∈ {0, …, 2T(n) − 1}`, `n = |x|`, and:

0. every entry lies in `[A] = {0, …, 2T − 1}`;
1. *(Input Layer)* an algorithm `A_in(x, j)` outputs `B₁(x)_j` in time `O(log T)`;
2. *(Downward self-reducibility)* a nondeterministic algorithm `A_DSR(x, i, j; w)`, `2 ≤ i ≤ d′ + 1`,
   with a witness `w ∈ {0,1}^{log T}` and oracle access to `B_{i−1}(x)`, outputs `⊥` or `Bᵢ(x)_j`
   for every `w`, outputs `Bᵢ(x)_j` for some `w`, and runs in time `polylog(T)`;
3. *(Batch-computability)* `A_prep(1ⁿ)` outputs an advice string `advₙ` of length `Õ(d·T)` in time
   `Õ(d·T)`, and `A_batch(1ⁿ, i)` with `advₙ` and oracle access to `B_{i−1}(x)` outputs the whole
   layer `Bᵢ(x)` in time `Õ(T)`;
4. *(Output Layer)* `B_{d′+1}(x)_{2(i−1)} = B_{d′+1}(x)_{2(i−1)+1} = f(x)ᵢ` for every `i ∈ [ℓ(n)]`;
5. *(Block Locality)* for every block size `s` and `2 ≤ i ≤ d′ + 1`, running `A_DSR` (item 2) on all
   entries of a block `k` of `Bᵢ(x)` queries positions of `B_{i−1}(x)` covered by at most 5 blocks.

**Formalization Note** Several inputs are one string (`encInput`); outputs are binary (`Nat.bits`,
or `bitsFixed` for a whole layer). `O(log T)` and `Õ(·)` are `budget`, `polylog(T)` is
`K · (log₂ T + 1)^k`. Item 3 is stated for `2 ≤ i`, since `B₀` does not exist (printed `i ∈ [d′+1]`).
Item 4 is stated for `i ∈ [ℓ(n)]` (printed `[n]`): `f(x)ᵢ` is defined only for `i ≤ ℓ(n)`. In item 5
the queried positions are taken over every witness `w`, and blocks are those with index
`< ⌈T′/s⌉`. -/
def IsBootstrappingSystem (d T ℓ : ℕ → ℕ) (f : List Bool → List Bool) (d' : ℕ → ℕ)
    (B : List Bool → ℕ → ℕ → ℕ) : Prop :=
  (∀ x : List Bool, ∀ i j, 1 ≤ i → i ≤ d' x.length + 1 → j < 2 * T x.length →
    B x i j < 2 * T x.length) ∧
  (∃ (Ain : Program) (K k : ℕ), ∀ x : List Bool, ∀ j, j < 2 * T x.length →
    Ain.RunsIn (Tapes.ofInput (encInput [j] [x]))
      (budget K k (Nat.log 2 (T x.length)) (T x.length)) (some (Nat.bits (B x 1 j)))) ∧
  (∃ (Adsr : Program) (K k : ℕ),
    (∀ x : List Bool, ∀ i j, 2 ≤ i → i ≤ d' x.length + 1 → j < 2 * T x.length →
      (∀ w : List Bool, w.length = Nat.log 2 (T x.length) →
        ∃ v, Adsr.RunsIn ⟨encInput [i, j] [x], [], w, entryOracle (B x (i - 1))⟩
            (K * (Nat.log 2 (T x.length) + 1) ^ k) v ∧
          (v = none ∨ v = some (Nat.bits (B x i j)))) ∧
      (∃ w : List Bool, w.length = Nat.log 2 (T x.length) ∧
        Adsr.Outputs ⟨encInput [i, j] [x], [], w, entryOracle (B x (i - 1))⟩
          (some (Nat.bits (B x i j))))) ∧
    (∀ s : ℕ, 0 < s → ∀ x : List Bool, ∀ i, 2 ≤ i → i ≤ d' x.length + 1 →
      ∀ kb, kb * s < 2 * T x.length →
      ∃ S : Finset ℕ, S.card ≤ 5 ∧ (∀ b ∈ S, b * s < 2 * T x.length) ∧
        ∀ j, kb * s ≤ j → j < (kb + 1) * s → j < 2 * T x.length →
        ∀ w : List Bool, w.length = Nat.log 2 (T x.length) →
        ∀ q ∈ Adsr.queriesAsked ⟨encInput [i, j] [x], [], w, entryOracle (B x (i - 1))⟩,
          ofBitsLE q / s ∈ S)) ∧
  (∃ (Aprep Abatch : Program) (K k : ℕ), ∀ n : ℕ, ∃ adv : List Bool,
    adv.length ≤ budget K k (d n * T n) n ∧
    Aprep.RunsIn (Tapes.ofInput (List.replicate n true)) (budget K k (d n * T n) n) (some adv) ∧
    ∀ x : List Bool, x.length = n → ∀ i, 2 ≤ i → i ≤ d' n + 1 →
      Abatch.RunsIn ⟨encInput [i] [List.replicate n true, adv], [], [], entryOracle (B x (i - 1))⟩
        (budget K k (T n) n) (some (layerEncoding (T n) (B x i)))) ∧
  (∀ x : List Bool, ∀ i, 1 ≤ i → i ≤ ℓ x.length →
    B x (d' x.length + 1) (2 * (i - 1)) = ((f x).getD (i - 1) false).toNat ∧
    B x (d' x.length + 1) (2 * (i - 1) + 1) = ((f x).getD (i - 1) false).toNat)

end TargetedSamplers


